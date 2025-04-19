import tkinter as tk
from tkinter import ttk
import os
import csv
from datetime import datetime

import logging
from App.ui.header import HeaderImage
from tkinter import filedialog, messagebox
import PIL.Image
import google.generativeai as genai
import json
import pyexiv2
import exifread
import re
import threading
import time
import speedtest
from queue import Queue
from concurrent.futures import ThreadPoolExecutor
from functools import partial
import psutil

class ImageMetadataGenerator(ttk.Frame):
    def __init__(self, parent, BASE_DIR, main_window):
        super().__init__(parent)
        self.parent = parent
        self.BASE_DIR = BASE_DIR
        self.main_window = main_window
        
        # Add temp folder path
        self.temp_folder = os.path.join(BASE_DIR, "Temp", "Images")
        if not os.path.exists(self.temp_folder):
            os.makedirs(self.temp_folder)
        
        # Configure window
        self.parent.title("Image Metadata Generator")
        
        # Set minimum size based on screen dimensions
        screen_width = self.parent.winfo_screenwidth()
        screen_height = self.parent.winfo_screenheight()
        min_width = int(screen_width * 0.8)
        min_height = int(screen_height * 0.8)
        self.parent.minsize(min_width, min_height)
        
        # Start maximized
        self.parent.state('zoomed')
        
        # Hapus transient() dan grab_set() agar window bisa diminimize
        # self.parent.transient()
        # self.parent.grab_set()
        
        # Create status bar first
        self.create_status_bar()
        
        # Load config
        self.config_path = os.path.join(BASE_DIR, "Database", "Config", "config.json")
        self.load_config()
        
        # Add header
        self.header = HeaderImage(self.parent, self.BASE_DIR)
        self.header.add_header_image()
        
        # Load window icon
        ICON_PATH = os.path.join(self.BASE_DIR, "Img", "icon", "rakikon.ico")
        if os.path.exists(ICON_PATH):
            self.parent.iconbitmap(ICON_PATH)
        else:
            self.update_status(f"Icon not found at: {ICON_PATH}")
        
        self.pack(fill='both', expand=True, padx=0, pady=(0,10))
        self.setup_ui()

        # Add file modification time tracking
        self.file_mtimes = {}
        
        # Fix AttributeError by initializing batch_results
        self.batch_results = {
            'success': 0,
            'failed': 0,
            'total_time': 0,
            'retries': 0,
            'processed': 0,
            'start_time': 0,
            'success_items': set(),
            'fastest_time': float('inf'),
            'slowest_time': 0,
            'generation_times': [],
            'last_total_time': 0  # Add last total processing time tracking
        }
        
        # Add UI throttling
        self._last_stats_update = 0
        self._stats_update_interval = 1  # 1 second between updates
        
        # Add preview caching
        self._preview_cache = {}
        self._max_preview_cache = 50
        
        # Add update debouncing
        self._pending_stats_update = None

        # Initialize speed test result
        self.network_speed = {'download': 0, 'upload': 0}
        
        # Start speed test in background
        self.speed_label.config(text="Internet Speed | Testing...")
        threading.Thread(target=self._initial_speed_test, daemon=True).start()

        # Start monitoring thread
        self._monitor_metadata_changes()

        # Add Ctrl+V binding for paste image
        self.parent.bind("<Control-v>", lambda e: self._paste_images())

        # Add drag and drop support
        try:
            import windnd
            windnd.hook_dropfiles(self.filelist_tree, func=self._handle_drag_drop)
        except ImportError:
            print("windnd not available - drag and drop disabled")

    def load_config(self):
        """Load configuration including API keys"""
        try:
            with open(self.config_path, 'r') as f:
                self.config = json.load(f)
                if 'gemini_api_key' not in self.config:
                    self.config['gemini_api_key'] = ''
                if 'gemini_api_keys' not in self.config:
                    self.config['gemini_api_keys'] = [self.config['gemini_api_key']]
                if 'default_gemini_model' not in self.config:
                    self.config['default_gemini_model'] = 'gemini-2.0-flash'
                if 'custom_prompt' not in self.config:
                    self.config['custom_prompt'] = ''
                if 'negative_prompt' not in self.config:
                    self.config['negative_prompt'] = ''
                if 'title_length' not in self.config:
                    self.config['title_length'] = {'min': '60', 'max': '100'}
                if 'tags_count' not in self.config:
                    self.config['tags_count'] = '50'
                if 'worker_count' not in self.config:
                    self.config['worker_count'] = '1'
                if 'default_resize' not in self.config:
                    self.config['default_resize'] = 'Full'
        except Exception as e:
            self.update_status(f"Failed to load config: {str(e)}")
            self.config = {
                'gemini_api_key': '',
                'gemini_api_keys': [],
                'default_gemini_model': 'gemini-2.0-flash',
                'custom_prompt': '',
                'negative_prompt': '',
                'title_length': {'min': '60', 'max': '100'},
                'tags_count': '50',
                'worker_count': '1',
                'default_resize': 'Full'
            }

    def save_config(self):
        """Save configuration including API key"""
        try:
            with open(self.config_path, 'w') as f, open(self.config_path, 'w') as f:
                json.dump(self.config, f, indent=4, sort_keys=True)
        except Exception as e:
            self.update_status(f"Failed to save config: {str(e)}")

    def _on_setting_change(self, event=None):
        """Save all settings to config"""
        try:
            # Get all current values
            self.config['custom_prompt'] = self.custom_prompt_var.get().strip()
            self.config['negative_prompt'] = self.neg_prompt_var.get().strip()
            self.config['title_length'] = {
                'min': self.min_title_var.get(),
                'max': self.max_title_var.get()
            }
            self.config['tags_count'] = self.tags_count_var.get()
            self.config['worker_count'] = self.worker_count_var.get()
            self.config['default_resize'] = self.resize_var.get()
            
            # Save to file
            self.save_config()
            self.update_status("Settings saved to config")
        except Exception as e:
            self.update_status(f"Failed to save settings: {e}")

    def create_status_bar(self):
        """Create status bar similar to main window"""
        self.status_frame = tk.Frame(self.parent, background="#f6f8f9")
        self.status_frame.pack(side="bottom", fill="x")

        self.status_bar = tk.Label(
            self.status_frame,
            text="Ready",
            anchor="w",
            background="#f6f8f9",
            foreground="#666",
            borderwidth=0,
            padx=10,
            pady=5
        )
        self.status_bar.pack(side="left", fill="x", expand=True)

    def update_status(self, message):
        """Update status bar message"""
        self.status_bar.config(text=message)

    def setup_ui(self):
        """Setup the tabbed UI"""
        # Konfigurasi ikon untuk semua tombol
        self.button_icons = {}
        icon_names = {
            'add_file': 'add_file.png',
            'open': 'open.png', 
            'reset': 'reset.png',
            'clear': 'clear.png',
            'rename': 'rename.png',
            'save': 'save.png',
            'ai': 'ai.png',
            'csv': 'load_csv.png',  # Add csv icon
            'paste': 'paste.png'  # Add paste icon
        }
        
        # Load semua ikon yang diperlukan
        for icon_id, icon_file in icon_names.items():
            icon_path = os.path.join(self.BASE_DIR, "Img", "icon", "ui", icon_file)
            self.button_icons[icon_id] = self._load_icon(icon_path)

        # Create main notebook
        self.notebook = ttk.Notebook(self)
        self.notebook.pack(fill='both', expand=True)

        # Konfigurasi tab dengan ikon 
        tabs_config = [
            ('generate_tab', 'Image Metadata Generator', 'add_file'),
            ('settings_tab', 'Settings', 'ai')
        ]

        # Konfigurasi tombol dengan ikon
        button_configs = {
            'load_buttons': [
                ('Load Images', self._load_multiple_images, 'add_file'),
                ('Load Folder', self._load_folder_images, 'open'),
                ('Paste Image', self._paste_images, 'paste'),  # Add paste button
                ('Clear Images', self._clear_images, 'reset'),
                ('Rename Images', self._rename_images, 'rename'),
                ('Export Metadata', self._rename_images, 'csv')
            ],
            'action_buttons': [
                ('Clear', self.clear_fields, 'reset'),
                ('Reset', self.reset_all, 'reset'), 
                ('Save', self.save_metadata, 'save'),
                ('Browse Image', self.browse_image, 'open'),
                ('Generate', self.generate_content, 'ai')
            ],
            'settings_buttons': [
                ('Configure Templates', self.configure_templates, 'open'),
                ('Preferences', self.configure_preferences, 'ai')
            ]
        }

        # Create tabs using config
        for attr_name, text, icon_id in tabs_config:
            tab = ttk.Frame(self.notebook)
            if icon_id in self.button_icons:
                self.notebook.add(tab, text=text, image=self.button_icons[icon_id], compound='left')
            else:
                self.notebook.add(tab, text=text)
            setattr(self, attr_name, tab)
            
            # Setup content for each tab
            if attr_name == 'generate_tab':
                self.setup_generator_tab(tab, button_configs)
            elif attr_name == 'settings_tab':
                self.setup_settings_tab(tab, button_configs['settings_buttons'])

        # Add context menu and shortcuts to treeview
        self.tree_context_menu = tk.Menu(self.filelist_tree, tearoff=0)
        self.tree_context_menu.add_command(label="Open File", command=self._open_selected_file)
        self.tree_context_menu.add_command(label="Open Folder", command=lambda: self._open_file_location())
        self.tree_context_menu.add_command(label="Copy Path", command=self._copy_file_path)
        self.tree_context_menu.add_command(label="Copy Title", command=self._copy_title)
        self.tree_context_menu.add_command(label="Copy Tags", command=self._copy_tags)
        self.tree_context_menu.add_command(label="Paste Image", command=self._paste_images)  # Add paste menu item
        self.tree_context_menu.add_separator()
        self.tree_context_menu.add_command(label="Rename", command=self._rename_images)
        self.tree_context_menu.add_command(label="Clear", command=self.clear_fields)
        self.tree_context_menu.add_command(label="Reset", command=self.reset_all)
        self.tree_context_menu.add_command(label="Save", command=self.save_metadata)
        self.tree_context_menu.add_command(label="Generate", command=self.generate_content)
        self.tree_context_menu.add_separator()
        self.tree_context_menu.add_command(label="Clear Metadata", command=self._clear_metadata)
        self.tree_context_menu.add_command(label="Remove From List", command=self._remove_from_list)

        # Bind context menu
        self.filelist_tree.bind("<Button-3>", self._show_context_menu)
        
        # Bind shortcuts
        self.parent.bind("<Control-e>", lambda e: self._open_file_location())
        self.parent.bind("<Control-c>", self._handle_copy)
        self.filelist_tree.bind("<Double-Button-1>", lambda e: self._open_file_location())

    def create_tab(self, parent, text, icon_path):
        """Create a tab with optional icon"""
        tab = ttk.Frame(parent)
        
        if os.path.exists(icon_path):
            try:
                icon = self._load_icon(icon_path)
                parent.add(tab, text=text, image=icon, compound='left')
                tab.icon = icon  # Keep reference
            except:
                parent.add(tab, text=text)
        else:
            parent.add(tab, text=text)
            
        return tab

    def _load_icon(self, path, size=(16, 16)):
        """Load and resize icon"""
        from PIL import Image, ImageTk
        with Image.open(path) as img:
            if img.mode != 'RGBA':
                img = img.convert('RGBA')
            img = img.resize(size, Image.Resampling.LANCZOS)
            return ImageTk.PhotoImage(img)

    def setup_generator_tab(self, tab, button_configs):
        # Main horizontal split
        main_frame = ttk.Frame(tab)
        main_frame.pack(fill='both', expand=True, padx=10, pady=10)
        
        # Fix column configuration to properly fill space
        main_frame.grid_columnconfigure(0, weight=1)  # Left side expands
        main_frame.grid_columnconfigure(1, minsize=300)  # Fixed 300px width
        main_frame.grid_rowconfigure(0, weight=1)  # Allow vertical expansion
        
        # --- LEFT SIDE (expandable) ---
        left_frame = ttk.Frame(main_frame)
        left_frame.grid(row=0, column=0, sticky='nsew', padx=(0,10))
        left_frame.grid_columnconfigure(0, weight=1)
        left_frame.grid_rowconfigure(1, weight=1)  # Give weight to filelist row
        
        # --- RIGHT SIDE (fixed 300px) ---
        right_frame = ttk.Frame(main_frame, width=300)
        right_frame.grid(row=0, column=1, sticky='nsew')
        right_frame.grid_propagate(False)  # Force fixed width
        right_frame.grid_columnconfigure(0, weight=1)
        right_frame.grid_rowconfigure(1, weight=1)  # Metadata expands
        right_frame.grid_rowconfigure(2, weight=0)  # Actions stay at bottom

        # Configuration at top left
        config_frame = ttk.LabelFrame(left_frame, text="Configuration")
        config_frame.grid(row=0, column=0, sticky='new', pady=(0, 8))
        config_frame.columnconfigure(0, weight=1)

        LABEL_WIDTH = 15  # Fixed width for all labels

        api_frame = ttk.Frame(config_frame)
        api_frame.pack(fill='x', padx=5, pady=5)
        api_left = ttk.Frame(api_frame)
        api_left.pack(side='left', fill='x', expand=True)
        ttk.Label(api_left, text="Gemini API Key:", width=LABEL_WIDTH, anchor='e').pack(side='left', padx=(0,5))
        
        # Replace entry with labels - updated styling
        self.api_key_display = ttk.Label(api_left, font=("Consolas", 12), anchor='w', foreground='#666666')
        self.api_key_display.pack(side='left', fill='x', expand=True)
        self._update_api_key_display(self.config.get('gemini_api_key', ''))

        api_right = ttk.Frame(api_frame)
        api_right.pack(side='left', fill='x', padx=(10,0))
        ttk.Label(api_right, text="Model:", width=LABEL_WIDTH, anchor='e').pack(side='left', padx=(0,5))
        self.model_var = tk.StringVar(value=self.config.get('default_gemini_model', 'gemini-2.0-flash'))
        models = self.config.get('gemini_models', ['gemini-2.0-flash'])
        self.model_combo = ttk.Combobox(api_right, textvariable=self.model_var, values=models, state='readonly', width=25, font=("Arial", 12))
        self.model_combo.pack(side='left')
        self.model_combo.bind('<<ComboboxSelected>>', self._on_model_change)

        # Add resize control after model combo
        resize_frame = ttk.Frame(api_right)
        resize_frame.pack(side='left', padx=(10,0))
        ttk.Label(resize_frame, text="Submit Size:", width=LABEL_WIDTH, anchor='e').pack(side='left', padx=(0,5))
        self.resize_var = tk.StringVar(value=self.config.get('default_resize', 'Full'))
        resize_values = ['Full'] + [f'{i}%' for i in range(10, 100, 10)]
        self.resize_combo = ttk.Combobox(resize_frame, textvariable=self.resize_var, values=resize_values, 
                                       state='readonly', width=10, font=("Arial", 12))
        self.resize_combo.pack(side='left')
        self.resize_combo.bind('<<ComboboxSelected>>', self._on_resize_change)

        # Add custom and negative prompts after API key config
        custom_prompt_frame = ttk.Frame(config_frame)
        custom_prompt_frame.pack(fill='x', padx=5, pady=5)
        ttk.Label(custom_prompt_frame, text="Custom Prompt:", width=LABEL_WIDTH, anchor='e').pack(side='left', padx=(0,5))
        self.custom_prompt_var = tk.StringVar(value=self.config.get('custom_prompt', ''))
        self.custom_prompt_entry = ttk.Entry(custom_prompt_frame, textvariable=self.custom_prompt_var, font=("Arial", 12))
        self.custom_prompt_entry.pack(side='left', fill='x', expand=True)
        self.custom_prompt_entry.bind('<FocusOut>', self._on_setting_change)
        
        neg_prompt_frame = ttk.Frame(config_frame)
        neg_prompt_frame.pack(fill='x', padx=5, pady=5)
        ttk.Label(neg_prompt_frame, text="Negative Prompt:", width=LABEL_WIDTH, anchor='e').pack(side='left', padx=(0,5))
        self.neg_prompt_var = tk.StringVar(value=self.config.get('negative_prompt', ''))
        self.neg_prompt_entry = ttk.Entry(neg_prompt_frame, textvariable=self.neg_prompt_var, font=("Arial", 12))
        self.neg_prompt_entry.pack(side='left', fill='x', expand=True)
        self.neg_prompt_entry.bind('<FocusOut>', self._on_setting_change)

        # Add length controls after negative prompt
        length_frame = ttk.Frame(config_frame)
        length_frame.pack(fill='x', padx=5, pady=5)
        
        # Title length inputs
        title_len_frame = ttk.Frame(length_frame)
        title_len_frame.pack(side='left', fill='x', expand=True)
        ttk.Label(title_len_frame, text="Title Length:", width=LABEL_WIDTH, anchor='e').pack(side='left', padx=(0,5))
        self.min_title_var = tk.StringVar(value=self.config.get('title_length', {}).get('min', '60'))
        ttk.Entry(title_len_frame, textvariable=self.min_title_var, width=4, font=("Arial", 12)).pack(side='left')
        ttk.Label(title_len_frame, text="-").pack(side='left', padx=2)
        self.max_title_var = tk.StringVar(value=self.config.get('title_length', {}).get('max', '100'))
        ttk.Entry(title_len_frame, textvariable=self.max_title_var, width=4, font=("Arial", 12)).pack(side='left')
        
        # Tags count and worker input
        controls_frame = ttk.Frame(length_frame)
        controls_frame.pack(side='right', fill='x', padx=(10,0))
        
        # Tags count
        tags_count_frame = ttk.Frame(controls_frame)
        tags_count_frame.pack(side='left', padx=(0,10))
        ttk.Label(tags_count_frame, text="Tags:", width=6, anchor='e').pack(side='left', padx=(0,5))
        self.tags_count_var = tk.StringVar(value=self.config.get('tags_count', '50'))
        ttk.Entry(tags_count_frame, textvariable=self.tags_count_var, width=4, font=("Arial", 12)).pack(side='left')
        
        # Worker count
        worker_frame = ttk.Frame(controls_frame)
        worker_frame.pack(side='left')
        ttk.Label(worker_frame, text="Workers:", width=8, anchor='e').pack(side='left', padx=(0,5))
        self.worker_count_var = tk.StringVar(value=self.config.get('worker_count', '1'))
        worker_entry = ttk.Entry(worker_frame, textvariable=self.worker_count_var, width=3, font=("Arial", 12))
        worker_entry.pack(side='left')
        
        # Bind worker count validation
        def validate_worker(P):
            if P == "": return True
            try:
                val = int(P)
                return val >= 1 and val <= 10
            except ValueError:
                return False
        vcmd = (self.register(validate_worker), '%P')
        worker_entry.configure(validate='key', validatecommand=vcmd)
        
        # Add worker count to settings save
        self.worker_count_var.trace_add('write', lambda *args: self._on_setting_change())

        # Bind all length controls to save on change
        for widget in [self.min_title_var, self.max_title_var, self.tags_count_var]:
            widget.trace_add('write', lambda *args: self._on_setting_change())

        # File list table (Treeview) moved up
        filelist_frame = ttk.LabelFrame(left_frame, text="Files to Generate Metadata")
        filelist_frame.grid(row=1, column=0, sticky='nsew', pady=(0, 8))
        filelist_frame.columnconfigure(0, weight=1)
        filelist_frame.rowconfigure(1, weight=1)  # Give weight to tree_frame

        # Add load buttons frame
        load_buttons_frame = ttk.Frame(filelist_frame)
        load_buttons_frame.pack(fill='x', padx=10, pady=5)
        
        # Create left and right button containers
        left_buttons = ttk.Frame(load_buttons_frame)
        left_buttons.pack(side='left')
        
        right_buttons = ttk.Frame(load_buttons_frame)
        right_buttons.pack(side='right')
        
        # Style untuk semua tombol normal
        style = ttk.Style()
        style.configure('Normal.TButton', padding=5)

        # Load buttons
        ttk.Button(left_buttons, text="Load Images", 
                  image=self.button_icons.get('add_file'),
                  compound='left',
                  style='Normal.TButton',
                  command=self._load_multiple_images).pack(side='left', padx=(0,5))
                  
        ttk.Button(left_buttons, text="Load Folder",
                  image=self.button_icons.get('open'),
                  compound='left',
                  style='Normal.TButton',
                  command=self._load_folder_images).pack(side='left', padx=(0,5))
                  
        ttk.Button(left_buttons, text="Paste Image",
                  image=self.button_icons.get('paste'),
                  compound='left',
                  style='Normal.TButton',
                  command=self._paste_images).pack(side='left', padx=(0,5))
                  
        ttk.Button(right_buttons, text="Clear Images",
                  image=self.button_icons.get('reset'),
                  compound='left',
                  style='Normal.TButton',
                  command=self._clear_images).pack(side='left', padx=(0,5))
                  
        ttk.Button(right_buttons, text="Rename Images",
                  image=self.button_icons.get('rename'),
                  compound='left',
                  style='Normal.TButton',
                  command=self._rename_images).pack(side='left', padx=(0,5))
        
        ttk.Button(right_buttons, text="Export Metadata",
                  image=self.button_icons.get('csv'),
                  compound='left',
                  style='Normal.TButton',
                  command=self._export_metadata_csv).pack(side='left')

        # Create frame for treeview + scrollbar first
        tree_frame = ttk.Frame(filelist_frame)
        tree_frame.pack(fill='both', expand=True, padx=10, pady=5)

        # Create treeview with expanded height
        self.filelist_tree = ttk.Treeview(tree_frame, 
            columns=("no", "filename", "ext", "title", "tags"), 
            show="headings",
            height=15
        )
        
        # Add hover style
        style = ttk.Style()
        style.map('Treeview',
            background=[('selected', '#0078d7'), ('hover', '#e5f3ff')],
            foreground=[('selected', 'white')]
        )
        
        # Bind hover events
        self.filelist_tree.bind('<Motion>', self._on_treeview_hover)
        self.filelist_tree.bind('<Leave>', self._on_treeview_leave)

        # Add vertical scrollbar
        vsb = ttk.Scrollbar(tree_frame, orient="vertical", command=self.filelist_tree.yview)
        self.filelist_tree.configure(yscrollcommand=vsb.set)

        # Now configure treeview style
        style = ttk.Style()
        style.configure(
            "Treeview.Heading",
            background="#e0e0e0",
            foreground="black",
            relief="flat",
            font=('Arial', 9, 'bold')
        )
        style.configure(
            "Treeview", 
            background="white",
            fieldbackground="white",
            rowheight=25
        )
        style.map('Treeview',
            background=[('selected', '#0078d7')],
            foreground=[('selected', 'white')]
        )

        # Add stripes to rows
        self.filelist_tree.tag_configure('oddrow', background='#f5f5f5')
        self.filelist_tree.tag_configure('evenrow', background='white')

        # Configure columns
        self.filelist_tree.heading("no", text="No")
        self.filelist_tree.heading("filename", text="Name") 
        self.filelist_tree.heading("ext", text="Ext")
        self.filelist_tree.heading("title", text="Title")
        self.filelist_tree.heading("tags", text="Tags")
        
        # Set column widths
        self.filelist_tree.column("no", width=40, minwidth=40, stretch=False, anchor="center")
        self.filelist_tree.column("filename", width=150, minwidth=100, stretch=True, anchor="w")
        self.filelist_tree.column("ext", width=40, minwidth=40, stretch=False, anchor="center") 
        self.filelist_tree.column("title", width=200, minwidth=150, stretch=True, anchor="w")
        self.filelist_tree.column("tags", width=200, minwidth=150, stretch=True, anchor="w")

        # Pack treeview and scrollbar
        self.filelist_tree.pack(side='left', fill='both', expand=True)
        vsb.pack(side='right', fill='y')

        # Store file paths for selection
        self.file_paths = {}
        
        # Bind selection events for treeview
        self.filelist_tree.bind('<ButtonRelease-1>', self._on_tree_select)

        # Add progress bar and info frames
        self.progress_frame = ttk.Frame(left_frame)
        self.progress_frame.grid(row=2, column=0, sticky='ew', pady=(0, 8))
        self.progress_frame.grid_columnconfigure(0, weight=1)

        # Network and generation info above progress bar
        self.network_frame = ttk.Frame(self.progress_frame)
        self.network_frame.pack(fill='x', pady=(0, 5))
        
        self.speed_label = ttk.Label(self.network_frame, text="Network: Checking...", anchor='w')
        self.speed_label.pack(side='left', padx=5)
        
        self.generation_label = ttk.Label(self.network_frame, text="", anchor='e')
        self.generation_label.pack(side='right', padx=5)

        # Progress bar
        self.progress_var = tk.DoubleVar(value=0.0)
        self.progress_bar = ttk.Progressbar(
            self.progress_frame, 
            mode='determinate',
            variable=self.progress_var
        )
        self.progress_bar.pack(fill='x', padx=5)

        self.progress_text = ttk.Label(
            self.progress_frame, 
            text="Ready",
            anchor='center'
        )
        self.progress_text.pack(fill='x', pady=(2,0))

        # Add statistics frame below progress bar
        self.stats_frame = ttk.Frame(self.progress_frame)
        self.stats_frame.pack(fill='x', pady=(5,0))
        
        # Left column - Total Files and Progress
        self.stats_left = ttk.Frame(self.stats_frame)
        self.stats_left.pack(side='left', padx=5)
        
        # Add total files and quality indicators above success/failed
        self.total_files_label = ttk.Label(
            self.stats_left, 
            text="Total Files: 0", 
            anchor='w',
        )
        self.total_files_label.pack(fill='x')
        
        self.quality_status_label = ttk.Label(
            self.stats_left, 
            text="Quality: N/A", 
            anchor='w',
        )
        self.quality_status_label.pack(fill='x')
        
        self.success_label = ttk.Label(self.stats_left, text="Success: 0", anchor='w')
        self.success_label.pack(fill='x')
        self.failed_label = ttk.Label(self.stats_left, text="Failed: 0", anchor='w')
        self.failed_label.pack(fill='x')
        
        # Center column - Times
        self.stats_center = ttk.Frame(self.stats_frame)
        self.stats_center.pack(side='left', expand=True, padx=5)
        
        # Create a single column for time stats
        time_stats = ttk.Frame(self.stats_center)
        time_stats.pack(fill='x', expand=True)
        
        # Combine all time stats into one column
        self.avg_time_label = ttk.Label(time_stats, text="Avg Generation: 0:00", anchor='w')
        self.avg_time_label.pack(fill='x')
        self.total_time_label = ttk.Label(time_stats, text="Total Processing: 0:00", anchor='w')
        self.total_time_label.pack(fill='x')
        self.fastest_time_label = ttk.Label(time_stats, text="Fastest: 0:00", anchor='w')
        self.fastest_time_label.pack(fill='x')
        self.slowest_time_label = ttk.Label(time_stats, text="Slowest: 0:00", anchor='w')
        self.slowest_time_label.pack(fill='x')
        
        # Right column - Workers/Retry
        self.stats_right = ttk.Frame(self.stats_frame)
        self.stats_right.pack(side='right', padx=5)
        self.worker_label = ttk.Label(self.stats_right, text="Workers: 1", anchor='e')
        self.worker_label.pack(fill='x')
        self.retry_label = ttk.Label(self.stats_right, text="Retries: 0", anchor='e')
        self.retry_label.pack(fill='x')
        self.scale_label = ttk.Label(self.stats_right, text="Adjust Submit Size", anchor='e')
        self.scale_label.pack(fill='x')
        self.scale_quality_label = ttk.Label(self.stats_right, text="", anchor='e', foreground='#666666', font=('Arial', 8))
        self.scale_quality_label.pack(fill='x')

        # Add resize quality descriptions
        self.resize_quality_messages = {
            'Full': "No data restrictions, highest image quality     \nMost accurate and stable analysis              \nLowest token usage with almost no retries      ",
            '90%':  "Very high accuracy with optimal data use        \nRetries are extremely rare                     \nHighly efficient and stable token usage        ",
            '80%':  "Balanced between data use and accuracy          \nRarely retries needed                          \nToken usage remains efficient                  ",
            '70%':  "Moderate data usage with good accuracy          \nOccasional retries may occur                   \nStill reasonably efficient token usage         ",
            '60%':  "Lower data use with decent accuracy             \nMore retries may start to appear               \nToken cost may begin to rise                   ",
            '50%':  "Half the data usage with fair accuracy          \nIncreased chance of retries                    \nToken consumption may be higher overall        ",
            '40%':  "Low data use with reduced accuracy              \nRetries expected more frequently               \nCan lead to increased total token usage        ",
            '30%':  "Very low data with limited accuracy             \nFrequent retries likely                         \nHigh total token usage from multiple attempts  ",
            '20%':  "Minimal data, accuracy becomes unstable         \nRetries are highly probable                    \nToken cost tends to be inefficient             ",
            '10%':  "Lowest data and poorest accuracy                \nRetries almost guaranteed on each request      \nToken usage may be extremely high overall      "
        }


        def update_resize_labels(resize_value):
            """Update both scale labels with resize info and quality message"""
            self.scale_label.config(text=f"Submit Rescale to: {resize_value}")
            quality_msg = self.resize_quality_messages.get(resize_value, "")
            self.scale_quality_label.config(text=quality_msg)
            # Save to config when value changes
            self.config['default_resize'] = resize_value
            self.save_config()
            
        # Update resize combo binding - combine label update and config save
        self.resize_combo.bind('<<ComboboxSelected>>', lambda e: (
            update_resize_labels(self.resize_var.get()),
            self._on_resize_change()
        ))

        # Set initial quality message
        update_resize_labels(self.resize_var.get())

        # Image preview at top right
        image_frame = ttk.LabelFrame(right_frame, text="Image")
        image_frame.grid(row=0, column=0, sticky='nsew')
        image_frame.columnconfigure(0, weight=1)
        ttk.Label(image_frame, text="Selected Image:").pack(anchor='w', padx=5)
        self.image_path_var = tk.StringVar()
        ttk.Entry(image_frame, textvariable=self.image_path_var, state='readonly').pack(fill='x', padx=5)
        ttk.Button(image_frame, text="Browse Image", 
                  image=self.button_icons.get('open'),
                  compound='left',
                  style='Normal.TButton',
                  command=self.browse_image).pack(anchor='w', padx=5, pady=5)
        
        # Create preview container with fixed size and prevent auto-resize
        preview_container = ttk.Frame(image_frame, width=300, height=300)
        preview_container.pack(fill='both', expand=True)
        preview_container.pack_propagate(False)  

        # Configure preview label
        self.image_preview_label = tk.Label(
            preview_container, 
            text="No preview",
            bg="#f6f8f9",
            relief="flat"
        )
        self.image_preview_label.pack(fill='both', expand=True)

        # Generated Metadata moved below image on right
        metadata_frame = ttk.LabelFrame(right_frame, text="Generated Metadata")
        metadata_frame.grid(row=1, column=0, sticky='nsew', pady=(8,0))
        metadata_frame.columnconfigure(0, weight=1)
        metadata_frame.rowconfigure(0, weight=0)  # Title fixed
        metadata_frame.rowconfigure(1, weight=1)  # Tags expand

        # Title area - no weight to keep fixed height
        title_row = ttk.Frame(metadata_frame)
        title_row.pack(fill='x', padx=5, pady=(5,0))
        ttk.Label(title_row, text="Title:").pack(side='left')
        self.title_char_count = ttk.Label(title_row, text="0/100 chars", foreground="#888")
        self.title_char_count.pack(side='right')
        self.title_text = tk.Text(metadata_frame, height=3, wrap='word')
        self.title_text.pack(fill='x', padx=5, pady=2)
        self.title_text.bind('<KeyRelease>', self.update_title_count)

        # Tags area with proper expansion
        tags_frame = ttk.Frame(metadata_frame)  
        tags_frame.pack(fill='both', expand=True, padx=5, pady=(5,0))
        
        tags_row = ttk.Frame(tags_frame)
        tags_row.pack(fill='x')
        ttk.Label(tags_row, text="Tags:").pack(side='left')
        self.tags_count = ttk.Label(tags_row, text="0/50 tags", foreground="#888")
        self.tags_count.pack(side='right')
        self.tags_text = tk.Text(tags_frame, wrap='word')
        self.tags_text.pack(fill='both', expand=True, pady=2)

        # Actions at bottom
        button_frame = ttk.LabelFrame(right_frame, text="Actions")
        button_frame.grid(row=2, column=0, sticky='ew', pady=(8,0))

        # Style untuk tombol normal
        style = ttk.Style()
        style.configure('Normal.TButton', padding=5) 

        # Tombol dengan padding normal (5)
        ttk.Button(button_frame, text="Clear", 
                  image=self.button_icons.get('clear'),
                  compound='left',
                  style='Normal.TButton',
                  command=self.clear_fields).pack(fill='x', padx=5, pady=(5,2))
                  
        ttk.Button(button_frame, text="Reset",
                  image=self.button_icons.get('reset'),
                  compound='left', 
                  style='Normal.TButton',
                  command=self.reset_all).pack(fill='x', padx=5, pady=2)
                  
        ttk.Button(button_frame, text="Save",
                  image=self.button_icons.get('save'),
                  compound='left',
                  style='Normal.TButton', 
                  command=self.save_metadata).pack(fill='x', padx=5, pady=2)
        
        # Configure style for bigger generate button only
        style.configure('Generate.TButton', font=('Arial', 12, 'bold'), padding=10)
        style.configure('Cancel.TButton', font=('Arial', 12, 'bold'), padding=10, foreground='red')
        
        # Generate button with larger padding and custom style
        self.generate_btn = ttk.Button(
            button_frame, 
            text="Generate",
            image=self.button_icons.get('ai'),
            compound='left',
            command=self.generate_content,
            style='Generate.TButton'
        )
        self.generate_btn.pack(fill='x', padx=5, pady=(15,10))  # Increased vertical padding
        
        # Add thread control variables
        self.generation_thread = None
        self.cancel_generation = False
        self.generation_queue = Queue()
        
        # Initial network speed label setup
        self.check_network_speed()

    def check_network_speed(self):
        """Initial network speed label setup"""
        self.speed_label.config(text="Internet Speed | Waiting for test...")

    def _initial_speed_test(self):
        """Run initial speed test once"""
        try:
            st = speedtest.Speedtest()
            st.get_best_server()
            
            # Get download speed
            download_speed = st.download() / 1_000_000  # Convert to Mbps
            self.network_speed['download'] = download_speed
            
            # Get upload speed
            upload_speed = st.upload() / 1_000_000  # Convert to Mbps
            self.network_speed['upload'] = upload_speed
            
            # Assess speed and create informative message
            if download_speed >= 100:
                speed_msg = "EXCELLENT - Perfect for batch processing"
            elif download_speed >= 50:
                speed_msg = "GOOD - Fast metadata generation"
            elif download_speed >= 20:
                speed_msg = "FAIR - Moderate generation speed"
            elif download_speed >= 10:
                speed_msg = "SLOW - Expect longer processing times"
            else:
                speed_msg = "POOR - Generation may be very slow"
            
            # Update label with speed assessment
            self.speed_label.config(
                text=f"Internet Speed | {speed_msg}\n↓{download_speed:.1f}Mbps ↑{upload_speed:.1f}Mbps"
            )
            
        except Exception as e:
            self.speed_label.config(text="Internet Speed | Test failed - Check your connection")
            print(f"Speed test error: {e}")

    def _clear_images(self):
        """Clear all images from the list and temp folder"""
        # Clear tree items first
        for item in self.filelist_tree.get_children():
            self.filelist_tree.delete(item)
            
        # Clear file paths dictionary
        self.file_paths.clear()
        
        # Clear temp folder
        try:
            for file in os.listdir(self.temp_folder):
                file_path = os.path.join(self.temp_folder, file)
                try:
                    if os.path.isfile(file_path):
                        os.unlink(file_path)
                except Exception as e:
                    print(f"Error deleting {file_path}: {e}")
        except Exception as e:
            print(f"Error clearing temp folder: {e}")
            
        # Reset UI elements
        self.image_path_var.set("")
        self.show_image_preview("")
        self.clear_fields()
        
        # Reset progress and stats
        self.progress_var.set(0)
        self.progress_text.config(text="Ready")
        self.generation_label.config(text="")
        
        # Reset processing status while maintaining resize setting
        current_resize = self.resize_var.get()  # Store current resize setting
        self.batch_results = {
            'success': 0,
            'failed': 0,
            'total_time': 0,
            'retries': 0,
            'processed': 0,
            'start_time': 0,
            'success_items': set(),
            'fastest_time': float('inf'),
            'slowest_time': 0,
            'generation_times': [],
            'last_total_time': 0
        }
        
        # Reset statistics display
        self.success_label.config(text="Success: 0")
        self.failed_label.config(text="Failed: 0")
        self.avg_time_label.config(text="Avg Generation: 0:00")
        self.total_time_label.config(text="Total Processing: 0:00")
        self.fastest_time_label.config(text="Fastest: 0:00")
        self.slowest_time_label.config(text="Slowest: 0:00")
        self.worker_label.config(text=f"Workers: {self.worker_count_var.get()}")
        self.retry_label.config(text="Retries: 0")
        self.total_files_label.config(text="Total Files: 0")
        self.quality_status_label.config(text="Quality: N/A")
        self.scale_label.config(text=f"Submit Rescale to: {current_resize}")  # Maintain resize setting display
        
        self.update_status("All images and statistics cleared")

    def _paste_images(self):
        """Handle pasting images from clipboard"""
        try:
            # Get image from clipboard
            from PIL import ImageGrab
            img = ImageGrab.grabclipboard()
            
            if img is None:
                self.update_status("No image in clipboard")
                return
                
            # Generate unique filename
            timestamp = time.strftime("%Y%m%d-%H%M%S")
            filename = f"pasted-image-{timestamp}.png"
            filepath = os.path.join(self.temp_folder, filename)
            
            # Save image
            img.save(filepath, "PNG")
            
            # Use existing function to add to tree
            self._add_files_to_tree([filepath])
            
            self.update_status(f"Image pasted and saved as {filename}")
            
        except Exception as e:
            self.update_status(f"Error pasting image: {str(e)}")

    def _handle_drag_drop(self, files):
        """Handle files dropped into treeview"""
        # Filter only image files
        image_files = [f.decode('gbk') for f in files if f.decode('gbk').lower().endswith(('.jpg', '.jpeg', '.png', '.gif', '.bmp'))]
        if image_files:
            self._add_files_to_tree(image_files)

    def generate_content(self):
        """Handle generation start/cancel"""
        if self.generation_thread and self.generation_thread.is_alive():
            # Cancel ongoing generation
            self.cancel_generation = True
            self.generate_btn.config(state='disabled')
            self.update_status("Canceling generation...")
            return
            
        # Check if image is selected
        tree_items = self.filelist_tree.get_children()
        selected_item = self.filelist_tree.selection()
        
        if not self.image_path_var.get() and not selected_item:
            self.update_status("Error: No image selected")
            messagebox.showerror("Error", "Please select an image", parent=self.parent)
            return
            
        # Start new generation
        self.cancel_generation = False
        
        if tree_items and selected_item:
            choice = messagebox.askquestion(
                "Generate Options",
                "Do you want to generate metadata for:\n\n"
                "Yes = Generate for selected image only\n"
                "No = Generate for all images in list",
                icon='question',
                parent=self.parent
            )
            
            if choice == 'yes':
                self.generation_thread = threading.Thread(
                    target=self._generate_single,
                    args=(self.file_paths[selected_item[0]], True)
                )
                # Change button to cancel only after thread is created
                self.generate_btn.config(text="Cancel", style='Cancel.TButton')
                self.generation_thread.start()
                
            else:
                self.generation_thread = threading.Thread(
                    target=self._generate_batch,
                    args=(tree_items,)
                )
                # Change button to cancel only after thread is created
                self.generate_btn.config(text="Cancel", style='Cancel.TButton')
                self.generation_thread.start()
                
        else:
            self.generation_thread = threading.Thread(
                target=self._generate_single,
                args=(self.image_path_var.get(), True)
            )
            # Change button to cancel only after thread is created
            self.generate_btn.config(text="Cancel", style='Cancel.TButton')
            self.generation_thread.start()
            
        self._check_generation_complete()

    def _check_generation_complete(self):
        """Monitor generation thread completion"""
        if self.generation_thread and self.generation_thread.is_alive():
            self.after(100, self._check_generation_complete)
        else:
            # Only reset button if generation was actually started
            if self.generation_thread:
                self.generate_btn.config(text="Generate", style='Generate.TButton')
                self.generate_btn.config(state='normal')
                if self.cancel_generation:
                    self.update_status("Generation canceled")
                    self.progress_var.set(0)
            self.generation_thread = None

    def _generate_single(self, image_path, update_ui=False, api_key=None):
        """Generate metadata for single image with specific API key"""
        try:
            start_time = time.time()
            
            if update_ui:
                self.progress_text.config(text="Configuring API...")
                self.progress_var.set(20)
                self.update_idletasks()

            # Use provided API key or default
            key_to_use = api_key or self.config['gemini_api_key']
            genai.configure(api_key=key_to_use)
            model = genai.GenerativeModel(self.model_var.get())
            
            if self.cancel_generation:
                return False
                
            if update_ui:
                self.progress_text.config(text="Loading image...")
                self.progress_var.set(40)
                self.update_idletasks()
            
            # Open and resize image if needed
            image = PIL.Image.open(image_path)
            resize_value = self.resize_var.get()
            
            if resize_value != 'Full':
                # Extract percentage and convert to float
                scale = float(resize_value.strip('%')) / 100
                
                # Calculate new dimensions
                new_width = int(image.width * scale)
                new_height = int(image.height * scale)
                
                # Create temp filename with scale percentage
                temp_filename = f"temp_resized_to_{resize_value.strip('%')}_{os.path.basename(image_path)}"
                temp_path = os.path.join(self.temp_folder, temp_filename)
                
                # Update scale label
                self.scale_label.config(text=f"Submit Rescale to: {resize_value}")
                
                # Resize and save
                resized_img = image.resize((new_width, new_height), PIL.Image.Resampling.LANCZOS)
                resized_img.save(temp_path, quality=95)
                
                # Use resized image for generation
                image = PIL.Image.open(temp_path)
            else:
                self.scale_label.config(text="Adjust Submit Size")

            if self.cancel_generation:
                return False

            if update_ui:
                self.progress_text.config(text="Generating content...")
                self.progress_var.set(60)
                self.update_idletasks()

            # Get base prompt with settings
            prompt = self._build_generation_prompt()
            
            # Track generation time
            gen_start = time.time()
            response = model.generate_content([prompt, image])
            gen_time = time.time() - gen_start
            
            if self.cancel_generation:
                return False
                
            if update_ui:
                self.progress_text.config(text="Applying changes...")
                self.progress_var.set(80)
                self.update_idletasks()

            parsed_result = self._parse_response(response.text)
            
            if parsed_result:
                self.generation_queue.put({
                    'title': parsed_result['title'],
                    'tags': parsed_result['tags']
                })
                
                if update_ui:
                    self._update_ui_with_result(parsed_result)
                    total_time = time.time() - start_time
                    self.generation_label.config(
                        text=f"Last gen: {gen_time:.1f}s (Total: {total_time:.1f}s)"
                    )
                return True

        except Exception as e:
            if update_ui:
                self.progress_var.set(0)
                self.progress_text.config(text=f"Error: {str(e)}")
            return False

    def _format_time(self, seconds):
        """Format seconds into MM:SS"""
        minutes = int(seconds // 60)
        seconds = int(seconds % 60)
        return f"{minutes:02d}:{seconds:02d}"

    def _format_time_diff(self, current, last):
        """Format time difference with +/- prefix"""
        if last is None or current is None:
            return ""
        diff = current - last
        sign = '+' if diff >= 0 else ''
        return f" ({sign}{self._format_time(abs(diff))})" if last > 0 else ""

    def _update_generation_stats(self, current_count, total, filename=None, avg_time=None, gen_time=None):
        """Centralized method to update all generation statistics"""
        # Update progress
        progress = min(((current_count + 1) / total * 100), 100) if total > 0 else 0
        self.progress_var.set(progress)
        
        # Update processing status - show only filename
        if filename:
            self.progress_text.config(text=f"Processing: {filename}")
        
        # Update timing information
        if current_count >= 0:
            elapsed_time = self.batch_results['total_time']
            if total > 0 and current_count < total:
                avg_per_item = elapsed_time / (current_count + 1)
                remaining_time = (total - (current_count + 1)) * avg_per_item
                status = f"Elapsed: {self._format_time(elapsed_time)} | Remaining: {self._format_time(remaining_time)}"
            else:
                status = f"Elapsed: {self._format_time(elapsed_time)}"
                
            if avg_time is not None:
                status += f" | Avg: {self._format_time(avg_time)}"
            self.generation_label.config(text=status)

    def _generate_batch(self, items):
        """Generate metadata for multiple images using multiple API keys"""
        total = len(items)
        batch_start_time = time.time()
        # Store current total_time before resetting batch_results
        last_time = self.batch_results.get('total_time', 0)
        
        self.batch_results = {
            'success': 0,
            'failed': 0,
            'total_time': 0,
            'last_total_time': last_time,  # Preserve last time
            'retries': 0,
            'processed': 0,
            'start_time': batch_start_time,
            'success_items': set(),
            'fastest_time': float('inf'),
            'slowest_time': 0,
            'generation_times': []
        }
        
        # Reset UI for batch processing
        self.title_text.delete(1.0, tk.END)
        self.tags_text.delete(1.0, tk.END)
        
        try:
            workers = max(1, min(10, int(self.worker_count_var.get())))
        except:
            workers = 1
            
        # Reset statistics display
        def reset_stats():
            self.success_label.config(text="Success: 0")
            self.failed_label.config(text="Failed: 0")
            self.avg_time_label.config(text="Avg Generation: 0:00")
            self.total_time_label.config(text="Total Processing: 0:00")
            self.fastest_time_label.config(text="Fastest: 0:00")
            self.slowest_time_label.config(text="Slowest: 0:00")
            self.worker_label.config(text=f"Workers: {workers}")
            self.retry_label.config(text="Retries: 0")
            self.generation_label.config(text="")
            self.total_files_label.config(text="Total Files: 0")
            self.quality_status_label.config(text="Quality: N/A")
            
        self.after(0, reset_stats)
        
        # Get available API keys
        api_keys = self.config.get('gemini_api_keys', [self.config['gemini_api_key']])
        api_keys = [key for key in api_keys if key.strip()]  # Filter out empty keys
        
        if not api_keys:
            self.update_status("Error: No valid API keys found")
            return
        
        # Calculate workers per API key
        total_workers = max(1, min(10, int(self.worker_count_var.get())))
        workers_per_key = max(1, total_workers // len(api_keys))
        
        def process_items(items_to_process):
            if not items_to_process or self.cancel_generation:
                return
                
            retry_items = []
            
            # Create a thread pool for each API key
            with ThreadPoolExecutor(max_workers=len(api_keys) * workers_per_key) as executor:
                futures = []
                
                # Distribute items across API keys
                for i, item in enumerate(items_to_process):
                    if self.cancel_generation:
                        break
                    # Rotate through API keys
                    api_key = api_keys[i % len(api_keys)]
                    futures.append(
                        executor.submit(
                            self._process_batch_item, 
                            item, 
                            total,
                            api_key
                        )
                    )
                
                # Wait for all futures to complete
                for future in futures:
                    try:
                        if self.cancel_generation:
                            break
                        result = future.result()
                        if result and not result.get('success'):
                            if result.get('item'):
                                retry_items.append(result.get('item'))
                    except Exception as e:
                        logging.error(f"Worker thread error: {str(e)}")
                
                # Update total time
                current_time = time.time()
                self.batch_results['total_time'] = current_time - batch_start_time
            
            # Handle retries if needed
            if retry_items and not self.cancel_generation:
                self.batch_results['retries'] += len(retry_items)
                time.sleep(1)  # Brief pause before retries
                process_items(retry_items)

        # Update worker label to show active API keys
        self.worker_label.config(
            text=f"Workers: {total_workers} ({len(api_keys)} API keys)"
        )
        
        process_items(items)
        
        # Add verification phase
        if not self.cancel_generation:
            retry_items = self._verify_batch_results(items)
            
            if retry_items:
                self.update_status(f"Regenerating {len(retry_items)} items that failed quality check...")
                self.batch_results['retries'] += len(retry_items)
                process_items(retry_items)
                # Verify again after retries
                retry_items = self._verify_batch_results(items)
                
            def update_final_status():
                total_time = time.time() - self.batch_results['start_time']
                last_time = self.batch_results.get('last_total_time', 0)
                self.batch_results['total_time'] = total_time
                
                time_diff = self._format_time_diff(total_time, last_time)
                time_display = f"Total Processing: {self._format_time(total_time)}{time_diff}"
                if last_time > 0:
                    time_display += f" Last {self._format_time(last_time)}"
                
                quality_status = "✓ All quality checks passed" if not retry_items else f"⚠ {len(retry_items)} items need review"
                final_status = (
                    f"Complete: {self.batch_results['success']}/{total} files "
                    f"({self.batch_results['success']/total*100:.1f}%) - {quality_status}"
                )
                self.progress_var.set(100)
                self.progress_text.config(text=final_status)
                self.generation_label.config(text=time_display)
                self.update_status(f"Batch processing complete - Success: {self.batch_results['success']}/{total} files")
            
            self.after(100, update_final_status)

    def _process_batch_item(self, item, total, api_key):
        """Process single item in batch with specific API key"""
        # Find key index for display
        key_index = self.config.get('gemini_api_keys', []).index(api_key) if api_key in self.config.get('gemini_api_keys', []) else None
        
        # Update API key display
        self.after(0, lambda: self._update_api_key_display(api_key, key_index))
        
        # Skip if already successful
        if item in self.batch_results['success_items']:
            return {'success': True, 'item': item}
            
        result = {'success': False, 'item': item}
        
        if self.cancel_generation or not item:
            return result
            
        try:
            file_path = self.file_paths[item]
            filename = os.path.basename(file_path)
            
            self.update_status(f"Processing: {filename} (using API key: ...{api_key[-8:]})")
            
            # Update processed count before UI updates
            current_count = self.batch_results['processed']
            
            # Thread-safe UI updates consolidated
            def update_ui():
                self.filelist_tree.selection_set(item)
                self.filelist_tree.see(item)
                self.image_path_var.set(file_path)
                self.show_image_preview(file_path)
                
                # Calculate elapsed time
                elapsed = time.time() - self.batch_results['start_time']
                if current_count > 0:
                    avg_time = elapsed / current_count
                    remaining = (total - current_count) * avg_time
                    status = f"Elapsed: {self._format_time(elapsed)} | Remaining: {self._format_time(remaining)}"
                else:
                    status = f"Elapsed: {self._format_time(elapsed)}"
                
                self.generation_label.config(text=status)
                self.progress_text.config(text=f"Processing: {filename}")
                progress = (current_count / total * 100)
                self.progress_var.set(progress)
                self._update_batch_stats()  # Update stats after UI changes
                
            self.after(0, update_ui)
            
            # Place increment after UI update
            self.batch_results['processed'] += 1

            start_time = time.time()
            if self._generate_single(file_path, update_ui=False, api_key=api_key):
                max_retries = 3  # Maximum number of retries for bad tags
                current_try = 0
                
                while current_try < max_retries:
                    try:
                        result = self.generation_queue.get(timeout=30)
                        
                        # Pre-process tags to ensure they're in correct format
                        if isinstance(result['tags'], str):
                            result['tags'] = [t.strip() for t in result['tags'].split(',') if t.strip()]
                        elif isinstance(result['tags'], (list, tuple)):
                            result['tags'] = [t.strip() for t in result['tags'] if t.strip()]
                        else:
                            current_try += 1
                            continue
                        
                        # Now validate the processed tags
                        if self._validate_tags_quality(result['tags']):
                            def update_success():
                                try:
                                    gen_time = time.time() - start_time
                                    self.batch_results['generation_times'].append(gen_time)
                                    self.batch_results['fastest_time'] = min(self.batch_results['fastest_time'], gen_time)
                                    self.batch_results['slowest_time'] = max(self.batch_results['slowest_time'], gen_time)
                                    self._update_metadata_and_ui(result, file_path)
                                    self.batch_results['success'] += 1
                                    self.batch_results['success_items'].add(item)  # Mark as successful
                                    elapsed_time = time.time() - self.batch_results['start_time']
                                    self.batch_results['total_time'] = elapsed_time
                                    avg_time = elapsed_time / self.batch_results['success']
                                    self.avg_time_label.config(text=f"Avg Generation: {self._format_time(avg_time)}")
                                    self.total_time_label.config(text=f"Total Processing: {self._format_time(elapsed_time)}")
                                    self.fastest_time_label.config(text=f"Fastest: {self._format_time(self.batch_results['fastest_time'])}")
                                    self.slowest_time_label.config(text=f"Slowest: {self._format_time(self.batch_results['slowest_time'])}")
                                    success_count = self.batch_results['success']
                                    failed_count = self.batch_results['failed']
                                    worker_count = int(self.worker_count_var.get())
                                    retry_count = self.batch_results['retries']
                                    self.success_label.config(text=f"Success: {success_count}")
                                    self.failed_label.config(text=f"Failed: {failed_count}")
                                    self.worker_label.config(text=f"Workers: {worker_count}")
                                    self.retry_label.config(text=f"Retries: {retry_count}")
                                    self.generation_label.config(
                                        text=f"Processing: {filename} ({(current_count + 1)}/{total})"
                                    )
                                    self.update_status(f"Successfully processed {filename}")
                                    self._update_batch_stats()  # Update stats after success
                                    result['success'] = True
                                except Exception as e:
                                    self._handle_batch_error(filename, str(e))
                                    result['success'] = False
                            
                            self.after(0, update_success)
                            break  # Break the retry loop if tags are good
                            
                        else:
                            # Bad tags quality, retry generation
                            current_try += 1
                            self.batch_results['retries'] += 1
                            
                            if current_try < max_retries:
                                self.update_status(f"Retrying {filename} due to poor tag quality (try {current_try + 1})")
                                if self._generate_single(file_path, update_ui=False, api_key=api_key):
                                    continue  # Try again
                                else:
                                    self.progress_var.set(95)  # Keep progress at 95% during retries
                                    self.progress_text.config(
                                        text=f"Retrying {filename} - Quality check failed (Attempt {current_try + 1}/{max_retries})"
                                    )
                            else:
                                self._handle_batch_error(filename, "Max retries reached - poor tag quality")
                                break
                            
                    except Exception as e:
                        self._handle_batch_error(filename, str(e))
                        break
                        
            else:
                self.batch_results['failed'] += 1
                self.update_status(f"Failed to generate content for {filename}")
                self._update_batch_stats()  # Update stats after failure
                
        except Exception as e:
            self._handle_batch_error(filename, str(e))
            self.update_status(f"Error: {str(e)}")
            self._update_batch_stats()  # Update stats after error
        
        return result

    def _validate_tags_quality(self, tags):
        """Validate tags quality with improved handling"""
        if not tags:
            return False
        
        # Normalize tags to list
        if isinstance(tags, str):
            tags = [t.strip() for t in tags.split(',')]
            
        # Clean and validate tags
        normalized_tags = []
        poor_quality_tags = []
        
        for tag in tags:
            if not isinstance(tag, str):
                continue
                
            # Basic cleaning
            clean_tag = tag.strip()
            clean_tag = ' '.join(clean_tag.split())  # Normalize spaces
            
            if not clean_tag:
                continue
                
            # Skip if already processed
            if clean_tag in normalized_tags or clean_tag in poor_quality_tags:
                continue
                
            # Quality checks
            words = clean_tag.split()
            
            # Check for poor quality conditions
            if any([
                # Single character tag
                len(clean_tag) == 1,
                # Single letter word (but allow multi-word tags that contain single letters)
                len(words) == 1 and len(words[0]) <= 2,
                # Common articles/prepositions as single words
                len(words) == 1 and clean_tag.lower() in ['a', 'an', 'the', 'in', 'on', 'at', 'to', 'of', 'for', 'by'],
                # Just numbers
                clean_tag.isdigit(),
                # No letters at all
                not any(c.isalpha() for c in clean_tag)
            ]):
                poor_quality_tags.append(clean_tag)
                continue
                
            normalized_tags.append(clean_tag)
        
        # Final validation
        min_required = max(3, int(int(self.tags_count_var.get()) * 0.25))  # At least 25% of requested or 3 tags
        
        if len(normalized_tags) < min_required:
            if poor_quality_tags:
                print(f"Poor quality tags ({len(normalized_tags)} valid / {min_required} required)")
                print(f"Poor quality tags found: {', '.join(poor_quality_tags)}")
            return False
            
        return True

    def _verify_batch_results(self, items):
        """Verify all generated metadata meets requirements"""
        total = len(items)
        verified_count = 0
        retry_items = []
        
        self.progress_var.set(0)
        self.progress_text.config(text="Verifying metadata quality...")
        
        min_title_len = int(self.min_title_var.get())
        max_title_len = int(self.max_title_var.get())
        min_tags = int(self.tags_count_var.get())
        
        for i, item in enumerate(items):
            # Skip already successful items
            if item in self.batch_results['success_items']:
                verified_count += 1
                continue
                
            values = self.filelist_tree.item(item)['values']
            title = values[3]
            tags = [t.strip() for t in values[4].split(',') if t.strip()]
            
            needs_retry = False
            # Verify title length
            if not title or len(title) < min_title_len or len(title) > max_title_len:
                needs_retry = True
                print(f"Title length issue: {len(title) if title else 0} chars")
                
            # Verify tags count and quality
            if not tags or len(tags) < min_tags:
                needs_retry = True
                print(f"Tags count issue: {len(tags)} tags")
            elif not self._validate_tags_quality(tags):
                needs_retry = True
                print("Tags quality check failed")
                
            if needs_retry:
                retry_items.append(item)
            else:
                verified_count += 1
                self.batch_results['success_items'].add(item)  # Mark as successful
                
            # Update verification progress
            progress = ((i + 1) / total * 100)
            self.progress_var.set(progress)
            self.progress_text.config(text=f"Verifying: {verified_count}/{total} files")
            self.update()
            
        return retry_items

    def _update_metadata_and_ui(self, result, file_path):
        """Centralized method to update metadata and UI"""
        self.title_text.delete(1.0, tk.END)
        self.title_text.insert(1.0, result['title'])
        self.tags_text.delete(1.0, tk.END)
        self.tags_text.insert(1.0, ', '.join(result['tags']))
        
        title = self.update_title_count()
        tag_list = self.update_tags_count()
        self._save_metadata_to_file(file_path, title, tag_list)
        self._update_tree_item(file_path, title, ', '.join(tag_list))

    def _update_batch_stats(self):
        """Update stats with throttling"""
        # Skip updates that are too frequent
        current_time = time.time()
        if hasattr(self, '_last_stats_update') and \
           current_time - self._last_stats_update < self._stats_update_interval:
            return
        
        self._last_stats_update = current_time
        
        # Cancel any pending update
        if self._pending_stats_update:
            self.after_cancel(self._pending_stats_update)
        
        def _do_update():
            try:
                # Get all stats at once
                total = len(self.filelist_tree.get_children())
                success = len(self.batch_results.get('success_items', set()))
                failed = self.batch_results['failed']
                retries = self.batch_results['retries']
                processed = success + failed
                
                # Calculate quality metrics
                if processed > 0:
                    quality_pct = (success / processed) * 100
                    if quality_pct >= 90:
                        quality_status = f"Excellent ({quality_pct:.1f}%)"
                    elif quality_pct >= 75:
                        quality_status = f"Good ({quality_pct:.1f}%)"
                    elif quality_pct >= 50:
                        quality_status = f"Fair ({quality_pct:.1f}%)"
                    else:
                        quality_status = f"Poor ({quality_pct:.1f}%)"
                    
                    if retries > 0:
                        quality_status += f" | {retries} retries"
                else:
                    quality_status = "Quality: Waiting..."
                
                # Prepare all updates
                updates = [
                    (self.total_files_label, f"Total Files: {total} (Remaining: {total-(success+failed)})"),
                    (self.success_label, f"Success: {success}/{total} ({success/total*100:.1f}%)" if total else "Success: 0"),
                    (self.failed_label, f"Failed: {failed}/{total} ({failed/total*100:.1f}%)" if total else "Failed: 0"),
                    (self.worker_label, f"Workers: {self.worker_count_var.get()}"),
                    (self.retry_label, f"Retries: {retries}"),
                    (self.quality_status_label, f"Quality: {quality_status}")
                ]
                
                # Update all labels in one batch
                for label, text in updates:
                    if label['text'] != text:  # Only update if changed
                        label['text'] = text
                        
            except Exception as e:
                print(f"Stats update error: {e}")
                
        # Schedule update
        self._pending_stats_update = self.after(1, _do_update)

    def _handle_batch_error(self, filename, error_msg):
        """Centralized error handling for batch processing"""
        logging.error(f"Failed to process {filename}: {error_msg}")
        self.batch_results['failed'] += 1
        self.failed_label.config(text=f"Failed: {self.batch_results['failed']}")
        self.progress_text.config(text=f"Failed to process: {filename}")

    def _save_metadata_to_file(self, file_path, title, tag_list):
        """Centralized method to save metadata to file"""
        with pyexiv2.Image(file_path) as metadata:
            metadata.modify_xmp({
                'Xmp.dc.title': title,
                'Xmp.dc.subject': tag_list,
                'Xmp.dc.description': title
            })
            metadata.modify_iptc({
                'Iptc.Application2.ObjectName': title,
                'Iptc.Application2.Keywords': tag_list,
                'Iptc.Application2.Caption': title
            })
            metadata.modify_exif({
                'Exif.Image.ImageDescription': title,
                'Exif.Image.Software': 'Rak Arsip'
            })

    def _build_generation_prompt(self):
        """Build smart generation prompt with best practices"""
        # Get filename context if available
        filename_context = ""
        if self.image_path_var.get():
            filename = os.path.splitext(os.path.basename(self.image_path_var.get()))[0]
            # Clean and normalize filename
            clean_filename = ' '.join(re.findall('[A-Za-z]+', filename))
            if clean_filename and len(clean_filename) > 3:
                filename_context = f"\nContext from filename where relevant: {clean_filename}\n"

        base_prompt = (
            "Create high-quality image metadata following these guidelines:\n\n"
            "1. Title/Description Requirements:\n"
            f"- Length: Min {self.min_title_var.get()} to max {self.max_title_var.get()} characters\n"
            "- Write as a natural, descriptive sentence/phrase (not keyword list)\n"
            "- Cover Who, What, When, Where, Why aspects where relevant\n"
            "- Capture mood, emotion, and visual impact\n"
            "- Must be unique and detailed\n"
            "- Include visual style/technique if notable\n"
            "- Be factual and objective\n\n"
            
            "2. Keywords Requirements:\n"
            f"- Provide exactly {self.tags_count_var.get()} keywords\n"
            "- Keywords must be precise and directly relevant\n"
            "- Include both literal and conceptual terms\n"
            "- Cover key visual elements, themes, emotions, techniques\n"
            "- Avoid overly generic or irrelevant terms\n"
            "- Use industry-standard terminology\n"
            "- Separate keywords with commas\n\n"
            
            "3. General Guidelines:\n"
            "- Use only English language\n"
            "- Be respectful and accurate with identities\n"
            "- No personally identifiable information\n"
            "- No special characters except commas between keywords\n"
            "- Focus on commercial value and searchability\n\n"
            
            "4. Strict Don'ts:\n"
            "- No brand names, trademarks, or company names\n"
            "- No celebrity names or personal names\n"
            "- No specific event references or newsworthy content\n"
            "- No copyrighted elements or protected designs\n"
            "- No editorial content or journalistic references\n"
            "- No offensive, controversial, or sensitive terms\n"
            "- No location-specific landmarks unless generic\n"
            "- No date-specific references or temporal events\n"
            "- No product names or model numbers\n"
            "- No camera/tech specifications in metadata\n\n"

            f"{filename_context}\n"
            "Format response as JSON with 'title' and 'tags' keys.\n"
        )
        
        # Add custom prompt if specified
        custom_prompt = self.custom_prompt_var.get().strip()
        if custom_prompt:
            base_prompt += f"\nAdditional context to consider: {custom_prompt}\n"
        
        # Add negative prompt if specified    
        negative_prompt = self.neg_prompt_var.get().strip()
        if negative_prompt:
            base_prompt += f"\nExclude these topics/themes: {negative_prompt}\n"
            
        return base_prompt

    def _update_ui_with_result(self, result):
        """Update UI with generation result"""
        self.title_text.delete(1.0, tk.END)
        self.title_text.insert(1.0, result['title'])
        self.tags_text.delete(1.0, tk.END)
        self.tags_text.insert(1.0, ', '.join(result['tags']))
        self.update_title_count()
        self.update_tags_count()
        
        self.progress_var.set(100)
        filename = os.path.basename(self.image_path_var.get())
        self.progress_text.config(text=f"Generated content for: {filename}")

    def _parse_response(self, text):
        """Parse Gemini API response with better JSON handling"""
        try:
            # Clean the response
            raw = text.strip()
            
            # Remove code block markers if present
            if raw.startswith("```"):
                lines = raw.splitlines()
                # Remove start markers
                if lines[0].strip().lower() in ("```json", "```python", "```txt", "```"):
                    lines = lines[1:]
                # Remove end markers
                if lines and lines[-1].strip() in ("```", "'''"):
                    lines = lines[:-1]
                raw = "\n".join(lines).strip()
                
            # Try parsing with default json first
            try:
                result = json.loads(raw)
            except:
                # If failed, try replacing single quotes with double quotes
                # But only for the outer structure
                fixed_raw = raw.replace("'title':", '"title":').replace("'tags':", '"tags":')
                # Handle the values
                fixed_raw = fixed_raw.replace("': '", '": "').replace("',", '",').replace("'}", '"}')
                fixed_raw = fixed_raw.replace('"{', '{').replace('}"', '}')  # Fix any double wrapping
                result = json.loads(fixed_raw)
                
            # Convert tags to list if string
            if isinstance(result.get('tags'), str):
                result['tags'] = [tag.strip() for tag in result['tags'].split(',')]
                
            return result
            
        except Exception as e:
            error_msg = (f"Failed to parse API response.\nError: {str(e)}\nRaw: {text}")
            print(error_msg)
            self.update_status("Error parsing response - retrying...")
            return None

    def _on_tree_select(self, event):
        """Handle treeview row selection"""
        selection = self.filelist_tree.selection()
        if not selection:
            return
            
        # Get selected item data
        item = self.filelist_tree.item(selection[0])
        file_path = self.file_paths.get(selection[0])
        
        if file_path and os.path.exists(file_path):
            self.image_path_var.set(file_path)
            self.show_image_preview(file_path)
            self.clear_fields()
            self.load_existing_metadata(file_path)
            self.update_status(f"Loaded: {os.path.basename(file_path)}")

    def _on_model_change(self, event=None):
        """Save selected model to config"""
        try:
            model = self.model_var.get()
            self.config['default_gemini_model'] = model
            self.save_config()
            self.update_status(f"Model set to: {model}")
        except Exception as e:
            self.update_status(f"Failed to save model selection: {str(e)}")

    def _on_resize_change(self, event=None):
        """Save selected resize value to config"""
        try:
            resize_value = self.resize_var.get()
            self.config['default_resize'] = resize_value
            self.save_config()
            self.scale_label.config(text=f"Submit Rescale to: {resize_value}")
            self.update_status(f"Submit size set to: {resize_value}")
        except Exception as e:
            self.update_status(f"Failed to save resize setting: {str(e)}")

    def _on_neg_prompt_change(self, event=None):
        """Save negative prompt to config"""
        try:
            new_prompt = self.neg_prompt_var.get().strip()
            if new_prompt != self.config.get('negative_prompt', ''):
                self.config['negative_prompt'] = new_prompt
                self.save_config()
                self.update_status("Negative prompt saved")
        except Exception as e:
            self.update_status(f"Failed to save negative prompt: {e}")

    def _on_custom_prompt_change(self, event=None):
        """Save custom prompt to config"""
        try:
            new_prompt = self.custom_prompt_var.get().strip()
            if new_prompt != self.config.get('custom_prompt', ''):
                self.config['custom_prompt'] = new_prompt
                self.save_config()
                self.update_status("Custom prompt saved")
        except Exception as e:
            self.update_status(f"Failed to save custom prompt: {e}")

    def update_title_count(self, event=None):
        """Update title count and cleanup if over limit while preserving whole words"""
        text = self.title_text.get(1.0, 'end-1c')
        
        if len(text) > 100:
            # Find the last complete word that fits within 100 chars
            truncated = text[:100].rsplit(' ', 1)[0]
            
            # Update text widget with cleaned title
            self.title_text.delete(1.0, tk.END)
            self.title_text.insert(1.0, truncated)
            text = truncated  # Update text for counter
        
        self.title_char_count.config(text=f"{len(text)}/100 chars")
        return text  # Return cleaned title

    def update_tags_count(self, event=None):
        """Update tag count and cleanup if over limit"""
        text = self.tags_text.get(1.0, 'end-1c')
        tags = [t.strip() for t in text.split(',') if t.strip()]
        
        # Limit to 50 tags
        if len(tags) > 50:
            tags = tags[:50]  # Keep only first 50 tags
            # Update text widget with cleaned tags
            self.tags_text.delete(1.0, tk.END)
            self.tags_text.insert(1.0, ', '.join(tags))
        
        self.tags_count.config(text=f"{len(tags)}/50 tags")
        return tags  # Return cleaned tags list

    def _on_api_key_change(self, api_key=None):
        """Save API key to config immediately when changed"""
        try:
            # Use passed api_key or get from config
            new_key = api_key or self.config.get('gemini_api_key', '')
            if new_key != self.config.get('gemini_api_key', ''):
                # Update config dictionary
                if 'checkbox_states' not in self.config:
                    self.config['checkbox_states'] = {}
                self.config['gemini_api_key'] = new_key
                
                # Save entire config
                print(f"Saving config to: {self.config_path}")
                with open(self.config_path, 'w') as f:
                    json.dump(self.config, f, indent=4, sort_keys=True)
                
                # Update display
                self._update_api_key_display(new_key)
                print(f"API key saved and display updated")
                self.update_status("API key saved to config")
        except Exception as e:
            error_msg = f"Failed to save API key: {str(e)}"
            print(error_msg)
            self.update_status(error_msg)

    def browse_image(self):
        file_path = filedialog.askopenfilename(
            filetypes=[("Image files", "*.jpg *.jpeg *.png *.gif *.bmp")],
            parent=self.parent
        )
        if file_path:
            self.image_path_var.set(file_path)
            self.show_image_preview(file_path)
            self.clear_fields()  # Clear previous metadata fields
            self.load_existing_metadata(file_path)  # Load existing metadata
        self.parent.lift()
        self.parent.focus_force()

    def clean_title(self, title):
        """Clean title by removing quoted words, special chars, and keeping only letters and spaces."""
        if not title:
            return ""
        try:
            # Remove any words/phrases in quotes (single or double)
            title = re.sub(r'(["\'])(.*?)\1', r'\2', title)
            # Remove any remaining quote characters
            title = title.replace('"', '').replace("'", "")
            # Remove language tag format if exists
            title = re.sub(r"\{'lang=[^']*':\s*'([^']*)'}", r"\1", title)
            # Replace specific punctuation with spaces
            title = re.sub(r'[:\-_/\\]', ' ', title)
            # Remove remaining special characters but keep letters and spaces
            title = re.sub(r'[^a-zA-Z\s]', '', title)
            # Normalize spaces
            title = ' '.join(title.split())
            # Capitalize each word
            return title.title()
        except Exception as e:
            print(f"Error cleaning title: {str(e)}")
            return ''.join(c for c in title if c.isalpha() or c.isspace()).strip()

    def _safe_read_iptc(self, metadata):
        """Safely read IPTC metadata with validation"""
        try:
            iptc_data = metadata.read_iptc()
            if not isinstance(iptc_data, dict):
                return {}
                
            # Validate IPTC data size
            safe_iptc = {}
            for key, value in iptc_data.items():
                try:
                    if key.startswith('Iptc.'):
                        # Check if value is string or list and reasonable size
                        if isinstance(value, str) and len(value < 1000):
                            safe_iptc[key] = value
                        elif isinstance(value, (list, tuple)):
                            # Filter list items
                            safe_items = [
                                item for item in value 
                                if isinstance(item, str) and len(item) < 1000
                            ]
                            if safe_items:
                                safe_iptc[key] = safe_items
                except:
                    continue
                    
            return safe_iptc
            
        except Exception as e:
            print(f"IPTC read error (non-critical): {str(e)}")
            return {}

    def _get_file_metadata(self, file_path):
        """Get metadata from file"""
        try:
            with pyexiv2.Image(file_path) as metadata:
                title = None
                tags = set()
                
                # Try XMP first
                try:
                    xmp = metadata.read_xmp() or {}
                    if 'Xmp.dc.title' in xmp:
                        title = xmp['Xmp.dc.title']
                        if isinstance(title, dict):
                            title = next(iter(title.values()))
                    if 'Xmp.dc.subject' in xmp:
                        tags.update(t for t in xmp['Xmp.dc.subject'] if isinstance(t, str))
                except:
                    xmp = {}

                # Try IPTC with new safe reader
                iptc = self._safe_read_iptc(metadata)
                if not title and 'Iptc.Application2.ObjectName' in iptc:
                    title = iptc['Iptc.Application2.ObjectName']
                if 'Iptc.Application2.Keywords' in iptc:
                    tags.update(t for t in iptc['Iptc.Application2.Keywords'] if isinstance(t, str))

                # Try EXIF last
                try:
                    exif = metadata.read_exif() or {}
                    if not title and 'Exif.Image.ImageDescription' in exif:
                        title = exif['Exif.Image.ImageDescription']
                except:
                    pass

                # Clean title if exists
                if title:
                    title = self.clean_title(title)

                return title, sorted(list(tags))

        except Exception as e:
            print(f"Error reading metadata from {file_path}: {str(e)}")
            return None, []

    def load_existing_metadata(self, file_path):
        """Load existing metadata using pyexiv2"""
        try:
            title, tags = self._get_file_metadata(file_path)
            
            # Update UI with found metadata
            if title:
                self.title_text.delete(1.0, tk.END)
                self.title_text.insert(1.0, title)
                self.update_title_count()

            if tags:
                self.tags_text.delete(1.0, tk.END)
                self.tags_text.insert(1.0, ', '.join(tags))
                self.update_tags_count()

            if title or tags:
                self.update_status("Existing metadata loaded")
            else:
                self.update_status("No existing metadata found")

        except Exception as e:
            print(f"Error loading metadata: {e}")
            self.update_status("Error loading metadata")

    def show_image_preview(self, file_path):
        """Optimized image preview with caching"""
        if not file_path:
            self.image_preview_label.config(image="", text="No preview")
            return
        
        # Use cached preview if available
        cache_key = f"{file_path}_{self.image_preview_label.winfo_width()}x{self.image_preview_label.winfo_height()}"
        if cache_key in self._preview_cache:
            self.image_preview_label.config(image=self._preview_cache[cache_key], text="")
            return
        
        try:
            img = PIL.Image.open(file_path)
            w, h = img.size
            
            # Get container size once
            container_width = max(self.image_preview_label.winfo_width(), 300)
            container_height = max(self.image_preview_label.winfo_height(), 300)
            
            # Calculate resize dimensions once
            scale = max(container_width / w, container_height / h)
            new_size = (int(w * scale), int(h * scale))
            
            # Resize and crop efficiently
            img = img.resize(new_size, PIL.Image.Resampling.LANCZOS)
            left = (new_size[0] - container_width) // 2
            top = (new_size[1] - container_height) // 2
            img = img.crop((
                left, 
                top,
                left + container_width,
                top + container_height
            ))
            
            # Cache the preview
            preview = PIL.ImageTk.PhotoImage(img)
            self._preview_cache[cache_key] = preview
            
            # Limit cache size
            if len(self._preview_cache) > self._max_preview_cache:
                self._preview_cache.pop(next(iter(self._preview_cache)))
                
            self.image_preview_label.config(image=preview, text="")
            self._current_preview = preview  # Prevent garbage collection
            
        except Exception as e:
            self.image_preview_label.config(image="", text="Preview failed")
            print(f"Preview error: {e}")

    def clear_fields(self):
        self.title_text.delete(1.0, tk.END)
        self.tags_text.delete(1.0, tk.END)
        self.update_title_count()
        self.update_tags_count()
        self.update_status("Fields cleared")

    def reset_all(self):
        # Only clear image and generated fields, not API key
        self.image_path_var.set("")
        self.show_image_preview("")  # Clear preview
        self.clear_fields()
        self.update_status("All fields reset")

    def save_metadata(self):
        if not self.image_path_var.get():
            self.update_status("Error: No image selected")
            messagebox.showerror("Error", "Please select an image", parent=self.parent)
            return

        try:
            # Clean and limit title before saving
            title = self.update_title_count()
            # Clean and limit tags before saving
            tag_list = self.update_tags_count()
            filename = os.path.basename(self.image_path_var.get())
            
            self.update_status(f"Saving metadata to {filename}...")
            
            # Handle RGBA images first if needed
            temp_path = None
            target_path = self.image_path_var.get()
            if PIL.Image.open(target_path).mode in ('RGBA', 'LA'):
                with PIL.Image.open(target_path) as img:
                    background = PIL.Image.new('RGB', img.size, (255, 255, 255))
                    background.paste(img, mask=img.split()[-1])
                    temp_path = f"{target_path}.temp.jpg"
                    background.save(temp_path, "JPEG", quality=95)
                target_path = temp_path

            # Write metadata using pyexiv2
            metadata = pyexiv2.Image(target_path)

            # Prepare metadata
            xmp_dict = {
                'Xmp.dc.title': title,
                'Xmp.dc.subject': tag_list,
                'Xmp.dc.description': title
            }
            
            iptc_dict = {
                'Iptc.Application2.ObjectName': title,
                'Iptc.Application2.Keywords': tag_list,
                'Iptc.Application2.Caption': title
            }

            exif_dict = {
                'Exif.Image.ImageDescription': title,
                'Exif.Image.Software': 'Rak Arsip'
            }

            # Write metadata
            metadata.modify_xmp(xmp_dict)
            metadata.modify_iptc(iptc_dict)
            metadata.modify_exif(exif_dict)
            metadata.close()

            # If using temp file, replace original
            if temp_path:
                os.replace(temp_path, self.image_path_var.get())

            # Update treeview after saving
            tags_str = ', '.join(tag_list)
            self._update_tree_item(self.image_path_var.get(), title, tags_str)

            self.update_status(
                f"Success: Metadata saved to {filename} - "
                f"Title ({len(title)} chars), {len(tag_list)} keywords"
            )

        except Exception as e:
            self.update_status(f"Failed to save metadata to {filename}: {str(e)}")
            
            # Clean up temp file if exists
            if temp_path and os.path.exists(temp_path):
                try:
                    os.remove(temp_path)
                except:
                    pass

    def _update_tree_item(self, file_path, title, tags_str):
        """Update single item in treeview"""
        for item_id in self.file_paths:
            if self.file_paths[item_id] == file_path:
                item_values = list(self.filelist_tree.item(item_id)['values'])
                item_values[3] = title  # Update title column
                item_values[4] = tags_str  # Update tags column
                self.filelist_tree.item(item_id, values=item_values)
                break

    def _monitor_metadata_changes(self):
        """Monitor metadata files for changes"""
        try:
            for item_id in self.file_paths:
                file_path = self.file_paths[item_id]
                if not os.path.exists(file_path):
                    continue

                mtime = os.path.getmtime(file_path)
                if mtime != self.file_mtimes.get(file_path):
                    # File changed, update metadata
                    title, tags = self._get_file_metadata(file_path)
                    tags_str = ", ".join(tags) if tags else ""
                    self._update_tree_item(file_path, title, tags_str)
                    self.file_mtimes[file_path] = mtime
                    # Don't update status - let calling methods handle that

        except Exception as e:
            self.update_status(f"Error monitoring changes: {e}")
        finally:
            # Check again in 1 second
            self.after(1000, self._monitor_metadata_changes)

    def _load_multiple_images(self):
        """Load multiple images via file dialog"""
        files = filedialog.askopenfilenames(
            parent=self.parent,
            title="Select Images",
            filetypes=[("Image files", "*.jpg *.jpeg *.png *.gif *.bmp")]
        )
        if files:
            self._add_files_to_tree(files)

    def _load_folder_images(self):
        """Load all supported images from selected folder"""
        folder = filedialog.askdirectory(
            parent=self.parent,
            title="Select Folder with Images"
        )
        if folder:
            supported_ext = ('.jpg','.jpeg','.png','.gif','.bmp')
            image_files = []
            for root, dirs, files in os.walk(folder):
                for file in files:
                    if file.lower().endswith(supported_ext):
                        image_files.append(os.path.join(root, file))
            if image_files:
                self._add_files_to_tree(image_files)

    def _add_files_to_tree(self, files):
        """Add files to treeview with metadata and alternating row colors"""
        # Get current item count for numbering
        current_count = len(self.filelist_tree.get_children())
            
        # Add new files while preserving existing ones
        for i, file_path in enumerate(files, current_count + 1):
            # Skip if file already exists in tree
            if file_path in self.file_paths.values():
                continue
                
            filename = os.path.basename(file_path)
            name, ext = os.path.splitext(filename)
            
            # Get metadata using existing function
            title, tags = self._get_file_metadata(file_path)
            tags_str = ", ".join(tags) if tags else ""
            
            # Insert with alternating colors based on total row count
            row_tags = ('evenrow',) if i % 2 == 0 else ('oddrow',)
            item = self.filelist_tree.insert('', 'end', 
                values=(str(i), name, ext[1:] if ext else '', 
                       title or '', tags_str),
                tags=row_tags
            )
            
            # Store path for selection
            self.file_paths[item] = file_path
        
        # Update stats after adding files
        self._update_batch_stats()
        
        # Update status
        total = len(self.filelist_tree.get_children())
        added = len(files)
        skipped = len(files) - (total - current_count)
        self.update_status(f"Added {added - skipped} new images. Skipped {skipped} duplicates. Total: {total}")

    def setup_batch_tab(self, tab, buttons):
        """Setup batch tab content"""
        self._create_button_grid(tab, buttons)

    def setup_settings_tab(self, tab, buttons):
        """Setup settings tab with configuration options"""
        # Main container
        main_frame = ttk.Frame(tab)
        main_frame.pack(fill='both', expand=True, padx=10, pady=10)

        # Left side - API & Models
        left_frame = ttk.Frame(main_frame)
        left_frame.pack(side='left', fill='both', expand=True, padx=(0,5))

        # API Keys Section
        api_frame = ttk.LabelFrame(left_frame, text="Gemini API Keys")
        api_frame.pack(fill='both', expand=True, pady=(0,10))
        
        self.api_keys_text = tk.Text(api_frame, height=10, width=50, font=("Consolas", 10))
        self.api_keys_text.pack(fill='both', expand=True, padx=5, pady=5)
        # Load existing API keys
        api_keys = self.config.get('gemini_api_keys', [])
        self.api_keys_text.insert('1.0', '\n'.join(api_keys))
        ttk.Label(api_frame, text="One API key per line").pack(pady=(0,5))

        # Models Section  
        models_frame = ttk.LabelFrame(left_frame, text="Gemini Models")
        models_frame.pack(fill='both', expand=True, pady=(0,10))
        
        self.models_text = tk.Text(models_frame, height=6, width=50, font=("Consolas", 10))
        self.models_text.pack(fill='both', expand=True, padx=5, pady=5)
        # Load existing models
        models = self.config.get('gemini_models', [])
        self.models_text.insert('1.0', '\n'.join(models))
        ttk.Label(models_frame, text="One model name per line").pack(pady=(0,5))

        # Right side - Prompts & Settings
        right_frame = ttk.Frame(main_frame)
        right_frame.pack(side='right', fill='both', expand=True, padx=(5,0))

        # Prompts Section
        prompts_frame = ttk.LabelFrame(right_frame, text="Default Prompts")
        prompts_frame.pack(fill='both', expand=True, pady=(0,10))
        
        # Custom prompt
        ttk.Label(prompts_frame, text="Custom Prompt:").pack(anchor='w', padx=5, pady=(5,0))
        self.custom_prompt_text = tk.Text(prompts_frame, height=4, width=50, font=("Arial", 10))
        self.custom_prompt_text.pack(fill='x', padx=5, pady=2)
        self.custom_prompt_text.insert('1.0', self.config.get('custom_prompt', ''))
        
        # Negative prompt
        ttk.Label(prompts_frame, text="Negative Prompt:").pack(anchor='w', padx=5, pady=(5,0))
        self.negative_prompt_text = tk.Text(prompts_frame, height=4, width=50, font=("Arial", 10))
        self.negative_prompt_text.pack(fill='x', padx=5, pady=2)
        self.negative_prompt_text.insert('1.0', self.config.get('negative_prompt', ''))

        # Processing Settings
        settings_frame = ttk.LabelFrame(right_frame, text="Processing Settings")
        settings_frame.pack(fill='x', pady=(0,10))
        
        # Grid for settings
        settings_grid = ttk.Frame(settings_frame)
        settings_grid.pack(fill='x', padx=5, pady=5)
        
        # Default model
        ttk.Label(settings_grid, text="Default Model:").grid(row=0, column=0, sticky='e', padx=5, pady=2)
        self.default_model_var = tk.StringVar(value=self.config.get('default_gemini_model'))
        default_model_combo = ttk.Combobox(settings_grid, textvariable=self.default_model_var, 
                                         values=models, state='readonly', width=30)
        default_model_combo.grid(row=0, column=1, sticky='w', padx=5, pady=2)
        
        # Title length
        ttk.Label(settings_grid, text="Title Length:").grid(row=1, column=0, sticky='e', padx=5, pady=2)
        title_frame = ttk.Frame(settings_grid)
        title_frame.grid(row=1, column=1, sticky='w', padx=5, pady=2)
        
        self.min_title_setting = tk.StringVar(value=self.config.get('title_length',{}).get('min','20'))
        self.max_title_setting = tk.StringVar(value=self.config.get('title_length',{}).get('max','30'))
        ttk.Entry(title_frame, textvariable=self.min_title_setting, width=5).pack(side='left')
        ttk.Label(title_frame, text=" - ").pack(side='left')
        ttk.Entry(title_frame, textvariable=self.max_title_setting, width=5).pack(side='left')
        
        # Tags count
        ttk.Label(settings_grid, text="Tags Count:").grid(row=2, column=0, sticky='e', padx=5, pady=2)
        self.tags_count_setting = tk.StringVar(value=self.config.get('tags_count','50'))
        ttk.Entry(settings_grid, textvariable=self.tags_count_setting, width=5).grid(row=2, column=1, sticky='w', padx=5, pady=2)
        
        # Workers count
        ttk.Label(settings_grid, text="Workers:").grid(row=3, column=0, sticky='e', padx=5, pady=2)
        self.workers_count_setting = tk.StringVar(value=self.config.get('worker_count','1'))
        ttk.Entry(settings_grid, textvariable=self.workers_count_setting, width=5).grid(row=3, column=1, sticky='w', padx=5, pady=2)

        # Action buttons
        btn_frame = ttk.Frame(right_frame)
        btn_frame.pack(fill='x', pady=10)
        
        ttk.Button(btn_frame, text="Save Settings", 
                  command=self._save_settings,
                  style='Normal.TButton').pack(side='right', padx=5)
                  
        ttk.Button(btn_frame, text="Reset to Default",
                  command=self._reset_settings,
                  style='Normal.TButton').pack(side='right', padx=5)
        
        # Add auto-update bindings
        self.api_keys_text.bind('<KeyRelease>', self._on_settings_change)
        self.models_text.bind('<KeyRelease>', self._on_settings_change)
        self.custom_prompt_text.bind('<KeyRelease>', self._on_settings_change)
        self.negative_prompt_text.bind('<KeyRelease>', self._on_settings_change)
        
        # Add variable traces
        self.min_title_setting.trace_add('write', self._on_settings_change)
        self.max_title_setting.trace_add('write', self._on_settings_change)
        self.tags_count_setting.trace_add('write', self._on_settings_change)
        self.workers_count_setting.trace_add('write', self._on_settings_change)
        self.default_model_var.trace_add('write', self._on_settings_change)

        # Update custom prompt and negative prompt bindings to synchronize with generation tab
        def sync_prompts(*args):
            custom = self.custom_prompt_var.get()
            negative = self.neg_prompt_var.get()
            # Update settings tab text widgets
            current_custom = self.custom_prompt_text.get('1.0', 'end-1c').strip()
            current_negative = self.negative_prompt_text.get('1.0', 'end-1c').strip()
            if custom != current_custom:
                self.custom_prompt_text.delete('1.0', tk.END)
                self.custom_prompt_text.insert('1.0', custom)
            if negative != current_negative:
                self.negative_prompt_text.delete('1.0', tk.END)
                self.negative_prompt_text.insert('1.0', negative)

        # Add trace to variables from generation tab
        self.custom_prompt_var.trace_add('write', sync_prompts)
        self.neg_prompt_var.trace_add('write', sync_prompts)

        # Modify text widget bindings to update generation tab
        def update_custom_prompt(*args):
            text = self.custom_prompt_text.get('1.0', 'end-1c').strip()
            if text != self.custom_prompt_var.get():
                self.custom_prompt_var.set(text)
                self._on_setting_change()

        def update_negative_prompt(*args):
            text = self.negative_prompt_text.get('1.0', 'end-1c').strip()
            if text != self.neg_prompt_var.get():
                self.neg_prompt_var.set(text)
                self._on_setting_change()

        self.custom_prompt_text.bind('<KeyRelease>', update_custom_prompt)
        self.negative_prompt_text.bind('<KeyRelease>', update_negative_prompt)

    def _save_settings(self):
        """Save all settings to config"""
        try:
            # Get API keys
            api_keys = [k.strip() for k in self.api_keys_text.get('1.0', 'end-1c').split('\n') if k.strip()]
            self.config['gemini_api_keys'] = api_keys
            if api_keys:
                self.config['gemini_api_key'] = api_keys[0]  # Set first as default
            
            # Get models
            models = [m.strip() for m in self.models_text.get('1.0', 'end-1c').split('\n') if m.strip()]
            self.config['gemini_models'] = models
            
            # Get prompts
            self.config['custom_prompt'] = self.custom_prompt_text.get('1.0', 'end-1c').strip()
            self.config['negative_prompt'] = self.negative_prompt_text.get('1.0', 'end-1c').strip()
            
            # Get other settings
            self.config['default_gemini_model'] = self.default_model_var.get()
            self.config['title_length'] = {
                'min': self.min_title_setting.get(),
                'max': self.max_title_setting.get()
            }
            self.config['tags_count'] = self.tags_count_setting.get()
            self.config['worker_count'] = self.workers_count_setting.get()
            self.config['default_resize'] = self.resize_var.get()
            
            # Save to file
            self.save_config()
            
            # Update display
            self._update_api_key_display(self.config['gemini_api_key'])
            
            self.update_status("Settings saved successfully")
            
        except Exception as e:
            self.update_status(f"Error saving settings: {str(e)}")

    def _reset_settings(self):
        """Reset settings to default values"""
        if messagebox.askyesno("Reset Settings", 
                             "Are you sure you want to reset all settings to default values?",
                             parent=self.parent):
            try:
                # Default values
                defaults = {
                    'gemini_api_keys': [],
                    'gemini_api_key': '',
                    'gemini_models': ['gemini-2.0-flash'],
                    'default_gemini_model': 'gemini-2.0-flash',
                    'custom_prompt': '',
                    'negative_prompt': '',
                    'title_length': {'min': '20', 'max': '30'},
                    'tags_count': '50',
                    'worker_count': '1',
                    'default_resize': 'Full'
                }
                
                # Update config
                self.config.update(defaults)
                
                # Update UI
                self.api_keys_text.delete('1.0', tk.END)
                self.models_text.delete('1.0', tk.END)
                self.models_text.insert('1.0', defaults['gemini_models'][0])
                self.custom_prompt_text.delete('1.0', tk.END)
                self.negative_prompt_text.delete('1.0', tk.END)
                self.default_model_var.set(defaults['default_gemini_model'])
                self.min_title_setting.set(defaults['title_length']['min'])
                self.max_title_setting.set(defaults['title_length']['max'])
                self.tags_count_setting.set(defaults['tags_count'])
                self.workers_count_setting.set(defaults['worker_count'])
                self.resize_var.set(defaults['default_resize'])
                
                # Save changes
                self.save_config()
                self.update_status("Settings reset to defaults")
                
            except Exception as e:
                self.update_status(f"Error resetting settings: {str(e)}")

    def _create_button_grid(self, parent, buttons):
        """Create a grid of buttons with icons"""
        frame = ttk.Frame(parent)
        frame.pack(fill='both', expand=True, padx=20, pady=20)
        
        for i in range(2):
            frame.columnconfigure(i, weight=1)
        
        for i, (text, command, icon_id) in enumerate(buttons):
            row = i // 2
            col = i % 2
            icon = self.button_icons.get(icon_id)
            btn = ttk.Button(frame, text=text, command=command,
                            image=icon if icon else "",
                            compound='left',
                            style='Normal.TButton')
            btn.grid(row=row, column=col, padx=5, pady=5, sticky="nsew")

    def _on_treeview_hover(self, event):
        """Handle treeview hover effect"""
        try:
            item = self.filelist_tree.identify_row(event.y)
            if item:
                # Remove hover tag from all items
                for all_item in self.filelist_tree.get_children():
                    tags = list(self.filelist_tree.item(all_item, "tags"))
                    if "hover" in tags:
                        tags.remove("hover")
                    self.filelist_tree.item(all_item, tags=tags)
                
                # Add hover tag to current item
                tags = list(self.filelist_tree.item(item, "tags"))
                if "hover" not in tags:
                    tags.append("hover")
                self.filelist_tree.item(item, tags=tags)
        except:
            pass

    def _on_treeview_leave(self, event):
        """Remove hover effect when mouse leaves treeview"""
        for item in self.filelist_tree.get_children():
            tags = list(self.filelist_tree.item(item, "tags"))
            if "hover" in tags:
                tags.remove("hover")
            self.filelist_tree.item(item, tags=tags)

    def _rename_images(self):
        """Rename images based on their metadata titles with better error handling"""
        if not self.filelist_tree.get_children():
            self.update_status("No images to rename")
            return
            
        selected = self.filelist_tree.selection()
        if not selected and not self.filelist_tree.get_children():
            return
            
        # Ask user whether to rename selected or all
        if selected:
            choice = messagebox.askquestion(
                "Rename Images",
                "Do you want to rename:\n\n"
                "Yes = Selected images only\n"
                "No = All images in list",
                icon='question',
                parent=self.parent
            )
            items_to_rename = selected if choice == 'yes' else self.filelist_tree.get_children()
        else:
            items_to_rename = self.filelist_tree.get_children()
            
        try:
            renamed = 0
            skipped = 0
            errors = []
            
            for item in items_to_rename:
                file_path = self.file_paths[item]
                if not os.path.exists(file_path):
                    continue
                    
                # Get current values
                values = self.filelist_tree.item(item)['values']
                title = values[3]  # Title column
                ext = values[2]    # Extension column
                
                if not title:
                    continue
                    
                # Clean title for filename
                clean_title = self.clean_title(title)
                
                # Create new filename
                dir_path = os.path.dirname(file_path)
                new_filename = f"{clean_title}.{ext.lower()}"
                new_path = os.path.join(dir_path, new_filename)
                
                # Handle duplicates
                base, ext = os.path.splitext(new_path)
                counter = 1
                while os.path.exists(new_path):
                    new_path = f"{base} ({counter}){ext}"
                    counter += 1
                
                try:
                    # Check if file is in use
                    locked_by = self._check_file_usage(file_path)
                    if locked_by:
                        # Show detailed message about which process is using the file
                        result = messagebox.askyesnocancel(
                            "File In Use",
                            f"The file '{os.path.basename(file_path)}' is being used by:\n\n"
                            f"{locked_by}\n\n"
                            "Would you like to:\n"
                            "Yes = Try force rename\n"
                            "No = Skip this file\n"
                            "Cancel = Stop renaming",
                            parent=self.parent
                        )
                        
                        if result is None:  # Cancel
                            self.update_status("Renaming operation cancelled")
                            return
                        elif result is False:  # Skip
                            skipped += 1
                            continue
                        # else continue with force rename
                    
                    # Try rename with retry logic
                    max_retries = 3
                    retry_count = 0
                    success = False
                    
                    while not success and retry_count < max_retries:
                        try:
                            if os.path.exists(new_path):
                                os.remove(new_path)  # Remove destination if exists
                            os.replace(file_path, new_path)  # Use replace instead of rename
                            success = True
                        except PermissionError:
                            retry_count += 1
                            if retry_count == max_retries:
                                raise
                            time.sleep(0.5)  # Short delay before retry
                    
                    # Update file path in dictionary and treeview
                    self.file_paths[item] = new_path
                    values[1] = os.path.splitext(os.path.basename(new_path))[0]  # Update filename column
                    self.filelist_tree.item(item, values=values)
                    renamed += 1
                    
                except Exception as e:
                    errors.append(f"{os.path.basename(file_path)}: {str(e)}")
                    continue
            
            # Show summary message
            status_msg = f"Renamed {renamed} images"
            if skipped > 0:
                status_msg += f", Skipped {skipped}"
            if errors:
                status_msg += f", Failed {len(errors)}"
                error_details = "\n".join(errors)
                messagebox.showwarning(
                    "Rename Results",
                    f"{status_msg}\n\nErrors:\n{error_details}",
                    parent=self.parent
                )
            
            self.update_status(status_msg)
            
        except Exception as e:
            self.update_status(f"Error during rename operation: {str(e)}")

    def _check_file_usage(self, file_path):
        """Check which process is using the file"""
        try:
            if os.name == 'nt':  # Windows only
                import psutil
                import win32file
                import pywintypes
                
                try:
                    # Try to open file with exclusive access
                    handle = win32file.CreateFile(
                        file_path,
                        win32file.GENERIC_READ,
                        0,  # No share mode
                        None,
                        win32file.OPEN_EXISTING,
                        win32file.FILE_ATTRIBUTE_NORMAL,
                        None
                    )
                    handle.close()
                    return None  # File is not in use
                except pywintypes.error:
                    # File is in use, find which process
                    processes_info = []
                    for proc in psutil.process_iter(['pid', 'name', 'username']):
                        try:
                            for item in proc.open_files():
                                if item.path == file_path:
                                    processes_info.append(
                                        f"Process: {proc.name()}\n"
                                        f"PID: {proc.pid}\n"
                                        f"User: {proc.username()}"
                                    )
                        except (psutil.NoSuchProcess, psutil.AccessDenied):
                            continue
                            
                    return "\n\n".join(processes_info) if processes_info else "Unknown process"
            return None  # Non-Windows OS
            
        except Exception as e:
            print(f"Error checking file usage: {e}")
            return None

    def _show_context_menu(self, event):
        """Show context menu on right click with proper window focus"""
        try:
            item = self.filelist_tree.identify_row(event.y)
            if item:
                self.filelist_tree.selection_set(item)
                self.parent.lift()
                self.parent.focus_force()
                self.tree_context_menu.tk_popup(event.x_root, event.y_root)
        finally:
            self.tree_context_menu.grab_release()

    def _open_selected_file(self):
        """Open the image file with default viewer"""
        selected = self.filelist_tree.selection()
        if not selected:
            return
    
        file_path = self.file_paths.get(selected[0])
        if file_path and os.path.exists(file_path):
            try:
                if os.name == 'nt':
                    os.startfile(file_path)
                else:
                    webbrowser.open(file_path)
                self.update_status(f"Opening image in default viewer: {os.path.basename(file_path)}")
            except Exception as e:
                self.update_status(f"Error opening {os.path.basename(file_path)}: {str(e)}")

    def _copy_title(self):
        """Copy title to clipboard"""
        selected = self.filelist_tree.selection()
        if not selected:
            return
            
        values = self.filelist_tree.item(selected[0])['values']
        if values and len(values) > 3:
            title = values[3]
            self.parent.clipboard_clear()
            self.parent.clipboard_append(title)
            self.update_status(f"Title copied: '{title}'")

    def _copy_tags(self):
        """Copy tags to clipboard"""
        selected = self.filelist_tree.selection()
        if not selected:
            return
            
        values = self.filelist_tree.item(selected[0])['values']
        if values and len(values) > 4:
            tags = values[4]
            self.parent.clipboard_clear()
            self.parent.clipboard_append(tags)
            truncated = tags[:100] + "..." if len(tags) > 100 else tags
            self.update_status(f"Tags copied: {truncated}")

    def _copy_file_path(self):
        """Copy full file path to clipboard"""
        selected = self.filelist_tree.selection()
        if not selected:
            return
            
        file_path = self.file_paths.get(selected[0])
        if file_path:
            self.parent.clipboard_clear()
            self.parent.clipboard_append(file_path)
            self.update_status(f"Path copied: {file_path}")

    def _open_file_location(self):
        """Open the folder containing the selected file"""
        selected = self.filelist_tree.selection()
        if not selected:
            return
            
        file_path = self.file_paths.get(selected[0])
        if file_path and os.path.exists(file_path):
            try:
                folder_path = os.path.dirname(file_path)
                if os.name == 'nt':
                    os.startfile(folder_path)
                else:
                    webbrowser.open(folder_path)
                self.update_status(f"Opening folder: {folder_path}")
            except Exception as e:
                self.update_status(f"Error opening location: {str(e)}")

    def _handle_copy(self, event):
        """Handle Ctrl+C to copy both title and tags"""
        selected = self.filelist_tree.selection()
        if not selected:
            return
            
        values = self.filelist_tree.item(selected[0])['values']
        if values and len(values) > 4:
            copy_text = f"Title: {values[3]}\nTags: {values[4]}"
            self.parent.clipboard_clear()
            self.parent.clipboard_append(copy_text)
            self.update_status("Title and tags copied to clipboard")

    def _clear_metadata(self):
        """Clear metadata from selected file"""
        selected = self.filelist_tree.selection()
        if not selected:
            return
            
        if not messagebox.askyesno("Confirm", "Clear metadata from selected file?", parent=self.parent):
            return
            
        file_path = self.file_paths.get(selected[0])
        if file_path and os.path.exists(file_path):
            try:
                # First clear metadata from file
                with pyexiv2.Image(file_path) as img:
                    # Clear all metadata types
                    img.clear_exif()
                    img.clear_xmp()
                    img.clear_iptc()
                    
                    # Re-write default software tag
                    img.modify_exif({
                        'Exif.Image.Software': 'Rak Arsip'
                    })
                
                # Clear metadata in UI
                self.title_text.delete(1.0, tk.END)
                self.tags_text.delete(1.0, tk.END)
                self.update_title_count()
                self.update_tags_count()
                
                # Update treeview
                values = list(self.filelist_tree.item(selected[0])['values'])
                values[3] = ""  # Clear title
                values[4] = ""  # Clear tags
                self.filelist_tree.item(selected[0], values=values)
                
                self.update_status("Metadata cleared successfully")
            except Exception as e:
                self.update_status(f"Error clearing metadata: {str(e)}")

    def _remove_from_list(self):
        """Remove selected item from list"""
        selected = self.filelist_tree.selection()
        if not selected:
            return
            
        if not messagebox.askyesno("Confirm", "Remove selected item from list?", parent=self.parent):
            return
            
        self.filelist_tree.delete(selected[0])
        if selected[0] in self.file_paths:
            del self.file_paths[selected[0]]
        self.update_status("Item removed from list")

    def _export_metadata_csv(self):
        """Export all treeview data to CSV with save dialog"""
        try:
            # Get all items from treeview
            items = self.filelist_tree.get_children()
            
            if not items:
                self.update_status("No data to export")
                return
            
            # Generate default filename with timestamp
            now = datetime.now()
            date_str = now.strftime("%Y-%m-%d-%H-%M")
            default_filename = f"Metadata-Export-{date_str}-Generated-by-Rak-Arsip-Desainia.csv"
            
            # Show save file dialog
            save_path = filedialog.asksaveasfilename(
                parent=self.parent,
                defaultextension=".csv",
                initialfile=default_filename,
                filetypes=[("CSV files", "*.csv"), ("All files", "*.*")],
                title="Export Metadata to CSV"
            )
            
            if not save_path:
                return  # User cancelled
                
            # Write to CSV
            with open(save_path, 'w', newline='', encoding='utf-8') as f:
                writer = csv.writer(f)
                # Write header with combined filename column
                writer.writerow(['No', 'Filename', 'Title', 'Tags', 'Full Path'])
                
                # Write data rows with combined filename and extension
                for item in items:
                    values = self.filelist_tree.item(item)['values']
                    # Combine filename and extension
                    filename = f"{values[1]}.{values[2]}" if values[2] else values[1]
                    # Create row with combined filename
                    row_data = [
                        values[0],  # No
                        filename,   # Combined filename.ext
                        values[3],  # Title  
                        values[4],  # Tags
                        self.file_paths.get(item, '')  # Full path
                    ]
                    writer.writerow(row_data)
                    
            self.update_status(f"Metadata exported to: {save_path}")
            
            # Open containing folder
            os.startfile(os.path.dirname(save_path)) if os.name == 'nt' else webbrowser.open(os.path.dirname(save_path))
            
        except Exception as e:
            self.update_status(f"Error exporting metadata: {str(e)}")

    # Existing command methods
    def generate_title(self): print("Generate title")
    def generate_tags(self): print("Generate tags")
    
    # New command methods
    def configure_templates(self): print("Configure templates")
    def configure_preferences(self): print("Configure preferences")

    def _update_api_key_display(self, key, index=None):
        """Update API key display with optional index indication"""
        if not key:
            self.api_key_display.config(text="No API key configured")
            return
            
        if index is not None:
            total_keys = len(self.config.get('gemini_api_keys', []))
            display_text = f"[{index+1}/{total_keys}] {key}"
        else:
            display_text = key
            
        self.api_key_display.config(text=display_text)

    def _on_settings_change(self, *args):
        """Auto-save settings and update generator tab when changes occur"""
        try:
            # Get all current values
            api_keys = [k.strip() for k in self.api_keys_text.get('1.0', 'end-1c').split('\n') if k.strip()]
            models = [m.strip() for m in self.models_text.get('1.0', 'end-1c').split('\n') if m.strip()]
            
            # Update config
            self.config['gemini_api_keys'] = api_keys
            if api_keys:
                self.config['gemini_api_key'] = api_keys[0]
            self.config['gemini_models'] = models
            self.config['custom_prompt'] = self.custom_prompt_text.get('1.0', 'end-1c').strip()
            self.config['negative_prompt'] = self.negative_prompt_text.get('1.0', 'end-1c').strip()
            self.config['title_length'] = {
                'min': self.min_title_setting.get(),
                'max': self.max_title_setting.get()
            }
            self.config['tags_count'] = self.tags_count_setting.get()
            self.config['worker_count'] = self.workers_count_setting.get()
            self.config['default_resize'] = self.resize_var.get()
            
            # Update generator tab
            self.update_generator_tab_from_config()
            
            # Save config
            self.save_config()
            
        except Exception as e:
            self.update_status(f"Error saving settings: {str(e)}")
        else:
            self.update_status("Settings updated")

    def update_generator_tab_from_config(self):
        """Update generator tab UI elements from config"""
        try:
            # Update API key display
            self._update_api_key_display(self.config.get('gemini_api_key', ''))
            
            # Update model combo
            models = self.config.get('gemini_models', [])
            self.model_combo['values'] = models
            if self.config.get('default_gemini_model') in models:
                self.model_var.set(self.config['default_gemini_model'])
            elif models:
                self.model_var.set(models[0])
                
            # Update prompts
            self.custom_prompt_var.set(self.config.get('custom_prompt', ''))
            self.neg_prompt_var.set(self.config.get('negative_prompt', ''))
            
            # Update lengths
            title_len = self.config.get('title_length', {})
            self.min_title_var.set(title_len.get('min', '20'))
            self.max_title_var.set(title_len.get('max', '30'))
            self.tags_count_var.set(self.config.get('tags_count', '50'))
            self.worker_count_var.set(self.config.get('worker_count', '1'))
            self.resize_var.set(self.config.get('default_resize', 'Full'))
            
        except Exception as e:
            self.update_status(f"Error updating generator tab: {str(e)}")