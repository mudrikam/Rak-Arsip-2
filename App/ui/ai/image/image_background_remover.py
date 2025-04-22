import tkinter as tk
from tkinter import ttk
import os
import csv
from datetime import datetime
import sys

# Try importing required dependencies with explicit Python path
try:
    import onnxruntime
except ImportError:
    python_exe = sys.executable
    import subprocess
    subprocess.check_call([python_exe, '-m', 'pip', 'install', 'onnxruntime'])
    import onnxruntime

try:    
    from rembg import remove, new_session
except ImportError:
    python_exe = sys.executable
    import subprocess
    subprocess.check_call([python_exe, '-m', 'pip', 'install', 'rembg'])
    from rembg import remove, new_session

import logging
from App.ui.header import HeaderImage
from tkinter import filedialog, messagebox
import PIL.Image
import pyexiv2
import exifread
import json
import re
import threading
import time
from queue import Queue
from concurrent.futures import ThreadPoolExecutor
from functools import partial
import psutil
import PIL.Image as Image
import PIL.ImageTk as ImageTk
import io
import numpy as np

class ImageBacgroundRemover(ttk.Frame):
    def __init__(self, parent, BASE_DIR, main_window):
        super().__init__(parent)
        self.parent = parent
        self.BASE_DIR = BASE_DIR
        self.main_window = main_window
        
        # Thread management
        self.active_threads = []
        self.thread_running = threading.Event()
        self.batch_lock = threading.Lock()
        
        # Use custom close protocol
        self.safe_close_pending = False
        self.parent.protocol("WM_DELETE_WINDOW", self._safe_close)
        
        # Add temp folder path
        self.temp_folder = os.path.join(BASE_DIR, "Temp", "Image")
        if not os.path.exists(self.temp_folder):
            os.makedirs(self.temp_folder)
        
        # Configure window
        self.parent.title("Image Background Remover")
        
        # Set fixed window size
        self.parent.geometry("700x600")
        self.parent.resizable(False, False)
        
        # Center window on screen
        screen_width = self.parent.winfo_screenwidth()
        screen_height = self.parent.winfo_screenheight()
        x = (screen_width - 700) // 2
        y = (screen_height - 600) // 2
        self.parent.geometry(f"700x600+{x}+{y}")
        
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
        
        # Configure tree style for hover effect
        self.style = ttk.Style()
        self.style.map('Treeview',
            background=[('selected', '#0078D7')],
            foreground=[('selected', 'white')])
            
        # Bind hover events
        self.tree_hover_item = None
        
        self.pack(fill='both', expand=True, padx=0, pady=(0,10))
        self.setup_ui()

        # Rembg session and preview
        self.session = new_session()
        self.current_preview = None
        self.preview_photo = None

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

    def _safe_close(self):
        """Handle window closing safely"""
        if self.safe_close_pending:
            return
            
        self.safe_close_pending = True
        self.parent.destroy()

    def cleanup_threads(self):
        """Safely cleanup all threads"""
        for thread in self.active_threads:
            if thread and thread.is_alive():
                thread.join(timeout=2.0)
        self.active_threads.clear()
        self.thread_running.clear()

    def load_config(self):
        """Load configuration"""
        try:
            with open(self.config_path, 'r') as f:
                self.config = json.load(f)
        except Exception as e:
            self.update_status(f"Failed to load config: {str(e)}")
            self.config = {}

    def save_config(self):
        """Save configuration"""
        try:
            with open(self.config_path, 'w') as f:
                json.dump(self.config, f, indent=4)
        except Exception as e:
            self.update_status(f"Failed to save config: {str(e)}")

    def _load_icon(self, path, size=(16, 16)):
        """Load and resize icon"""
        try:
            from PIL import Image, ImageTk
            with Image.open(path) as img:
                if img.mode != 'RGBA':
                    img = img.convert('RGBA')
                img = img.resize(size, Image.Resampling.LANCZOS)
                return ImageTk.PhotoImage(img)
        except Exception as e:
            print(f"Could not load icon {path}: {e}")
            return None

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
            'convert': 'convert.png',
            'settings': 'settings.png',
            'paste': 'paste.png',
            'image': 'image.png',
            'ai': 'ai.png',
            'removebg': 'rmbackground.png',
        }
        
        # Load semua ikon yang diperlukan
        for icon_id, icon_file in icon_names.items():
            icon_path = os.path.join(self.BASE_DIR, "Img", "icon", "ui", icon_file)
            self.button_icons[icon_id] = self._load_icon(icon_path)

        # Create main notebook
        self.notebook = ttk.Notebook(self)
        self.notebook.pack(fill='both', expand=True)

        # Create main tabs with icons
        self.converter_tab = ttk.Frame(self.notebook)
        self.settings_tab = ttk.Frame(self.notebook)

        # Configure grid for both tabs
        self.converter_tab.columnconfigure(0, weight=1)
        self.converter_tab.rowconfigure(0, weight=1)
        self.settings_tab.columnconfigure(0, weight=1)
        self.settings_tab.rowconfigure(0, weight=1)

        # Add tabs to notebook with icons
        self.notebook.add(self.converter_tab, text="Background Remover", 
                         image=self.button_icons.get('convert'),
                         compound='left')
        self.notebook.add(self.settings_tab, text="Settings",
                         image=self.button_icons.get('settings'),
                         compound='left')

        # Setup the tabs content
        self.setup_background_remover()
        self.setup_settings()

    def setup_background_remover(self):
        """Setup the converter tab with split layout"""
        # Main container frame with left and right sections
        main_frame = ttk.Frame(self.converter_tab)
        main_frame.pack(fill='both', expand=True, padx=5, pady=5)
        
        # Configure grid
        main_frame.columnconfigure(0, weight=1)  # Left side
        main_frame.columnconfigure(1, weight=1)  # Right side
        
        # Left Frame - Source
        left_frame = ttk.LabelFrame(main_frame, text="Source")
        left_frame.grid(row=0, column=0, sticky="nsew", padx=5, pady=5)
        
        # Info frame (path and count)
        info_frame = ttk.Frame(left_frame)
        info_frame.pack(fill='x', padx=5, pady=5)
        
        ttk.Label(info_frame, text="Path:").pack(side='left')
        path_label = ttk.Label(info_frame, text="-")
        path_label.pack(side='left', padx=(5,0))
        
        count_frame = ttk.Frame(left_frame)
        count_frame.pack(fill='x', padx=5, pady=5)
        
        ttk.Label(count_frame, text="Files:").pack(side='left')
        file_count = ttk.Label(count_frame, text="0")
        file_count.pack(side='left', padx=(5,0))
        
        # Right Frame - Actions
        right_frame = ttk.LabelFrame(main_frame, text="Actions")
        right_frame.grid(row=0, column=1, sticky="nsew", padx=5, pady=5)
        
        # Load folder label
        load_label = ttk.Label(right_frame, text="Load Folder")
        load_label.pack(padx=5, pady=5)
        
        # Store references
        self.source_path_label = path_label
        self.source_count_label = file_count

    def setup_settings(self):
        """Setup the settings tab"""
        pass