import tkinter as tk
from tkinter import ttk
import os
import csv
from datetime import datetime

import logging
from App.ui.header import HeaderImage
from tkinter import filedialog, messagebox
import PIL.Image
import json
import re
import threading
import time
from queue import Queue
from concurrent.futures import ThreadPoolExecutor
from functools import partial
import psutil

class ImageConverterTool(ttk.Frame):
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
        self.temp_folder = os.path.join(BASE_DIR, "Temp", "Images")
        if not os.path.exists(self.temp_folder):
            os.makedirs(self.temp_folder)
        
        # Configure window
        self.parent.title("Image Converter Tool")
        
        # Set minimum size based on screen dimensions
        screen_width = self.parent.winfo_screenwidth()
        screen_height = self.parent.winfo_screenheight()
        min_width = int(screen_width * 0.8)
        min_height = int(screen_height * 0.8)
        self.parent.minsize(min_width, min_height)
        
        # Start maximized
        self.parent.state('zoomed')
        
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
        
        try:
            # Check if conversion is in progress
            if hasattr(self, 'conversion_thread') and self.conversion_thread and self.conversion_thread.is_alive():
                response = messagebox.askokcancel(
                    "Conversion In Progress",
                    "Image conversion is still running.\n\n"
                    "Closing now may result in:\n"
                    "- Incomplete conversions\n"
                    "- Temporary files not cleaned up\n\n"
                    "Are you sure you want to force close?",
                    icon='warning',
                    parent=self.parent
                )
                if not response:
                    self.safe_close_pending = False
                    return
            
            # Clean up temp files
            try:
                self._clear_temp_files()
            except Exception as e:
                messagebox.showwarning(
                    "Cleanup Warning",
                    f"Could not fully clean temporary files:\n{str(e)}\n\n"
                    "The application will close but some temp files may remain.",
                    parent=self.parent
                )
            
            # Final cleanup
            self.cleanup_threads()
            self.parent.destroy()
            
        except Exception as e:
            messagebox.showerror(
                "Close Error",
                f"Error while closing: {str(e)}",
                parent=self.parent
            )
        finally:
            self.safe_close_pending = False

    def cleanup_threads(self):
        """Safely cleanup all threads"""
        self.cancel_conversion = True
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
            'convert': 'convert.png',  # Icon for convert button
            'settings': 'settings.png'  # Icon for settings tab
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

        # Add tabs to notebook with icons
        self.notebook.add(self.converter_tab, text="Image Converter", 
                         image=self.button_icons.get('convert'),
                         compound='left')
        self.notebook.add(self.settings_tab, text="Settings",
                         image=self.button_icons.get('settings'),
                         compound='left')
                         
        # Setup the converter tab
        self.setup_converter_tab()

    def setup_converter_tab(self):
        """Setup the converter tab with source and destination frames"""
        # Configure grid weights for equal width
        self.converter_tab.grid_columnconfigure(0, weight=1)
        self.converter_tab.grid_columnconfigure(1, weight=1)
        
        # Create source frame
        source_frame = ttk.LabelFrame(self.converter_tab, text="Source")
        source_frame.grid(row=0, column=0, padx=5, pady=5, sticky="nsew")
        
        # Create destination frame
        dest_frame = ttk.LabelFrame(self.converter_tab, text="Destination")
        dest_frame.grid(row=0, column=1, padx=5, pady=5, sticky="nsew")
        
        # Add placeholder text
        ttk.Label(source_frame, text="Lorem ipsum dolor sit amet,\nconsectetur adipiscing elit.").pack(
            padx=10, pady=10)
        ttk.Label(dest_frame, text="Lorem ipsum dolor sit amet,\nconsectetur adipiscing elit.").pack(
            padx=10, pady=10)

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

    # Fungsi tab kosong
    def setup_settings_tab(self):
        pass

    # Empty method implementations
    def _load_files(self): pass
    def _load_folder(self): pass
    def _clear_files(self): pass
    def _remove_selected(self): pass
    def _start_conversion(self): pass
    def _clear_temp_files(self): pass
    def _save_settings(self): pass
    def _reset_settings(self): pass