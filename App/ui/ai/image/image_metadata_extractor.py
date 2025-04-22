import tkinter as tk
from tkinter import ttk
import os
import csv
from datetime import datetime

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

class ImageMetadataExtractor(ttk.Frame):
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
        self.temp_folder = os.path.join(BASE_DIR, "Temp", "Metadata")
        if not os.path.exists(self.temp_folder):
            os.makedirs(self.temp_folder)
        
        # Configure window
        self.parent.title("Image Metadata Extractor")
        
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

    def setup_ui(self):
        """Setup the tabbed UI"""
        # Create main notebook
        self.notebook = ttk.Notebook(self)
        self.notebook.pack(fill='both', expand=True)

        # Create main tabs
        self.extractor_tab = ttk.Frame(self.notebook)
        self.settings_tab = ttk.Frame(self.notebook) 

        # Add tabs to notebook
        self.notebook.add(self.extractor_tab, text="Metadata Extractor")
        self.notebook.add(self.settings_tab, text="Settings")
