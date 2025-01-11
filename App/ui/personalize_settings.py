# ---------------------------------------------------------------
# Hak Cipta (C) 2025 M. Mudrikul Hikam
# ---------------------------------------------------------------
# Program ini adalah perangkat lunak bebas: Anda dapat 
# mendistribusikan ulang dan/atau memodifikasinya di bawah 
# ketentuan Lisensi Publik Umum GNU (GNU GPL v3) sebagaimana 
# diterbitkan oleh Free Software Foundation, baik versi 3 dari 
# Lisensi, atau (sesuai pilihan Anda) versi yang lebih baru.
# 
# Program ini didistribusikan dengan harapan bahwa itu akan 
# berguna, tetapi TANPA JAMINAN; bahkan tanpa jaminan tersirat
# tentang DIPERDAGANGKAN atau KESESUAIAN UNTUK TUJUAN TERTENTU. 
# Lihat Lisensi Publik Umum GNU untuk lebih jelasnya.
# 
# Anda seharusnya telah menerima salinan Lisensi Publik Umum GNU
# bersama dengan program ini. Jika tidak, lihat 
# <https://www.gnu.org/licenses/>.
# 
# ---------------------------------------------------------------
# Mohon untuk tidak menghapus header ini.
# Jika ingin berkontribusi, tuliskan namamu di sini.
# ---------------------------------------------------------------
# | Nama Kontributor       | Kontribusi                         |
# |------------------------|------------------------------------|
# |                        |                                    |
# |                        |                                    |
# |                        |                                    |
# ---------------------------------------------------------------

import json
import os
import csv
import tkinter as tk
from tkinter import ttk
from tkinter import messagebox
from tkinter import filedialog
import webbrowser

class PersonalizeSettings(ttk.LabelFrame):
    def __init__(self, parent, BASE_DIR, main_window):
        super().__init__(parent, text="Personalisasi Rak Arsip untuk kebutuhanmu :", padding=10)
        self.grid(row=0, column=0, padx=10, pady=10, sticky="nsew")
        self.main_window = main_window
        self.BASE_DIR = BASE_DIR
        
        # Apply vista theme on init
        self.main_window.style.theme_use('vista')
        self._configure_vista_theme()

    def _configure_vista_theme(self):
        """Configure vista theme specific settings"""
        self.main_window.style.configure(
            "TNotebook.Tab",
            padding=[12, 6],
            background="#f0f0f0",
            relief="flat"
        )
        
        self.main_window.style.map(
            "TNotebook.Tab",
            padding=[("selected", [12, 6])],
            background=[("selected", "#ff7d19")],
            foreground=[("selected", "black")],
            relief=[("selected", "flat")],
            bordercolor=[('selected', '#F0F0F0')],
            focuscolor=[("!selected", "transparent")]
        )
        
        self.main_window.style.configure(
            "TNotebook", 
            tabmargins=[2, 5, 2, 0]
        )
        self.main_window.style.configure(
            "TNotebook.Tab",
            padding=[12, 6],
            expand=[("selected", [1, 1, 1, 0])]
        )

    def create_default_config(self):
        """Membuat file config.json default jika tidak ditemukan"""
        config_dir = os.path.join(self.BASE_DIR, 'Database', 'Config')
        config_path = os.path.join(config_dir, 'config.json')
        
        if not os.path.exists(config_dir):
            os.makedirs(config_dir)
            
        default_config = {
            'checkbox_states': {
                'include_date': True,
                'include_markdown': True,
                'open_explorer': True,
                'sanitize_name': True
            }
        }
        
        with open(config_path, 'w') as f:
            json.dump(default_config, f, indent=4)
        
        return default_config

    # Remove theme-related methods, keep only checkbox state methods
    @staticmethod
    def get_checkbox_states(BASE_DIR):
        """Static method untuk mendapatkan checkbox states dari config"""
        config_path = os.path.join(BASE_DIR, 'Database', 'Config', 'config.json')
        try:
            with open(config_path, 'r') as f:
                config = json.load(f)
                return config.get('checkbox_states', {
                    'include_date': True,
                    'include_markdown': True,
                    'open_explorer': True,
                    'sanitize_name': True  # Add default for sanitize name
                })
        except (FileNotFoundError, json.JSONDecodeError):
            return {
                'include_date': True,
                'include_markdown': True,
                'open_explorer': True,
                'sanitize_name': True  # Add default for sanitize name
            }

    @staticmethod 
    def save_checkbox_states(BASE_DIR, states):
        """Static method untuk menyimpan checkbox states ke config"""
        config_path = os.path.join(BASE_DIR, 'Database', 'Config', 'config.json')
        try:
            with open(config_path, 'r') as f:
                config = json.load(f)
        except (FileNotFoundError, json.JSONDecodeError):
            config = {'theme': 'vista'}

        config['checkbox_states'] = states
        
        with open(config_path, 'w') as f:
            json.dump(config, f, indent=4)