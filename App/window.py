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

from datetime import date
import os
import tkinter as tk
from tkinter import ttk
import markdown
import re
from tkhtmlview import HTMLLabel
from App.ui.category_editor import CategoryEditor
from App.ui.header import HeaderImage
from App.ui.disk_selector import DiskSelector
from App.ui.category_selector import CategorySelector
from App.ui.batch_generator import BatchGenerator
from App.ui.help import LoadHelpFile
from App.ui.project_generator import ProjectGenerator
from App.ui.project_library import ProjectLibrary
from App.ui.project_name_input import ProjectNameInput
from App.ui.template_creator import TemplateCreator
from App.ui.splash_screen import SplashScreen
from App.ui.database_backup import DatabaseBackup
from App.ui.relocate_files import RelocateFiles
from App.ui.personalize_settings import PersonalizeSettings  # Add this import
from App.ui.disk_analyzer import DiskAnalyzer  # Add this import
from App.config import CURRENT_VERSION, WINDOW_SIZE  # Update the import to use config
from PIL import Image, ImageTk

class MainWindow(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(f"Rak Arsip {CURRENT_VERSION}")  # Use version from Launcher
        self.geometry(WINDOW_SIZE)
        self.resizable(True, True)  # Allow resizing
        
        # Setup BASE_DIR
        self.BASE_DIR = os.path.dirname(os.path.abspath(__file__))
        
        # Setup style with vista theme
        self.style = ttk.Style()
        self.style.theme_use('vista')
        
        # Center the window
        self.center_window()

        # Memuat ikon aplikasi
        ICON_PATH = os.path.join(self.BASE_DIR, "Img", "icon", "rakikon.ico")  # Path ikon yang benar
        if os.path.exists(ICON_PATH):
            self.iconbitmap(ICON_PATH)
        else:
            print(f"Ikon tidak ditemukan di: {ICON_PATH}")

        # Tambahkan gambar header ke jendela
        self.header = HeaderImage(self, self.BASE_DIR)  # Buat instance HeaderImage
        self.header.add_header_image()  # Panggil metode untuk menampilkan gambar header tanpa padding dan border

        # Inisialisasi splash screen untuk proses pemuatan
        self.splash_screen = SplashScreen(self, self.BASE_DIR)  # Buat instance SplashScreen
        self.splash_screen.show()  # Tampilkan splash screen

        # Tambahkan status bar
        self.create_status_bar()

        # Mulai pemuatan dan inisialisasi UI setelah selesai
        self.after(100, self.start_loading)

        # Variabel StringVar untuk sinkronisasi
        self.selected_disk = tk.StringVar()
        self.root_folder = tk.StringVar()
        self.category = tk.StringVar()
        self.sub_category = tk.StringVar()
        self.date_var = tk.StringVar(value=date.today().strftime("%Y_%B_%d"))
        self.project_name = tk.StringVar()
        self.project_name.trace_add("write", self.update_project_path)

        # Add this list of fun messages
        self.loading_messages = [
            "Let's Go....!",
            "Meluncuuur...",
            "Dikit lagi nyampe...",
            "Sabaaarrr...",
            "Dikiiiiitttt lagi...",
            "Rak-nya aku rapikan dulu...",
            "Aku siapin arsip kamu...",
            "Siap...!"
        ]
        self.message_index = 0
        
    def center_window(self):
        """Center the window on the screen."""
        # Get screen width and height
        screen_width = self.winfo_screenwidth()
        screen_height = self.winfo_screenheight()
        
        # Calculate position coordinates
        window_width = 700
        window_height = 600
        pos_x = (screen_width - window_width) // 2
        pos_y = (screen_height - window_height) // 2
        
        # Set the position
        self.geometry(f"{window_width}x{window_height}+{pos_x}+{pos_y}")
        
    def update_date(self):
        """Perbarui tanggal setiap hari."""
        self.date_var.set(date.today().strftime("%Y-%m-%d"))
        # Atur untuk dijalankan kembali keesokan hari
        self.after(86400000, self.update_date)  # 86400000 ms = 24 jam

    def update_value(self, var_name, value):
        """
        Metode generik untuk memperbarui nilai variabel berdasarkan nama.
        """
        if hasattr(self, var_name):  # Cek apakah variabel ada di dalam instance
            var = getattr(self, var_name)  # Ambil variabel dengan nama var_name
            if isinstance(var, tk.StringVar):  # Pastikan variabel adalah StringVar
                var.set(value)  # Perbarui nilai StringVar
            else:
                print(f"Error: '{var_name}' bukan StringVar.")
        else:
            print(f"Error: Variabel '{var_name}' tidak ditemukan.")
        
    def create_status_bar(self):
        """
        Buat status bar dengan dua bagian: status di kiri dan tutorial di kanan
        """
        # Buat frame untuk status bar
        status_frame = tk.Frame(self, background="#f6f8f9")
        status_frame.pack(side="bottom", fill="x")

        # Label status di kiri
        self.status_bar = tk.Label(
            status_frame,
            text="",
            anchor="w",
            background="#f6f8f9",
            foreground="#666",
            borderwidth=0,
            padx=10,
            pady=5
        )
        self.status_bar.pack(side="left", fill="x", expand=True)

        # Label tutorial di kanan
        tutorial_label = tk.Label(
            status_frame,
            text=f"Tutorial v{CURRENT_VERSION}",  # Use version from Launcher
            anchor="e",
            background="#f6f8f9",
            foreground="#0066cc",
            font=("Arial", 8, "underline"),
            cursor="hand2",
            borderwidth=0,
            padx=10,
            pady=5
        )
        tutorial_label.pack(side="right")
        tutorial_label.bind("<Button-1>", self.show_tutorial)

    def show_tutorial(self, event=None):
        """
        Tampilkan tutorial dalam window baru dengan format HTML
        """
        tutorial_window = tk.Toplevel(self)
        
        tutorial_window.title(F"Tutorial Rak Arsip {CURRENT_VERSION}")  # Use version from Launcher
        tutorial_window.geometry("800x600")

        # Set ikon window
        icon_path = os.path.join(self.BASE_DIR, "Img", "icon", "rakikon.ico")
        if os.path.exists(icon_path):
            tutorial_window.iconbitmap(icon_path)
        
        # Buat frame untuk konten
        html_frame = tk.Frame(tutorial_window, bg="white")
        html_frame.pack(fill='both', expand=True)
        
        try:
            # Baca file User_Guide.md
            with open("User_Guide.md", "r", encoding="utf-8") as file:
                content = file.read()
                
            # Konversi konten Markdown ke HTML
            html_content = markdown.markdown(content)
            
            # Terapkan gaya ke tag HTML tertentu
            tag_styles = {
                "p": "font-size: 12px; line-height: 1.5; font-weight: normal; color: #555;)",
                "h1": "font-size: 20px; color: #ff7d19; font-weight: normal;",
                "h2": "font-size: 14px; font-weight: normal;",
                "h3": "font-size: 10px; font-weight: light; color: #ff7d19; ",
                "li": "font-size: 12px; list-style-type: disc; font-weight: normal; color: #555;",
                "ol": "font-size: 12px; font-weight: normal; color: #555;",
            }
            
            new_html_content = self.replace_tags(html_content, tag_styles)
            
            # Buat HTMLLabel dengan konten yang telah di-style
            html_label = HTMLLabel(
                html_frame,
                html=new_html_content,
                background="white",
                padx=100,
                pady=10,
            )
            html_label.pack(fill="both", expand=True)
            html_label.config(cursor="hand2")
                
        except FileNotFoundError:
            error_label = tk.Label(
                html_frame,
                text="Tutorial file (User_Guide.md) tidak ditemukan.",
                padx=20,
                pady=20
            )
            error_label.pack()
        except Exception as e:
            error_label = tk.Label(
                html_frame,
                text=f"Error membaca file tutorial: {str(e)}",
                padx=20,
                pady=20
            )
            error_label.pack()

    def replace_tags(self, html_content, tag_styles):
        """Mengganti beberapa tag dengan style sekaligus."""
        def replace_match(match):
            tag = match.group(1)
            if tag in tag_styles:
                style = tag_styles[tag]
                return f'<{tag} style="{style}">'
            return match.group(0)

        tag_regex = "|".join(tag_styles.keys())
        pattern = rf"<({tag_regex})>"
        return re.sub(pattern, replace_match, html_content)

    def update_status(self, message):
        """
        Perbarui teks di status bar.
        """
        print(f"Memperbarui status bar dengan pesan: {message}")  # Pernyataan debugging
        self.status_bar.config(text=message)

    def start_loading(self):
        """Mulai proses pemuatan dan inisialisasi UI."""
        self.status_message = self.loading_messages[0]
        self.update_status(self.status_message)
        self.animate_messages()
        self.after(50, self.initialize_ui) # Loading time

    def animate_messages(self):
        """Animasi pergantian pesan pada status."""
        self.message_index = (self.message_index + 1) % len(self.loading_messages)
        self.status_message = self.loading_messages[self.message_index]
        self.update_status(self.status_message)
        self.message_animation = self.after(500, self.animate_messages)  # Ganti pesan setiap 1000ms (1 detik)

    def load_theme_from_config(self):
        """Always use vista theme"""
        try:
            self.style.theme_use('vista')
        except tk.TclError:
            print("Vista theme not available, using default")
            self.style.theme_use('default')

    def _load_icon(self, icon_path, size=(16, 16)):
        """Helper function to load and process icons"""
        if not os.path.exists(icon_path):
            return None
            
        try:
            with Image.open(icon_path) as img:
                if (img.mode != 'RGBA'):
                    img = img.convert('RGBA')
                img = img.resize(size, Image.Resampling.LANCZOS)
                return ImageTk.PhotoImage(img)
        except Exception as e:
            print(f"Error loading icon {icon_path}: {e}")
            return None

    def create_tab(self, parent, text, icon_path, notebook=None, nested=False):
        """Unified function to create both main and nested tabs"""
        tab_frame = ttk.Frame(parent)
        target_notebook = notebook if nested else self.notebook
        
        icon_image = self._load_icon(icon_path)
        if icon_image:
            tab_frame.icon_image = icon_image
            target_notebook.add(tab_frame, text=text, image=icon_image, compound='left')
        else:
            target_notebook.add(tab_frame, text=text)
            
        return tab_frame

    def configure_notebook_style(self):
        """Configure notebook styles"""
        self.style.configure(
            "TNotebook.Tab",
            padding=[12, 6],
            background="#f0f0f0",
            relief="flat",
        )

        self.style.map(
            "TNotebook.Tab",
            padding=[("selected", [12, 6])],
            background=[("selected", "#ff7d19")],
            foreground=[("selected", "black")],
            relief=[("selected", "flat")],
            bordercolor=[('selected', '#F0F0F0')],
            focuscolor=[("!selected", "transparent")],
        )
        
        if self.style.theme_use() == 'vista':
            self.style.configure(
                "TNotebook", 
                tabmargins=[2, 5, 2, 0]
            )
            self.style.configure(
                "TNotebook.Tab",
                padding=[12, 6],
                expand=[("selected", [1, 1, 1, 0])]
            )

    def initialize_ui(self):
        """Inisialisasi semua elemen UI setelah pemuatan selesai."""
        if hasattr(self, 'message_animation'):
            self.after_cancel(self.message_animation)

        # Setup database directory
        database_dir = os.path.join(self.BASE_DIR, "Database")
        os.makedirs(database_dir, exist_ok=True)

        # Configure notebook styles
        self.configure_notebook_style()

        # Create main notebook
        self.notebook = ttk.Notebook(self)
        self.notebook.pack(fill='both', expand=True)

        # Initialize all tabs
        self._create_main_tabs()
        self._create_ai_tabs()
        self._create_settings_tabs()
        self._setup_widgets()

        # Hide splash screen
        self.splash_screen.hide()

        # Configure grid and bind resize event
        self._configure_grid()
        self.bind("<Configure>", self.on_resize)

    def _create_main_tabs(self):
        """Create main navigation tabs"""
        tab_configs = {
            'project_tab': ("Arsip", "add_folder.png"),
            'library_tab': ("Pustaka", "library.png"),
            'tools_tab': ("Alat", "tools.png"),  # New tools tab
            'ai_tab': ("AI", "ai.png"),
            'setting_tab': ("Setting", "settings.png"),
            'help_tab': ("Bantuan", "help.png")
        }

        for attr_name, (text, icon_name) in tab_configs.items():
            icon_path = os.path.join(self.BASE_DIR, "Img", "icon", "ui", icon_name)
            setattr(self, attr_name, self.create_tab(self.notebook, text, icon_path))

        # Create nested notebooks for tools
        self.tools_nested_notebook = ttk.Notebook(self.tools_tab)
        self.tools_nested_notebook.pack(fill='both', expand=True, pady=(5,0))

        # Create nested tabs for tools
        tools_nested_tab_configs = [
            ("Relokasi", "relocate_files.png", "relocation_tab"),
            ("Massal", "batch.png", "batch_generator_tab"),
            ("Gudang", "disk_analyzer.png", "disk_analyzer_tab")  # Add Disk Analyzer tab
        ]

        for text, icon_filename, attr_name in tools_nested_tab_configs:
            icon_path = os.path.join(self.BASE_DIR, "Img", "icon", "ui", icon_filename)
            tab = self.create_tab(self.tools_nested_notebook, text, icon_path, 
                                notebook=self.tools_nested_notebook, nested=True)
            setattr(self, attr_name, tab)

    def _setup_widgets(self):
        """Setup all UI widgets"""
        # Project tab widgets
        self.disk_selector = DiskSelector(self.project_tab, BASE_DIR=self.BASE_DIR, main_window=self)
        self.project_name_input = ProjectNameInput(self.project_tab, BASE_DIR=self.BASE_DIR, main_window=self)
        self.category_selector = CategorySelector(self.project_tab, BASE_DIR=self.BASE_DIR, main_window=self)
        self.project_generator = ProjectGenerator(self.project_tab, BASE_DIR=self.BASE_DIR, main_window=self,
                                               selected_disk=self.selected_disk, root_folder=self.root_folder,
                                               category=self.category, sub_category=self.sub_category,
                                               date_var=self.date_var, project_name=self.project_name)

        # Grid layout for project tab
        self.disk_selector.grid(row=0, column=0, padx=10, pady=(10,0), sticky="nsew")
        self.project_name_input.grid(row=0, column=1, padx=10, pady=(10,0), sticky="nsew")
        self.category_selector.grid(row=1, column=0, padx=10, pady=5, sticky="nsew")
        self.project_generator.grid(row=1, column=1, padx=10, pady=5, sticky="nsew")

        # Other tab widgets
        widgets = {
            'relocate_files': (RelocateFiles, self.relocation_tab),
            'load_help_file': (LoadHelpFile, self.help_tab),
            'template_creator': (TemplateCreator, self.template_tab),
            'batch_generator': (BatchGenerator, self.batch_generator_tab),
            'project_library': (ProjectLibrary, self.library_tab),
            'category_editor': (CategoryEditor, self.category_editor_tab),
            'database_backup': (DatabaseBackup, self.backup_tab),
            'disk_analyzer': (DiskAnalyzer, self.disk_analyzer_tab)  # Add DiskAnalyzer widget
        }

        for attr_name, (widget_class, parent) in widgets.items():
            widget = widget_class(parent, BASE_DIR=self.BASE_DIR, main_window=self)
            setattr(self, attr_name, widget)
            widget.pack(fill="both", expand=True, padx=10, pady=10)

    def _configure_grid(self):
        """Configure grid weights and constraints"""
        self.project_tab.columnconfigure(0, weight=0, minsize=200)
        self.project_tab.columnconfigure(1, weight=3)
        self.project_tab.rowconfigure(0, weight=0)
        self.project_tab.rowconfigure(1, weight=1)

    def _create_ai_tabs(self):
        """Create AI nested tabs"""
        self.ai_nested_notebook = ttk.Notebook(self.ai_tab)
        self.ai_nested_notebook.pack(fill='both', expand=True, pady=(5,5))

        ai_nested_tab_configs = [
            ("Segera ditambahkan...!", "ai.png", "ai_sub_tab1"),
            ("Tunggu updatenya...!", "ai.png", "ai_sub_tab2")
        ]

        for text, icon_filename, attr_name in ai_nested_tab_configs:
            icon_path = os.path.join(self.BASE_DIR, "Img", "icon", "ui", icon_filename)
            tab = self.create_tab(self.ai_nested_notebook, text, icon_path, notebook=self.ai_nested_notebook, nested=True)
            setattr(self, attr_name, tab)

            if attr_name == "ai_sub_tab1":
                ai_features_label = ttk.Label(
                    tab,
                    text=(
                        "Fitur AI yang ingin ditambahkan:\n\n"
                        "- Deteksi Gambar dan Video\n"
                        "- Generate Metadata Otomatis\n"
                        "- Nama Otomatis\n"
                        "- Generate Template\n"
                        "- Sub Kategori Otomatis\n"
                        "- Moderasi Teks\n"
                        "- Pengenalan Teks (OCR)\n"
                        "- Klasifikasi Dokumen\n"
                        "- Ekstraksi Metadata Otomatis\n"
                        "- Deteksi Duplikasi\n"
                        "- Ringkasan Dokumen Otomatis\n"
                        "- Fitur AI Berguna untuk Arsip Lainnya\n\n"
                        "Jika kamu punya ide atau saran, \nsilakan beri tahu kami dengan membuat issue di GitHub."
                    ),
                    justify="left",
                    padding=10
                )
                ai_features_label.pack(anchor="n", fill="both", expand=True, padx=10, pady=10)

    def _create_settings_tabs(self):
        """Create settings nested tabs"""
        self.nested_notebook = ttk.Notebook(self.setting_tab)
        self.nested_notebook.pack(fill='both', expand=True, pady=(5,0))

        nested_tab_configs = [
            ("Template", "template.png", "template_tab"),
            ("Kategori", "category.png", "category_editor_tab"), 
            ("Cadangkan", "backup.png", "backup_tab")
        ]

        for text, icon_filename, attr_name in nested_tab_configs:
            icon_path = os.path.join(self.BASE_DIR, "Img", "icon", "ui", icon_filename)
            tab = self.create_tab(self.nested_notebook, text, icon_path, notebook=self.nested_notebook, nested=True)
            setattr(self, attr_name, tab)

    def on_resize(self, event):
        """Adjust widget sizes dynamically based on window size."""
        width = self.winfo_width()
        height = self.winfo_height()

        # Adjust the sizes of widgets based on the new window size
        self.disk_selector.grid_configure(sticky="nsew")
        self.project_name_input.grid_configure(sticky="nsew")
        self.category_selector.grid_configure(sticky="nsew")
        self.project_generator.grid_configure(sticky="nsew")
        self.load_help_file.pack_configure(fill="both", expand=True)
        self.template_creator.pack_configure(fill="both", expand=True)
        self.batch_generator.pack_configure(fill="both", expand=True)
        self.project_library.pack_configure(fill="both", expand=True)
        self.category_editor.pack_configure(fill="both", expand=True)

    def update_project_path(self, *args):
        """Update project path in real-time if ProjectGenerator is initialized."""
        if hasattr(self, 'project_generator') and self.project_generator:
            try:
                self.project_generator._create_project_path()
            except Exception as e:
                print(f"Could not update project path: {e}")


