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

class MainWindow(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Rak Arsip 2.0")
        self.geometry("700x600")
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
            text="Tutorial v2.0.2",
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
        tutorial_window.title("Tutorial Rak Arsip 2.0")
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
                "p": "font-size: 12px; line-height: 1.5; font-weight: normal;",
                "h1": "font-size: 18px; color: #ff7d19; font-weight: normal;",
                "h2": "font-size: 16px; font-weight: normal;",
                "h3": "font-size: 14px; font-weight: normal;",
                "li": "font-size: 12px; list-style-type: disc; font-weight: normal;",
            }
            
            new_html_content = self.replace_tags(html_content, tag_styles)
            
            # Buat HTMLLabel dengan konten yang telah di-style
            html_label = HTMLLabel(
                html_frame,
                html=new_html_content,
                background="white",
                padx=100,
                pady=100
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
        self.after(4000, self.initialize_ui)

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

    def initialize_ui(self):
        """Inisialisasi semua elemen UI setelah pemuatan selesai."""
        # Hentikan animasi pesan
        if hasattr(self, 'message_animation'):
            self.after_cancel(self.message_animation)
        
        # Style already initialized in __init__, no need to create new one
        style = self.style  # Use existing style instance
        
        self.BASE_DIR = os.path.dirname(os.path.abspath(__file__))

        # Cek apakah direktori "Database" ada, jika tidak buatkan
        database_dir = os.path.join(self.BASE_DIR, "Database")
        if not os.path.exists(database_dir):
            os.makedirs(database_dir)
            print(f"Direktori 'Database' telah dibuat di: {database_dir}")
        else:
            print(f"Direktori 'Database' sudah ada di: {database_dir}")

        # Buat objek style untuk notebook
        style = ttk.Style()

        # Konfigurasi umum tab - Perbaikan untuk kompatibilitas tema
        style.configure(
            "TNotebook.Tab",
            padding=[12, 6],  # Menambah padding untuk semua tema
            background="#f0f0f0",
            relief="flat",
        )

        # Hilangkan border aktif dan atur warna latar belakang tab
        style.map(
            "TNotebook.Tab",
            padding=[("selected", [12, 6])],  # Memastikan padding tetap saat tab dipilih
            background=[("selected", "#ff7d19")],
            foreground=[("selected", "black")],
            relief=[("selected", "flat")],
            bordercolor=[('selected', '#F0F0F0')],
            focuscolor=[("!selected", "transparent")],
        )
        
        # Tambahan konfigurasi khusus untuk tema vista
        if style.theme_use() == 'vista':
            style.configure(
                "TNotebook", 
                tabmargins=[2, 5, 2, 0]  # [left, top, right, bottom]
            )
            style.configure(
                "TNotebook.Tab",
                padding=[12, 6],
                expand=[("selected", [1, 1, 1, 0])]  # Ekspansi tab yang dipilih
            )

        # Notebook Utama
        self.notebook = ttk.Notebook(self)
        self.notebook.pack(fill='both', expand=True)

        # Tab Buat Arsip
        self.project_tab = ttk.Frame(self.notebook)
        self.notebook.add(self.project_tab, text="Buat Arsip")

        # Tab Relokasi
        self.relocation_tab = ttk.Frame(self.notebook)
        self.notebook.add(self.relocation_tab, text="Relokasi")

        # Tab Pustaka
        self.library_tab = ttk.Frame(self.notebook)
        self.notebook.add(self.library_tab, text="Pustaka")

        # Tab Masal
        self.batch_generator_tab = ttk.Frame(self.notebook)
        self.notebook.add(self.batch_generator_tab, text="Massal")
        
        # Tab AI
        self.ai_tab = ttk.Frame(self.notebook)
        self.notebook.add(self.ai_tab, text="Ai")

        # Notebook bersarang untuk AI
        self.ai_nested_notebook = ttk.Notebook(self.ai_tab)
        self.ai_nested_notebook.pack(fill='both', expand=True, pady=(5,5))

        # Tab AI Sub Tab 1
        self.ai_sub_tab1 = ttk.Frame(self.ai_nested_notebook)
        self.ai_nested_notebook.add(self.ai_sub_tab1, text="Segera ditambahkan...!")

        # Add description and list of AI features to AI Sub Tab 1
        ai_features_label = ttk.Label(
            self.ai_sub_tab1,
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

        # Tab AI Sub Tab 2
        self.ai_sub_tab2 = ttk.Frame(self.ai_nested_notebook)
        self.ai_nested_notebook.add(self.ai_sub_tab2, text="Tunggu updatenya...!")

        # Tab Bantuan
        self.help_tab = ttk.Frame(self.notebook)
        self.notebook.add(self.help_tab, text="?")

        # Tab Atur dengan Notebook bersarang
        self.setting_tab = ttk.Frame(self.notebook)
        self.notebook.insert(self.notebook.index(self.help_tab), self.setting_tab, text="Setting")

        # Notebook bersarang untuk Template dan Kategori
        self.nested_notebook = ttk.Notebook(self.setting_tab)
        self.nested_notebook.pack(fill='both', expand=True, pady=(5,0))

        # Tab Template
        self.template_tab = ttk.Frame(self.nested_notebook)
        self.nested_notebook.add(self.template_tab, text="Template")

        # Tab Kategori
        self.category_editor_tab = ttk.Frame(self.nested_notebook)
        self.nested_notebook.add(self.category_editor_tab, text="Kategori")

        # Tab Cadangkan
        self.backup_tab = ttk.Frame(self.nested_notebook)
        self.nested_notebook.add(self.backup_tab, text="Cadangkan")
        
        # Tab Personalisasi
        self.personalize_tab = ttk.Frame(self.nested_notebook)
        self.nested_notebook.add(self.personalize_tab, text="Personalisasi")

        # Pemilih disk
        self.disk_selector = DiskSelector(self.project_tab, BASE_DIR=self.BASE_DIR, main_window=self)
        self.disk_selector.grid(row=0, column=0, padx=10, pady=(10,0), sticky="nsew")
        
        # Input nama proyek
        self.project_name_input = ProjectNameInput(self.project_tab, BASE_DIR=self.BASE_DIR, main_window=self)
        self.project_name_input.grid(row=0, column=1, padx=10, pady=(10,0), sticky="nsew")
        
        # Pemilih kategori
        self.category_selector = CategorySelector(self.project_tab, BASE_DIR=self.BASE_DIR, main_window=self)
        self.category_selector.grid(row=1, column=0, padx=10, pady=5, sticky="nsew")

        #Relokasi File
        self.relocate_files = RelocateFiles(self.relocation_tab, BASE_DIR=self.BASE_DIR, main_window=self)
        self.relocate_files.pack(fill="both", expand=True, padx=10, pady=10)
        
        # Generator Proyek
        self.project_generator = ProjectGenerator(self.project_tab, BASE_DIR=self.BASE_DIR, main_window=self, selected_disk=self.selected_disk, root_folder=self.root_folder, category=self.category, sub_category=self.sub_category, date_var=self.date_var, project_name=self.project_name)
        self.project_generator.grid(row=1, column=1, padx=10, pady=5, sticky="nsew")

        # File Bantuan
        self.load_help_file = LoadHelpFile(self.help_tab, BASE_DIR=self.BASE_DIR, main_window=self)
        self.load_help_file.pack(fill="both", expand=True, padx=10, pady=10)
        
        # Pembuat Template Sub Folder
        self.template_creator = TemplateCreator(self.template_tab, BASE_DIR=self.BASE_DIR, main_window=self)
        self.template_creator.pack(fill="both", expand=True, padx=10, pady=10)
        
        # Pembuat Batch Sub
        self.batch_generator = BatchGenerator(self.batch_generator_tab, BASE_DIR=self.BASE_DIR, main_window=self)
        self.batch_generator.pack(fill="both", expand=True, padx=10, pady=10)
        
        # Pustaka Proyek
        self.project_library = ProjectLibrary(self.library_tab, BASE_DIR=self.BASE_DIR, main_window=self)
        self.project_library.pack(fill="both", expand=True, padx=10, pady=10)
        
        # Editor Kategori
        self.category_editor = CategoryEditor(self.category_editor_tab, BASE_DIR=self.BASE_DIR, main_window=self)
        self.category_editor.pack(fill="both", expand=True, padx=10, pady=10)

        # Add DatabaseBackup to the Cadangkan tab
        self.database_backup = DatabaseBackup(self.backup_tab, BASE_DIR=self.BASE_DIR, main_window=self)
        self.database_backup.pack(fill="both", expand=True, padx=10, pady=10)
        
        # Add PersonalizeSettings to the Personalisasi tab
        self.personalize_settings = PersonalizeSettings(self.personalize_tab, BASE_DIR=self.BASE_DIR, main_window=self)
        self.personalize_settings.pack(fill="both", expand=True, padx=10, pady=10)
        
        # Sembunyikan splash screen setelah pemuatan selesai
        self.splash_screen.hide()

        # Configure grid to be resizable with weight constraints
        self.project_tab.columnconfigure(0, weight=0, minsize=200)  # Minimum width for "Pilih Disk"
        self.project_tab.columnconfigure(1, weight=3)  # More weight for the second column
        self.project_tab.rowconfigure(0, weight=0) # Resizable row for other widgets
        self.project_tab.rowconfigure(1, weight=1) # Resizable row for other widgets

        # Bind the configure event to adjust widget sizes dynamically
        self.bind("<Configure>", self.on_resize)

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
        """Update project path in real-time."""
        if hasattr(self, 'project_generator'):
            self.project_generator._create_project_path()
        else:
            print("ProjectGenerator instance not found.")

