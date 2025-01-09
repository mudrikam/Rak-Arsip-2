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

class MainWindow(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Rak Arsip 2.0")
        self.geometry("700x600")
        self.resizable(True, True)  # Allow resizing

        # Pengaturan direktori dasar
        BASE_DIR = os.path.dirname(os.path.abspath(__file__))

        # Memuat ikon aplikasi
        ICON_PATH = os.path.join(BASE_DIR, "Img", "icon", "rakikon.ico")  # Path ikon yang benar
        if os.path.exists(ICON_PATH):
            self.iconbitmap(ICON_PATH)
        else:
            print(f"Ikon tidak ditemukan di: {ICON_PATH}")

        # Terapkan tema ke Tkinter
        style = ttk.Style()
        try:
            style.theme_use('vista')  # Gunakan tema 'vista'
        except tk.TclError:
            style.theme_use('default')  # Gunakan tema default jika vista tidak tersedia

        # Tambahkan gambar header ke jendela
        self.header = HeaderImage(self, BASE_DIR)  # Buat instance HeaderImage
        self.header.add_header_image()  # Panggil metode untuk menampilkan gambar header tanpa padding dan border

        # Inisialisasi splash screen untuk proses pemuatan
        self.splash_screen = SplashScreen(self, BASE_DIR)  # Buat instance SplashScreen
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
        Buat status bar penuh di bagian bawah jendela dengan latar belakang abu-abu, tanpa border, dan padding.
        """
        self.status_bar = tk.Label(
            self,
            text="",
            anchor="w",
            background="#f6f8f9",
            foreground="#666",
            borderwidth=0,
            padx=10,  # Padding horizontal
            pady=5    # Padding vertikal
        )
        self.status_bar.pack(side="bottom", fill="x")

    def update_status(self, message):
        """
        Perbarui teks di status bar.
        """
        print(f"Memperbarui status bar dengan pesan: {message}")  # Pernyataan debugging
        self.status_bar.config(text=message)

    def start_loading(self):
        """Mulai proses pemuatan dan inisialisasi UI."""
        self.status_message = "Meluncuuur"
        self.update_status(self.status_message)
        self.animate_ellipsis()
        self.after(5000, self.initialize_ui)

    def animate_ellipsis(self):
        """Animasi titik-titik pada pesan status."""
        current_text = self.status_message
        if current_text.endswith("..."):
            self.status_message = "Meluncuuur"
        else:
            self.status_message += "."
        self.update_status(self.status_message)
        self.ellipsis_animation = self.after(100, self.animate_ellipsis)  # Ubah titik-titik setiap 500 ms

    def initialize_ui(self):
        """Inisialisasi semua elemen UI setelah pemuatan selesai."""
        # Hentikan animasi titik-titik
        if hasattr(self, 'ellipsis_animation'):
            self.after_cancel(self.ellipsis_animation)
        
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

        # Konfigurasi umum tab
        style.configure(
            "TNotebook.Tab",
            padding=[10, 5],
            background="#f0f0f0",  # Warna tab tidak aktif
            relief="flat",
        )

        # Hilangkan border aktif dan atur warna latar belakang tab
        style.map(
            "TNotebook.Tab",
            background=[("selected", "#ff7d19")],  # Warna tab aktif
            foreground=[("selected", "black")],  # Warna teks tab aktif
            relief=[("selected", "flat")],  # Hilangkan border untuk tab aktif
            bordercolor=[('selected', '#F0F0F0')],
            focuscolor=[("!selected", "transparent")],  # Hilangkan garis titik-titik di tab tak aktif
        )
        
        # Notebook Utama
        self.notebook = ttk.Notebook(self)
        self.notebook.pack(fill='both', expand=True)

        # Tab Buat Arsip
        self.project_tab = ttk.Frame(self.notebook)
        self.notebook.add(self.project_tab, text="Buat Arsip")

        # Tab Atur dengan Notebook bersarang
        self.atur_tab = ttk.Frame(self.notebook)
        self.notebook.add(self.atur_tab, text="Atur")

        # Notebook bersarang untuk Template dan Kategori
        self.nested_notebook = ttk.Notebook(self.atur_tab)
        self.nested_notebook.pack(fill='both', expand=True, pady=(5,5))

        # Tab Template
        self.template_tab = ttk.Frame(self.nested_notebook)
        self.nested_notebook.add(self.template_tab, text="Template")

        # Tab Kategori
        self.category_editor_tab = ttk.Frame(self.nested_notebook)
        self.nested_notebook.add(self.category_editor_tab, text="Kategori")

        # Tab Masal
        self.batch_generator_tab = ttk.Frame(self.notebook)
        self.notebook.add(self.batch_generator_tab, text="Massal")
        
        # Tab Pustaka
        self.library_tab = ttk.Frame(self.notebook)
        self.notebook.add(self.library_tab, text="Pustaka")
        
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
            "- Deteksi Gambar\n"
            "- Nama Otomatis\n"
            "- Tag Gambar Otomatis\n"
            "- Generate Template\n"
            "- Tanya\n"
            "- Sub Kategori Otomatis\n"
            "- Moderasi Teks\n"
            "- Pengenalan Teks (OCR)\n"
            "- Pencarian Cerdas\n"
            "- Rekomendasi Arsip\n"
            "- Klasifikasi Dokumen\n"
            "- Ekstraksi Metadata Otomatis\n"
            "- Deteksi Duplikasi\n"
            "- Ringkasan Dokumen Otomatis\n"
            "- Fitur AI Berguna untuk Arsip Lainnya"
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

        # Pemilih disk
        self.disk_selector = DiskSelector(self.project_tab, BASE_DIR=self.BASE_DIR, main_window=self)
        self.disk_selector.grid(row=0, column=0, padx=10, pady=(10,0), sticky="nsew")
        
        # Input nama proyek
        self.project_name_input = ProjectNameInput(self.project_tab, BASE_DIR=self.BASE_DIR, main_window=self)
        self.project_name_input.grid(row=0, column=1, padx=10, pady=(10,0), sticky="nsew")
        
        # Pemilih kategori
        self.category_selector = CategorySelector(self.project_tab, BASE_DIR=self.BASE_DIR, main_window=self)
        self.category_selector.grid(row=1, column=0, padx=10, pady=5, sticky="nsew")

        
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

