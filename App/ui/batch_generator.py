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

import csv
import datetime
import os
import re
import tkinter as tk
from tkinter import ttk
from tkinter import filedialog
from tkinter import messagebox
from datetime import datetime
from PIL import Image, ImageTk


class BatchGenerator(ttk.LabelFrame): 
    def __init__(self, parent, BASE_DIR, main_window):
        super().__init__(parent, text="Buat folder secara massal, praktis!", padding=10)
        self.grid(row=0, column=0, padx=10, pady=10, sticky="nsew")
        self.current_file_path = None
        self.root_path = None
        self.BASE_DIR = BASE_DIR
        self.main_window = main_window  # Simpan referensi ke MainWindow
        
        self.last_modified_time = None

        # Create main container frame
        main_container = ttk.Frame(self)
        main_container.pack(fill="both", expand=True)
        
        # Create left frame with fixed width
        left_frame = ttk.Frame(main_container)
        left_frame.pack(side="left", fill="y", padx=(0, 5))
        left_frame.pack_propagate(False)  # Prevent frame from resizing
        left_frame.configure(width=250)  # Set fixed width
        
        # Create right frame that expands
        right_frame = ttk.Frame(main_container)
        right_frame.pack(side="left", fill="both", expand=True, padx=(5, 0))

        # Left frame contents
        self.path_button_frame = ttk.Frame(left_frame)
        self.path_button_frame.pack(fill=tk.X, pady=(5,5))

        # Load button icons
        self.choose_icon = self._load_icon(os.path.join(BASE_DIR, "Img", "icon", "ui", "add_folder.png"))
        self.load_icon = self._load_icon(os.path.join(BASE_DIR, "Img", "icon", "ui", "load_csv.png"))
        self.template_icon = self._load_icon(os.path.join(BASE_DIR, "Img", "icon", "ui", "template.png"))
        self.generate_icon = self._load_icon(os.path.join(BASE_DIR, "Img", "icon", "ui", "generate.png"))

        # Update buttons with icons
        self.choose_button = ttk.Button(self.path_button_frame, 
            text="Pilih Folder",
            image=self.choose_icon, compound='left',
            command=self.choose_folder, padding=5, takefocus=0)
        self.choose_button.pack(side=tk.LEFT)
        
        self.path_label = ttk.Label(self.path_button_frame, text="Belum memilih folder...", font=("Lato Medium", 10), wraplength=300, padding=5, foreground="#999999")
        self.path_label.pack(fill=tk.X)

        # Instructions in left frame
        instructions = ttk.Label(left_frame, text=(
            "Petunjuk Penggunaan:\n"
            "1. Pilih folder tujuan dengan klik 'Pilih Folder'\n"
            "2. Pilih salah satu:\n"
            "   - Muat file CSV yang sudah ada\n"
            "   - Buat template CSV baru\n"
            "3. Edit struktur folder sesuai kebutuhan\n\n"
            "Tips:\n"
            "• Tekan TAB untuk membuat sub-folder (/)\n"
            "• Spasi akan otomatis jadi underscore (_)\n"
            "• Edit CSV bisa menggunakan Excel/LibreOffice\n"
            "• Centang 'Abaikan karakter spesial' jika\n"
            "  diperlukan\n"
            "• File CSV akan otomatis tersimpan saat\n"
            "  mengetik\n"
            "• Folder yang dibuat akan tercatat di\n"
            "  Daftar Pustaka"
        ), justify="left", foreground="#999")
        instructions.pack(fill=tk.X, pady=(10, 0))

        # Right frame contents
        self.main_frame = ttk.LabelFrame(right_frame, text="Gunakan template CSV", padding=10)
        self.main_frame.pack(fill="both", expand=True, padx=0, pady=5)

        # Rest of the widgets in main_frame (right side)
        self.button_container = ttk.Frame(self.main_frame)
        self.button_container.pack(fill=tk.X)

        self.load_button = ttk.Button(self.button_container, 
            text="Muat CSV",
            image=self.load_icon, compound='left',
            takefocus=0, command=self.load_csv_file, padding=(5,5))
        self.load_button.pack(side="left", padx=5, pady=(0, 5))

        self.create_csv_button = ttk.Button(self.button_container, 
            text="Buat CSV",
            image=self.template_icon, compound='left',
            takefocus=0, command=self.create_csv_template, padding=(5,5))
        self.create_csv_button.pack(side="left", padx=5, pady=(0, 5))

        self.file_label = ttk.Label(self.main_frame, text="CSV belum dimuat...", foreground="#999999")
        self.file_label.pack(anchor="w", padx=5, pady=(0, 5))

        self.text_area = tk.Text(self.main_frame, wrap="word", height=3)
        self.text_area.pack(fill="both", expand=True, padx=5, pady=5)
        self.text_area.bind("<KeyRelease>", self.validate_text_area)
        self.text_area.bind("<Key>", self.handle_key_press)

        self.ignore_special_var = tk.BooleanVar(value=False)
        self.ignore_special_checkbox = ttk.Checkbutton(self.main_frame, text="Abaikan jika ada karakter spesial", variable=self.ignore_special_var, command=self.validate_text_area)
        self.ignore_special_checkbox.pack(anchor="w", padx=5, pady=10)

        self.generate_button = ttk.Button(self.main_frame, 
            text="Buat Folder Massal",
            image=self.generate_icon, compound='left',
            padding=10, takefocus=0, command=self.generate_folders, 
            state=tk.DISABLED)
        self.generate_button.pack(fill=tk.X, pady=(10, 0))
        
    def choose_folder(self):
        """Membuka dialog pemilihan folder dan menampilkan path di Label."""
        folder_path = filedialog.askdirectory()
        if folder_path:
            self.path_label.config(text=folder_path)  # Ubah teks label
            self.root_path = folder_path
            self.validate_text_area()  # Periksa kembali validasi
            
    def load_csv_file(self, file_path=None):
        """Memuat file .csv dan memvalidasi karakter tidak valid."""
        if file_path is None:
            file_path = filedialog.askopenfilename(filetypes=[["CSV Files", "*.csv"]])
        if file_path:
            try:
                with open(file_path, 'r', encoding="utf-8") as file:  # Tambahkan encoding utf-8
                    reader = csv.reader(file)
                    content = "\n".join(["/".join(row) for row in reader])

                self.text_area.delete("1.0", tk.END)
                self.text_area.insert(tk.END, content)
                self.current_file_path = file_path  # Simpan path di atribut instance
                self.file_label.config(text=f"{file_path}")

                self.ignore_special_var.set(False)  # Gunakan self.ignore_special_var

                self.validate_text_area()  # Panggil method validate_text_area
                
                # Set waktu modifikasi terakhir
                self.last_modified_time = os.path.getmtime(file_path)

                # Mulai memeriksa pembaruan
                self.check_for_updates()

            except Exception as e:
                messagebox.showerror("Error", f"Gagal memuat file: {e}")

                
    def check_invalid_characters(self, folder_name):
        """Memeriksa nama folder untuk karakter tidak valid."""
        invalid_chars = r'[<>:"/\\|?*]'
        return re.search(invalid_chars, folder_name) is not None

    def validate_text_area(self, event=None):
        """Memvalidasi konten area teks untuk karakter tidak valid dan memperbarui status tombol."""
        content = self.text_area.get("1.0", tk.END).strip()
        folder_paths = content.splitlines()
        ignore_special_characters = self.ignore_special_var.get()

        if not self.root_path:
            self.generate_button.config(state=tk.DISABLED)
            messagebox.showwarning("Peringatan", "Silakan pilih folder tujuan terlebih dahulu!")
            return

        if not content:
            self.generate_button.config(state=tk.DISABLED)
            return

        invalid_detected = any(
            self.check_invalid_characters(folder)
            for path in folder_paths
            for folder in path.split("/")
        )

        if invalid_detected and not ignore_special_characters:
            self.generate_button.config(state=tk.DISABLED)
            invalid_chars = r'[<>:"/\\|?*]'
            messagebox.showwarning("Peringatan", "CSV mengandung karakter tidak valid di nama folder.\n\nTekan Tab untuk membuat folder bersarang.")
            self.main_window.update_status(f"Karakter {invalid_chars} tidak diperbolehkan di nama folder.")
        else:
            self.generate_button.config(state=tk.NORMAL)

        # Simpan perubahan ke file CSV secara otomatis
        self.save_csv_file()

    def create_csv_template(self):
        """Membuat file template CSV."""
        template = "Sub Folder 1/Sub Folder 2/Sub Folder 3/Dst"  # Contoh struktur template
        file_path = filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[["CSV Files", "*.csv"]])
        if file_path:
            try:
                with open(file_path, 'w', newline='') as file:
                    writer = csv.writer(file)
                    for line in template.splitlines():
                        writer.writerow(line.split("/"))
                messagebox.showinfo("Sukses", f"Template CSV disimpan: {file_path}")
                
                # Muat file CSV yang baru dibuat
                self.load_csv_file(file_path)
                
            except Exception as e:
                messagebox.showerror("Error", f"Gagal menyimpan CSV: {e}")

    def save_csv_file(self, event=None):
        """Menyimpan konten area teks secara otomatis kembali ke file CSV yang dimuat."""
        if self.current_file_path:
            try:
                # Ambil konten yang diperbarui dari area teks
                content = self.text_area.get("1.0", tk.END).strip()

                # Buka kembali file saat ini dalam mode tulis dan simpan konten baru
                with open(self.current_file_path, 'w', newline='') as file:
                    writer = csv.writer(file)
                    for line in content.splitlines():
                        writer.writerow(line.split("/"))  # Pisahkan dengan '/' untuk mencocokkan hierarki folder

                # Reset status modifikasi untuk menghindari pemicu event lagi
                self.text_area.edit_modified(False)

            except Exception as e:
                messagebox.showerror("Error", f"Gagal menyimpan CSV: {e}")

    def generate_folders(self):
        """Menghasilkan folder bersarang berdasarkan konten CSV."""
        # Periksa apakah file sudah dimuat
        if not self.current_file_path:
            messagebox.showwarning("Peringatan", "Silakan muat file CSV terlebih dahulu!")
            return

        if not self.root_path:
            messagebox.showwarning("Peringatan", "Silakan pilih folder tujuan terlebih dahulu!")
            return

        folder_paths = self.text_area.get("1.0", tk.END).strip().splitlines()

        # Periksa apakah karakter spesial harus diabaikan
        ignore_special_characters = self.ignore_special_var.get()

        existing_folders = []
        created_folders = []

        for folder_path in folder_paths:
            folders = folder_path.split("/")
            # Periksa setiap folder dalam path untuk karakter tidak valid di Windows
            if not ignore_special_characters:
                for folder in folders:
                    if self.check_invalid_characters(folder):
                        messagebox.showwarning("Peringatan", f"Karakter tidak valid terdeteksi di nama folder: {folder_path}.")
                        return  # Keluar dari fungsi dan hentikan pembuatan folder jika karakter spesial ditemukan

            try:
                current_path = self.root_path
                for folder in folders:
                    current_path = os.path.join(current_path, folder)
                    if os.path.exists(current_path):
                        existing_folders.append(current_path)
                    else:
                        os.makedirs(current_path, exist_ok=True)
                        created_folders.append(current_path)
            except OSError:
                messagebox.showwarning("Peringatan", f"Tidak dapat membuat folder untuk: {folder_path}")

        # Kompilasi pesan
        messages = []
        if existing_folders:
            messages.append("Folder berikut sudah ada sehingga tidak perlu dibuat ulang :\n")
            messages.extend(existing_folders)
        if created_folders:
            messages.append("\nFolder berikut berhasil dibuat:\n")
            messages.extend(created_folders)
            
        # Jika ada folder baru yang dibuat, tambahkan entri ke project_library.csv
        if created_folders:
            self.update_project_library(created_folders)

        if messages:
            messagebox.showinfo("Informasi pembuatan folder massal.", "\n".join(messages))
        else:
            messagebox.showinfo("Sukses", "Tidak ada folder yang perlu dibuat.")

        # Buka explorer dan arahkan ke folder utama hanya untuk Windows
        try:
            if os.name == 'nt':  # Untuk Windows
                os.startfile(self.root_path)
        except Exception as e:
            messagebox.showerror("Error", f"Gagal membuka folder: {e}")



    def handle_key_press(self, event):
        """Menangani event penekanan tombol di area teks."""
        if event.char == ' ':
            # Ganti ' ' dengan '_'
            self.text_area.insert(tk.INSERT, '_')
            return 'break'  # Cegah aksi default

        if event.keysym == 'Tab':
            # Ganti Tab dengan '/'
            self.text_area.insert(tk.INSERT, '/')
            return 'break'  # Cegah aksi default
        
    def check_for_updates(self):
        """Memeriksa pembaruan file CSV secara berkala."""
        if self.current_file_path:
            try:
                current_modified_time = os.path.getmtime(self.current_file_path)
                if current_modified_time != self.last_modified_time:
                    self.last_modified_time = current_modified_time
                    self.reload_csv_file()  # Gunakan metode baru ini
            except Exception as e:
                messagebox.showerror("Error", f"Gagal memeriksa perubahan file: {e}")

        # Jadwalkan pemeriksaan berikutnya
        self.after(20000, self.check_for_updates)

        
    def reload_csv_file(self):
        """Memuat ulang file CSV tanpa membuka dialog file."""
        file_path = self.current_file_path
        if file_path:
            try:
                with open(file_path, 'r', encoding="utf-8") as file:
                    reader = csv.reader(file)
                    content = "\n".join(["/".join(row) for row in reader])

                self.text_area.delete("1.0", tk.END)
                self.text_area.insert(tk.END, content)
                self.file_label.config(text=f"{file_path}")

                self.ignore_special_var.set(False)

                self.validate_text_area()

            except Exception as e:
                messagebox.showerror("Error", f"Gagal memuat file: {e}")
                
    def update_project_library(self, created_folders):
        """Menambahkan entri baru ke project_library.csv."""
        base_dir = os.path.dirname(os.path.abspath(__file__))
        db_path = os.path.join(self.BASE_DIR, "Database", "Library", "project_library.csv")

        # Pastikan direktori ada
        os.makedirs(os.path.dirname(db_path), exist_ok=True)

        # Ambil nama file CSV yang dimuat
        csv_file_name = os.path.basename(self.current_file_path)

        # Ambil tanggal saat ini dengan format bulan dalam bahasa Indonesia
        bulan_indonesia = {
            1: "Januari", 2: "Februari", 3: "Maret", 4: "April", 5: "Mei", 6: "Juni",
            7: "Juli", 8: "Agustus", 9: "September", 10: "Oktober", 11: "November", 12: "Desember"
        }
        now = datetime.now()
        current_date = f"{now.day}_{bulan_indonesia[now.month]}_{now.year}"

        # Baca file CSV yang ada untuk menentukan nomor terakhir
        try:
            with open(db_path, 'r', newline='', encoding='utf-8') as file:
                reader = csv.reader(file)
                rows = list(reader)
                if rows and rows[0] == ['No', 'Tanggal', 'Nama', 'Lokasi']:
                    last_no = int(rows[-1][0]) if len(rows) > 1 else 0
                else:
                    rows = [['No', 'Tanggal', 'Nama', 'Lokasi']]
                    last_no = 0
        except FileNotFoundError:
            rows = [['No', 'Tanggal', 'Nama', 'Lokasi']]
            last_no = 0

        # Tambahkan entri baru untuk setiap folder yang dibuat
        if created_folders:
            last_no += 1
            rows.append([str(last_no), current_date, csv_file_name, self.root_path])

        # Tulis kembali ke file CSV
        try:
            with open(db_path, 'w', newline='', encoding='utf-8') as file:
                writer = csv.writer(file)
                writer.writerows(rows)
            self.main_window.update_status("Data berhasil ditambahkan ke daftar Pustaka")

        except Exception as e:
            messagebox.showerror("Error", f"Gagal menulis ke project_library.csv: {e}")

    def _load_icon(self, icon_path, size=(16, 16)):
        """Helper function to load and process icons"""
        if not os.path.exists(icon_path):
            return None
            
        try:
            with Image.open(icon_path) as img:
                if img.mode != 'RGBA':
                    img = img.convert('RGBA')
                img = img.resize(size, Image.Resampling.LANCZOS)
                return ImageTk.PhotoImage(img)
        except Exception as e:
            print(f"Error loading icon {icon_path}: {e}")
            return None

