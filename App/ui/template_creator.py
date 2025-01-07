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
# | Nama Kontributor       | Fitur yang Ditambahkan atau Ubah   |
# |------------------------|------------------------------------|
# |                        |                                    |
# |                        |                                    |
# |                        |                                    |
# ---------------------------------------------------------------

import os
import sys
import tkinter as tk
from tkinter import ttk
from tkinter import messagebox
from App.ui.core_scan import forbidden_words

class TemplateCreator(ttk.LabelFrame):
    def __init__(self, parent, x, y, width, height, BASE_DIR, main_window):
        """
        Inisialisasi kelas TemplateCreator untuk mengelola tampilan file, pengeditan konten, dan pembuatan folder.
        """
        super().__init__(parent, text="Buat template untuk sub folder :", padding=10)
        self.place(x=x, y=y, width=width, height=height)  # Atur posisi dan ukuran
        self.main_window = main_window
        
        # Pastikan folder 'Database' ada di dalam BASE_DIR
        self.BASE_DIR = os.path.join(BASE_DIR, "Database", "Template")
        self.file_mapping = {}
        self.forbidden_words = forbidden_words
        self.current_warning_level = 0
        self.last_bad_word = None
        self.warning_messages = [
            ("Aduh....!", "Ada kata '{}' di template, kamu yakin itu gak papa?"),
            ("Maaf kalau salah...", "Sebenarnya aku harap kita pakai aplikasi ini secara aman sih..."),
            ("Aku gak yakin nih...","Sepertinya kata '{}' kurang aman kalau mau pakai aplikasi ini"),
            ("Hem...","Sebenernya gapapa sih kalau kamu maksa, tapi kalau bisa tolong pakai kata yang aman saja ya"),
            ("Mending ganti","Aku udah ingetin berkali-kali loh, seriusan aku nggak suka kalau aplikasi ini dipakai untuk hal jelek"),
            ("Seriusan?","Kayanya kamu emang tetep pengen pakai kata '{}' ya?"),
            ("Pliss....","Plis banget pakai kata lain yang lebih aman ya"),
            ("Aku kasih kesempatan","Oke deh untuk kali ini gapapa pakai '{}', tapi ini terakhir ya"),
            ("Maaf nih...","Maaf banget, tapi aku gak bisa toleransi sama kata '{}', kalau belum diubah juga aku pamit undur diri ya"),
            ("Yasudah...","Makasih atas waktunya saya pamit undur diri"),
        ]

        os.makedirs(self.BASE_DIR, exist_ok=True)  # Buat 'Database' jika belum ada

        self.current_file = None

        self._create_widgets()

    def _create_widgets(self):
        """
        Buat dan atur semua widget yang digunakan dalam template creator.
        """
        # Bagian Manajemen File
        self.file_frame = ttk.LabelFrame(self, text="Pilih Template")
        self.file_frame.pack(pady=10, fill=tk.X)

        # Dropdown combobox untuk pemilihan file
        self.combobox = ttk.Combobox(self.file_frame, font= 14)
        self.combobox.pack(side=tk.LEFT, padx=5, pady=10)
        self.combobox.bind("<<ComboboxSelected>>", self.display_file_content)

        # Bagian Konten File (Daftar sub folder)
        self.text_frame = ttk.LabelFrame(self, text="Daftar sub folder :", padding=10)
        self.text_frame.pack(fill=tk.BOTH, expand=True)

        # Frame untuk nomor baris dan area teks
        frame = ttk.Frame(self.text_frame)
        frame.pack(fill=tk.BOTH, expand=True)

        # Tambahkan tombol di dalam frame yang sama dengan area teks
        save_button = ttk.Button(frame, text="Tambah Template", command=self.save_as_template, padding=10)
        save_button.pack(side=tk.BOTTOM, anchor='w', pady=10)  # Tempatkan di bawah dalam frame

        # Tampilan nomor baris
        self.line_numbers = tk.Text(frame, width=4, padx=5, state="disabled", wrap="none", bg="#f0f0f0")
        self.line_numbers.pack(side=tk.LEFT, fill=tk.Y)

        # Area teks untuk konten file
        self.text_area = tk.Text(frame, wrap=tk.WORD, height=20, width=60)
        self.text_area.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.text_area.bind("<Key>", self.replace_special_characters)
        self.text_area.bind("<KeyRelease>", lambda e: (self.save_file_content(e), self.update_line_numbers(), self.check_forbidden_words_dynamically(e)))

        # Scrollbar untuk area teks dan nomor baris
        scrollbar = ttk.Scrollbar(frame, orient="vertical", command=self.on_scroll)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        # Hubungkan scrollbar ke area teks dan nomor baris
        self.text_area.config(yscrollcommand=scrollbar.set)
        self.line_numbers.config(yscrollcommand=scrollbar.set)

        # Muat file saat aplikasi dimulai
        self.selected_template = None
        self.load_files()
        
    def load_files(self):
        """Muat nama file ke dalam combobox dan pilih template_0 secara default."""
        self.check_and_load_files()  # Panggil metode untuk memeriksa dan memuat file

    def check_and_load_files(self):
        """Periksa file .txt dan pastikan template_0 ada, muat ulang hanya jika file diperbarui."""
        try:
            # Ambil daftar file .txt di direktori
            current_files = [
                f for f in os.listdir(self.BASE_DIR)
                if os.path.isfile(os.path.join(self.BASE_DIR, f)) and f.endswith(".txt")
            ]

            # Pastikan template_0.txt ada; jika tidak, buat file tersebut
            if "template_0.txt" not in current_files:
                self.create_template_file("template_0.txt")  # Buat file template_0.txt
                current_files.append("template_0.txt")  # Tambahkan ke daftar file

            # Bandingkan daftar file baru dengan daftar file sebelumnya
            if hasattr(self, 'previous_files') and set(current_files) == set(self.previous_files):
                # Jika tidak ada perubahan, tidak perlu memperbarui *combobox*
                self.after(1000, self.check_and_load_files)  # Jadwalkan pengecekan ulang
                return

            # Perbarui daftar file sebelumnya jika ada perubahan
            self.previous_files = current_files

            # Buat mapping file untuk menghilangkan ekstensi .txt
            self.file_mapping = {os.path.splitext(f)[0]: f for f in current_files}  # {display_name: full_name}
            display_names = list(self.file_mapping.keys())

            # Simpan pilihan saat ini di combobox
            current_selection = self.combobox.get()
            self.combobox['values'] = display_names  # Perbarui daftar nama di combobox

            # Tetapkan default jika tidak ada pilihan atau pilihan tidak valid
            if not current_selection or current_selection not in display_names:
                if "template_0" in display_names:
                    self.combobox.set("template_0")
                    self.display_file_content("template_0")  # Tampilkan konten template_0
                else:
                    self.combobox.current(0)  # Pilih item pertama
                    self.display_file_content(display_names[0])
            else:
                # Jika ada pilihan sebelumnya, kembalikan pilihan tersebut
                self.combobox.set(current_selection)
                self.display_file_content(current_selection)

        except FileNotFoundError:
            # Jika folder tidak ditemukan, buat folder dan file template_0.txt
            os.makedirs(self.BASE_DIR, exist_ok=True)
            self.create_template_file("template_0.txt")
            self.previous_files = []  # Kosongkan daftar file sebelumnya
            self.check_and_load_files()  # Muat ulang setelah membuat file

        # Jadwalkan pengecekan ulang setelah 1 detik
        self.after(1000, self.check_and_load_files)

    def on_template_selected(self, event):
        """Callback untuk menangani pemilihan template."""
        self.selected_template = self.combobox.get()  # Simpan template yang dipilih
        self.display_file_content(self.selected_template)  # Tampilkan isi template yang dipilih

    def create_template_file(self):
        """Buat file template_0.txt kosong di BASE_DIR."""
        template_path = os.path.join(self.BASE_DIR, "template_0.txt")
        if not os.path.exists(template_path):
            with open(template_path, "w") as file:
                file.write("")  # Buat file kosong

    def display_file_content(self, event=None, display_nama=None):
        """Tampilkan konten file yang dipilih di area teks dan periksa kata-kata terlarang."""
        if display_nama is None:
            # Jika dipanggil melalui event (misal, dari Combobox)
            display_nama = self.combobox.get()
            
        # Ambil nama file asli dari display_nama
        full_name = self.file_mapping.get(display_nama)
        if not full_name:
            self.text_area.delete("1.0", tk.END)
            self.text_area.insert(tk.END, "File tidak ditemukan.")
            return

        file_path = os.path.join(self.BASE_DIR, full_name)

        if os.path.exists(file_path):
            try:
                with open(file_path, "r") as file:
                    content = file.read()
                    
                    # Tampilkan konten di text area
                    self.text_area.delete("1.0", tk.END)
                    self.text_area.insert(tk.END, content)
                    
                    # Simpan file saat ini
                    self.current_file = file_path
                    
                    # Perbarui nomor baris (jika ada fitur line number)
                    self.update_line_numbers()
                    
                    # Periksa kata-kata terlarang
                    if self.check_forbidden_words(content):
                        self.display_forbidden_word_warning()

            except Exception as e:
                # Tampilkan pesan error di text area
                self.text_area.delete("1.0", tk.END)
                self.text_area.insert(tk.END, f"Error membaca file: {e}")
        else:
            self.text_area.delete("1.0", tk.END)
            self.text_area.insert(tk.END, "File tidak ditemukan.")

    def save_file_content(self, event):
        """Simpan konten area teks kembali ke file."""
        if self.current_file:
            try:
                with open(self.current_file, "w") as file:
                    file.write(self.text_area.get("1.0", tk.END).strip())
            except Exception as e:
                self.text_area.insert(tk.END, f"\nError menyimpan file: {e}")

    def save_as_template(self):
        """Simpan konten area teks sebagai file template baru dan muat ulang daftar file."""
        if not self.before_save_checks():
            return

        os.makedirs(self.BASE_DIR, exist_ok=True)

        base_name = "template"
        extension = ".txt"
        index = 0

        while True:
            file_name = f"{base_name}_{index}{extension}"
            file_path = os.path.join(self.BASE_DIR, file_name)

            if not os.path.exists(file_path):
                with open(file_path, "w") as file:
                    file.write(self.text_area.get("1.0", tk.END).strip())
                self.load_files()  # Perbarui file_mapping dan combobox
                self.combobox.set(os.path.splitext(file_name)[0])  # Pilih file baru
                self.display_file_content(display_nama=os.path.splitext(file_name)[0])
                return

            index += 1

    def update_line_numbers(self):
        """Perbarui nomor baris di panel kiri."""
        self.line_numbers.config(state="normal")
        self.line_numbers.delete("1.0", tk.END)
        row_count = self.text_area.index("end").split(".")[0]
        for i in range(1, int(row_count)):
            self.line_numbers.insert(tk.END, f"{i}\n")
        self.line_numbers.config(state="disabled")

    def on_scroll(self, *args):
        """Sinkronkan scrollbar area teks dan nomor baris."""
        self.text_area.yview(*args)
        self.line_numbers.yview(*args)

    def replace_special_characters(self, event):
        """Ganti spasi dengan '_' dan tab dengan '\\'."""
        allowed_chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_\\"

        if event.char == " ":  # Jika karakter adalah spasi
            self.text_area.insert(tk.INSERT, "_")
            return "break"
        elif event.keysym == "Tab":  # Jika tombol adalah Tab
            self.text_area.insert(tk.INSERT, "\\")
            return "break"
        elif event.keysym in ("Return", "BackSpace"):  # Izinkan Enter dan Backspace
            return
        elif event.char and event.char not in allowed_chars:  # Blokir karakter yang tidak diizinkan
            return "break"
        
    def before_save_checks(self):
        """Lakukan pemeriksaan sebelum menyimpan konten."""
        content = self.text_area.get("1.0", tk.END).strip()
        if self.check_forbidden_words(content):
            self.display_forbidden_word_warning()
            return False
        return True
    
    def check_forbidden_words(self, content):
        """Periksa apakah konten mengandung kata-kata terlarang dan simpan kata pertama yang ditemukan."""
        for word in self.forbidden_words:
            if word.lower() in content.lower():
                self.last_bad_word = word
                return True
        self.last_bad_word = None
        return False
    
    def display_forbidden_word_warning(self): 
        if self.current_warning_level < len(self.warning_messages):
            title, message = self.warning_messages[self.current_warning_level]

            if "{}" in title:
                title = title.format(self.last_bad_word)
            if "{}" in message:
                message = message.format(self.last_bad_word)

            if self.current_warning_level == 0:
              messagebox.showwarning(title, message)
            else:
              messagebox.showwarning(title, message)

            self.current_warning_level += 1

        if self.current_warning_level == len(self.warning_messages):
            messagebox.showerror("Maaf Sekali Lagi", "Saya tidak bisa mentolerir kata terlarang ini. Aplikasi akan berhenti.")
            sys.exit()
        
    def check_forbidden_words_dynamically(self, event=None):
        """Periksa secara dinamis apakah konten mengandung kata-kata terlarang."""
        content = self.text_area.get("1.0", tk.END).strip()
        found_forbidden = False

        for word in self.forbidden_words:
            if word.lower() in content.lower():
                self.last_bad_word = word
                self.display_forbidden_word_warning()
                found_forbidden = True
                break

        # Reset level jika tidak ada kata terlarang
        if not found_forbidden:
            self.current_warning_level = 0
            self.last_bad_word = None
