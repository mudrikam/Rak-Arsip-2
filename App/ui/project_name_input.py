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

import sys
import tkinter as tk
from tkinter import ttk
from tkinter import messagebox

from App.ui.core_scan import forbidden_words

class ProjectNameInput(ttk.LabelFrame):
    def __init__(self, parent, BASE_DIR, main_window):
        """
        Inisialisasi kelas ProjectNameInput.
        """
        super().__init__(parent, text="Masukkan Nama Arsip :")  # LabelFrame sebagai induk komponen
        self.grid(row=0, column=0, padx=10, pady=10, sticky="nsew")
        self.BASE_DIR = BASE_DIR
        
        self.main_window = main_window  # Simpan referensi ke MainWindow
        self.forbidden_words = forbidden_words
        self.project_name_value = tk.StringVar()  # Gunakan StringVar untuk nilai dinamis
        self._add_project_name_input()

    def _add_project_name_input(self):
        """
        Metode untuk membuat frame input nama Arsip.
        """
        # Widget Entry untuk nama Arsip
        self.project_name_entry = ttk.Entry(
            self, 
            font=("Lato Medium", 14), 
            justify="left", 
            textvariable=self.project_name_value
        )
        self.project_name_entry.place(x=10, y=10, width=self.winfo_width()-20, height=40)  # set width to 100%
        self.bind("<Configure>", self._resize_entry)  # bind resize event

        # Label untuk menampilkan nama Arsip yang telah diformat
        self.formatted_project_name_label = ttk.Label(
            self, 
            text="-", 
            font=("Helvetica", 10), 
            foreground="green"
        )
        self.formatted_project_name_label.place(x=10, y=55)  # Posisi di bawah entry

        # Checkbox untuk sanitasi karakter spesial
        self.skip_sanitization_var = tk.BooleanVar(value=True)
        self.skip_sanitization_var.trace_add("write", self._on_sanitization_change)
        self.skip_sanitization_checkbox = ttk.Checkbutton(
            self, 
            text="Sanitasi nama Arsip", 
            variable=self.skip_sanitization_var
        )
        self.skip_sanitization_checkbox.place(x=10, y=75)  # Posisi di bawah label

        # Bind event <KeyRelease> untuk memperbarui nama yang diformat
        self.project_name_entry.bind("<KeyRelease>", lambda e: (self._update_formatted_name(e), self.check_forbidden_words(e)))

        self.invalid_char_count = 0  # Inisialisasi counter karakter invalid
        self.hahaha_count = 0  # Inisialisasi counter untuk "hahaha"

        
    def check_forbidden_words(self, event=None):
        """
        Memeriksa apakah ada kata terlarang dalam input nama Arsip.
        Menampilkan pesan berbeda pada deteksi pertama dan kedua.
        """
        project_name = self.project_name_value.get().lower()
        found_word = None

        # Cari kata terlarang dalam input
        for word in self.forbidden_words:
            if word in project_name:
                found_word = word
                break  # Hentikan loop setelah menemukan kata pertama

        if found_word:
            if not hasattr(self, 'forbidden_word_detected'):
                self.forbidden_word_detected = False

            if not self.forbidden_word_detected:
                # Peringatan pertama
                messagebox.showinfo("Eh bentar...!", "Sepertinya ada yang salah dengan nama Arsip kamu. Tapi kalau itu memang benar, yaudah, abaikan aja deh.")
                self.forbidden_word_detected = True
                self.main_window.update_status("Peringatan: Kata terlarang terdeteksi!")
            else:
                # Peringatan kedua
                messagebox.showwarning("Cek lagi gak sih...?", f"Apa kamu beneran yakin nama Arsipmu aman? Soalnya '{found_word}' kayaknya nggak aman deh")
                self.main_window.update_status(f"Saran: '{found_word}' Saya anggap kata sensitif! (^_^)")
        else:
            # Reset status jika tidak ada kata terlarang
            if hasattr(self, 'forbidden_word_detected') and self.forbidden_word_detected:
                self.forbidden_word_detected = False
                self.main_window.update_status("Nama Arsip aman.")


    def _show_warning(self, title, message):
        """Menampilkan messagebox."""
        result = messagebox.showwarning(title, message)
        return result
    def _update_formatted_name(self, event=None):
        project_name = self.project_name_value.get()
        project_name = project_name[:40]

        formatted_name = ""
        invalid_char_detected = False

        if "maaf" in project_name.lower():
            if self.invalid_char_count == 0:
                self._show_warning("Eh...", "Buat apa minta maaf? udahlah gak usah aneh-aneh pakai karakter segala macam (-_-)")
                self.project_name_value.set("")
                self.formatted_project_name_label.config(text="", foreground="black")
                return
            elif self.invalid_char_count == 9:
                self._show_warning("Nahh... gitu dong!", "Baiklah dimaafkan tapi jangan diulangi ya (^_-)")
                self.main_window.update_status("Permintaan maaf diterima, aku harap kamu paham kesalahanmu!. (^_^)")
                self.project_name_value.set("")
                self.formatted_project_name_label.config(text="", foreground="black")
                self.invalid_char_count = 0
                return

        elif "hahaha" in project_name.lower():
            self.project_name_value.set("")
            self.formatted_project_name_label.config(text="", foreground="black")
            print(f"Haha Counter: {self.hahaha_count}")

            if self.hahaha_count == 0:
                self._show_warning("Serius dong!", "Ini aplikasi kerja bukan komedi loh! (-_-)")
                self.hahaha_count += 1
            elif self.hahaha_count >= 2:
                result = self._show_warning("Haha lucu ya?", "Bukannya kerja malah ketawa mulu, mau aku close aplikasinya?")
                if result:
                    self.master.destroy()
                    sys.exit()
                else:
                    self.hahaha_count = 0
            else:
                self._show_warning("Sana Lanjut...!", "Gak usah ketawa terus, sana kerja yang bener! (>_<)")
                self.hahaha_count += 1
            return
        
        
        for char in project_name:
            if self.skip_sanitization_var.get():
                # Jika dicentang, sanitasi ketat dilakukan
                if char.isalnum() or char == "_":
                    formatted_name += char
                elif char == " ":
                    formatted_name += "_"
                else:
                    invalid_char_detected = True
            else:
                # Jika tidak dicentang, semua karakter valid langsung ditambahkan
                if char.isalnum() or char == "_" or char == " ":
                    formatted_name += char
                else:
                    invalid_char_detected = True


        if invalid_char_detected:
            self.invalid_char_count += 1

            if self.invalid_char_count == 3:
                self._show_warning("Peringatan", "Jangan pakai karakter khusus nanti error Nehehe... (^_-)")
                self.main_window.update_status("Karakter seperti [<>:\"/\\|?*] tidak didukung saat membuat nama folder")
            elif self.invalid_char_count == 6:
                result = self._show_warning("Peringatan Keras!", "Kok masih ngeyel sih... kan sudah ku bilang bisa error (T_T)")
                if result:
                    self._show_warning("Keterlaluan!", "Sukurin aku hapus!")
                    self.project_name_value.set("")
                    formatted_name = ""
                    self.main_window.update_status("Dihapus karena karakter spesial.")
                else:
                    self.invalid_char_count = 0
            elif self.invalid_char_count == 9:
                if "maaf" not in project_name.lower():
                    self.main_window.update_status("Minta maaf sama Krea, kalau gak aplikasinya bakalan ditutup!.")
                    self._show_warning("Ultimatum!!!", "Kalau masih ngeyel aku tutup nih aplikasinya (-_-)")
            elif self.invalid_char_count >= 10:
                result = self._show_warning("Yasudah...", "Oke Byee....")
                if result:
                    self.master.destroy()
                    sys.exit()
                else:
                    self.invalid_char_count = 0

        self.project_name_value.set(formatted_name)

        if formatted_name:
            self.formatted_project_name_label.config(
                text=formatted_name,
                foreground="green"
            )
            self.main_window.update_value("project_name", formatted_name)
        else:
            self.formatted_project_name_label.config(
                text="",
                foreground="black"
            )

    def get_project_name(self):
        """
        Ambil nama Arsip yang telah diformat.
        """
        # Format nama Arsip sebelum mengembalikannya
        return self.project_name_value.get()
    
    def _on_sanitization_change(self, *args):
        """
        Tangani perubahan pada checkbox sanitasi.
        """
        if self.skip_sanitization_var.get():
            self.main_window.update_status("Lewati sanitasi, selanjutnya filter nama Arsip aku serahkan padamu!")
        else:
            self.main_window.update_status("Serahkan padaku! nama Arsip akan disanitasi supaya aman. (^_-)")

    def _resize_entry(self, event):
        """Resize the entry dynamically."""
        self.project_name_entry.place_configure(width=event.width-20)
