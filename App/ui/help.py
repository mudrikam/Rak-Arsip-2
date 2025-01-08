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

import re
import tkinter as tk
from tkinter import ttk
import os
import markdown
from tkhtmlview import HTMLLabel

class LoadHelpFile(ttk.LabelFrame):
    def __init__(self, parent, x, y, width, height, BASE_DIR, main_window):
        """
        Inisialisasi kelas LoadHelpFile untuk menampilkan konten file bantuan.
        """
        super().__init__(parent, text="Bantuan :")  # LabelFrame sebagai widget induk
        self.place(x=x, y=y, width=width, height=height)  # Atur posisi dan ukuran
        self.BASE_DIR = BASE_DIR
        
        self.main_window = main_window  # Simpan referensi ke MainWindow

        # Buat frame untuk menampung HTMLLabel
        self.html_frame = tk.Frame(self, bg="white")
        self.html_frame.pack(fill='both', expand=True, padx=0, pady=0)

        # Muat dan tampilkan file README.md
        self.load_help_file()

    def load_help_file(self):
        """
        Muat konten file README.md, konversi ke HTML, dan tampilkan.
        """
        # Set path file bantuan di luar folder App
        help_file_path = os.path.join(os.path.dirname(self.BASE_DIR), "README.md")
        print(help_file_path)

        try:
            # Pastikan file ada
            if os.path.exists(help_file_path):
                with open(help_file_path, "r", encoding="utf-8") as file:
                    file_content = file.read()

                    # Konversi konten Markdown ke HTML
                    html_content = markdown.markdown(file_content)

                    # Terapkan gaya ke tag HTML tertentu
                    tag_styles = {
                        "p": "font-size: 12px; line-height: 1.5; font-weight: normal; ",
                        "h1": "font-size: 18px; color: #ff7d19; font-weight: normal; ",
                        "h2": "font-size: 16px; font-weight: normal; ",
                        "h3": "font-size: 14px; font-weight: normal; ",
                        "li": "font-size: 12px; list-style-type: disc; font-weight: normal; ",
                    }

                    new_html_content = self.replace_tags(html_content, tag_styles)
                    
                    # # Ekspor konten ke file HTML baru (untuk tujuan pengujian)
                    # export_path = r"Z:\help_content.html"
                    # with open(export_path, "w", encoding="utf-8") as export_file:
                    #     export_file.write(new_html_content)
                    # print(f"Konten diekspor ke {export_path}")  # Pesan pengujian ekspor

                    # Buat widget HTMLLabel untuk merender konten HTML yang telah diberi gaya
                    html_label = HTMLLabel(self.html_frame, html=new_html_content, background="white", padx=40, pady=40,)
                    html_label.pack(fill="both", expand=True)
                    html_label.config(cursor="hand2")
                    
                    # Perbarui status bar
                    self.main_window.update_status("Kalau bingung cara pakainya bisa cek di tab tanda tanya [?] ya (^_-)")
            else:
                error_message = f"File tidak ditemukan: {help_file_path}"
                self.show_error(error_message)
        except Exception as e:
            self.show_error(f"Error memuat file: {str(e)}")

    def show_error(self, error_message):
        """
        Tampilkan pesan kesalahan di label frame jika terjadi kesalahan.
        """
        error_label = tk.Label(self.html_frame, text=error_message, fg="red", font=("Arial", 12))
        error_label.pack(padx=10, pady=10)

    def replace_tags(self, html_content, tag_styles):
        """Mengganti beberapa tag dengan style sekaligus."""
        def replace_match(match):
            tag = match.group(1)
            if tag in tag_styles:
                style = tag_styles[tag]
                return f'<{tag} style="{style}">'
            return match.group(0)  # Kembalikan match asli jika tag tidak ada di dictionary

        tag_regex = "|".join(tag_styles.keys())  # Membuat regex dari key dictionary
        pattern = rf"<({tag_regex})>"  # Membuat regex dengan f-string
        return re.sub(pattern, replace_match, html_content)


