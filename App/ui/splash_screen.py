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

import tkinter as tk
import os

class SplashScreen:
    def __init__(self, parent, BASE_DIR):
        """
        Inisialisasi splash screen dengan gambar.
        :param parent: Widget induk tempat splash screen akan ditempatkan.
        :param BASE_DIR: Direktori dasar tempat gambar berada.
        """
        self.parent = parent
        self.BASE_DIR = BASE_DIR  # Simpan BASE_DIR

        # Set path gambar splash screen berdasarkan BASE_DIR
        self.image_path = os.path.join(self.BASE_DIR, "img", "splash_screen.png")
        
        # Buat label untuk menampilkan gambar (jika image_path disediakan)
        self.splash_image = tk.PhotoImage(file=self.image_path)
        self.image_label = tk.Label(self.parent, image=self.splash_image)

    def show(self):
        """Tampilkan gambar splash screen pada widget induk."""
        self.image_label.pack(fill="both", expand=True)

    def hide(self):
        """Sembunyikan gambar splash screen."""
        self.image_label.pack_forget()
