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

import tkinter as tk
from tkinter import ttk
import os

class LoaderBar:
    def __init__(self, parent, BASE_DIR, progress_bar_length=300):
        """
        Inisialisasi loader bar (label progress dengan gambar dan progress bar).
        :param parent: Widget induk tempat loader akan ditempatkan.
        :param BASE_DIR: Direktori dasar tempat gambar dan sumber daya berada.
        :param progress_bar_length: Panjang progress bar.
        """
        self.parent = parent
        self.BASE_DIR = BASE_DIR  # Simpan BASE_DIR

        # Set path gambar loader berdasarkan BASE_DIR
        self.image_path = os.path.join(self.BASE_DIR, "img", "loader.ppm")
        
        # Buat label untuk menampilkan gambar (jika image_path disediakan)
        self.loader_image = tk.PhotoImage(file=self.image_path)
        self.image_label = tk.Label(self.parent, image=self.loader_image)
        
        # Buat progress bar
        self.progress_bar = ttk.Progressbar(self.parent, length=progress_bar_length, mode='determinate', maximum=100)
        
        self.progress = 0  # Nilai awal progress

    def start_loading(self, callback=None):
        """
        Mulai proses loading dengan menampilkan gambar dan memperbarui progress bar.
        :param callback: Fungsi yang dipanggil saat loading selesai (opsional).
        """
        self._display_loader()
        self._update_progress(callback)

    def _display_loader(self):
        """Tampilkan gambar loader dan progress bar pada widget induk."""
        self.image_label.pack(pady=50)  # Tampilkan gambar di tengah jendela
        self.progress_bar.pack(pady=20)  # Posisi progress bar di bawah gambar

    def _update_progress(self, callback):
        """
        Perbarui nilai progress bar dan panggil callback saat loading selesai.
        """
        self.progress += 1
        self.progress_bar['value'] = self.progress

        if self.progress < 100:
            self.parent.after(5, self._update_progress, callback)  # Lanjutkan memperbarui progress bar
        else:
            # Hentikan progress bar dan sembunyikan elemen loading
            self.progress_bar.stop()
            self.image_label.pack_forget()  # Sembunyikan gambar
            self.progress_bar.pack_forget()  # Sembunyikan progress bar
            if callback:
                callback()  # Panggil fungsi callback setelah loading selesai
