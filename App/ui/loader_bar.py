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
        Initializes the loader bar (progress label with image and progress bar).
        :param parent: Parent widget where the loader will be placed.
        :param BASE_DIR: The base directory where images and resources are located.
        :param progress_bar_length: The length of the progress bar.
        """
        self.parent = parent
        self.BASE_DIR = BASE_DIR  # Store BASE_DIR

        # Set the loader image path based on BASE_DIR
        self.image_path = os.path.join(self.BASE_DIR, "img", "loader.ppm")
        
        # Create a label to display the image (if image_path is provided)
        self.loader_image = tk.PhotoImage(file=self.image_path)
        self.image_label = tk.Label(self.parent, image=self.loader_image)
        
        # Create progress bar
        self.progress_bar = ttk.Progressbar(self.parent, length=progress_bar_length, mode='determinate', maximum=100)
        
        self.progress = 0  # Initial progress value

    def start_loading(self, callback=None):
        """
        Starts the loading process by displaying the image and updating the progress bar.
        :param callback: Function to call when loading is finished (optional).
        """
        self._display_loader()
        self._update_progress(callback)

    def _display_loader(self):
        """Display the loader image and progress bar on the parent widget."""
        self.image_label.pack(pady=50)  # Display the image at the center of the window
        self.progress_bar.pack(pady=20)  # Position progress bar below the image

    def _update_progress(self, callback):
        """
        Updates the progress bar value and triggers the callback when loading is complete.
        """
        self.progress += 1
        self.progress_bar['value'] = self.progress

        if self.progress < 100:
            self.parent.after(5, self._update_progress, callback)  # Continue updating the progress bar
        else:
            # Stop the progress bar and hide loading elements
            self.progress_bar.stop()
            self.image_label.pack_forget()  # Hide the image
            self.progress_bar.pack_forget()  # Hide the progress bar
            if callback:
                callback()  # Call the callback function after loading is complete
