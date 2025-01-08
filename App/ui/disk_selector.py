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
from tkinter import ttk
import subprocess

class DiskSelector(ttk.LabelFrame):
    def __init__(self, parent, BASE_DIR, main_window):
        super().__init__(parent, text="Pilih Disk :")
        self.grid(row=0, column=0, padx=10, pady=10, sticky="nsew")  # Use grid for dynamic resizing
        self.parent = parent
        self.BASE_DIR = BASE_DIR
        self.main_window = main_window
        
        # StringVar untuk menyimpan disk yang dipilih
        self.selected_disk = tk.StringVar()

        # Ambil daftar drive
        self.drives = self.get_disk_names()

        # Tambahkan kontrol untuk memilih disk
        self.add_disk_selector_controls()

        # Configure grid to be resizable
        self.columnconfigure(0, weight=1)
        self.rowconfigure(0, weight=1)

    def add_disk_selector_controls(self):
        """Menambahkan combobox dan label untuk memilih disk."""
        # Format untuk menampilkan drives di combobox
        display_drives = [drive.replace("|", " ") for drive in self.drives]

        # Combobox untuk memilih drive
        self.disk_selector = ttk.Combobox(self, values=display_drives, state="readonly", font=("Arial", 12), height=10)  # increase height to show more items
        self.disk_selector.grid(row=0, column=0, padx=20, pady=10, sticky="new")  # sticky top

        # Set awal combobox kosong
        self.disk_selector.set("")  

        # Frame untuk label drive letter dan drive name
        self.label_frame = ttk.Frame(self)
        self.label_frame.grid(row=1, column=0, padx=10, pady=5, sticky="new")  # sticky below disk selector

        # Label untuk menampilkan drive letter dan volume name
        self.selected_drive_letter_label = ttk.Label(self.label_frame, text="-", font=("Arial", 9), foreground="#999", anchor="center")
        self.selected_drive_letter_label.grid(row=0, column=0, sticky="ew")  # sticky expand horizontally

        self.selected_drive_name_label = ttk.Label(self.label_frame, text="-", font=("Arial", 12), foreground="#666", anchor="center")
        self.selected_drive_name_label.grid(row=1, column=0, pady=5, sticky="ew")  # sticky expand horizontally

        # Configure column to center align the labels
        self.label_frame.columnconfigure(0, weight=1)

        # Fungsi callback untuk memperbarui label ketika memilih drive
        def on_select(event):
            selected_index = self.disk_selector.current()
            if (selected_index >= 0):
                selected_drive_info = self.drives[selected_index].split("|")  # Pisahkan menggunakan delimiter "|"
                selected_letter = selected_drive_info[0]
                selected_name = selected_drive_info[1]

                # Update label dengan informasi drive yang dipilih
                self.selected_drive_letter_label.config(text=f"Arsip akan dibuat di :")
                self.selected_drive_name_label.config(text=f"{selected_letter}  {selected_name}")

                # Set selected letter pada StringVar
                self.selected_disk.set(selected_letter)

                # Update nilai selected_disk di main_window
                self.main_window.update_value("selected_disk", selected_letter)

                print(f"Selected Drive Letter: {selected_letter}")
            else:
                self.selected_drive_letter_label.config(text="None")
                self.selected_drive_name_label.config(text="None")
                print("No drive selected.")

        # Bind event ke Combobox
        self.disk_selector.bind("<<ComboboxSelected>>", on_select)

    def get_disk_names(self):
        """
        Mengambil daftar drive dan nama volume yang tersedia.
        """
        disks = []
        try:
            # Menggunakan perintah wmic untuk mengambil nama drive dan volume
            result = subprocess.check_output("wmic logicaldisk get caption, volumename", shell=True, text=True).splitlines()
            for line in result[1:]:
                parts = line.strip().split()
                if len(parts) >= 2:
                    drive_letter = parts[0]
                    volume_name = " ".join(parts[1:])  # Gabungkan nama volume jika ada spasi
                    disks.append(f"{drive_letter}|{volume_name}")  # Gunakan delimiter untuk memisahkan drive dan volume name
                elif len(parts) == 1:
                    drive_letter = parts[0]
                    disks.append(f"{drive_letter}|(No Label)")  # Tambahkan "(No Label)" jika volume name kosong
        except subprocess.CalledProcessError:
            print("Error fetching disk names.")
        return disks

    def get_selected_drive_letter(self):
        """Mengembalikan drive letter yang dipilih."""
        return self.selected_disk.get()  # Mengakses nilai dari StringVar yang menyimpan drive letter yang dipilih
