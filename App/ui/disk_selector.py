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
import threading
# Hapus import time yang tidak digunakan

class DiskSelector(ttk.LabelFrame):
    def __init__(self, parent, BASE_DIR, main_window):
        super().__init__(parent, text="Pilih Disk :")
        self.grid(row=0, column=0, padx=10, pady=10, sticky="nsew")
        self.parent = parent
        self.BASE_DIR = BASE_DIR
        self.main_window = main_window
        self.selected_disk = tk.StringVar()
        self.drives = []  # Initialize empty drives list
        self.scanning = False

        # Create widgets with loading state
        self.add_disk_selector_controls()
        
        # Start scanning disks in background
        self.start_disk_scan()
        
        # Start periodic scan
        self.schedule_disk_scan()

        # Configure grid to be resizable
        self.columnconfigure(0, weight=1)
        self.rowconfigure(0, weight=1)

    def add_disk_selector_controls(self):
        """Add combobox and labels with initial loading state"""
        # Combobox for drive selection
        self.disk_selector = ttk.Combobox(self, state="disabled", font=("Arial", 12), height=10, width=0)
        self.disk_selector.grid(row=0, column=0, padx=20, pady=10, sticky="new")
        self.disk_selector.set("Memindai disk...")

        # Frame for labels
        self.label_frame = ttk.Frame(self)
        self.label_frame.grid(row=1, column=0, padx=10, pady=5, sticky="new")

        # Labels for drive info
        self.selected_drive_letter_label = ttk.Label(self.label_frame, text="-", font=("Arial", 9), foreground="#999")
        self.selected_drive_letter_label.grid(row=0, column=0, sticky="ew")

        self.selected_drive_name_label = ttk.Label(self.label_frame, text="-", font=("Arial", 12), foreground="#666")
        self.selected_drive_name_label.grid(row=1, column=0, pady=5, sticky="ew")

        self.label_frame.columnconfigure(0, weight=1)

        # Bind selection event
        self.disk_selector.bind("<<ComboboxSelected>>", self.on_select)

    def start_disk_scan(self):
        """Start disk scanning in background thread"""
        if not self.scanning:
            self.scanning = True
            thread = threading.Thread(target=self._scan_disks_thread, daemon=True)
            thread.start()

    def schedule_disk_scan(self):
        """Schedule periodic disk scan"""
        self.start_disk_scan()
        # Reschedule every 5 seconds
        self.after(5000, self.schedule_disk_scan)

    def _scan_disks_thread(self):
        """Background thread for scanning disks"""
        try:
            # Get disk list
            new_drives = self.get_disk_names()
            
            # If drives list changed, update UI
            if new_drives != self.drives:
                self.drives = new_drives
                self.after(0, self._update_disk_selector)
                
        finally:
            self.scanning = False

    def _update_disk_selector(self):
        """Update disk selector UI in main thread"""
        # Format drives for display
        display_drives = [drive.replace("|", " ") for drive in self.drives]
        
        # Update combobox
        self.disk_selector["values"] = display_drives
        self.disk_selector["state"] = "readonly"
        
        # If nothing selected yet, clear loading text
        if not self.disk_selector.get() or self.disk_selector.get() == "Memindai disk...":
            self.disk_selector.set("")

    def on_select(self, event):
        """Handle disk selection"""
        selected_index = self.disk_selector.current()
        if selected_index >= 0:
            selected_drive_info = self.drives[selected_index].split("|")
            selected_letter = selected_drive_info[0]
            selected_name = selected_drive_info[1]

            self.selected_drive_letter_label.config(text="Arsip akan dibuat di :")
            self.selected_drive_name_label.config(text=f"{selected_letter}  {selected_name}")
            self.selected_disk.set(selected_letter)
            self.main_window.update_value("selected_disk", selected_letter)
        else:
            self.selected_drive_letter_label.config(text="-")
            self.selected_drive_name_label.config(text="-")

    def get_disk_names(self):
        """Get list of available drives and volume names"""
        disks = []
        try:
            result = subprocess.check_output(
                "wmic logicaldisk get caption, volumename", 
                shell=True, 
                text=True,
                creationflags=subprocess.CREATE_NO_WINDOW  # Hide console window
            ).splitlines()

            for line in result[1:]:  # Skip header
                parts = line.strip().split()
                if not parts:
                    continue
                    
                drive_letter = parts[0]
                volume_name = " ".join(parts[1:]) if len(parts) > 1 else "(No Label)"
                disks.append(f"{drive_letter}|{volume_name}")
                
        except subprocess.CalledProcessError as e:
            print(f"Error scanning disks: {e}")
            
        return disks

    def get_selected_drive_letter(self):
        """Return selected drive letter"""
        return self.selected_disk.get()
