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
from tkinter import filedialog
import os
import shutil

class RelocateFiles(ttk.LabelFrame):
    def __init__(self, parent, BASE_DIR, main_window):
        super().__init__(parent, text="Relokasi File", padding=10)
        self.grid(row=0, column=0, padx=10, pady=10, sticky="nsew")
        self.parent = parent
        self.BASE_DIR = BASE_DIR
        self.main_window = main_window
        self.create_widgets()

    def create_widgets(self):
        # Create left panel to list selected files
        self.left_panel = ttk.Frame(self)
        self.left_panel.grid(row=1, column=0, padx=(0, 10), sticky="nsew")

        # Create top panel with buttons to select files and folders inside left panel
        top_panel = ttk.Frame(self.left_panel)
        top_panel.pack(pady=(0, 10), fill="x")

        select_files_button = ttk.Button(top_panel, text="Pilih File", command=self.select_files, padding=5)
        select_files_button.pack(side="left", padx=(0, 5))

        or_label = ttk.Label(top_panel, text="atau")
        or_label.pack(side="left", padx=(0, 5))

        select_folder_button = ttk.Button(top_panel, text="Pilih Folder", command=self.select_folder, padding=5)
        select_folder_button.pack(side="left", padx=(0, 5))

        self.file_listbox = tk.Listbox(self.left_panel, selectmode=tk.MULTIPLE)
        self.file_listbox.pack(fill="both", expand=True)

        # Create right panel (empty for now)
        self.right_panel = ttk.Frame(self)
        self.right_panel.grid(row=1, column=1, sticky="nsew")

        # Create bottom panel with buttons
        bottom_panel = ttk.Frame(self)
        bottom_panel.grid(row=2, column=0, columnspan=2, padx=0, pady=(10, 0), sticky="ew")

        bottom_panel.columnconfigure(0, weight=1)

        move_button = ttk.Button(bottom_panel, text="Pindahkan", command=self.move_files, padding=5)
        move_button.grid(row=0, column=1, padx=(0, 10), sticky="e")

        copy_button = ttk.Button(bottom_panel, text="Salin", command=self.copy_files, padding=5)
        copy_button.grid(row=0, column=2, padx=(0, 10), sticky="e")

        reset_button = ttk.Button(bottom_panel, text="Reset", command=self.reset_files, padding=5)
        reset_button.grid(row=0, column=3, padx=(0, 0), sticky="e")

        # Create progress bar panel
        progress_panel = ttk.Frame(self)
        progress_panel.grid(row=3, column=0, columnspan=2, pady=(10, 0), sticky="ew")

        self.progress_bar = ttk.Progressbar(progress_panel, orient="horizontal", mode="determinate")
        self.progress_bar.pack(fill="x", expand=True)

        # Configure grid weights
        self.columnconfigure(0, weight=1)
        self.columnconfigure(1, weight=1)
        self.rowconfigure(1, weight=1)
        self.rowconfigure(2, weight=0)
        self.rowconfigure(3, weight=0)

    def select_files(self):
        file_paths = filedialog.askopenfilenames(title="Pilih File", filetypes=[("All Files", "*.*")])
        if file_paths:
            self.file_listbox.delete(0, tk.END)
            for file_path in file_paths:
                self.file_listbox.insert(tk.END, file_path)

    def select_folder(self):
        folder_path = filedialog.askdirectory(title="Pilih Folder")
        if folder_path:
            folder_files = [os.path.join(folder_path, f) for f in os.listdir(folder_path)]
            self.file_listbox.delete(0, tk.END)
            for file_path in folder_files:
                self.file_listbox.insert(tk.END, file_path)

    def move_files(self):
        # Function to move files
        pass

    def copy_files(self):
        destination_folder = filedialog.askdirectory(title="Pilih Folder Tujuan")
        if not destination_folder:
            return

        files = self.file_listbox.get(0, tk.END)
        if not files:
            return

        self.progress_bar["maximum"] = 100
        self.progress_bar["value"] = 0

        for file_path in files:
            try:
                self.copy_file_with_progress(file_path, destination_folder)
            except Exception as e:
                print(f"Error copying {file_path}: {e}")

        tk.messagebox.showinfo("Selesai", "Proses penyalinan selesai.")
        self.progress_bar["value"] = 0  # Reset progress bar
        self.main_window.update_status(f"File berhasil disalin ke {destination_folder}")

    def copy_file_with_progress(self, src, dst_folder):
        dst = os.path.join(dst_folder, os.path.basename(src))
        total_size = os.path.getsize(src)
        copied_size = 0

        with open(src, 'rb') as fsrc, open(dst, 'wb') as fdst:
            while True:
                buf = fsrc.read(1024 * 1024)  # Read in chunks of 1MB
                if not buf:
                    break
                fdst.write(buf)
                copied_size += len(buf)
                progress = (copied_size / total_size) * 100
                self.progress_bar["value"] = progress
                self.update_idletasks()

    def reset_files(self):
        # Function to reset file selection
        pass
