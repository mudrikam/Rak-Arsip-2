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

import os
import csv
import tkinter as tk
from tkinter import ttk
from tkinter import messagebox
from tkinter import filedialog
import webbrowser
from PIL import Image, ImageTk

class LibraryManager:
    def __init__(self, base_dir):
        self.BASE_DIR = os.path.join(base_dir, "Database", "Library")
        self.csv_file_path = os.path.join(self.BASE_DIR, "project_library.csv")

    def initialize_library(self):
        """Initialize directory and library file"""
        try:
            os.makedirs(self.BASE_DIR, exist_ok=True)
            
            if not os.path.exists(self.csv_file_path):
                with open(self.csv_file_path, mode="w", newline="", encoding="utf-8") as file:
                    writer = csv.writer(file)
                    writer.writerow(["No", "Tanggal", "Nama", "Lokasi"])
                return "new"  # Return "new" if file was created
            return "exists"  # Return "exists" if file already existed
            
        except Exception as e:
            return False

    def ensure_library_exists(self):
        """Ensure library exists and is initialized"""
        if not os.path.exists(self.csv_file_path):
            return self.initialize_library()
        return True

    def get_library_path(self):
        """Return the path to the library file"""
        return self.csv_file_path

class ProjectLibrary(ttk.LabelFrame):
    def __init__(self, parent, BASE_DIR, main_window):
        super().__init__(parent, text="Daftar Arsip yang telah dibuat :", padding=10)
        self.grid(row=0, column=0, padx=10, pady=10, sticky="nsew")
        self.main_window = main_window
        
        # Create LibraryManager instance
        self.library_manager = LibraryManager(BASE_DIR)
        
        # Setup directory and file paths through library manager
        self.BASE_DIR = os.path.join(BASE_DIR, "Database", "Library")
        self.csv_file_path = self.library_manager.get_library_path()
        
        # Initialize directory and file first through library manager
        self.initialize_library()

        # Frame untuk tombol pencarian dan buka
        self.search_frame = ttk.Frame(self)
        self.search_frame.pack(pady=5, fill=tk.X)

        # Label "Cari :"
        self.search_label = ttk.Label(self.search_frame, text="Cari :")
        self.search_label.grid(row=0, column=0, padx=(0,5), sticky="w")  # sticky left

        # Entry untuk pencarian
        self.search_var = tk.StringVar()
        self.search_entry = ttk.Entry(self.search_frame, textvariable=self.search_var, font=("Lato Medium", 14))
        self.search_entry.grid(row=0, column=1, padx=(0,5), sticky="w")  # sticky left
        self.search_entry.config(width=20)  # set fixed width
        self.search_entry.bind("<KeyRelease>", self.search_library)
        self.search_entry.bind("<Double-Button-1>", self.clear_search)

        # Load button icons
        self.open_icon = self._load_icon(os.path.join(BASE_DIR, "Img", "icon", "ui", "folder.png"))
        self.backup_icon = self._load_icon(os.path.join(BASE_DIR, "Img", "icon", "ui", "backup.png"))
        self.import_icon = self._load_icon(os.path.join(BASE_DIR, "Img", "icon", "ui", "import.png"))
        self.restore_icon = self._load_icon(os.path.join(BASE_DIR, "Img", "icon", "ui", "restore.png"))

        # Update open button with icon
        self.open_button = ttk.Button(
            self.search_frame, 
            text="Buka Folder",
            image=self.open_icon,
            compound='left',
            command=self.open_file,
            state=tk.DISABLED,
            padding=5
        )
        self.open_button.grid(row=0, column=2, padx=(5,0), sticky="e")

        self.search_frame.columnconfigure(1, weight=0)  # remove weight from column 1
        self.search_frame.columnconfigure(2, weight=1)  # set weight to 1 for column 2
        
        # Frame untuk Treeview dan scrollbar
        self.tree_frame = ttk.Frame(self)
        self.tree_frame.pack(fill=tk.BOTH, expand=True)

        self.tree = ttk.Treeview(self.tree_frame, columns=("No", "Tanggal", "Nama", "Lokasi"), show="headings", height=6)
        self.tree.heading("No", text="No")
        self.tree.heading("Tanggal", text="Tanggal")
        self.tree.heading("Nama", text="Nama")
        self.tree.heading("Lokasi", text="Lokasi")
        
        # Set fixed width for No and Tanggal columns
        self.tree.column("No", width=40, minwidth=40, stretch=False, anchor="center")
        self.tree.column("Tanggal", width=150, minwidth=150, stretch=False, anchor="center")
        self.tree.column("Nama", width=150, anchor="w")
        self.tree.column("Lokasi", width=300, anchor="w")
        
        # Add a scrollbar to the Treeview
        self.tree_scrollbar = ttk.Scrollbar(self.tree_frame, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscroll=self.tree_scrollbar.set)
        self.tree_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.tree.pack(fill=tk.BOTH, expand=True)
        self.tree.bind("<<TreeviewSelect>>", self.on_row_select)
        self.tree.bind("<Double-Button-1>", self.on_double_click)
        self.load_library()
        self.selected_file = None
        self.check_for_upDates()

        # Frame untuk tombol cadangkan dan impor
        self.button_frame = ttk.Frame(self)
        self.button_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=(10, 0))

        # Update backup and import buttons with icons
        self.backup_button = ttk.Button(
            self.button_frame, 
            text="Cadangkan",
            image=self.backup_icon,
            compound='left',
            command=self.backup_library,
            padding=5
        )
        self.backup_button.pack(side=tk.LEFT, padx=(0, 10))

        self.import_button = ttk.Button(
            self.button_frame, 
            text="Impor",
            image=self.import_icon,
            compound='left', 
            command=self.import_existing_library,
            padding=5
        )
        self.import_button.pack(side=tk.LEFT, padx=(0, 10))

        self.restore_button = ttk.Button(
            self.button_frame,
            text="Pulihkan",
            image=self.restore_icon,
            compound='left',
            command=self.restore_library,
            padding=5,
            state="disabled"
        )
        self.restore_button.pack(side=tk.LEFT)

        # Configure grid to be resizable with weight constraints
        self.columnconfigure(0, weight=1)
        self.rowconfigure(1, weight=1)

        # Bind the configure event to adjust widget sizes dynamically
        self.bind("<Configure>", self.on_resize)

    def initialize_library(self):
        """Initialize directory and library file"""
        result = self.library_manager.initialize_library()
        if result == "new":
            self.last_modified_time = os.path.getmtime(self.library_manager.get_library_path())
            self.main_window.update_status("Daftar Pustaka baru telah dibuat.")
        elif result == "exists":
            self.last_modified_time = os.path.getmtime(self.library_manager.get_library_path())
        else:
            self.main_window.update_status("Error initializing library")
            messagebox.showerror("Error", "Gagal membuat direktori/file")
        return result in ["new", "exists"]

    def load_library(self):
        """Load library data from CSV file with validation."""
        self.tree.delete(*self.tree.get_children())
        
        if not os.path.exists(self.csv_file_path):
            if not self.initialize_library():
                return
            
        try:
            rows = []
            with open(self.csv_file_path, mode="r", encoding="utf-8") as file:
                reader = csv.reader(file)
                header = next(reader, None)
                
                if header != ["No", "Tanggal", "Nama", "Lokasi"]:
                    raise ValueError("Format CSV tidak valid")
                
                # Perbaiki validasi row untuk lebih efisien
                for row in reader:
                    if len(row) == 4:
                        try:
                            int(row[0])  # Validate No is numeric
                            rows.append(row)
                        except ValueError:
                            continue
                        
            if rows:
                rows.sort(key=lambda x: int(x[0]), reverse=True)
                for row in rows:
                    self.tree.insert("", "end", values=row)
                    
        except Exception as e:
            self.main_window.update_status(f"Error loading library: {str(e)}")
            messagebox.showerror("Error", f"Gagal memuat Daftar Pustaka:\n{e}")

    def on_row_select(self, event):
        selected_item = self.tree.selection()
        if selected_item:
            item = self.tree.item(selected_item[0])
            self.selected_file = item["values"][3]
            self.open_button.config(state=tk.NORMAL)
            file_dir=self.selected_file
            self.main_window.update_status(f"Buka di Explorer : {file_dir}")

    def open_file(self):
        if self.selected_file and os.path.exists(self.selected_file):
            try:
                webbrowser.open(self.selected_file)
            except Exception as e:
                messagebox.showerror("Error", f"Failed to open file:\n{e}")
        else:
            messagebox.showwarning("Periksa!", "Sepertinya ada masalah pada lokasi file")

    def check_for_upDates(self):
        """Check for file updates and .old file existence"""
        try:
            current_modified_time = os.path.getmtime(self.csv_file_path)
            if current_modified_time != self.last_modified_time:
                self.last_modified_time = current_modified_time
                self.load_library()
            # Only call update_restore_button if it exists and has been initialized
            if hasattr(self, 'restore_button'):
                self.update_restore_button()
        except FileNotFoundError:
            # If file is deleted, try to recreate it
            if self.initialize_library():
                self.load_library()
        except Exception as e:
            self.main_window.update_status(f"Error checking updates: {str(e)}")
        finally:
            self.after(1000, self.check_for_upDates)

    def search_library(self, event=None):
        """Cari baris dalam file CSV yang sesuai dengan kata kunci."""
        keyword = self.search_var.get().strip().lower()
        self.tree.delete(*self.tree.get_children())  # Hapus semua baris dari Treeview

        if not keyword:
            self.load_library()  # Muat ulang semua data jika entri pencarian kosong
            return

        matching_rows = []
        with open(self.csv_file_path, mode="r", encoding="utf-8") as file:
            reader = csv.reader(file)
            next(reader, None)  # Lewati baris header
            for row in reader:
                if any(keyword in field.lower() for field in row):  # Periksa apakah kata kunci ada di bidang mana pun
                    matching_rows.append(row)

        for row in matching_rows:
            self.tree.insert("", "end", values=row)
            
    def clear_search(self, event=None):
        self.search_var.set("")  # Setel StringVar menjadi kosong
        self.search_library()  # Panggil search_library agar data kembali semula
            
    def on_double_click(self, event):
        selected_item = self.tree.selection()
        if selected_item:
            item = self.tree.item(selected_item[0])
            self.selected_file = item["values"][3]
            self.open_file()
            self.clear_search()
            
    def backup_library(self):
        try:
            if os.name == 'nt':  # Windows
                initialdir = "::{20D04FE0-3AEA-1069-A2D8-08002B30309D}"
            # Tampilkan dialog untuk memilih lokasi penyimpanan file backup
            backup_file_path = filedialog.asksaveasfilename(
                initialdir=initialdir,
                initialfile="project_library_backup.csv",
                defaultextension=".csv",
                filetypes=[("CSV files", "*.csv"), ("All files", "*.*")]
            )
            if not backup_file_path:
                return  # Jika pengguna membatalkan dialog, keluar dari fungsi

            with open(self.csv_file_path, mode="r", encoding="utf-8") as source_file:
                with open(backup_file_path, mode="w", newline="", encoding="utf-8") as backup_file:
                    reader = csv.reader(source_file)
                    writer = csv.writer(backup_file)
                    for row in reader:
                        writer.writerow(row)
            messagebox.showinfo(f"Daftar Pustaka telah dicadangkan.", f"Pastikan simpan file {os.path.basename(backup_file_path)} ke tempat aman.\n\nDaftar Pustaka dapat dikembalikan ke :\n\nRak Arsip\\App\\Database\\Library \n\nJika aplikasi Rak Arsip mengalami masalah.")
            self.main_window.update_status(f"Amaannn...., daftar Pustaka sudah dicadangkan (^_^)")
        except Exception as e:
            messagebox.showerror("Error", f"Gagal mencadangkan arsip:\n{e}")


    def import_existing_library(self):
        try:
            import_file_path = filedialog.askopenfilename(
                filetypes=[("CSV files", "*.csv"), ("All files", "*.*")]
            )
            if not import_file_path:
                return

            # Backup existing file with .old extension first
            if os.path.exists(self.csv_file_path):
                backup_path = f"{self.csv_file_path}.old"
                os.replace(self.csv_file_path, backup_path)

            # Read existing data from backup
            existing_rows = []
            last_no = 0
            with open(backup_path, 'r', encoding='utf-8') as existing_file:
                reader = csv.reader(existing_file)
                header = next(reader)  # Skip header
                for row in reader:
                    existing_rows.append(row)
                    try:
                        last_no = max(last_no, int(row[0]))
                    except ValueError:
                        continue

            # Read and process imported data
            imported_rows = []
            with open(import_file_path, 'r', encoding='utf-8') as source:
                reader = csv.reader(source)
                header = next(reader)  # Get header row
                
                # Validate header
                if header != ["No", "Tanggal", "Nama", "Lokasi"]:
                    raise ValueError("Format CSV tidak valid")
                
                # Add imported data with new numbers and _import suffix
                for row in reader:
                    if len(row) == 4:
                        last_no += 1
                        new_row = row.copy()
                        new_row[0] = str(last_no)  # Update number
                        new_row[2] = f"{row[2]}_import"  # Add _import to name
                        imported_rows.append(new_row)

            # Write combined data to library file
            with open(self.csv_file_path, 'w', newline='', encoding='utf-8') as dest:
                writer = csv.writer(dest)
                writer.writerow(["No", "Tanggal", "Nama", "Lokasi"])  # Write header
                writer.writerows(existing_rows)  # Write existing data
                writer.writerows(imported_rows)  # Append imported data

            messagebox.showinfo("Berhasil", 
                f"Berhasil menambahkan {len(imported_rows)} data baru ke Daftar Pustaka.\n" +
                "Data lama telah dicadangkan dengan ekstensi .old")
            self.main_window.update_status("Data baru berhasil ditambahkan dan data lama dicadangkan")
            self.load_library()
            self.update_restore_button()

        except ValueError as ve:
            messagebox.showerror("Error", str(ve))
        except Exception as e:
            messagebox.showerror("Error", f"Gagal mengimpor Daftar Pustaka:\n{e}")

    def restore_library(self):
        """Restore library from .old file"""
        if not messagebox.askyesno("Konfirmasi Pemulihan", 
            "Tindakan ini akan:\n"
            "1. Menghapus daftar pustaka yang baru diimpor\n"
            "2. Memulihkan daftar pustaka yang lama\n\n"
            "Kamu yakin ingin melanjutkan?"):
            return

        try:
            old_file = f"{self.csv_file_path}.old"
            if os.path.exists(old_file):
                # Remove current file
                if os.path.exists(self.csv_file_path):
                    os.remove(self.csv_file_path)
                
                # Restore .old file
                os.rename(old_file, self.csv_file_path)
                
                messagebox.showinfo("Sukses", "Daftar pustaka berhasil dipulihkan ke versi sebelumnya")
                self.main_window.update_status("Daftar pustaka berhasil dipulihkan")
                self.load_library()
                self.update_restore_button()
            else:
                messagebox.showinfo("Informasi", "Tidak ada file cadangan yang dapat dipulihkan")
                
        except Exception as e:
            messagebox.showerror("Error", f"Gagal memulihkan daftar pustaka:\n{e}")

    def update_restore_button(self):
        """Enable/disable restore button based on existence of .old file"""
        old_file = f"{self.csv_file_path}.old"
        if os.path.exists(old_file):
            self.restore_button.configure(state="normal")
        else:
            self.restore_button.configure(state="disabled")

    def on_resize(self, event):
        """Adjust column widths dynamically based on window size."""
        width = self.winfo_width()
        # Skip No and Tanggal columns as they have fixed width
        fixed_width = 40 + 150  # No (40) + Tanggal (150)
        remaining_width = width - fixed_width
        self.tree.column("Nama", width=int(remaining_width * 0.35))
        self.tree.column("Lokasi", width=int(remaining_width * 0.65))

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

