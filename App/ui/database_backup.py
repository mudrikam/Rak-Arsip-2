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
import zipfile
from datetime import date
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import threading
import time
from PIL import Image, ImageTk

class DatabaseBackup(ttk.LabelFrame):
    def __init__(self, parent, BASE_DIR, main_window):
        super().__init__(parent, text="Cadangkan Database :", padding=10)
        self.grid(row=0, column=0, padx=10, pady=10, sticky="nsew")
        self.BASE_DIR = BASE_DIR
        self.main_window = main_window

        # Load button icons
        self.backup_icon = self._load_icon(os.path.join(BASE_DIR, "Img", "icon", "ui", "backup.png"))
        self.import_icon = self._load_icon(os.path.join(BASE_DIR, "Img", "icon", "ui", "import.png"))
        self.restore_icon = self._load_icon(os.path.join(BASE_DIR, "Img", "icon", "ui", "restore.png"))

        # Frame for buttons
        self.button_frame = ttk.Frame(self)
        self.button_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=(10, 0))  # Moved to bottom

        # Update buttons with icons
        self.backup_button = ttk.Button(self.button_frame, 
            text="Cadangkan",
            image=self.backup_icon, compound='left',
            command=self.export_database, padding=5)
        self.backup_button.pack(side=tk.LEFT, padx=(0, 10), pady=5)

        self.import_button = ttk.Button(self.button_frame,
            text="Impor",
            image=self.import_icon, compound='left',
            command=self.import_database, padding=5)
        self.import_button.pack(side=tk.LEFT, pady=5)

        self.restore_button = ttk.Button(self.button_frame,
            text="Pulihkan",
            image=self.restore_icon, compound='left',
            command=self.restore_database, padding=5, state="disabled")
        self.restore_button.pack(side=tk.LEFT, padx=(10,0), pady=5)

        # Scrollable Treeview for files
        self.file_treeview = ttk.Treeview(self, columns=("No", "Direktori", "File"), show="headings")
        self.file_treeview.heading("No", text="No")
        self.file_treeview.heading("Direktori", text="Direktori")
        self.file_treeview.heading("File", text="File")
        
        # Set fixed column widths - update initial widths
        self.file_treeview.column("No", width=40, minwidth=40, stretch=False, anchor="center")
        self.file_treeview.column("Direktori", width=200, anchor="w")
        self.file_treeview.column("File", width=200, anchor="w")
        
        self.file_treeview.pack(side=tk.LEFT, fill="both", expand=True)
        self.scrollbar = ttk.Scrollbar(self, orient="vertical", command=self.file_treeview.yview)
        self.scrollbar.pack(side=tk.RIGHT, fill="y")
        self.file_treeview.config(yscrollcommand=self.scrollbar.set)
        self.update_file_list()

        # Start a thread to monitor the database directory
        self.monitor_thread = threading.Thread(target=self.monitor_database_directory, daemon=True)
        self.monitor_thread.start()

        # Bind the configure event to adjust widget sizes dynamically
        self.bind("<Configure>", self.on_resize)

    def update_file_list(self):
        """Update the Treeview with the list of files to be backed up."""
        for item in self.file_treeview.get_children():
            self.file_treeview.delete(item)
        database_dir = os.path.join(self.BASE_DIR, "Database")
        file_no = 1
        for root, dirs, files in os.walk(database_dir):
            for file in files:
                if not file.endswith(".old"):
                    directory = os.path.relpath(root, self.BASE_DIR)
                    self.file_treeview.insert("", "end", values=(file_no, directory, file))
                    file_no += 1

    def export_database(self):
        """Export the database to a zip file."""
        default_filename = f"Rak-Arsip-DB-{date.today().strftime('%Y-%m-%d')}.zip"
        zip_filepath = filedialog.asksaveasfilename(defaultextension=".zip", filetypes=[("Zip files", "*.zip")], initialfile=default_filename)
        if not zip_filepath:
            return

        database_dir = os.path.join(self.BASE_DIR, "Database")
        with zipfile.ZipFile(zip_filepath, 'w', zipfile.ZIP_DEFLATED) as zipf:
            for root, dirs, files in os.walk(database_dir):
                for file in files:
                    if not file.endswith(".old"):
                        file_path = os.path.join(root, file)
                        zipf.write(file_path, os.path.relpath(file_path, self.BASE_DIR))

        messagebox.showinfo("Sukses", f"Database berhasil dicadangkan ke {zip_filepath}")
        self.main_window.update_status(f"Database berhasil dicadangkan ke {zip_filepath}")

    def import_database(self):
        """Import a zip file into the database directory."""
        try:
            zip_filepath = filedialog.askopenfilename(filetypes=[("Zip files", "*.zip")])
            if not zip_filepath:
                print("No file selected")
                return

            print(f"Selected file: {zip_filepath}")
            database_dir = os.path.join(self.BASE_DIR)
            
            # Verify zip file is valid
            if not zipfile.is_zipfile(zip_filepath):
                messagebox.showerror("Error", "File yang dipilih bukan file zip yang valid")
                return
                
            with zipfile.ZipFile(zip_filepath, 'r') as zipf:
                # Check if zip contains any files
                files = zipf.namelist()
                if not files:
                    messagebox.showwarning("Peringatan", "File zip kosong")
                    return
                    
                print(f"Files in zip: {files}")
                
                for file_info in zipf.infolist():
                    extracted_path = os.path.join(database_dir, file_info.filename)
                    extracted_dir = os.path.dirname(extracted_path)
                    
                    # Create directory if it doesn't exist
                    if not os.path.exists(extracted_dir):
                        os.makedirs(extracted_dir)
                        
                    print(f"Extracting: {file_info.filename} to {extracted_path}")
                    
                    # Backup existing file if it exists
                    if os.path.exists(extracted_path):
                        backup_path = f"{extracted_path}.old"
                        try:
                            os.replace(extracted_path, backup_path)
                            print(f"Backed up: {extracted_path} to {backup_path}")
                        except Exception as e:
                            print(f"Error backing up file: {e}")
                            
                    # Extract new file
                    try:
                        zipf.extract(file_info, database_dir)
                        print(f"Successfully extracted: {file_info.filename}")
                    except Exception as e:
                        print(f"Error extracting file: {e}")
                        messagebox.showerror("Error", f"Gagal mengekstrak file: {file_info.filename}\n{str(e)}")
                        continue

            messagebox.showinfo("Sukses", "Database berhasil diimport. Data lama telah digantikan dan ditambahkan ekstensi .old")
            self.main_window.update_status("Database berhasil diimport. Data lama telah digantikan dan ditambahkan ekstensi .old")
            self.update_file_list()
            
        except Exception as e:
            error_message = f"Terjadi kesalahan saat mengimport database:\n{str(e)}"
            print(error_message)
            messagebox.showerror("Error", error_message)
            self.main_window.update_status("Gagal mengimport database")

    def check_old_files(self):
        """Check if there are any .old files in database directory"""
        database_dir = os.path.join(self.BASE_DIR, "Database")
        for root, dirs, files in os.walk(database_dir):
            for file in files:
                if file.endswith(".old"):
                    return True
        return False

    def update_restore_button(self):
        """Enable/disable restore button based on existence of .old files"""
        if self.check_old_files():
            self.restore_button.configure(state="normal")
        else:
            self.restore_button.configure(state="disabled")

    def restore_database(self):
        """Restore database from .old files"""
        if not messagebox.askyesno("Konfirmasi Pemulihan", 
            "Tindakan ini akan:\n"
            "1. Menghapus semua file baru yang diimpor\n"
            "2. Memulihkan file lama yang ada di Rak Arsip\n\n"
            "Kamu yakin ingin melanjutkan?"):
            return

        try:
            database_dir = os.path.join(self.BASE_DIR, "Database")
            restored_count = 0
            
            for root, dirs, files in os.walk(database_dir):
                for file in files:
                    if file.endswith(".old"):
                        old_path = os.path.join(root, file)
                        new_path = old_path[:-4]  # Remove .old extension
                        
                        # Remove the current file if exists
                        if os.path.exists(new_path):
                            os.remove(new_path)
                            
                        # Restore the .old file
                        os.rename(old_path, new_path)
                        restored_count += 1

            if restored_count > 0:
                messagebox.showinfo("Sukses", f"Berhasil memulihkan {restored_count} file database ke versi sebelumnya")
                self.main_window.update_status("Database berhasil dipulihkan ke versi sebelumnya")
            else:
                messagebox.showinfo("Informasi", "Tidak ada file yang perlu dipulihkan")
                
            self.update_file_list()
            self.update_restore_button()
            
        except Exception as e:
            error_message = f"Terjadi kesalahan saat memulihkan database:\n{str(e)}"
            print(error_message)
            messagebox.showerror("Error", error_message)
            self.main_window.update_status("Gagal memulihkan database")

    def monitor_database_directory(self):
        """Monitor the database directory for changes and update the file list."""
        database_dir = os.path.join(self.BASE_DIR, "Database")
        previous_files = set()

        while True:
            current_files = set()
            for root, dirs, files in os.walk(database_dir):
                for file in files:
                    current_files.add(os.path.join(root, file))

            if current_files != previous_files:
                self.update_file_list()
                # Update restore button when files change
                self.after(100, self.update_restore_button)
                previous_files = current_files

            time.sleep(5)  # Check for changes every 5 seconds

    def on_resize(self, event):
        """Adjust column widths dynamically based on window size."""
        width = self.winfo_width()
        remaining_width = width - 40  # Subtract fixed No column width
        column_width = remaining_width // 2  # Divide remaining space equally
        
        # No column stays fixed at 40px
        self.file_treeview.column("No", width=40, minwidth=40, stretch=False)
        self.file_treeview.column("Direktori", width=column_width)
        self.file_treeview.column("File", width=column_width)

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
