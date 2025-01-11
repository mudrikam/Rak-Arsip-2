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
import csv
import threading  # Add this import
import windnd  # Tambahkan ini
import time  # Add this with other imports

class RelocateFiles(ttk.LabelFrame):
    def __init__(self, parent, BASE_DIR, main_window):
        super().__init__(parent, text="Relokasi File ke Rak Arsip agar mudah di akses.", padding=10)
        self.grid(row=0, column=0, padx=10, pady=10, sticky="nsew")
        self.parent = parent
        self.BASE_DIR = BASE_DIR
        self.main_window = main_window
        self.csv_file_path = os.path.join(BASE_DIR, "Database", "Library", "project_library.csv")
        self.selected_destination = tk.StringVar()
        self.move_button = None
        self.copy_button = None
        self.create_widgets()
        self.update_button_states()
        self.last_modified_time = os.path.getmtime(self.csv_file_path)
        self.after(1000, self.check_for_updates)
        self.replace_all = False
        self.rename_all = False
        self.skip_all = False
        self._resolved_path = None  # Add this line
        self.operation_running = False  # Add this line
        self.stats = {
            'replaced': 0,
            'renamed': 0,
            'skipped': 0,
            'success': 0,
            'failed': 0
        }
        self.moved_files = []  # Add this to track successfully moved files
        self.update_dropzone_overlay()  # Add this line

    def create_widgets(self):
        # Configure equal width columns
        self.columnconfigure(0, weight=1, uniform="group1")
        self.columnconfigure(1, weight=1, uniform="group1")

        # Create left panel (Source) with drag and drop support
        self.left_panel = ttk.LabelFrame(self, text="Sumber :", padding=10)
        self.left_panel.grid(row=1, column=0, padx=(0, 10), sticky="nsew")

        # Create top panel with buttons
        top_panel = ttk.Frame(self.left_panel)
        top_panel.pack(pady=(0, 10), fill="x")

        select_files_button = ttk.Button(top_panel, text="Pilih File", command=self.select_files, padding=5)
        select_files_button.pack(side="left", padx=(0, 5))

        or_label = ttk.Label(top_panel, text="atau")
        or_label.pack(side="left", padx=(0, 5))

        select_folder_button = ttk.Button(top_panel, text="Pilih Folder", command=self.select_folder, padding=5)
        select_folder_button.pack(side="left", padx=(0, 5))

        # Create drop frame to contain both listbox and overlay
        self.drop_frame = ttk.Frame(self.left_panel)
        self.drop_frame.pack(fill="both", expand=True)

        # Create file listbox inside drop frame
        self.file_listbox = tk.Listbox(self.drop_frame, selectmode=tk.MULTIPLE)
        self.file_listbox.pack(fill="both", expand=True)

        # Create overlay label inside drop frame
        self.overlay_label = ttk.Label(
            self.drop_frame,
            text="Seret dan lepaskan,\nfile atau folder\nke sini.\n\nBiar aku Relokasi\nfile-filemu ke\nRak Arsip. (^_-)",
            background='#FFFFFF',
            foreground='#999999',
            font=('Segoe UI', 12),
            anchor='center'
        )
        
        # Enable drag and drop for both the listbox and the frame
        windnd.hook_dropfiles(self.file_listbox, func=self.handle_drop)
        windnd.hook_dropfiles(self.drop_frame, func=self.handle_drop)
        windnd.hook_dropfiles(self.overlay_label, func=self.handle_drop)

        # Make overlay label semi-transparent and lift it
        self.overlay_label.lift()
        self.overlay_label.place(relx=0.5, rely=0.5, anchor='center')

        # Create right panel (Destination)
        self.right_panel = ttk.LabelFrame(self, text="Tujuan :", padding=10)
        self.right_panel.grid(row=1, column=1, sticky="nsew")
        
        # Configure right panel to fill space
        self.right_panel.columnconfigure(0, weight=1)
        self.right_panel.rowconfigure(1, weight=1)

        # Search frame - modified to include folder selection button
        search_frame = ttk.Frame(self.right_panel)
        search_frame.pack(fill="x", pady=(0, 10))
        
        # Configure grid weights for search frame
        search_frame.columnconfigure(1, weight=1)  # Make the entry column expandable
        
        # Use grid instead of pack for better control
        ttk.Label(search_frame, text="Cari:").grid(row=0, column=0, padx=(0, 5))
        self.search_var = tk.StringVar()
        search_entry = ttk.Entry(search_frame, textvariable=self.search_var, font=("Lato Medium", 14))
        search_entry.grid(row=0, column=1, sticky="ew", padx=(0, 5))
        search_entry.bind("<KeyRelease>", self.search_destinations)

        # Add folder selection button with fixed width
        select_folder_btn = ttk.Button(search_frame, text="Pilih Folder", command=self.select_destination_folder, padding=5)
        select_folder_btn.grid(row=0, column=2)

        # TreeView for saved locations - modified columns configuration
        self.tree = ttk.Treeview(self.right_panel, columns=("number", "name"), show="headings", height=8)
        # Configure columns with number column smaller
        self.tree.column("number", width=30, anchor="center", stretch=False)
        self.tree.column("name", width=50, anchor="w", stretch=True)
        self.tree.heading("number", text="No")
        self.tree.heading("name", text="Nama")
        
        # Add selection binding
        self.tree.bind('<<TreeviewSelect>>', self.on_select_destination)
        # Bind column resize event
        self.tree.bind('<Configure>', self.on_treeview_configure)
        self.tree.pack(fill="both", expand=True, pady=(0))
        
        # Configure flat style for treeview
        style = ttk.Style()
        style.configure("Treeview", relief="flat")
        style.configure("Treeview.Heading", relief="flat")
        
        # Make treeview fill remaining space
        self.tree.pack(fill="both", expand=True)

        # Bottom panel with action buttons - modified arrangement
        bottom_panel = ttk.Frame(self)
        bottom_panel.grid(row=2, column=0, columnspan=2, pady=(10,0), sticky="ew")
        
        bottom_panel.columnconfigure(0, weight=1)

        reset_button = ttk.Button(bottom_panel, text="Reset", command=self.reset_files, padding=5)
        reset_button.grid(row=0, column=0, padx=(0, 10), sticky="e")

        self.open_folder_button = ttk.Button(bottom_panel, text="Buka Folder", command=self.open_selected_folder, padding=5)
        self.open_folder_button.grid(row=0, column=1, padx=(0, 10), sticky="e")
        self.open_folder_button["state"] = "disabled"

        self.move_button = ttk.Button(bottom_panel, text="Pindahkan", command=self.move_files, padding=5)
        self.move_button.grid(row=0, column=2, padx=(0, 10), sticky="e")

        self.copy_button = ttk.Button(bottom_panel, text="Salin", command=self.copy_files, padding=5)
        self.copy_button.grid(row=0, column=3, padx=(0, 0), sticky="e")

        # Create progress bar panel - modified to show location
        progress_panel = ttk.Frame(self)
        progress_panel.grid(row=3, column=0, columnspan=2, pady=(10, 0), sticky="ew")

        self.progress_bar = ttk.Progressbar(progress_panel, orient="horizontal", mode="determinate", style="Location.Horizontal.TProgressbar")
        self.progress_bar.pack(fill="x", expand=True, padx=0)
        
        # Create style for progress bar with text
        style = ttk.Style()
        style.layout('Location.Horizontal.TProgressbar',
                    [('Horizontal.Progressbar.trough',
                      {'children': [('Horizontal.Progressbar.pbar',
                                   {'side': 'left', 'sticky': 'ns'})],
                       'sticky': 'nswe'}),
                     ('Horizontal.Progressbar.label', {'sticky': ''})])
        style.configure('Location.Horizontal.TProgressbar', text='Belum ada lokasi tujuan yang dipilih')

        # Configure grid weights
        self.columnconfigure(0, weight=1)
        self.columnconfigure(1, weight=1)
        self.rowconfigure(1, weight=1)
        self.rowconfigure(2, weight=0)
        self.rowconfigure(3, weight=0)

        # Load destinations from CSV
        self.load_destinations()

        # Add bindings for listbox and tree selection
        self.file_listbox.bind('<<ListboxSelect>>', self.update_button_states)
        self.tree.bind('<<TreeviewSelect>>', lambda e: (self.on_select_destination(e), self.update_button_states()))

    def on_treeview_configure(self, event):
        total_width = event.width
        num_width = 40  # Fixed width for number column
        self.tree.column("number", width=num_width)
        self.tree.column("name", width=total_width - num_width)

    def check_for_updates(self):
        try:
            current_modified_time = os.path.getmtime(self.csv_file_path)
            if current_modified_time != self.last_modified_time:
                self.last_modified_time = current_modified_time
                self.load_destinations()
                if self.search_var.get().strip():
                    self.search_destinations()
        except FileNotFoundError:
            pass
        finally:
            self.after(1000, self.check_for_updates)

    def load_destinations(self):
        if os.path.exists(self.csv_file_path):
            with open(self.csv_file_path, 'r', encoding='utf-8') as file:
                reader = csv.reader(file)
                next(reader)  # Skip header
                
                # Store complete row data (number, date, name, location)
                self.destinations = []
                for row in reader:
                    if len(row) >= 4:  # Ensure row has all required fields
                        self.destinations.append((row[0], row[1], row[2], row[3]))
                
                # Sort by number in reverse order
                self.destinations.sort(key=lambda x: int(x[0]), reverse=True)
                
                # Update treeview
                self.tree.delete(*self.tree.get_children())
                for number, date, name, location in self.destinations:
                    self.tree.insert("", "end", values=(number, name))

    def search_destinations(self, event=None):
        keyword = self.search_var.get().strip().lower()
        self.tree.delete(*self.tree.get_children())

        if not keyword:
            # Show all entries if search is empty
            for number, date, name, location in self.destinations:
                self.tree.insert("", "end", values=(number, name))
            return

        # Search in all fields 
        matching_destinations = []
        for number, date, name, location in self.destinations:
            # Check if keyword exists in any field
            if any(keyword in field.lower() for field in [number, date, name, location]):
                matching_destinations.append((number, date, name, location))

        # Display filtered results
        for number, date, name, location in matching_destinations:
            self.tree.insert("", "end", values=(number, name))

    def on_select_destination(self, event):
        selection = self.tree.selection()
        if selection:
            item_values = self.tree.item(selection[0])['values']
            number = str(item_values[0])
            # Find matching destination using number
            for dest_number, dest_date, dest_name, dest_location in self.destinations:
                if str(dest_number) == number:
                    self.selected_destination.set(dest_location)
                    self.update_location_label(dest_location)
                    self.open_folder_button["state"] = "normal"  # Sudah benar disini
                    break
        else:
            # Cek apakah ada folder yang dipilih manual
            if self.selected_destination.get():
                self.open_folder_button["state"] = "normal"
            else:
                self.open_folder_button["state"] = "disabled"

    def select_destination_folder(self):
        folder = filedialog.askdirectory()
        if folder:
            self.selected_destination.set(folder)
            self.update_location_label(folder)
            self.update_button_states()
            # Aktifkan tombol Buka Folder
            self.open_folder_button["state"] = "normal"

    def update_location_label(self, path):
        if path:
            # Update progress bar text.
            style = ttk.Style()
            style.configure('Location.Horizontal.TProgressbar', text=f"Tujuan: {path}")
            self.progress_bar["value"] = 0
        else:
            style = ttk.Style()
            style.configure('Location.Horizontal.TProgressbar', text="Belum ada lokasi tujuan yang dipilih")
            self.progress_bar["value"] = 0

    def select_files(self):
        file_paths = filedialog.askopenfilenames(title="Pilih File", filetypes=[("All Files", "*.*")])
        if file_paths:
            duplicates = []
            # Tidak menghapus list yang ada, langsung menambahkan
            for file_path in file_paths:
                # Cek duplikasi sebelum menambahkan
                if file_path not in self.file_listbox.get(0, tk.END):
                    self.file_listbox.insert(tk.END, file_path)
                else:
                    duplicates.append(os.path.basename(file_path))
            
            if duplicates:
                self.main_window.update_status(f"File sudah ada dalam daftar: {', '.join(duplicates)}")
                
            self.update_dropzone_overlay()
            self.update_button_states()

    def select_folder(self):
        folder_path = filedialog.askdirectory(title="Pilih Folder")
        if folder_path:
            folder_files = [os.path.join(folder_path, f) for f in os.listdir(folder_path)]
            duplicates = []
            # Tidak menghapus list yang ada, langsung menambahkan
            for file_path in folder_files:
                # Cek duplikasi sebelum menambahkan
                if file_path not in self.file_listbox.get(0, tk.END):
                    self.file_listbox.insert(tk.END, file_path)
                else:
                    duplicates.append(os.path.basename(file_path))

            if duplicates:
                self.main_window.update_status(f"File sudah ada dalam daftar: {', '.join(duplicates)}")
                
            self.update_dropzone_overlay()
            self.update_button_states()

    def move_files(self):
        if self.operation_running:
            return
            
        if not tk.messagebox.askyesno("Konfirmasi", "Apakah Kamu yakin ingin memindahkan file yang dipilih?"):
            self.main_window.update_status("Pemindahan file dibatalkan")
            return
            
        # Reset the "all" flags at the start of a new operation
        self.replace_all = False
        self.rename_all = False
        self.skip_all = False

        destination_folder = self.selected_destination.get()
        if not destination_folder:
            destination_folder = filedialog.askdirectory(title="Pilih Folder Tujuan")
            if not destination_folder:
                return

        files = list(self.file_listbox.get(0, tk.END))  # Convert to list
        if not files:
            return

        # Disable buttons during operation
        self.operation_running = True
        self.move_button["state"] = "disabled"
        self.copy_button["state"] = "disabled"
        
        # Start operation in background thread
        thread = threading.Thread(
            target=self._move_files_thread,
            args=(files, destination_folder),
            daemon=True
        )
        thread.start()

    def _move_files_thread(self, files, destination_folder):
        try:
            total_files = len(files)
            self.progress_bar["maximum"] = 100
            self.progress_bar["value"] = 0
            self._reset_stats()
            self.moved_files = []

            for index, file_path in enumerate(files, 1):
                if not os.path.exists(file_path):
                    continue
                    
                filename = os.path.basename(file_path)
                status_text = f"Memindahkan {index}/{total_files}: {filename}"
                
                self.after(0, self._update_progress_text, status_text)
                self.after(0, self.main_window.update_status, status_text)
                
                try:
                    dst_path = os.path.join(destination_folder, filename)
                    original_path = dst_path  # Simpan path asli untuk pengecekan
                    self._resolved_path = None
                    
                    # Cek apakah file sudah ada sebelum menampilkan dialog
                    if os.path.exists(dst_path):
                        self.after(0, lambda p=dst_path: self._handle_conflict_async(p))
                        
                        timeout = 0
                        while self._resolved_path is None and timeout < 300:
                            self.update()
                            self.after(100)
                            timeout += 1
                            
                        if self._resolved_path is False:
                            self._update_stats('skipped')
                            continue
                        elif self._resolved_path is None:
                            self._update_stats('failed')
                            raise TimeoutError("Dialog timeout")
                    else:
                        self._resolved_path = dst_path

                    # Baca ukuran file sumber
                    src_size = os.path.getsize(file_path)
                    if src_size == 0:
                        raise Exception("File sumber kosong (0 bytes)")

                    BUFFER_SIZE = 32 * 1024 * 1024  # 32MB buffer
                    copied_size = 0
                    start_time = time.time()
                    
                    # Gunakan with untuk memastikan file ditutup dengan benar
                    try:
                        with open(file_path, 'rb') as fsrc:
                            with open(self._resolved_path, 'wb') as fdst:
                                last_update = time.time()  # Tambahkan ini
                                while True:
                                    buf = fsrc.read(BUFFER_SIZE)
                                    if not buf:
                                        break
                                    fdst.write(buf)
                                    fdst.flush()  # Pastikan data ditulis ke disk
                                    copied_size += len(buf)
                                    
                                    current_time = time.time()
                                    # Update progress setiap 50ms
                                    if current_time - last_update >= 0.05:  # 50ms
                                        file_progress = (copied_size / src_size) * 100
                                        total_progress = ((index - 1 + (copied_size / src_size)) / total_files) * 100
                                        speed = copied_size / (current_time - start_time)
                                        speed_text = f"{speed / (1024 * 1024):.2f} MB/s" if speed > 1024 * 1024 else f"{speed / 1024:.2f} KB/s"
                                        
                                        status_text = f"Memindahkan {index}/{total_files}: {filename} ({int(file_progress)}%) - {speed_text}"
                                        self.after(0, self._update_progress_text, status_text)
                                        self.after(0, self.main_window.update_status, status_text)
                                        self.after(0, self._increment_progress, total_progress)
                                        self.update()
                                        last_update = current_time

                    except Exception as e:
                        # Jika terjadi error saat copy, hapus file tujuan yang tidak lengkap
                        if os.path.exists(self._resolved_path):
                            os.remove(self._resolved_path)
                        raise Exception(f"Error saat menyalin: {str(e)}")

                    # Verifikasi ukuran file setelah copy
                    dst_size = os.path.getsize(self._resolved_path)
                    if dst_size != src_size:
                        if os.path.exists(self._resolved_path):
                            os.remove(self._resolved_path)
                        raise Exception(f"Verifikasi gagal - ukuran tidak sama (sumber: {src_size}, tujuan: {dst_size})")

                    # Setelah verifikasi sukses, hapus file sumber dan hitung statistik
                    os.remove(file_path)
                    if original_path == self._resolved_path:  # Jika path tetap sama (tidak berubah)
                        if os.path.exists(original_path):  # Dan file sudah ada sebelumnya
                            self._update_stats('replaced')  # Berarti file diganti
                    elif self._resolved_path != original_path:  # Jika path berubah
                        self._update_stats('renamed')  # Berarti file diberi nama baru
                    self._update_stats('success')
                    self.moved_files.append(file_path)
                    
                except Exception as e:
                    self._update_stats('failed')
                    error_msg = f"Error memindahkan {filename}: {str(e)}"
                    print(error_msg)
                    self.after(0, self.main_window.update_status, error_msg)

            stats_msg = self._get_stats_message("dipindahkan")
            self.after(0, self.main_window.update_status, f"Selesai memindahkan file - {stats_msg}")
            self.after(0, self._finish_move_operation, destination_folder)
            
        finally:
            self.after(0, self._enable_buttons)

    def copy_files(self):
        if self.operation_running:
            return
            
        if not tk.messagebox.askyesno("Konfirmasi", "Apakah Kamu yakin ingin menyalin file yang dipilih?"):
            self.main_window.update_status("Penyalinan file dibatalkan")
            return
            
        # Reset the "all" flags at the start of a new operation
        self.replace_all = False
        self.rename_all = False
        self.skip_all = False

        destination_folder = self.selected_destination.get()
        if not destination_folder:
            destination_folder = filedialog.askdirectory(title="Pilih Folder Tujuan")
            if not destination_folder:
                return

        files = list(self.file_listbox.get(0, tk.END))
        if not files:
            return

        # Disable buttons during operation
        self.operation_running = True
        self.move_button["state"] = "disabled"
        self.copy_button["state"] = "disabled"

        # Start operation in background thread
        thread = threading.Thread(
            target=self._copy_files_thread,
            args=(files, destination_folder),
            daemon=True
        )
        thread.start()

    def _copy_files_thread(self, files, destination_folder):
        try:
            total_files = len(files)
            self.progress_bar["maximum"] = 100
            self.progress_bar["value"] = 0
            self._reset_stats()

            for index, file_path in enumerate(files, 1):
                if not os.path.exists(file_path):
                    continue
                    
                filename = os.path.basename(file_path)
                status_text = f"Menyalin {index}/{total_files}: {filename}"
                
                self.after(0, self._update_progress_text, status_text)
                self.after(0, self.main_window.update_status, status_text)
                
                try:
                    dst_path = os.path.join(destination_folder, filename)
                    original_path = dst_path  # Simpan path asli untuk pengecekan
                    self._resolved_path = None
                    
                    # Cek apakah file sudah ada sebelum menampilkan dialog
                    if os.path.exists(dst_path):
                        self.after(0, lambda p=dst_path: self._handle_conflict_async(p))
                        
                        timeout = 0
                        while self._resolved_path is None and timeout < 300:
                            self.update()
                            self.after(100)
                            timeout += 1
                            
                        if self._resolved_path is False:
                            self._update_stats('skipped')
                            continue
                        elif self._resolved_path is None:
                            self._update_stats('failed')
                            raise TimeoutError("Dialog timeout")
                    else:
                        self._resolved_path = dst_path

                    # Baca ukuran file sumber
                    src_size = os.path.getsize(file_path)
                    if src_size == 0:
                        raise Exception("File sumber kosong (0 bytes)")

                    BUFFER_SIZE = 32 * 1024 * 1024  # 32MB buffer
                    copied_size = 0
                    start_time = time.time()
                    
                    # Gunakan with untuk memastikan file ditutup dengan benar
                    try:
                        with open(file_path, 'rb') as fsrc:
                            with open(self._resolved_path, 'wb') as fdst:
                                last_update = time.time()  # Tambahkan ini
                                while True:
                                    buf = fsrc.read(BUFFER_SIZE)
                                    if not buf:
                                        break
                                    fdst.write(buf)
                                    fdst.flush()  # Pastikan data ditulis ke disk
                                    copied_size += len(buf)
                                    
                                    current_time = time.time()
                                    # Update progress setiap 50ms
                                    if current_time - last_update >= 0.05:  # 50ms
                                        file_progress = (copied_size / src_size) * 100
                                        total_progress = ((index - 1 + (copied_size / src_size)) / total_files) * 100
                                        speed = copied_size / (current_time - start_time)
                                        speed_text = f"{speed / (1024 * 1024):.2f} MB/s" if speed > 1024 * 1024 else f"{speed / 1024:.2f} KB/s"
                                        
                                        status_text = f"Menyalin {index}/{total_files}: {filename} ({int(file_progress)}%) - {speed_text}"
                                        self.after(0, self._update_progress_text, status_text)
                                        self.after(0, self.main_window.update_status, status_text)
                                        self.after(0, self._increment_progress, total_progress)
                                        self.update()
                                        last_update = current_time

                    except Exception as e:
                        # Jika terjadi error saat copy, hapus file tujuan yang tidak lengkap
                        if os.path.exists(self._resolved_path):
                            os.remove(self._resolved_path)
                        raise Exception(f"Error saat menyalin: {str(e)}")

                    # Verifikasi ukuran file setelah copy
                    dst_size = os.path.getsize(self._resolved_path)
                    if dst_size != src_size:
                        if os.path.exists(self._resolved_path):
                            os.remove(self._resolved_path)
                        raise Exception(f"Verifikasi gagal - ukuran tidak sama (sumber: {src_size}, tujuan: {dst_size})")

                    # Hitung statistik setelah verifikasi berhasil
                    if original_path == self._resolved_path:  # Jika path tetap sama (tidak berubah)
                        if os.path.exists(original_path) and self.replace_all:  # Tambahkan pengecekan replace_all
                            self._update_stats('replaced')  # Berarti file diganti
                    elif self._resolved_path != original_path:  # Jika path berubah
                        self._update_stats('renamed')  # Berarti file diberi nama baru
                    self._update_stats('success')
                    
                except Exception as e:
                    self._update_stats('failed')
                    error_msg = f"Error menyalin {filename}: {str(e)}"
                    print(error_msg)
                    self.after(0, self.main_window.update_status, error_msg)

            # Update final status
            stats_msg = self._get_stats_message("disalin")
            self.after(0, self.main_window.update_status, f"Selesai menyalin file - {stats_msg}")
            self.after(0, self._finish_copy_operation, destination_folder)
            
        finally:
            self.after(0, self._enable_buttons)

    # Add new helper methods for async file conflict handling
    def _handle_conflict_async(self, dst_path):
        if not os.path.exists(dst_path):
            self._resolved_path = dst_path
            return
            
        # Check existing "all" decisions first
        if self.replace_all:
            self._resolved_path = dst_path
            return
        elif self.rename_all:
            base, ext = os.path.splitext(dst_path)
            counter = 1
            while os.path.exists(dst_path):
                dst_path = f"{base} ({counter}){ext}"
                counter += 1
            self._resolved_path = dst_path
            return
        elif self.skip_all:
            self._resolved_path = False
            return

        # Create dialog in main thread
        def show_dialog():
            dialog = tk.Toplevel(self)
            dialog.title("File sudah ada")
            dialog.transient(self)
            dialog.grab_set()

            # Set icon
            icon_path = os.path.join(self.BASE_DIR, "Img", "Icon", "rakikon.ico")
            if os.path.exists(icon_path):
                dialog.iconbitmap(icon_path)
            
            # Center dialog
            dialog.update_idletasks()
            x = (self.winfo_screenwidth() - dialog.winfo_width()) // 2
            y = (self.winfo_screenheight() - dialog.winfo_height()) // 2
            dialog.geometry(f"+{x}+{y}")

            message = f"'{os.path.basename(dst_path)}' sudah ada.\nApa yang ingin dilakukan?"
            ttk.Label(dialog, text=message, padding=10).pack()

            def on_button(action):
                if action == "replace_all":
                    self.replace_all = True
                    self._resolved_path = dst_path
                elif action == "replace":
                    self._resolved_path = dst_path
                elif action == "rename_all":
                    self.rename_all = True
                    base, ext = os.path.splitext(dst_path)
                    counter = 1
                    new_path = dst_path
                    while os.path.exists(new_path):
                        new_path = f"{base} ({counter}){ext}"
                        counter += 1
                    self._resolved_path = new_path
                elif action == "rename":
                    base, ext = os.path.splitext(dst_path)
                    counter = 1
                    new_path = dst_path
                    while os.path.exists(new_path):
                        new_path = f"{base} ({counter}){ext}"
                        counter += 1
                    self._resolved_path = new_path
                elif action in ("skip_all", "skip"):
                    self.skip_all = True if action == "skip_all" else False
                    self._resolved_path = False
                dialog.destroy()

            button_frame = ttk.Frame(dialog, padding=(10, 5))
            button_frame.pack(fill="x")

            buttons = [
                ("Ganti", "replace"),
                ("Buat Baru", "rename"),
                ("Lewati", "skip"),
                ("Ganti Semua", "replace_all"),
                ("Buat Baru Semua", "rename_all"), 
                ("Lewati Semua", "skip_all")
            ]

            for i, (text, action) in enumerate(buttons):
                row = i // 3
                col = i % 3
                ttk.Button(
                    button_frame, 
                    text=text,
                    command=lambda a=action: on_button(a),
                    width=15
                ).grid(row=row, column=col, padx=5, pady=2)

            dialog.protocol("WM_DELETE_WINDOW", lambda: on_button("skip"))
            dialog.wait_window()

        self.after(0, show_dialog)

    def _update_progress_text(self, text):
        style = ttk.Style()
        style.configure('Location.Horizontal.TProgressbar', text=text)
        
    def _increment_progress(self, value):
        self.progress_bar["value"] = value
        self.update_idletasks()

    def reset_files(self):
        # Reset the "all" flags
        self.replace_all = False
        self.rename_all = False
        self.skip_all = False

        # Clear file listbox
        self.file_listbox.delete(0, tk.END)
        self.update_dropzone_overlay()
        
        # Clear treeview selection
        self.tree.selection_remove(self.tree.selection())
        
        # Clear search entry
        self.search_var.set("")
        
        # Reset location label and progress bar
        self.selected_destination.set("")
        self.update_location_label("")
        
        # Reload destinations
        self.tree.delete(*self.tree.get_children())
        self.load_destinations()
        self.update_button_states()
        # Pastikan tombol Buka Folder dinonaktifkan karena tidak ada folder yang dipilih
        self.open_folder_button["state"] = "disabled"

    def update_button_states(self, event=None):
        has_files = len(self.file_listbox.get(0, tk.END)) > 0
        has_destination = bool(self.selected_destination.get())
        
        state = "normal" if (has_files and has_destination) else "disabled"
        self.move_button["state"] = state
        self.copy_button["state"] = state

    def open_selected_folder(self):
        folder_path = self.selected_destination.get()
        if (folder_path and os.path.exists(folder_path)):
            os.startfile(folder_path)

    def _enable_buttons(self):
        """Re-enable buttons after operation completes"""
        self.operation_running = False
        if len(self.file_listbox.get(0, tk.END)) > 0 and self.selected_destination.get():
            self.move_button["state"] = "normal"
            self.copy_button["state"] = "normal"
        else:
            self.move_button["state"] = "disabled" 
            self.copy_button["state"] = "disabled"
        
        self.update_idletasks()

    def _finish_move_operation(self, destination_folder):
        """Finish up move operation"""
        self._update_progress_text(f"Lokasi: {destination_folder}")
        self.progress_bar["value"] = 0
        
        # Remove only successfully moved files from listbox
        if self.moved_files:
            items = list(self.file_listbox.get(0, tk.END))
            remaining_items = [item for item in items if item not in self.moved_files]
            self.file_listbox.delete(0, tk.END)
            for item in remaining_items:
                self.file_listbox.insert(tk.END, item)
        
        # Buat pesan detail
        detail_msg = []
        if self.stats['success'] > 0:
            # Tambahkan daftar file yang berhasil
            success_files = [os.path.basename(f) for f in self.moved_files]
            files_msg = "\n".join(success_files)
            detail_msg.append(f"File yang berhasil dipindahkan:\n{files_msg}\n")
            detail_msg.append(f"Ke: {destination_folder}")
            
            # Tambahkan statistik tambahan jika ada
            stats = []
            if self.stats['renamed'] > 0:
                stats.append(f"{self.stats['renamed']} dibuat baru")
            if self.stats['skipped'] > 0:
                stats.append(f"{self.stats['skipped']} dilewati")
            if stats:
                detail_msg.append(f"\nDengan rincian: {', '.join(stats)}")
                
            # Tambahkan peringatan jika folder tujuan dipilih manual
            if not any(destination_folder == dest[3] for dest in self.destinations):
                detail_msg.append("\nMohon diingat: Lokasi tujuan tidak berada di Rak Arsip!")
                
            tk.messagebox.showinfo("Selesai", "\n".join(detail_msg))
            self.main_window.update_status(f"File berhasil dipindahkan ke {destination_folder}")
        else:
            error_files = [item for item in items if item not in self.moved_files]
            if error_files:
                files_msg = "\n".join([os.path.basename(f) for f in error_files])
                detail_msg.append(f"File yang gagal dipindahkan:\n{files_msg}\n")
            
            if self.stats['failed'] > 0:
                detail_msg.append(f"Total {self.stats['failed']} file gagal dipindahkan")
            if self.stats['skipped'] > 0:
                detail_msg.append(f"{self.stats['skipped']} file dilewati")
                
            tk.messagebox.showwarning("Peringatan", "\n".join(detail_msg))
            self.main_window.update_status("Gagal memindahkan file - lihat pesan error sebelumnya")
        
        self.update_button_states()
        self.moved_files = []

    def _finish_copy_operation(self, destination_folder):
        """Finish up copy operation"""
        self._update_progress_text(f"Lokasi: {destination_folder}")
        self.progress_bar["value"] = 0
        
        # Buat pesan detail
        detail_msg = []
        if self.stats['success'] > 0:
            # Hitung jumlah file yang berhasil
            detail_msg.append(f"{self.stats['success']} file berhasil disalin ke:")
            detail_msg.append(destination_folder)
            
            # Tambahkan statistik tambahan jika ada
            stats = []
            if self.stats['renamed'] > 0:
                stats.append(f"{self.stats['renamed']} dibuat baru")
            if self.stats['skipped'] > 0:
                stats.append(f"{self.stats['skipped']} dilewati")
            if stats:
                detail_msg.append(f"\nDengan rincian: {', '.join(stats)}")
                
            # Tambahkan peringatan jika folder tujuan dipilih manual
            if not any(destination_folder == dest[3] for dest in self.destinations):
                detail_msg.append("\nMohon diingat: Lokasi tujuan tidak berada di Rak Arsip!")
                
            tk.messagebox.showinfo("Selesai", "\n".join(detail_msg))
            self.main_window.update_status(f"File berhasil disalin ke {destination_folder}")
        else:
            if self.stats['failed'] > 0:
                detail_msg.append(f"Total {self.stats['failed']} file gagal disalin")
            if self.stats['skipped'] > 0:
                detail_msg.append(f"{self.stats['skipped']} file dilewati")
                
            tk.messagebox.showwarning("Peringatan", "\n".join(detail_msg))
            self.main_window.update_status("Gagal menyalin file - lihat pesan error sebelumnya")

    def _reset_stats(self):
        """Reset operation statistics"""
        self.stats = {
            'replaced': 0,
            'renamed': 0,
            'skipped': 0,
            'success': 0,
            'failed': 0
        }

    def _update_stats(self, action):
        """Update operation statistics"""
        if action in self.stats:
            self.stats[action] += 1

    def _get_stats_message(self, operation=""):
        """Generate statistics message for status bar"""
        msg = []
        
        # Selalu tampilkan status sukses/gagal terlebih dahulu
        if self.stats['success'] > 0:
            msg.append(f"{self.stats['success']} berhasil {operation}")
        elif self.stats['failed'] > 0:  # Gunakan elif untuk memastikan hanya satu status utama
            msg.append(f"{self.stats['failed']} gagal")
            return ", ".join(msg) if msg else "Dibatalkan"  # Jika gagal, langsung return
            
        # Tambahkan detail hanya jika ada operasi yang sukses
        if self.stats['success'] > 0:
            details = []
            if self.stats['replaced'] > 0:
                details.append(f"{self.stats['replaced']} diganti")
            if self.stats['renamed'] > 0:
                details.append(f"{self.stats['renamed']} dibuat baru")
            if self.stats['skipped'] > 0:
                details.append(f"{self.stats['skipped']} dilewati")
            if details:
                msg.extend(details)
                
        return ", ".join(msg) if msg else "Dibatalkan"

    def handle_drop(self, files):
        """Handle drag and drop file events"""
        duplicates = []  # Define duplicates list here
        
        # Process each dropped file/folder
        for path in files:
            # Convert bytes to string if needed
            if isinstance(path, bytes):
                path = path.decode('utf-8')
                
            if os.path.isdir(path):
                # If it's a directory, add all files in it
                folder_files = [os.path.join(path, f) for f in os.listdir(path)]
                for file_path in folder_files:
                    if os.path.isfile(file_path):  # Only add files, not subdirectories
                        # Cek duplikasi sebelum menambahkan
                        if file_path not in self.file_listbox.get(0, tk.END):
                            self.file_listbox.insert(tk.END, file_path)
                        else:
                            duplicates.append(os.path.basename(file_path))
            else:
                # If it's a file, add it directly if belum ada
                if path not in self.file_listbox.get(0, tk.END):  # Fixed extra parenthesis
                    self.file_listbox.insert(tk.END, path)
                else:
                    duplicates.append(os.path.basename(path))
        
        if duplicates:
            self.main_window.update_status(f"File sudah ada dalam daftar: {', '.join(duplicates)}")
        
        # Update button states after adding files
        self.update_dropzone_overlay()
        self.update_button_states()
        
        return "ok"  # Required by some systems

    def update_dropzone_overlay(self):
        """Update overlay visibility based on listbox content"""
        if self.file_listbox.size() == 0:
            self.overlay_label.place(relx=0.5, rely=0.5, anchor='center')
        else:
            self.overlay_label.place_forget()

    def confirm_exit(self):
        """Konfirmasi keluar saat operasi sedang berjalan"""
        if self.operation_running:
            return tk.messagebox.askyesno(
                "Konfirmasi",
                "Operasi file sedang berjalan.\nYakin ingin keluar?"
            )
        return True

# ...end of class...