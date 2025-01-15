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
import threading
from tkinter import messagebox  # Add this import
import windnd  # Tambahkan ini
import time  # Add this with other imports
from App.ui.project_library import LibraryManager
from PIL import Image, ImageTk

class RelocateFiles(ttk.LabelFrame):
    def __init__(self, parent, BASE_DIR, main_window):
        super().__init__(parent, text="Relokasi File ke Rak Arsip agar mudah di akses.", padding=10)
        self.grid(row=0, column=0, padx=10, pady=10, sticky="nsew")
        self.parent = parent
        self.BASE_DIR = BASE_DIR
        self.main_window = main_window
        
        # Initialize all instance variables first
        self.file_paths = {}  # Change to dictionary to store both path and name
        self.thumbnail_cache = {}
        self.default_icon = None
        self.selected_destination = tk.StringVar()
        self.move_button = None
        self.copy_button = None
        self.replace_all = False
        self.rename_all = False
        self.skip_all = False
        self._resolved_path = None
        self.operation_running = False
        self.moved_files = []
        self.stats = {
            'replaced': 0,
            'renamed': 0,
            'skipped': 0,
            'success': 0,
            'failed': 0
        }
        
        # Create LibraryManager instance
        try:
            self.library_manager = LibraryManager(BASE_DIR)
            self.csv_file_path = self.library_manager.get_library_path()
            
            if not self.library_manager.ensure_library_exists():
                raise Exception("Failed to initialize library")
                
        except Exception as e:
            messagebox.showerror("Error", f"Gagal inisialisasi: {str(e)}")
            return

        # Initialize UI and load resources
        self.load_default_icon()
        self.create_widgets()
        self.update_button_states()
        
        # Monitor CSV file changes
        if os.path.exists(self.csv_file_path):
            self.last_modified_time = os.path.getmtime(self.csv_file_path)
            self.after(1000, self.check_for_updates)
            
        self.update_dropzone_overlay()

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

    def load_default_icon(self):
        """Load default icon for non-image files"""
        try:
            # Create a gray rectangle as default icon
            img = Image.new('RGB', (32, 32), '#E0E0E0')
            self.default_icon = ImageTk.PhotoImage(img)
        except Exception:
            self.default_icon = None

    def get_thumbnail(self, file_path):
        """Generate thumbnail for file"""
        if file_path in self.thumbnail_cache:
            return self.thumbnail_cache[file_path]
            
        try:
            # Get file extension
            ext = os.path.splitext(file_path)[1].lower().lstrip('.')
            
            # Check if there's an icon for this extension
            icon_path = os.path.join(self.BASE_DIR, "Img", "Icon", "Extension", f"{ext}.png")
            
            if os.path.exists(icon_path):
                # Load and use custom icon for this extension
                img = Image.open(icon_path)
                img.thumbnail((32, 32))
                thumb = ImageTk.PhotoImage(img)
                self.thumbnail_cache[file_path] = thumb
                return thumb
                
            # Try to handle as image first
            try:
                img = Image.open(file_path)
                # Check if it's actually an image by accessing format
                if img.format:
                    img.thumbnail((32, 32))
                    thumb = ImageTk.PhotoImage(img)
                    self.thumbnail_cache[file_path] = thumb
                    return thumb
            except:
                # If not an image, use generic file.png
                generic_icon_path = os.path.join(self.BASE_DIR, "Img", "Icon", "Extension", "file.png")
                if os.path.exists(generic_icon_path):
                    img = Image.open(generic_icon_path)
                    img.thumbnail((32, 32))
                    thumb = ImageTk.PhotoImage(img)
                    self.thumbnail_cache[file_path] = thumb
                    return thumb
                
            # If all else fails, return default icon
            return self.default_icon
                
        except Exception as e:
            print(f"Error generating thumbnail for {file_path}: {e}")
            return self.default_icon

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

        # Load button icons
        self.select_files_icon = self._load_icon(os.path.join(self.BASE_DIR, "Img", "icon", "ui", "add_file.png"))
        self.select_folder_icon = self._load_icon(os.path.join(self.BASE_DIR, "Img", "icon", "ui", "add_folder.png"))
        self.open_icon = self._load_icon(os.path.join(self.BASE_DIR, "Img", "icon", "ui", "folder.png"))
        self.reset_icon = self._load_icon(os.path.join(self.BASE_DIR, "Img", "icon", "ui", "reset.png"))
        self.move_icon = self._load_icon(os.path.join(self.BASE_DIR, "Img", "icon", "ui", "move.png"))
        self.copy_icon = self._load_icon(os.path.join(self.BASE_DIR, "Img", "icon", "ui", "copy.png"))

        # Update buttons with icons
        select_files_button = ttk.Button(top_panel, text="Pilih File", 
            image=self.select_files_icon, compound='left',
            command=self.select_files, padding=5)
        select_files_button.pack(side="left", padx=(0, 5))

        or_label = ttk.Label(top_panel, text="atau")
        or_label.pack(side="left", padx=(0, 5))

        select_folder_button = ttk.Button(top_panel, text="Pilih Folder",
            image=self.select_folder_icon, compound='left', 
            command=self.select_folder, padding=5)
        select_folder_button.pack(side="left", padx=(0, 5))

        # Create drop frame to contain both listbox and overlay
        self.drop_frame = ttk.Frame(self.left_panel)
        self.drop_frame.pack(fill="both", expand=True)

        # Replace Listbox with Text widget
        self.file_listbox = tk.Text(
            self.drop_frame,
            wrap="none",  # Ubah ke none untuk mencegah wrap
            relief="flat",
            height=10,
            cursor="arrow",
            font=("Segoe UI", 10),
            padx=5,
            pady=2  # Tambah padding y
        )
        self.file_listbox.pack(fill="both", expand=True)
        
        # Configure tags for alignment and selection
        self.file_listbox.tag_configure("item", lmargin1=5, lmargin2=40)  # Adjust margins for items
        self.file_listbox.tag_configure("selected", background="#0078D7", foreground="white")
        
        # Add selection support
        self.file_listbox.tag_configure("selected", background="#0078D7", foreground="white")
        self.file_listbox.bind("<Button-1>", self.on_text_click)

        # Add horizontal scrollbar
        h_scroll = ttk.Scrollbar(self.drop_frame, orient="horizontal", command=self.file_listbox.xview)
        h_scroll.pack(fill="x", side="bottom")
        self.file_listbox.configure(xscrollcommand=h_scroll.set)

        # Create overlay label inside drop frame
        self.overlay_label = ttk.Label(
            self.drop_frame,
            text="Seret dan lepaskan,\nfile atau folder\nke sini.",
            background='#FFFFFF',
            foreground='#999999',
            font=('Segoe UI', 11),
            anchor='center',
            padding=5
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
        select_folder_btn = ttk.Button(search_frame, text="Pilih Folder", image=self.select_folder_icon, command=self.select_destination_folder, padding=5)
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

        reset_button = ttk.Button(bottom_panel, text="Reset",
            image=self.reset_icon, compound='left',
            command=self.reset_files, padding=5)
        reset_button.grid(row=0, column=0, padx=(0, 10), sticky="e")

        self.open_folder_button = ttk.Button(bottom_panel, text="Buka Folder",
            image=self.open_icon, compound='left',
            command=self.open_selected_folder, padding=5)
        self.open_folder_button.grid(row=0, column=1, padx=(0, 10), sticky="e")
        self.open_folder_button["state"] = "disabled"

        self.move_button = ttk.Button(bottom_panel, text="Pindahkan",
            image=self.move_icon, compound='left',
            command=self.move_files, padding=5)
        self.move_button.grid(row=0, column=2, padx=(0, 10), sticky="e")

        self.copy_button = ttk.Button(bottom_panel, text="Salin",
            image=self.copy_icon, compound='left',
            command=self.copy_files, padding=5)
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
        self.file_listbox.bind('<Configure>', self.redraw_thumbnails)
        self.tree.bind('<<TreeviewSelect>>', lambda e: (self.on_select_destination(e), self.update_button_states()))
        self.tree.bind('<Double-1>', self.on_treeview_double_click)  # Add double click handler

    def on_treeview_configure(self, event):
        total_width = event.width
        num_width = 40  # Fixed width for number column
        self.tree.column("number", width=num_width)
        self.tree.column("name", width=total_width - num_width)

    def check_for_updates(self):
        """Check for file updates"""
        try:
            if not self.csv_file_path or not os.path.exists(self.csv_file_path):
                return
                
            current_modified_time = os.path.getmtime(self.csv_file_path)
            if current_modified_time != self.last_modified_time:
                self.last_modified_time = current_modified_time
                self.load_destinations()
        except Exception as e:
            self.main_window.update_status(f"Error checking updates: {str(e)}")
        finally:
            self.after(1000, self.check_for_updates)

    def load_destinations(self):
        """Load destinations using ProjectLibrary's CSV"""
        if not os.path.exists(self.csv_file_path):
            # Let ProjectLibrary handle initialization
            if not self.project_library.ensure_library_exists():
                return
            self.csv_file_path = self.project_library.get_library_path()
            
        # Continue with existing loading logic
        try:
            with open(self.csv_file_path, 'r', encoding='utf-8') as file:
                reader = csv.reader(file)
                next(reader)  # Skip header
                
                # Store complete row data
                self.destinations = []
                for row in reader:
                    if len(row) >= 4:
                        self.destinations.append((row[0], row[1], row[2], row[3]))
                
                # Sort and update treeview
                self.destinations.sort(key=lambda x: int(x[0]), reverse=True)
                self.tree.delete(*self.tree.get_children())
                for number, date, name, location in self.destinations:
                    self.tree.insert("", "end", values=(number, name))
                    
        except Exception as e:
            self.main_window.update_status(f"Error loading destinations: {str(e)}")
            messagebox.showerror("Error", f"Gagal memuat lokasi tujuan:\n{e}")

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
                    self.open_folder_button["state"] = "normal"
                    # Update status bar with location
                    self.main_window.update_status(f"Lokasi: {dest_location}")
                    break
        else:
            # Cek apakah ada folder yang dipilih manual
            if self.selected_destination.get():
                self.open_folder_button["state"] = "normal"
            else:
                self.open_folder_button["state"] = "disabled"

    def on_treeview_double_click(self, event):
        """Handle double click on treeview item"""
        selection = self.tree.selection()
        if selection:
            item_values = self.tree.item(selection[0])['values']
            number = str(item_values[0])
            # Find matching destination using number
            for dest_number, dest_date, dest_name, dest_location in self.destinations:
                if str(dest_number) == number:
                    if os.path.exists(dest_location):
                        os.startfile(dest_location)
                    else:
                        messagebox.showerror("Error", f"Folder tidak ditemukan:\n{dest_location}")
                    break

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

    def add_file_to_list(self, file_path, thumb):
        """Helper method to add file with thumbnail to list"""
        if file_path not in self.file_paths:
            name = os.path.basename(file_path)
            # Truncate filename if too long (40 chars)
            if len(name) > 40:
                base, ext = os.path.splitext(name)
                name = base[:37-len(ext)] + "..." + ext
                
            self.file_paths[file_path] = {
                'name': name,
                'thumb': thumb
            }
            
            # Insert file info as single line with proper spacing
            self.file_listbox.insert(tk.END, " ")  # Small initial space
            self.file_listbox.image_create(tk.END, image=thumb)
            self.file_listbox.insert(tk.END, f" {name}\n", "item")
            return True
        return False

    def select_files(self):
        file_paths = filedialog.askopenfilenames(title="Pilih File", filetypes=[("All Files", "*.*")])
        if file_paths:
            duplicates = []
            for file_path in file_paths:
                thumb = self.get_thumbnail(file_path)
                if thumb:
                    if not self.add_file_to_list(file_path, thumb):
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
            for file_path in folder_files:
                if os.path.isfile(file_path):
                    thumb = self.get_thumbnail(file_path)
                    if thumb:
                        if not self.add_file_to_list(file_path, thumb):
                            duplicates.append(os.path.basename(file_path))

            if duplicates:
                self.main_window.update_status(f"File sudah ada dalam daftar: {', '.join(duplicates)}")
                
            self.update_dropzone_overlay()
            self.update_button_states()

    def move_files(self):
        if self.operation_running:
            return
            
        if not self._validate_operation("move"):
            return
            
        # Reset all flags at start of new operation
        self.replace_all = False
        self.rename_all = False
        self.skip_all = False
        
        self.operation_running = True
        self._disable_buttons()
        
        thread = threading.Thread(
            target=self._process_files_thread,
            args=(self.file_paths, self.selected_destination.get(), "move"),
            daemon=True
        )
        thread.start()

    def copy_files(self):
        if self.operation_running:
            return
            
        if not self._validate_operation("copy"):
            return
            
        # Reset all flags at start of new operation  
        self.replace_all = False
        self.rename_all = False
        self.skip_all = False
        
        self.operation_running = True
        self._disable_buttons()
        
        thread = threading.Thread(
            target=self._process_files_thread,
            args=(self.file_paths, self.selected_destination.get(), "copy"),
            daemon=True
        )
        thread.start()

    def _do_file_operation(self, src_path, dst_path, operation="copy"):
        """Helper for file copy/move operations with proper error handling"""
        try:
            if not os.path.exists(src_path):
                raise FileNotFoundError(f"File sumber tidak ditemukan: {src_path}")
                
            # Check permissions
            if not os.access(src_path, os.R_OK):
                raise PermissionError(f"Tidak ada akses baca ke file: {src_path}")
                
            if os.path.exists(dst_path) and not os.access(dst_path, os.W_OK):
                raise PermissionError(f"Tidak ada akses tulis ke tujuan: {dst_path}")
                
            src_size = os.path.getsize(src_path)
            if src_size == 0:
                raise ValueError("File sumber kosong (0 bytes)")

            # Copy operation with progress
            BUFFER_SIZE = 32 * 1024 * 1024
            copied_size = 0
            start_time = time.time()
            last_update = time.time()

            with open(src_path, 'rb') as fsrc:
                with open(dst_path, 'wb') as fdst:
                    while True:
                        buf = fsrc.read(BUFFER_SIZE)
                        if not buf:
                            break
                        fdst.write(buf)
                        fdst.flush()
                        copied_size += len(buf)
                        
                        current_time = time.time()
                        if current_time - last_update >= 0.05:
                            yield copied_size, src_size, current_time - start_time
                            last_update = current_time

            # Verify size
            dst_size = os.path.getsize(dst_path)
            if dst_size != src_size:
                if os.path.exists(dst_path):
                    os.remove(dst_path)
                raise ValueError(f"Verifikasi gagal - ukuran tidak sama (sumber: {src_size}, tujuan: {dst_size})")

            # Delete source if moving
            if operation == "move":
                os.remove(src_path)
                
            return True

        except Exception as e:
            if os.path.exists(dst_path):
                try:
                    os.remove(dst_path)
                except:
                    pass
            raise e

    def _process_files_thread(self, files, destination_folder, operation="copy"):
        """Combined function for move/copy operations"""
        try:
            total_files = len(files)
            self._reset_stats()
            self.moved_files = []

            for index, (file_path, info) in enumerate(files.items(), 1):
                try:
                    if not os.path.exists(file_path):
                        continue
                        
                    filename = info['name']
                    dst_path = os.path.join(destination_folder, filename)
                    
                    # Reset resolved path untuk setiap file
                    self._resolved_path = None
                    
                    # Handle conflicts terlebih dahulu sebelum operasi file
                    if os.path.exists(dst_path):
                        # Panggil dialog di main thread dan tunggu hasilnya
                        self.after(0, lambda p=dst_path: self._handle_conflict_async(p))
                        
                        # Tunggu sampai user memberi keputusan
                        timeout = 0
                        while self._resolved_path is None and timeout < 300:
                            time.sleep(0.1)
                            timeout += 1
                            
                        # Cek hasil keputusan user
                        if self._resolved_path is False:  # User memilih skip
                            self._update_stats('skipped')
                            continue
                        elif self._resolved_path is None:  # Dialog timeout
                            self._update_stats('failed')
                            raise TimeoutError("Dialog timeout")
                            
                        # Gunakan path yang sudah diresolve
                        dst_path = self._resolved_path

                    # Update status sebelum memulai operasi
                    status = f"Memproses {index}/{total_files}: {filename}"
                    self.after(0, self._update_progress_text, status)

                    try:
                        # Lakukan operasi file setelah konflik resolved
                        for copied_size, total_size, elapsed in self._do_file_operation(
                            file_path, dst_path, operation
                        ):
                            progress = (copied_size / total_size) * 100
                            total_progress = ((index - 1 + (copied_size / total_size)) / total_files) * 100
                            speed = copied_size / elapsed
                            speed_text = f"{speed / (1024 * 1024):.2f} MB/s" if speed > 1024 * 1024 else f"{speed / 1024:.2f} KB/s"
                            
                            status = f"{operation.capitalize()}ing {index}/{total_files}: {filename} ({int(progress)}%) - {speed_text}"
                            self.after(0, self._update_progress_text, status)
                            self.after(0, self._increment_progress, total_progress)

                        # Update stats setelah operasi sukses
                        self._update_stats('success')
                        if operation == "move":
                            self.moved_files.append(file_path)
                            
                    except Exception as e:
                        self._update_stats('failed')
                        self.after(0, self.main_window.update_status, f"Error: {str(e)}")
                        continue

                except Exception as e:
                    self._update_stats('failed') 
                    self.after(0, self.main_window.update_status, f"Error: {str(e)}")

            # Update final status
            stats_msg = self._get_stats_message(f"di{operation}")
            self.after(0, self.main_window.update_status, f"Selesai {operation} file - {stats_msg}")
            
            # Call appropriate finish handler
            if operation == "move":
                self.after(0, self._finish_move_operation, destination_folder)
            else:
                self.after(0, self._finish_copy_operation, destination_folder)
                
        finally:
            self.after(0, self._enable_buttons)

    def _validate_operation(self, op_type):
        """Validate operation before starting"""
        if not self.file_paths:
            messagebox.showwarning("Peringatan", "Tidak ada file yang dipilih!")
            return False
            
        if not self.selected_destination.get():
            messagebox.showwarning("Peringatan", "Pilih lokasi tujuan terlebih dahulu!")
            return False
            
        if not os.path.exists(self.selected_destination.get()):
            messagebox.showerror("Error", "Folder tujuan tidak ditemukan!")
            return False
            
        if not tk.messagebox.askyesno(
            "Konfirmasi", 
            f"Apakah Kamu yakin ingin {op_type} file yang dipilih?"
        ):
            self.main_window.update_status(f"{op_type.capitalize()} file dibatalkan")
            return False
            
        return True

    def _disable_buttons(self):
        """Disable buttons during operation"""
        self.move_button["state"] = "disabled"
        self.copy_button["state"] = "disabled"
        self.update_idletasks()

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

        # Clear stored paths
        self.file_paths.clear()
        
        # Clear text widget
        self.file_listbox.delete("1.0", tk.END)
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
        has_files = bool(self.file_paths)  # Use stored paths instead
        has_destination = bool(self.selected_destination.get())
        
        state = "normal" if (has_files and has_destination) else "disabled"
        self.move_button["state"] = state
        self.copy_button["state"] = state

    def open_selected_folder(self):
        folder_path = self.selected_destination.get()
        if not folder_path:
            tk.messagebox.showwarning("Peringatan", "Tidak ada folder yang dipilih!")
            return
        
        if not os.path.exists(folder_path):
            tk.messagebox.showerror("Error", f"Folder tidak ditemukan:\n{folder_path}")
            return
        
        os.startfile(folder_path)

    def _enable_buttons(self):
        """Re-enable buttons after operation completes"""
        self.operation_running = False
        has_files = bool(self.file_paths)  # Gunakan file_paths dictionary
        has_destination = bool(self.selected_destination.get())
        
        state = "normal" if (has_files and has_destination) else "disabled"
        self.move_button["state"] = state
        self.copy_button["state"] = state
        
        self.update_idletasks()

    def _finish_move_operation(self, destination_folder):
        """Finish up move operation"""
        self._update_progress_text(f"Lokasi: {destination_folder}")
        self.progress_bar["value"] = 0
        
        # Remove only successfully moved files from listbox
        if self.moved_files:
            # Get content using correct Text widget indices
            content = self.file_listbox.get("1.0", tk.END)
            lines = content.split('\n')
            remaining_lines = []
            
            # Filter out moved files
            for line in lines:
                if not any(os.path.basename(moved) in line for moved in self.moved_files):
                    remaining_lines.append(line)
                    
            # Clear and reinsert remaining lines
            self.file_listbox.delete("1.0", tk.END)
            if remaining_lines:
                self.file_listbox.insert("1.0", "\n".join(remaining_lines))
                
            # Update file_paths dictionary
            for moved_file in self.moved_files:
                if moved_file in self.file_paths:
                    del self.file_paths[moved_file]
        
        # Buat pesan detail
        detail_msg = []
        if self.stats['success'] > 0:
            # Tambahkan daftar file yang berhasil
            success_files = [os.path.basename(f) for f in self.moved_files]
            files_msg = "\n".join(success_files)
            detail_msg.append(f"File yang berhasil dipindahkan:\n\n{files_msg}\n")
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
            # Get remaining files for error message
            content = self.file_listbox.get("1.0", tk.END)
            remaining_files = [line.strip() for line in content.split('\n') if line.strip()]
            
            if remaining_files:
                files_msg = "\n".join(remaining_files)
                detail_msg.append(f"File yang gagal dipindahkan:\n\n{files_msg}\n")
            
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
        duplicates = []
        for path in files:
            if isinstance(path, bytes):
                path = path.decode('utf-8')
                
            if os.path.isdir(path):
                folder_files = [os.path.join(path, f) for f in os.listdir(path)]
                for file_path in folder_files:
                    if os.path.isfile(file_path):
                        thumb = self.get_thumbnail(file_path)
                        if thumb:
                            if not self.add_file_to_list(file_path, thumb):
                                duplicates.append(os.path.basename(file_path))
            else:
                if os.path.isfile(path):
                    thumb = self.get_thumbnail(path)
                    if thumb:
                        if not self.add_file_to_list(path, thumb):
                            duplicates.append(os.path.basename(path))
        
        if duplicates:
            self.main_window.update_status(f"File sudah ada dalam daftar: {', '.join(duplicates)}")
        
        self.update_dropzone_overlay()
        self.update_button_states()
        return "ok"

    def update_dropzone_overlay(self):
        """Update overlay visibility based on stored paths"""
        if not self.file_paths:
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

    def redraw_thumbnails(self, event=None):
        """Redraw all thumbnails in text widget"""
        try:
            self.file_listbox.delete("1.0", tk.END)
            for file_path, info in self.file_paths.items():
                thumb = info['thumb']
                if thumb:
                    self.file_listbox.insert(tk.END, " ")  # Small initial space
                    self.file_listbox.image_create(tk.END, image=thumb)
                    self.file_listbox.insert(tk.END, f" {info['name']}\n", "item")
        except Exception as e:
            print(f"Error redrawing thumbnails: {e}")

    def _get_files(self):
        """Helper to get current files in text widget"""
        return list(self.file_paths.keys())  # Return stored file paths instead of parsing text

    def on_text_click(self, event):
        """Handle text widget clicks for selection"""
        self.file_listbox.tag_remove("selected", "1.0", tk.END)
        try:
            index = self.file_listbox.index(f"@{event.x},{event.y}")
            line = int(float(index))
            if line % 2 == 1:  # Only select text lines, not spacing lines
                self.file_listbox.tag_add("selected", f"{line}.0", f"{line}.end")
        except:
            pass
        self.update_button_states()

    def get_selected_files(self):
        """Get selected files from text widget"""
        selected = []
        try:
            content = self.file_listbox.get("1.0", tk.END)
            lines = content.split('\n')
            ranges = self.file_listbox.tag_ranges("selected")
            
            for i in range(0, len(ranges), 2):
                start_line = int(float(str(ranges[i]).split('.')[0]))
                if start_line < len(lines):
                    selected_text = lines[start_line-1].strip()
                    if selected_text:
                        # Find matching file path from stored paths
                        for path, info in self.file_paths.items():
                            if info['name'] in selected_text:
                                selected.append(path)
                                break
        except Exception as e:
            print(f"Error getting selected files: {e}")
        return selected

# ...end of class...