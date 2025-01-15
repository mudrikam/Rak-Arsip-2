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
import tkinter as tk
from tkinter import ttk
import psutil
import ctypes
from ctypes import create_unicode_buffer
from PIL import Image, ImageTk
import threading
from queue import Queue
import time

class DiskAnalyzer(ttk.LabelFrame):
    def __init__(self, parent, BASE_DIR, main_window):
        super().__init__(parent, text="Analisa Penyimpanan :", padding=10)
        self.grid(row=0, column=0, padx=10, pady=10, sticky="nsew")
        self.BASE_DIR = BASE_DIR
        self.main_window = main_window
        self.parent = parent  # Tambahkan referensi ke parent window
        
        # Initialize variables
        self.all_partitions = []
        self.current_page = 0
        self.disks_per_page = 2
        self.active_disk_path = None
        self.selected_disk_frame = None
        self.disk_icon = None
        self.queue = Queue()
        self.current_thread = None
        self.current_scan_id = 0  # Add scan ID tracker
        
        # Initialize path tracking variables
        self.current_path = None
        self.path_history = []
        
        # Add file icon cache
        self.file_icons = {}
        self._load_file_icons()
        
        # Main vertical container
        self.main_container = ttk.Frame(self)
        self.main_container.pack(fill=tk.BOTH, expand=True)
        
        # Configure main_container to expand
        self.main_container.grid_rowconfigure(1, weight=1)  # Row for bottom_container
        self.main_container.grid_columnconfigure(0, weight=1)
        
        # Top frame for disks
        self.disks_container = ttk.LabelFrame(self.main_container, text="Daftar Disk:", padding=5)
        self.disks_container.grid(row=0, column=0, sticky="ew", pady=(0,10))
        
        # Create horizontal container for disk cards and navigation
        self.disk_nav_container = ttk.Frame(self.disks_container)
        self.disk_nav_container.pack(fill=tk.X, expand=True)
        
        # Left frame for disk cards
        self.disk_frame = ttk.Frame(self.disk_nav_container)
        self.disk_frame.pack(side=tk.LEFT, fill=tk.X, expand=True)
        
        # Right frame for navigation buttons
        self.nav_frame = ttk.Frame(self.disk_nav_container)
        self.nav_frame.pack(side=tk.RIGHT, padx=5)
        
        # Bottom container for content and stats - switch to grid
        self.bottom_container = ttk.Frame(self.main_container)
        self.bottom_container.grid(row=1, column=0, sticky="nsew")
        
        # Configure bottom container grid weights for equal width (50:50)
        self.bottom_container.grid_rowconfigure(0, weight=1)  # Full height
        self.bottom_container.grid_columnconfigure(0, weight=5)  # Left frame - 50%
        self.bottom_container.grid_columnconfigure(1, weight=5)  # Right frame - 50%
        
        # Content frame (left) - configure to expand
        self.content_frame = ttk.LabelFrame(self.bottom_container, text="Konten")
        self.content_frame.grid(row=0, column=0, padx=(0,5), sticky="nsew")
        self.content_frame.grid_rowconfigure(0, weight=1)
        self.content_frame.grid_columnconfigure(0, weight=1)
        
        # Statistics frame (right) - configure to expand
        self.stats_frame = ttk.LabelFrame(self.bottom_container, text="Statistik")
        self.stats_frame.grid(row=0, column=1, padx=(5,0), sticky="nsew")
        self.stats_frame.grid_rowconfigure(0, weight=1)
        self.stats_frame.grid_columnconfigure(0, weight=1)
        
        # Initialize components
        self._load_icons()
        self.create_navigation_buttons()
        self.setup_content_tree()
        
        # Load disks initially
        self.load_disks()

        # Load additional icons for navigation buttons - perbaiki pemanggilan method
        self.back_icon = self._load_icon(os.path.join(BASE_DIR, "Img", "icon", "ui", "back.png"), (16,16))
        self.open_icon = self._load_icon(os.path.join(BASE_DIR, "Img", "icon", "ui", "open.png"), (16,16))
        
        # Add navigation frame in content_frame - ubah konfigurasi grid
        self.nav_content_frame = ttk.Frame(self.content_frame)
        self.nav_content_frame.grid(row=0, column=0, sticky="ew", padx=5, pady=5)
        
        # Pastikan nav_content_frame tidak mengecil
        self.content_frame.grid_rowconfigure(0, weight=0)  # nav_content_frame - tidak mengecil
        self.content_frame.grid_rowconfigure(1, weight=1)  # tree_container - bisa mengecil
        self.content_frame.grid_columnconfigure(0, weight=1)

        # Back dan Open buttons dengan ikon
        self.back_btn = ttk.Button(
            self.nav_content_frame,
            text="Kembali",
            image=self.back_icon if self.back_icon else None,
            compound='left',
            command=self.go_back,
            padding=5,
            state="disabled"
        )
        self.back_btn.pack(side=tk.LEFT, padx=(0,5))
        
        self.open_folder_btn = ttk.Button(
            self.nav_content_frame,
            text="Buka",
            image=self.open_icon if self.open_icon else None,
            compound='left',
            command=self.open_current_folder,
            padding=5
        )
        self.open_folder_btn.pack(side=tk.LEFT, padx=5)
        
        self.path_label = ttk.Label(self.nav_content_frame, text="")
        self.path_label.pack(side=tk.LEFT, padx=5, fill=tk.X, expand=True)

        # Tree container sekarang akan mengecil saat ruang terbatas
        self.tree_container.grid(row=1, column=0, sticky="nsew", padx=5, pady=5)
        
        # Update content_frame grid weights
        self.content_frame.grid_rowconfigure(1, weight=1)  # TreeView row

    def create_navigation_buttons(self):
        """Create navigation buttons with modern style"""
        style = ttk.Style()
        style.configure("Nav.TButton", padding=2)
        
        self.prev_btn = ttk.Button(
            self.nav_frame, 
            text="◀", 
            width=3,
            style="Nav.TButton",
            command=self.prev_page
        )
        self.prev_btn.pack(side=tk.LEFT)

        self.page_label = ttk.Label(self.nav_frame, text="1/1")
        self.page_label.pack(side=tk.LEFT, padx=5)

        self.next_btn = ttk.Button(
            self.nav_frame,
            text="▶",
            width=3,
            style="Nav.TButton",
            command=self.next_page
        )
        self.next_btn.pack(side=tk.LEFT)

    def prev_page(self):
        if self.current_page > 0:
            self.current_page -= 1
            self.load_disks()

    def next_page(self):
        total_disks = len(self.all_partitions)
        total_pages = (total_disks + self.disks_per_page - 1) // self.disks_per_page
        if self.current_page < total_pages - 1:
            self.current_page += 1
            self.load_disks()

    def load_disks(self):
        try:
            # Clear selection when changing pages
            self.selected_disk_frame = None
            
            # Clear existing frames
            for widget in self.disk_frame.winfo_children():
                widget.destroy()
            
            # Get all partitions if not already loaded
            if not self.all_partitions:
                self.all_partitions = [p for p in psutil.disk_partitions(all=False)
                                     if not (p.mountpoint == '' or 
                                           ('cdrom' in p.opts.lower() and 
                                            not os.path.exists(p.mountpoint)))]
            
            # Calculate total pages
            total_disks = len(self.all_partitions)
            total_pages = (total_disks + self.disks_per_page - 1) // self.disks_per_page
            
            # Update navigation buttons
            self.prev_btn["state"] = "disabled" if self.current_page == 0 else "normal"
            self.next_btn["state"] = "disabled" if self.current_page >= total_pages - 1 else "normal"
            
            # Update page label
            self.page_label["text"] = f"{self.current_page + 1}/{total_pages}"
            
            # Get current page's partitions
            start_idx = self.current_page * self.disks_per_page
            end_idx = start_idx + self.disks_per_page
            current_partitions = self.all_partitions[start_idx:end_idx]
            
            # Create frames for current page's partitions
            for partition in current_partitions:
                try:
                    usage = psutil.disk_usage(partition.mountpoint)
                    frame = self.create_disk_frame(partition, usage)
                    if frame and partition.mountpoint == self.active_disk_path:
                        # Reselect active disk if it's on this page
                        # Gunakan parent bukan root
                        self.parent.after(100, lambda f=frame, p=partition.mountpoint: 
                                        self.select_disk_frame(f, p))
                except Exception as e:
                    print(f"Error processing partition {partition.mountpoint}: {str(e)}")
                    continue
                    
        except Exception as e:
            print(f"Error loading disks: {str(e)}")

    def _load_icons(self, size=(32, 32)):
        """Load icon untuk disk dari folder assets"""
        try:
            icon_path = os.path.join(self.BASE_DIR, "Img", "icon", "ui", "disk.png")
            if os.path.exists(icon_path):
                with Image.open(icon_path) as img:
                    if img.mode != 'RGBA':
                        img = img.convert('RGBA')
                    img = img.resize(size, Image.Resampling.LANCZOS)
                    self.disk_icon = ImageTk.PhotoImage(img)
        except Exception as e:
            print(f"Error loading disk icon: {e}")
            self.disk_icon = None

    def _load_file_icons(self, size=(24,24)):
        """Load all file icons from BASE_DIR/Img/Icon/Extension/"""
        try:
            icon_dir = os.path.join(self.BASE_DIR, "Img", "Icon", "Extension")
            if os.path.exists(icon_dir):
                for file in os.listdir(icon_dir):
                    if file.endswith(".png"):
                        ext = os.path.splitext(file)[0].lower()
                        icon_path = os.path.join(icon_dir, file)
                        try:
                            with Image.open(icon_path) as img:
                                if img.mode != 'RGBA':
                                    img = img.convert('RGBA')
                                img = img.resize(size, Image.Resampling.LANCZOS)
                                self.file_icons[ext] = ImageTk.PhotoImage(img)
                        except Exception as e:
                            print(f"Error loading icon {file}: {e}")
                            
            # Load default file and folder icons
            default_icons = {
                "file": "file.png",
                "folder": "folder.png"
            }
            
            for icon_type, filename in default_icons.items():
                path = os.path.join(self.BASE_DIR, "Img", "Icon", "ui", filename)
                if os.path.exists(path):
                    with Image.open(path) as img:
                        if img.mode != 'RGBA':
                            img = img.convert('RGBA')
                        img = img.resize(size, Image.Resampling.LANCZOS)
                        self.file_icons[icon_type] = ImageTk.PhotoImage(img)
                        
        except Exception as e:
            print(f"Error loading file icons: {e}")

    def create_disk_frame(self, partition, usage):
        try:
            # Create card frame with horizontal layout
            card = tk.Frame(self.disk_frame, bg='white', width=250, height=60)
            card.pack(side=tk.LEFT, padx=5, pady=5)  # Changed to LEFT for horizontal layout
            card.pack_propagate(False)
            
            # Left panel for icon
            icon_frame = tk.Frame(card, bg='white', width=50)
            icon_frame.pack(side=tk.LEFT, fill=tk.Y, padx=(5,0), pady=5)
            icon_frame.pack_propagate(False)
            
            # Update bagian icon label untuk menggunakan gambar
            if self.disk_icon:
                icon_label = tk.Label(icon_frame, image=self.disk_icon, bg='white')
            else:
                # Fallback ke emoji jika gambar tidak dapat dimuat
                icon_label = tk.Label(icon_frame, text="💾", font=('Arial', 16), bg='white')
            icon_label.pack(expand=True, padx=3, pady=3)
            
            # Right panel for info
            info_frame = tk.Frame(card, bg='white')
            info_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=5)
            
            # Get volume info dan info penggunaan disk
            volume_name = self.get_volume_name(partition.mountpoint)
            total_str = self.format_size(usage.total)
            used_str = self.format_size(usage.used)
            free_str = self.format_size(usage.free)
            
            # Update label untuk menampilkan informasi dalam satu baris
            name_label = tk.Label(info_frame, 
                                text=f"{volume_name}", 
                                font=('Arial', 9, 'bold'),
                                justify=tk.LEFT,
                                bg='white')
            name_label.pack(anchor=tk.W)
            
            info_label = tk.Label(info_frame, 
                                text=f"{total_str} ({used_str} / {free_str})", 
                                font=('Arial', 7),
                                justify=tk.LEFT,
                                bg='white')
            info_label.pack(anchor=tk.W)
            
            # Add progress bar
            progress = tk.Canvas(info_frame, height=5, bg='#E0E0E0', bd=0, highlightthickness=0)
            progress.pack(fill=tk.X, pady=(5,0))
            
            # Calculate used ratio and draw progress bar
            used_ratio = usage.used / usage.total
            
            # Binding untuk update progress bar saat ukuran berubah
            def update_progress(event=None):
                try:
                    width = progress.winfo_width()
                    if width > 0:
                        used_width = int(width * used_ratio)
                        progress.delete('all')  # Hapus konten sebelumnya
                        if used_width > 0:
                            progress.create_rectangle(0, 0, used_width, 5, 
                                                   fill='#2196F3', width=0)
                except:
                    pass

            # Bind resize event
            progress.bind('<Configure>', update_progress)
            card.after(100, update_progress)  # Schedule initial draw
            
            # Store all clickable widgets
            clickable_widgets = [card, icon_frame, info_frame, icon_label, name_label, info_label]
            
            def update_colors(color):
                card.configure(bg=color)
                icon_frame.configure(bg=color)
                info_frame.configure(bg=color)
                icon_label.configure(bg=color)
                name_label.configure(bg=color) 
                info_label.configure(bg=color)
            
            def on_enter(e):
                if card != self.selected_disk_frame:
                    update_colors('#F5F5F5')
                
            def on_leave(e):
                if card != self.selected_disk_frame:
                    update_colors('white')
            
            def on_click(e):
                self.select_disk_frame(card, partition.mountpoint)
            
            # Bind events to all clickable widgets
            for widget in clickable_widgets:
                widget.bind('<Enter>', on_enter)
                widget.bind('<Leave>', on_leave)
                widget.bind('<Button-1>', on_click)
            
            # Store widgets for selection state
            card.widgets = clickable_widgets
            
            return card
            
        except Exception as e:
            print(f"Error creating disk frame: {e}")
            return None

    def get_volume_name(self, path):
        if not path:
            return "Unknown"
        
        try:
            if os.name == 'nt':  # Windows
                kernel32 = ctypes.windll.kernel32
                volume_name_buffer = create_unicode_buffer(1024)
                file_system_name_buffer = create_unicode_buffer(1024)
                serial_number = None
                max_component_length = None
                file_system_flags = None

                kernel32.GetVolumeInformationW(
                    str(path),
                    volume_name_buffer,
                    ctypes.sizeof(volume_name_buffer),
                    serial_number,
                    max_component_length,
                    file_system_flags,
                    file_system_name_buffer,
                    ctypes.sizeof(file_system_name_buffer)
                )
                
                volume_name = volume_name_buffer.value
                return volume_name if volume_name else "Local Disk"
            else:
                return "Local Disk"
        except:
            return "Local Disk"

    def format_size(self, size):
        for unit in ['B', 'KB', 'MB', 'GB', 'TB']:
            if size < 1024:
                return f"{size:.2f} {unit}"
            size /= 1024

    def select_disk_frame(self, frame, path):
        """Select disk frame and update content"""
        try:
            # Cancel any existing scan first
            self.current_scan_id += 1
            if self.current_thread and self.current_thread.is_alive():
                self.queue.put(('cancel', None))
                
            # Update UI immediately
            if self.selected_disk_frame and hasattr(self.selected_disk_frame, 'widgets'):
                try:
                    for widget in self.selected_disk_frame.widgets:
                        widget.configure(bg='white')
                except tk.TclError:
                    pass

            # Select new frame
            if frame and hasattr(frame, 'widgets'):
                for widget in frame.widgets:
                    widget.configure(bg='#E3F2FD')
                self.selected_disk_frame = frame
                self.active_disk_path = path
                
                # Start content update in background
                self.parent.after(50, lambda: self.update_details(path))
            
        except Exception as e:
            print(f"Error in select_disk_frame: {e}")

    def setup_content_tree(self):
        """Setup treeview dengan kolom minimal"""
        style = ttk.Style()
        style.configure("Disk.Treeview", rowheight=32)
        style.layout("Disk.Treeview", [('Disk.Treeview.treearea', {'sticky': 'nswe'})])
        
        # Configure content_frame expansion
        self.content_frame.grid_rowconfigure(0, weight=1)
        self.content_frame.grid_columnconfigure(0, weight=1)
        
        # Create container frame that fills parent
        self.tree_container = ttk.Frame(self.content_frame)
        self.tree_container.grid(row=0, column=0, sticky="nsew", padx=5, pady=5)
        
        # Configure tree_container expansion
        self.tree_container.grid_rowconfigure(0, weight=1)
        self.tree_container.grid_columnconfigure(0, weight=1)
        
        # Create simplified treeview with fewer columns
        self.content_tree = ttk.Treeview(
            self.tree_container,
            style="Disk.Treeview",
            selectmode="browse",
            columns=("size", "name"),  # Hanya ukuran dan nama
            show="tree"
        )
        
        # Configure column widths
        self.content_tree.column("#0", width=50, minwidth=50, stretch=False)  # Kolom ikon
        self.content_tree.column("size", width=70, minwidth=70, stretch=False)  # Kolom ukuran
        self.content_tree.column("name", width=250, minwidth=100, stretch=True)  # Kolom nama
        
        vsb = ttk.Scrollbar(self.tree_container, orient="vertical")
        
        # Use grid for components
        self.content_tree.grid(row=0, column=0, sticky='nsew')
        vsb.grid(row=0, column=1, sticky='ns')
        
        # Configure scrolling
        self.content_tree.configure(yscrollcommand=vsb.set)
        vsb.configure(command=self.content_tree.yview)
        
        # Bind events
        self.content_tree.bind('<Double-1>', self.on_item_double_click)
        self.bind_tree_scroll()

    def bind_tree_scroll(self):
        """Bind scroll events for treeview"""
        def on_scroll(*args):
            self.content_tree.yview_scroll(int(-1*(args[0].delta/120)), "units")
            return "break"
            
        self.content_tree.bind('<MouseWheel>', on_scroll)
        self.content_tree.bind('<Button-4>', lambda e: self.content_tree.yview_scroll(-1, "units"))
        self.content_tree.bind('<Button-5>', lambda e: self.content_tree.yview_scroll(1, "units"))

    def update_details(self, path):
        """Update path display and history"""
        try:
            # Clear existing content first
            self.content_tree.delete(*self.content_tree.get_children())
            
            if not path or not os.path.exists(path):
                return
                
            # Update path tracking
            if path != self.current_path:
                if self.current_path:
                    self.path_history.append(self.current_path)
                self.current_path = path
                self.path_label["text"] = path
                self.back_btn["state"] = "normal" if self.path_history else "disabled"
            
            # Cancel any existing scan
            if self.current_thread and self.current_thread.is_alive():
                self.queue.put(('cancel', None))
                self.current_thread.join()
            
            # Start new scan thread
            self.current_thread = threading.Thread(
                target=self._scan_directory,
                args=(path,),
                daemon=True
            )
            self.current_thread.start()
            
            self.check_scan_queue()
            
        except Exception as e:
            print(f"Error updating details: {e}")

    def calculate_folder_size(self, path):
        """Calculate folder size more accurately"""
        total = 0
        try:
            with os.scandir(path) as it:
                for entry in it:
                    try:
                        if entry.is_file(follow_symlinks=False):
                            # Get actual file size
                            total += entry.stat().st_size
                        elif entry.is_dir(follow_symlinks=False):
                            # Recursively calculate subfolder size
                            total += self.calculate_folder_size(entry.path)
                    except (PermissionError, OSError):
                        continue
        except (PermissionError, OSError):
            pass
        return total

    def _scan_directory(self, path):
        """Improved scanning with better accuracy"""
        scan_id = self.current_scan_id
        try:
            items = []
            for item in os.scandir(path):
                if scan_id != self.current_scan_id:
                    return
                    
                try:
                    name = item.name
                    is_dir = item.is_dir(follow_symlinks=False)
                    
                    # More accurate size calculation
                    if is_dir:
                        size = self.calculate_folder_size(item.path)
                    else:
                        size = item.stat().st_size
                    
                    # Get icon
                    ext = os.path.splitext(name)[1].lower().lstrip('.')
                    icon = self.file_icons.get(
                        "folder" if is_dir else ext,
                        self.file_icons.get("file" if not is_dir else "folder")
                    )
                    
                    items.append((name, size, is_dir, icon, item.path))
                    
                    # Update UI with current sorted items
                    if len(items) % 10 == 0:  
                        current = sorted(items, key=lambda x: x[1], reverse=True)[:20]
                        self.queue.put(('partial', current))
                    
                except Exception as e:
                    print(f"Error scanning {name}: {e}")
                    continue

            if scan_id == self.current_scan_id:
                final_items = sorted(items, key=lambda x: x[1], reverse=True)[:20]
                self.queue.put(('results', final_items))
                
        except Exception as e:
            print(f"Scan error: {e}")

    def check_scan_queue(self):
        """Updated queue checking with simplified columns"""
        try:
            if not self.queue.empty():
                action, data = self.queue.get_nowait()
                
                if action in ('results', 'partial'):
                    self.content_tree.delete(*self.content_tree.get_children())
                    for name, size, is_dir, icon, item_path in data:
                        size_str = self.format_size(size)
                        
                        self.content_tree.insert(
                            "", "end",
                            text="",  # Empty for icon column
                            image=icon,
                            values=(size_str, name),  # Hanya ukuran dan nama
                            tags=(item_path,)
                        )
                    
                    if action == 'results':
                        return
                        
            self.parent.after(25, self.check_scan_queue)
            
        except Exception as e:
            print(f"Queue check error: {e}")

    def on_item_double_click(self, event):
        """Handle double click using tags for path"""
        try:
            item_id = self.content_tree.selection()[0]
            item_path = self.content_tree.item(item_id)['tags'][0]  # Get path from tags
            
            if os.path.isdir(item_path):
                self.update_details(item_path)
        except Exception as e:
            print(f"Error handling double click: {e}")

    def go_back(self):
        """Navigate to previous folder"""
        if self.path_history:
            prev_path = self.path_history.pop()
            self.current_path = None  # Reset so update_details will work
            self.update_details(prev_path)

    def open_current_folder(self):
        """Open current folder in system file explorer"""
        try:
            if self.current_path and os.path.exists(self.current_path):
                if os.name == 'nt':  # Windows
                    os.startfile(self.current_path)
                else:  # Linux/Mac
                    subprocess.call(['xdg-open', self.current_path])
        except Exception as e:
            print(f"Error opening folder: {e}")

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