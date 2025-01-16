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
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import random
import colorsys  # Tambahkan import ini di bagian atas
import subprocess  # Tambahkan import ini

class DiskAnalyzer(ttk.Frame):
    def __init__(self, parent, BASE_DIR, main_window):
        super().__init__(parent)
        self.grid(row=0, column=0, padx=10, pady=0, sticky="nsew")
        
        self.BASE_DIR = BASE_DIR
        self.main_window = main_window
        self.parent = parent
        
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
        self.disks_container = ttk.LabelFrame(self.main_container, text="Daftar Disk :", padding=5)
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
        self.bottom_container.grid_columnconfigure(0, weight=3)  # Left frame - 30%
        self.bottom_container.grid_columnconfigure(1, weight=7)  # Right frame - 70%
        
        # Content frame (left) - configure to expand
        self.content_frame = ttk.LabelFrame(self.bottom_container, text="Konten :", padding=5)
        self.content_frame.grid(row=0, column=0, padx=(0,5), sticky="nsew")
        self.content_frame.grid_rowconfigure(0, weight=1)
        self.content_frame.grid_columnconfigure(0, weight=1)
        
        # Statistics frame (right) - configure to expand
        self.stats_frame = ttk.LabelFrame(self.bottom_container, text="Statistik :", padding=5)
        self.stats_frame.grid(row=0, column=1, padx=(5,0), sticky="nsew")
        self.stats_frame.grid_rowconfigure(0, weight=1)
        self.stats_frame.grid_columnconfigure(0, weight=1)
        
        # Set background color untuk stats_frame
        style = ttk.Style()
        style.configure("Stats.TLabelframe", background="#f0f0f0")
        style.configure("Stats.TLabelframe.Label", background="#f0f0f0")  # Untuk label frame
        self.stats_frame.configure(style="Stats.TLabelframe")
        
        # Ganti placeholder label dengan matplotlib canvas
        self.fig = plt.Figure(figsize=(5, 5), dpi=100, facecolor='#f0f0f0')
        self.ax = self.fig.add_subplot(111)
        self.canvas = FigureCanvasTkAgg(self.fig, master=self.stats_frame)
        self.canvas.get_tk_widget().configure(bg='#f0f0f0')
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
        # Bind resize event untuk update ukuran chart
        self.stats_frame.bind('<Configure>', self._update_chart_size)
        
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
        self.content_frame.grid_rowconfigure(0, weight=0)  # nav_buttons_frame - tidak mengecil
        self.content_frame.grid_rowconfigure(1, weight=0)  # path_frame - tidak mengecil
        self.content_frame.grid_rowconfigure(2, weight=1)  # tree_container - bisa mengecil
        self.content_frame.grid_columnconfigure(0, weight=1)

        # Frame untuk tombol-tombol
        nav_buttons_frame = ttk.Frame(self.nav_content_frame)
        nav_buttons_frame.grid(row=0, column=0, sticky="w")

        # Back dan Open buttons dengan ikon di nav_buttons_frame
        self.back_btn = ttk.Button(
            nav_buttons_frame,
            text="Kembali",
            image=self.back_icon if self.back_icon else None,
            compound='left',
            command=self.go_back,
            padding=5,
            state="disabled"
        )
        self.back_btn.pack(side=tk.LEFT, padx=(0,5))
        
        self.open_folder_btn = ttk.Button(
            nav_buttons_frame,
            text="Buka",
            image=self.open_icon if self.open_icon else None,
            compound='left',
            command=self.open_current_folder,
            padding=5,
            state="disabled"
        )
        self.open_folder_btn.pack(side=tk.LEFT, padx=5)

        # Frame untuk path label
        path_frame = ttk.Frame(self.nav_content_frame)
        path_frame.grid(row=1, column=0, sticky="ew", pady=(5,0))
        
        self.path_label = ttk.Label(path_frame, text="")
        self.path_label.pack(side=tk.LEFT, fill=tk.X, expand=True)

        # Tree container sekarang akan mengecil saat ruang terbatas
        self.tree_container.grid(row=2, column=0, sticky="nsew", padx=5, pady=5)
        
        # Update content_frame grid weights
        self.content_frame.grid_rowconfigure(1, weight=1)  # TreeView row

        # Add style for colored text in treeview
        self.style = ttk.Style()
        self.style.configure(
            "Disk.Treeview", 
            rowheight=32,
            background="white",
            fieldbackground="white"
        )
        
        # Dictionary untuk menyimpan warna item
        self.item_colors = {}

        # Tambahkan konstanta untuk warna
        self.FIXED_SATURATION = 0.6
        self.FIXED_VALUE = 0.9
        
        # Tambahkan variabel untuk tracking item yang dipilih
        self.selected_item_path = None
        
        # Tambahkan binding untuk klik pada treeview
        self.content_tree.bind('<<TreeviewSelect>>', self._on_tree_select)

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
                # Get local partitions
                local_partitions = [p for p in psutil.disk_partitions(all=False)
                                  if not (p.mountpoint == '' or 
                                        ('cdrom' in p.opts.lower() and 
                                         not os.path.exists(p.mountpoint)))]
                
                # Get network drives using subprocess
                try:
                    result = subprocess.check_output(
                        "net use", 
                        shell=True,
                        text=True,
                        creationflags=subprocess.CREATE_NO_WINDOW
                    ).splitlines()
                    
                    for line in result[2:]:  # Skip header lines
                        if line.strip() and "OK" in line:
                            parts = line.split()
                            if len(parts) >= 2:
                                drive_letter = parts[1]
                                if os.path.exists(drive_letter):
                                    # Create custom partition object for network drive
                                    net_part = psutil._common.sdiskpart(
                                        device=parts[-1],
                                        mountpoint=drive_letter,
                                        fstype='Network',
                                        opts='network'
                                    )
                                    local_partitions.append(net_part)
                                    
                except subprocess.CalledProcessError:
                    print("Failed to get network drives")
                    
                self.all_partitions = local_partitions
            
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
                        self.parent.after(100, lambda f=frame, p=partition.mountpoint: 
                                        self.select_disk_frame(f, p))
                except (PermissionError, OSError) as e:
                    print(f"Error accessing {partition.mountpoint}: {str(e)}")
                    # Tetap buat frame untuk drive yang tidak bisa diakses
                    frame = self.create_disk_frame(partition, None)
                    continue
                    
        except Exception as e:
            print(f"Error loading disks: {e}")

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

    def get_network_drive_info(self, drive_letter):
        """Get network drive share name and UNC path"""
        try:
            result = subprocess.check_output(
                "net use",
                shell=True,
                text=True,
                creationflags=subprocess.CREATE_NO_WINDOW
            ).splitlines()
            
            for line in result[2:]:  # Skip header lines
                if line.strip() and drive_letter.rstrip('\\') in line:
                    parts = line.split()
                    if len(parts) >= 3:
                        remote_path = parts[-1]
                        # Try to get share label from mounted network drive
                        try:
                            kernel32 = ctypes.windll.kernel32
                            volume_name_buffer = create_unicode_buffer(1024)
                            kernel32.GetVolumeInformationW(
                                str(drive_letter),
                                volume_name_buffer,
                                ctypes.sizeof(volume_name_buffer),
                                None, None, None, None, 0
                            )
                            share_label = volume_name_buffer.value
                            if share_label:
                                return f"{share_label} ({remote_path})"
                        except:
                            pass
                            
                        # Fallback: Extract share name from UNC path
                        share_name = remote_path.split('\\')[-1]
                        return f"{share_name} ({remote_path})"
        except:
            pass
        return None

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
            
            # Choose appropriate icon based on drive type
            is_network = hasattr(partition, 'opts') and 'network' in partition.opts.lower()
            icon_name = "network.png" if is_network else "disk.png"
            icon_path = os.path.join(self.BASE_DIR, "Img", "icon", "ui", icon_name)
            
            if os.path.exists(icon_path):
                with Image.open(icon_path) as img:
                    if img.mode != 'RGBA':
                        img = img.convert('RGBA')
                    img = img.resize((32, 32), Image.Resampling.LANCZOS)
                    icon = ImageTk.PhotoImage(img)
                    icon_label = tk.Label(icon_frame, image=icon, bg='white')
                    icon_label.image = icon  # Keep reference
            else:
                icon_label = tk.Label(icon_frame, text="💾", font=('Arial', 16), bg='white')
                
            icon_label.pack(expand=True, padx=3, pady=3)
            
            # Right panel for info
            info_frame = tk.Frame(card, bg='white')
            info_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=5)
            
            # Get volume info with better network drive handling
            if hasattr(partition, 'opts') and 'network' in partition.opts.lower():
                net_name = self.get_network_drive_info(partition.mountpoint)
                volume_name = net_name if net_name else f"Shared Folder ({partition.device})"
            else:
                volume_name = self.get_volume_name(partition.mountpoint)
            
            # Add drive letter to volume name
            drive_letter = partition.mountpoint.rstrip('\\')  # Remove trailing backslash
            volume_name = f"{drive_letter} - {volume_name}"
            
            # Handle usage info
            if usage:
                total_str = self.format_size(usage.total)
                used_str = self.format_size(usage.used)
                free_str = self.format_size(usage.free)
                info_text = f"{total_str} ({used_str} / {free_str})"
            else:
                info_text = "Access Denied"
                
            # Update labels
            name_label = tk.Label(info_frame, 
                                text=f"{volume_name}", 
                                font=('Arial', 9, 'bold'),
                                justify=tk.LEFT,
                                bg='white')
            name_label.pack(anchor=tk.W)
            
            info_label = tk.Label(info_frame, 
                                text=info_text, 
                                font=('Arial', 7),
                                justify=tk.LEFT,
                                bg='white')
            info_label.pack(anchor=tk.W)
            
            # Add progress bar only if usage info is available
            if usage:
                progress = tk.Canvas(info_frame, height=5, bg='#E0E0E0', bd=0, highlightthickness=0)
                progress.pack(fill=tk.X, pady=(5,0))
                
                used_ratio = usage.used / usage.total
                
                def update_progress(event=None):
                    try:
                        width = progress.winfo_width()
                        if width > 0:
                            used_width = int(width * used_ratio)
                            progress.delete('all')
                            if used_width > 0:
                                progress.create_rectangle(0, 0, used_width, 5, 
                                                       fill='#2196F3', width=0)
                    except:
                        pass

                progress.bind('<Configure>', update_progress)
                card.after(100, update_progress)
            
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
        
        # Add binding for pie chart clicks
        self.canvas.get_tk_widget().bind('<Button-1>', self._on_pie_click)

    def bind_tree_scroll(self):
        """Bind scroll events for treeview"""
        def on_scroll(*args):
            self.content_tree.yview_scroll(int(-1*(args[0].delta/120)), "units")
            return "break"
            
        self.content_tree.bind('<MouseWheel>', on_scroll)
        self.content_tree.bind('<Button-4>', lambda e: self.content_tree.yview_scroll(-1, "units"))
        self.content_tree.bind('<Button-5>', lambda e: self.content_tree.yview_scroll(1, "units"))

    def update_details(self, path):
        """Update path display and history with timeout handling"""
        try:
            self.content_tree.delete(*self.content_tree.get_children())
            self.open_folder_btn["state"] = "disabled"
            
            if not path:
                return
                
            # Quick check for path existence with timeout
            try:
                import socket
                socket.setdefaulttimeout(2)
                if not os.path.exists(path):
                    return
            except (TimeoutError, OSError):
                print(f"Timeout checking path: {path}")
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
                self.current_thread.join(timeout=1)  # Wait max 1 second
            
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
        """Calculate folder size with timeout and check responsiveness"""
        total = 0
        try:
            # Add timeout for network operations
            if '\\\\' in path or hasattr(path, 'opts') and 'network' in path.opts.lower():
                import socket
                socket.setdefaulttimeout(2)  # 2 second timeout for network ops
                
            with os.scandir(path) as it:
                for entry in it:
                    try:
                        # Allow GUI to update
                        self.update_idletasks()
                        
                        if entry.is_file(follow_symlinks=False):
                            try:
                                # Quick timeout for stat operations
                                total += entry.stat(follow_symlinks=False).st_size
                            except (TimeoutError, OSError):
                                continue
                        elif entry.is_dir(follow_symlinks=False):
                            try:
                                # Recursively calculate with timeout
                                subtotal = self.calculate_folder_size(entry.path)
                                if subtotal is not None:  # Check if calculation succeeded
                                    total += subtotal
                            except (TimeoutError, OSError):
                                continue
                    except (PermissionError, OSError):
                        continue
            return total
        except Exception:
            # Suppress error messages for common access issues
            return 0

    def _scan_directory(self, path):
        """Improved scanning with better network handling"""
        scan_id = self.current_scan_id
        try:
            items = []
            # Set timeout for network paths
            if '\\\\' in path:
                import socket
                socket.setdefaulttimeout(2)
                
            for item in os.scandir(path):
                if scan_id != self.current_scan_id:
                    return
                    
                try:
                    # Allow GUI to update periodically
                    if len(items) % 5 == 0:
                        self.update_idletasks()
                        
                    name = item.name
                    is_dir = item.is_dir(follow_symlinks=False)
                    
                    try:
                        if is_dir:
                            size = self.calculate_folder_size(item.path)
                        else:
                            size = item.stat(follow_symlinks=False).st_size
                    except (TimeoutError, OSError):
                        size = 0
                    
                    # Get icon
                    ext = os.path.splitext(name)[1].lower().lstrip('.')
                    icon = self.file_icons.get(
                        "folder" if is_dir else ext,
                        self.file_icons.get("file" if not is_dir else "folder")
                    )
                    
                    items.append((name, size, is_dir, icon, item.path))
                    
                    # Update UI more frequently for responsiveness
                    if len(items) % 5 == 0:  
                        current = sorted(items, key=lambda x: x[1], reverse=True)[:20]
                        self.queue.put(('partial', current))
                    
                except Exception:
                    # Suppress error messages for file access issues
                    continue

            if scan_id == self.current_scan_id:
                final_items = sorted(items, key=lambda x: x[1], reverse=True)[:20]
                self.queue.put(('results', final_items))
                
        except Exception as e:
            print(f"Scan error: {e}")

    def check_scan_queue(self):
        try:
            if not self.queue.empty():
                action, data = self.queue.get_nowait()
                
                if action in ('results', 'partial'):
                    self.content_tree.delete(*self.content_tree.get_children())
                    
                    self.item_colors = {}
                    sizes = []
                    colors = []
                    items = []
                    
                    # Store complete data for reference
                    sorted_data = sorted(data, key=lambda x: x[1], reverse=True)[:20]
                    self.current_chart_data = []
                    
                    # Enable/disable open button based on data availability
                    if sorted_data:
                        self.open_folder_btn["state"] = "normal"
                    else:
                        self.open_folder_btn["state"] = "disabled"
                    
                    # Hitung total size dari 20 item terbesar
                    max_size = sorted_data[0][1] if sorted_data else 0
                    
                    for name, size, is_dir, icon, item_path in sorted_data:
                        # Generate warna berdasarkan proporsi ukuran relatif terhadap yang terbesar
                        size_ratio = size / max_size if max_size > 0 else 0
                        color = self._generate_color(size_ratio)
                        self.item_colors[item_path] = color
                        
                        # Store complete data tuple for chart
                        self.current_chart_data.append((name, size, item_path))
                        
                        items.append((name, size, icon, item_path))
                        sizes.append(size)
                        colors.append(color)
                    
                    self._draw_pie_chart(sizes, colors)
                    
                    for name, size, icon, item_path in items:
                        size_str = self.format_size(size)
                        item_id = self.content_tree.insert(
                            "", "end",
                            text="",
                            image=icon,
                            values=(size_str, name),
                            tags=(item_path,)
                        )
                        self.content_tree.tag_configure(
                            item_path,
                            foreground=self.item_colors[item_path]
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

    def _update_chart_size(self, event=None):
        """Update chart size when frame is resized"""
        try:
            # Kurangi padding
            width = self.stats_frame.winfo_width() - 10   # Dari 40 ke 10
            height = self.stats_frame.winfo_height() - 10  # Dari 40 ke 10
            
            # Use smaller dimension for perfect circle
            size = min(width, height) / 100  # Convert to inches (assuming 100 dpi)
            self.fig.set_size_inches(size, size)
            
            # Force redraw
            self.canvas.draw()
                
        except Exception as e:
            print(f"Error updating chart size: {e}")

    def _draw_pie_chart(self, sizes, colors):
        """Draw simple donut chart"""
        try:
            self.ax.clear()
            if sizes:
                # Draw pie chart
                wedges, _ = self.ax.pie(
                    sizes, 
                    colors=colors,
                    wedgeprops=dict(
                        width=0.4,
                        edgecolor='#f0f0f0',
                        linewidth=1
                    ),
                    startangle=90,
                    radius=0.98
                )
                
                self.pie_wedges = wedges
                
                self.ax.axis('equal')
                self.fig.patch.set_facecolor('none')
                self.ax.patch.set_facecolor('none')
                self.fig.subplots_adjust(left=0.02, right=0.98, top=0.98, bottom=0.02)
                
                # Reset selection and center text
                self.selected_item_path = None
                # Hapus text di tengah saat tidak ada yang dipilih
                self.center_text = self.ax.text(0, 0, '', 
                                              horizontalalignment='center',
                                              verticalalignment='center',
                                              fontsize=9)
                
                # Store sector data
                self.sectors = []
                for i, wedge in enumerate(wedges):
                    if i < len(self.current_chart_data):
                        name, size, item_path = self.current_chart_data[i]
                        self.sectors.append({
                            'path': item_path,
                            'size': size,
                            'name': name,
                            'original_color': colors[i],
                            'start': wedge.theta1,
                            'end': wedge.theta2
                        })
                
                self.canvas.draw()
            
        except Exception as e:
            print(f"Error drawing pie chart: {e}")

    def _update_pie_colors(self):
        """Update pie colors based on selection"""
        if not hasattr(self, 'sectors') or not self.sectors:
            return
            
        if self.selected_item_path is None:
            # Reset semua pie ke warna asli
            for wedge, sector in zip(self.pie_wedges, self.sectors):
                wedge.set_facecolor(sector['original_color'])
            # Hapus text di tengah
            if hasattr(self, 'center_text'):
                self.center_text.set_text('')
        else:
            # Buat warna baru berdasarkan selection
            colors = []
            selected_size = None
            selected_name = None
            
            for sector in self.sectors:
                if sector['path'] == self.selected_item_path:
                    colors.append(sector['original_color'])
                    selected_size = sector['size']
                    selected_name = sector['name']
                else:
                    colors.append('#E0E0E0')
            
            # Update wedges dengan warna baru
            for wedge, color in zip(self.pie_wedges, colors):
                wedge.set_facecolor(color)
                
            # Update text di tengah dengan ukuran dan nama yang dipilih
            if hasattr(self, 'center_text') and selected_size is not None:
                size_text = self.format_size(selected_size)
                name_text = selected_name if len(selected_name) < 20 else selected_name[:17] + '...'
                center_text = f'{name_text}\n{size_text}'
                self.center_text.set_text(center_text)
                
        self.canvas.draw()

    def _generate_color(self, size_ratio):
        """
        Generate warna berdasarkan rasio ukuran:
        """
        hue = 30 + (size_ratio * (60 - 180))
        
        # Konversi ke range 0-1
        hue = (hue % 360) / 360
        
        rgb = colorsys.hsv_to_rgb(hue, self.FIXED_SATURATION, self.FIXED_VALUE)
        return f'#{int(rgb[0]*255):02x}{int(rgb[1]*255):02x}{int(rgb[2]*255):02x}'

    def _on_tree_select(self, event):
        """Handle tree item selection"""
        selection = self.content_tree.selection()
        if selection:
            item_path = self.content_tree.item(selection[0])['tags'][0]
            self.selected_item_path = item_path
            self._update_pie_colors()
    
    def _update_pie_colors(self):
        """Update pie colors based on selection"""
        if not hasattr(self, 'sectors') or not self.sectors:
            return
            
        if self.selected_item_path is None:
            # Reset semua pie ke warna asli
            for wedge, sector in zip(self.pie_wedges, self.sectors):
                wedge.set_facecolor(sector['original_color'])
            # Hapus text di tengah
            if hasattr(self, 'center_text'):
                self.center_text.set_text('')
        else:
            # Buat warna baru berdasarkan selection
            colors = []
            selected_size = None
            selected_name = None
            
            for sector in self.sectors:
                if sector['path'] == self.selected_item_path:
                    colors.append(sector['original_color'])
                    selected_size = sector['size']
                    selected_name = sector['name']
                else:
                    colors.append('#E0E0E0')
            
            # Update wedges dengan warna baru
            for wedge, color in zip(self.pie_wedges, colors):
                wedge.set_facecolor(color)
                
            # Update text di tengah dengan ukuran dan nama yang dipilih
            if hasattr(self, 'center_text') and selected_size is not None:
                size_text = self.format_size(selected_size)
                name_text = selected_name if len(selected_name) < 20 else selected_name[:17] + '...'
                center_text = f'{name_text}\n{size_text}'
                self.center_text.set_text(center_text)
                
        self.canvas.draw()

    def _on_pie_click(self, event):
        """Handle clicks on pie chart area"""
        try:
            # Deselect tree items
            for item in self.content_tree.selection():
                self.content_tree.selection_remove(item)
            
            # Reset pie colors
            self.selected_item_path = None
            self._update_pie_colors()
        except Exception as e:
            print(f"Error handling pie click: {e}")