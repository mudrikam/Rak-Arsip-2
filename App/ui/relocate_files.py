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
import csv

class RelocateFiles(ttk.LabelFrame):
    def __init__(self, parent, BASE_DIR, main_window):
        super().__init__(parent, text="Relokasi File", padding=10)
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

    def create_widgets(self):
        # Configure equal width columns
        self.columnconfigure(0, weight=1, uniform="group1")
        self.columnconfigure(1, weight=1, uniform="group1")

        # Create left panel (Source)
        self.left_panel = ttk.LabelFrame(self, text="Sumber", padding=10)
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

        self.file_listbox = tk.Listbox(self.left_panel, selectmode=tk.MULTIPLE)
        self.file_listbox.pack(fill="both", expand=True)

        # Make listbox fill space
        self.left_panel.columnconfigure(0, weight=1)
        self.left_panel.rowconfigure(1, weight=1)
        self.file_listbox.pack(fill="both", expand=True)

        # Create right panel (Destination)
        self.right_panel = ttk.LabelFrame(self, text="Tujuan", padding=10)
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
        style.configure('Location.Horizontal.TProgressbar', text='Belum ada lokasi yang dipilih')

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
                    self.open_folder_button["state"] = "normal"
                    break
        else:
            self.open_folder_button["state"] = "disabled"

    def select_destination_folder(self):
        folder = filedialog.askdirectory()
        if folder:
            self.selected_destination.set(folder)
            self.update_location_label(folder)
            self.update_button_states()

    def update_location_label(self, path):
        if path:
            # Update progress bar text.
            style = ttk.Style()
            style.configure('Location.Horizontal.TProgressbar', text=f"Tujuan: {path}")
            self.progress_bar["value"] = 0
        else:
            style = ttk.Style()
            style.configure('Location.Horizontal.TProgressbar', text="Belum ada lokasi yang dipilih")
            self.progress_bar["value"] = 0

    def select_files(self):
        file_paths = filedialog.askopenfilenames(title="Pilih File", filetypes=[("All Files", "*.*")])
        if file_paths:
            self.file_listbox.delete(0, tk.END)
            for file_path in file_paths:
                self.file_listbox.insert(tk.END, file_path)
            self.update_button_states()

    def select_folder(self):
        folder_path = filedialog.askdirectory(title="Pilih Folder")
        if folder_path:
            folder_files = [os.path.join(folder_path, f) for f in os.listdir(folder_path)]
            self.file_listbox.delete(0, tk.END)
            for file_path in folder_files:
                self.file_listbox.insert(tk.END, file_path)
            self.update_button_states()

    def handle_file_conflict(self, dst_path):
        """Handle file conflict with options for handling all similar cases."""
        if not os.path.exists(dst_path):
            return dst_path

        # Check existing "all" decisions
        if self.replace_all:
            return dst_path
        elif self.rename_all:
            base, ext = os.path.splitext(dst_path)
            counter = 1
            while os.path.exists(dst_path):
                dst_path = f"{base} ({counter}){ext}"
                counter += 1
            return dst_path
        elif self.skip_all:
            return None

        # Create and configure dialog
        dialog = tk.Toplevel()
        dialog.title("File sudah ada")
        dialog.transient(self)
        dialog.grab_set()
        
        # Set icon
        icon_path = os.path.join(self.BASE_DIR, "Img", "Icon", "rakikon.ico")
        if os.path.exists(icon_path):
            dialog.iconbitmap(icon_path)

        # Configure grid
        dialog.grid_columnconfigure(0, weight=1)
        
        # Message
        message = f"'{os.path.basename(dst_path)}' sudah ada di folder tujuan.\nApa yang ingin dilakukan?"
        ttk.Label(dialog, text=message, padding=10).grid(row=0, column=0, sticky="ew")

        result = {"action": None}

        def set_action(action):
            result["action"] = action
            dialog.destroy()

        # Button frame with grid layout
        button_frame = ttk.Frame(dialog, padding=10)
        button_frame.grid(row=1, column=0, sticky="ew")
        button_frame.grid_columnconfigure(0, weight=1)
        button_frame.grid_columnconfigure(1, weight=1)
        button_frame.grid_columnconfigure(2, weight=1)

        # First row buttons
        ttk.Button(button_frame, text="Ganti", width=15,
                  command=lambda: set_action("replace")).grid(row=0, column=0, padx=5, pady=2)
        ttk.Button(button_frame, text="Buat Baru", width=15,
                  command=lambda: set_action("rename")).grid(row=0, column=1, padx=5, pady=2)
        ttk.Button(button_frame, text="Lewati", width=15,
                  command=lambda: set_action("skip")).grid(row=0, column=2, padx=5, pady=2)

        # Second row buttons
        ttk.Button(button_frame, text="Ganti Semua", width=15,
                  command=lambda: set_action("replace_all")).grid(row=1, column=0, padx=5, pady=2)
        ttk.Button(button_frame, text="Buat Baru Semua", width=15,
                  command=lambda: set_action("rename_all")).grid(row=1, column=1, padx=5, pady=2)
        ttk.Button(button_frame, text="Lewati Semua", width=15,
                  command=lambda: set_action("skip_all")).grid(row=1, column=2, padx=5, pady=2)

        # Center dialog on screen
        dialog.update_idletasks()
        width = dialog.winfo_width()
        height = dialog.winfo_height()
        x = (dialog.winfo_screenwidth() // 2) - (width // 2)
        y = (dialog.winfo_screenheight() // 2) - (height // 2)
        dialog.geometry(f"{width}x{height}+{x}+{y}")

        dialog.wait_window()

        # Handle result
        if result["action"] == "replace_all":
            self.replace_all = True
            return dst_path
        elif result["action"] == "replace":
            return dst_path
        elif result["action"] == "rename_all":
            self.rename_all = True
            base, ext = os.path.splitext(dst_path)
            counter = 1
            while os.path.exists(dst_path):
                dst_path = f"{base} ({counter}){ext}"
                counter += 1
            return dst_path
        elif result["action"] == "rename":
            base, ext = os.path.splitext(dst_path)
            counter = 1
            while os.path.exists(dst_path):
                dst_path = f"{base} ({counter}){ext}"
                counter += 1
            return dst_path
        elif result["action"] == "skip_all":
            self.skip_all = True
            return None
        elif result["action"] == "skip":
            return None
        else:
            return None

    def move_files(self):
        # Reset the "all" flags at the start of a new operation
        self.replace_all = False
        self.rename_all = False
        self.skip_all = False

        destination_folder = self.selected_destination.get()
        if not destination_folder:
            destination_folder = filedialog.askdirectory(title="Pilih Folder Tujuan")
            if not destination_folder:
                return

        files = self.file_listbox.get(0, tk.END)
        if not files:
            return

        if not tk.messagebox.askyesno("Konfirmasi", "Apakah Kamu yakin ingin memindahkan file yang dipilih?"):
            return

        self.progress_bar["maximum"] = 100
        self.progress_bar["value"] = 0

        style = ttk.Style()
        for file_path in files:
            try:
                dst_path = os.path.join(destination_folder, os.path.basename(file_path))
                resolved_path = self.handle_file_conflict(dst_path)
                
                if resolved_path is None:  # User chose to skip
                    continue
                    
                style.configure('Location.Horizontal.TProgressbar', 
                              text=f"Memindahkan: {os.path.basename(file_path)}")
                shutil.move(file_path, resolved_path)
                self.progress_bar["value"] += (100 / len(files))
                self.update_idletasks()
            except Exception as e:
                print(f"Error moving {file_path}: {e}")

        style.configure('Location.Horizontal.TProgressbar', 
                       text=f"Lokasi: {destination_folder}")
        self.progress_bar["value"] = 0
        tk.messagebox.showinfo("Selesai", "Proses pemindahan selesai.")
        self.main_window.update_status(f"File berhasil dipindahkan ke {destination_folder}")
        self.reset_files()

    def copy_files(self):
        # Reset the "all" flags at the start of a new operation
        self.replace_all = False
        self.rename_all = False
        self.skip_all = False

        if not tk.messagebox.askyesno("Konfirmasi", "Apakah Kamu yakin ingin menyalin file yang dipilih?"):
            return

        destination_folder = self.selected_destination.get()
        if not destination_folder:
            destination_folder = filedialog.askdirectory(title="Pilih Folder Tujuan")
            if not destination_folder:
                return

        files = self.file_listbox.get(0, tk.END)
        if not files:
            return

        self.progress_bar["maximum"] = 100
        self.progress_bar["value"] = 0

        style = ttk.Style()
        for file_path in files:
            try:
                style.configure('Location.Horizontal.TProgressbar', 
                              text=f"Menyalin: {os.path.basename(file_path)}")
                self.copy_file_with_progress(file_path, destination_folder)
            except Exception as e:
                print(f"Error copying {file_path}: {e}")

        style.configure('Location.Horizontal.TProgressbar', 
                       text=f"Lokasi: {destination_folder}")
        self.progress_bar["value"] = 0
        tk.messagebox.showinfo("Selesai", "Proses penyalinan selesai.")
        self.main_window.update_status(f"File berhasil disalin ke {destination_folder}")

    def copy_file_with_progress(self, src, dst_folder):
        dst_path = os.path.join(dst_folder, os.path.basename(src))
        resolved_path = self.handle_file_conflict(dst_path)
        
        if resolved_path is None:  # User chose to skip
            return
            
        total_size = os.path.getsize(src)
        copied_size = 0

        with open(src, 'rb') as fsrc, open(resolved_path, 'wb') as fdst:
            while True:
                buf = fsrc.read(1024 * 1024)  # Read in chunks of 1MB
                if not buf:
                    break
                fdst.write(buf)
                copied_size += len(buf)
                progress = (copied_size / total_size) * 100
                self.progress_bar["value"] = progress
                style = ttk.Style()
                style.configure('Location.Horizontal.TProgressbar', 
                              text=f"Menyalin: {os.path.basename(src)} ({int(progress)}%)")
                self.update_idletasks()

    def reset_files(self):
        # Reset the "all" flags
        self.replace_all = False
        self.rename_all = False
        self.skip_all = False

        # Clear file listbox
        self.file_listbox.delete(0, tk.END)
        
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
        self.open_folder_button["state"] = "disabled"

    def update_button_states(self, event=None):
        has_files = len(self.file_listbox.get(0, tk.END)) > 0
        has_destination = bool(self.selected_destination.get())
        
        state = "normal" if (has_files and has_destination) else "disabled"
        self.move_button["state"] = state
        self.copy_button["state"] = state

    def open_selected_folder(self):
        folder_path = self.selected_destination.get()
        if folder_path and os.path.exists(folder_path):
            os.startfile(folder_path)
