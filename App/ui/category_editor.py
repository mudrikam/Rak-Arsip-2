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
from tkinter import scrolledtext
from tkinter import messagebox

class CategoryEditor(ttk.LabelFrame): 
    def __init__(self, parent, BASE_DIR, main_window):
        super().__init__(parent, text="Kelola Kategori dan Sub Kategori :", padding=10)
        self.grid(row=0, column=0, padx=10, pady=10, sticky="nsew")
        
        # Pastikan folder 'Database' ada di dalam BASE_DIR
        self.BASE_DIR = os.path.join(BASE_DIR, "Database")
        self.SUB_CATEGORY_DIR = os.path.join(self.BASE_DIR, "Sub_Category")
        os.makedirs(self.SUB_CATEGORY_DIR, exist_ok=True)
        self.main_window = main_window  # Simpan referensi ke MainWindow

        os.makedirs(self.BASE_DIR, exist_ok=True)

        # Buat Category.txt jika belum ada
        self.category_file = os.path.join(self.BASE_DIR, "Category.txt")
        if not os.path.exists(self.category_file):
            with open(self.category_file, "w") as file:
                pass

        # Inisialisasi waktu modifikasi terakhir
        try:
            self.last_modified_time = os.path.getmtime(self.category_file)
        except FileNotFoundError:
            self.last_modified_time = None

        # Tambahkan variabel untuk menyimpan konten terakhir
        self.last_content = self.get_category_content()

        # Buat LabelFrame kiri untuk "Kategori :" dengan lebar tetap
        self.left_frame = ttk.LabelFrame(self, text="Kategori :", padding=10)
        self.left_frame.pack(side=tk.LEFT, fill=tk.Y, expand=False, pady=0, padx=(0, 10))
        self.left_frame.configure(width=200)  # Set lebar tetap

        # Tambahkan Frame untuk Entry dan Tombol tambah kategori
        self.entry_button_frame = ttk.Frame(self.left_frame)
        self.entry_button_frame.pack(fill=tk.X, pady=(0, 10))

        # Tambahkan Entry untuk kategori baru
        self.category_entry = ttk.Entry(self.entry_button_frame, font=("Arial", 12))
        self.category_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.category_entry.bind("<KeyRelease>", self.sanitize_category_entry)
        self.category_entry.bind("<FocusIn>", self.disable_delete_button)
        self.category_entry.bind("<FocusOut>", self.enable_delete_button)
        self.category_entry.bind("<Return>", lambda e: (self.handle_category_entry_return(), self.focus_text_without_newline()))

        # Load and resize icons
        plus_icon_path = os.path.join(BASE_DIR, "Img", "icon", "ui", "plus.png")
        delete_icon_path = os.path.join(BASE_DIR, "Img", "icon", "ui", "delete.png")
        
        # Create PhotoImage objects and resize them to 16x16
        if os.path.exists(plus_icon_path):
            plus_img = tk.PhotoImage(file=plus_icon_path)
            self.plus_icon = plus_img.subsample(plus_img.width()//16, plus_img.height()//16)
        else:
            self.plus_icon = None
            
        if os.path.exists(delete_icon_path):
            delete_img = tk.PhotoImage(file=delete_icon_path)
            self.delete_icon = delete_img.subsample(delete_img.width()//16, delete_img.height()//16)
        else:
            self.delete_icon = None

        # Tambahkan Tombol untuk menambah kategori baru
        self.add_category_button = ttk.Button(
            self.entry_button_frame,
            image=self.plus_icon if self.plus_icon is not None else "",
            command=self.add_category,
            width=1,  # Set fixed width
        )
        self.add_category_button.pack(side=tk.LEFT, padx=(5, 0))

        # Buat Frame untuk Treeview dan scrollbar
        self.treeview_frame = ttk.Frame(self.left_frame)
        self.treeview_frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

        # Buat Treeview untuk kategori tanpa heading
        self.category_tree = ttk.Treeview(self.treeview_frame, columns=("Category"), show="")
        self.category_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        # Add a scrollbar to the category Treeview
        self.category_scrollbar = ttk.Scrollbar(self.treeview_frame, orient="vertical", command=self.category_tree.yview)
        self.category_tree.configure(yscroll=self.category_scrollbar.set)
        self.category_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.category_tree.bind("<<TreeviewSelect>>", self.on_category_select)

        # Buat Frame untuk Tombol Hapus
        self.delete_button_frame = ttk.Frame(self.left_frame)
        self.delete_button_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=(10, 0))

        # Tambahkan Tombol Hapus di bawah Treeview
        self.delete_category_button = ttk.Button(
            self.delete_button_frame, 
            text="Hapus",
            image=self.delete_icon if self.delete_icon is not None else "",
            compound='left',  # Show icon to the left of text
            command=self.delete_category, 
            state=tk.DISABLED, 
            padding=5
        )
        self.delete_category_button.pack(fill=tk.X)

        # Muat kategori dari Category.txt
        self.load_categories()

        # Buat LabelFrame kanan untuk "Sub Kategori :"
        self.right_frame = ttk.LabelFrame(self, text="Sub Kategori :", padding=10)
        self.right_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, pady=0)  # Ubah RIGHT menjadi LEFT

        # Add rename frame and controls
        self.rename_frame = ttk.Frame(self.right_frame)
        self.rename_frame.pack(fill=tk.X, pady=(0, 10))
        self.rename_frame.grid_columnconfigure(0, weight=1)

        self.rename_entry = ttk.Entry(self.rename_frame, font=("Arial", 12))
        self.rename_entry.grid(row=0, column=0, sticky="ew", padx=(0, 5))
        self.rename_entry.bind("<Return>", lambda e: (self.handle_rename_entry_return(), self.focus_text_without_newline()))

        # Load rename icon
        self.rename_icon = tk.PhotoImage(file=os.path.join(BASE_DIR, "Img", "icon", "ui", "rename.png"))
        self.rename_icon = self.rename_icon.subsample(self.rename_icon.width() // 16, self.rename_icon.height() // 16)

        ttk.Button(self.rename_frame, 
                  text="Ganti",
                  command=self.rename_current_category,
                  image=self.rename_icon,
                  compound=tk.LEFT,
                  padding=3,
                  width=8).grid(row=0, column=1)

        # Buat widget Text untuk sub-kategori dengan binding yang dimodifikasi
        self.subcategory_text = scrolledtext.ScrolledText(self.right_frame, wrap=tk.WORD)
        self.subcategory_text.pack(side=tk.TOP, fill=tk.BOTH, expand=True)
        
        # Sederhanakan binding
        self.subcategory_text.bind("<KeyPress>", self.replace_special_characters)
        self.subcategory_text.bind("<KeyRelease>", self.save_subcategory_text)
        self.subcategory_text.bind("<FocusIn>", self.handle_text_focus_in)

        # Variabel untuk menyimpan kategori yang dipilih saat ini
        self.selected_category = None

        # Mulai memonitor Category.txt untuk perubahan
        self.check_for_updates()

    def load_categories(self, preserve_selection=None):
        """Load categories and optionally preserve selection"""
        # Simpan item yang sedang dipilih jika tidak ada parameter preserve_selection
        if preserve_selection is None and self.category_tree.selection():
            preserve_selection = self.category_tree.item(self.category_tree.selection()[0])['values'][0]

        self.category_tree.delete(*self.category_tree.get_children())  # Hapus kategori yang ada
        if os.path.exists(self.category_file):
            with open(self.category_file, "r") as file:
                categories = file.readlines()
            categories = sorted([category.strip() for category in categories])  # Sort categories alphabetically
            for category in categories:
                item = self.category_tree.insert("", tk.END, values=(category,))
                # Pilih kembali item yang sebelumnya dipilih
                if preserve_selection and category == preserve_selection:
                    self.category_tree.selection_set(item)
                    self.category_tree.see(item)

    def on_category_select(self, event):
        selected_item = self.category_tree.selection()
        if selected_item:
            self.selected_category = self.category_tree.item(selected_item[0], "values")[0]
            self.load_subcategories(self.selected_category)
            self.delete_category_button.config(state=tk.NORMAL)
            # Update rename entry with current category name
            self.rename_entry.delete(0, tk.END)
            self.rename_entry.insert(0, self.selected_category)
        else:
            self.selected_category = None
            self.delete_category_button.config(state=tk.DISABLED)
            self.rename_entry.delete(0, tk.END)

    def load_subcategories(self, category):
        """Load subcategories dengan penanganan error yang lebih baik"""
        subcategory_file = os.path.join(self.SUB_CATEGORY_DIR, f"{category}.txt")
        self.subcategory_text.delete(1.0, tk.END)
        
        try:
            if not os.path.exists(subcategory_file):
                with open(subcategory_file, "w") as file:
                    pass
                self.main_window.update_status(f"File sub kategori untuk '{category}' telah dibuat!")
            
            with open(subcategory_file, "r") as file:
                content = file.read().rstrip('\n')
                if content:
                    self.subcategory_text.insert(tk.END, content)
            
        except Exception as e:
            self.main_window.update_status(f"Error loading subcategory: {str(e)}")
        
        return self.subcategory_text.get(1.0, tk.END).rstrip('\n')

    def sanitize_category_entry(self, event):
        sanitized_text = self.sanitize_category_text(self.category_entry.get())
        self.category_entry.delete(0, tk.END)
        self.category_entry.insert(0, sanitized_text)

    def sanitize_category_text(self, text):
        # Hanya izinkan karakter alfanumerik, garis bawah, dan ganti spasi dengan garis bawah
        sanitized = ''.join(c if c.isalnum() or c == '_' else '_' if c.isspace() else '' for c in text)
        return sanitized

    def replace_special_characters(self, event):
        """Ganti spasi dengan '_' dan tab dengan '\\'."""
        allowed_chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_\\"

        if event.char == " ":  # Jika karakter adalah spasi
            self.subcategory_text.insert(tk.INSERT, "_")
            return "break"
        elif event.keysym == "Tab":  # Jika tombol adalah Tab
            self.subcategory_text.insert(tk.INSERT, "\\")
            return "break"
        elif event.keysym in ("Return", "BackSpace"):  # Izinkan Enter dan Backspace
            return
        elif event.char and event.char not in allowed_chars:  # Blokir karakter yang tidak diizinkan
            return "break"

    def save_subcategory_text(self, event):
        """Simpan teks dengan penanganan error yang lebih baik"""
        if not self.selected_category:
            return
            
        try:
            subcategory_file = os.path.join(self.SUB_CATEGORY_DIR, f"{self.selected_category}.txt")
            os.makedirs(self.SUB_CATEGORY_DIR, exist_ok=True)
            
            with open(subcategory_file, "w") as file:
                file.write(self.subcategory_text.get(1.0, tk.END))
        except Exception as e:
            self.main_window.update_status(f"Error saving subcategory: {str(e)}")

    def add_category(self):
        new_category = self.category_entry.get().strip()
        if new_category:
            category_file = os.path.join(self.BASE_DIR, "Category.txt")
            
            # Periksa apakah kategori sudah ada di file
            if os.path.exists(category_file):
                with open(category_file, "r") as file:
                    existing_categories = [line.strip() for line in file if line.strip()]
                    if new_category in existing_categories:
                        messagebox.showwarning("Peringatan", "Kategori sudah ada!")
                        self.main_window.update_status(f"Masukkan kategori yang lain karena '{new_category}' sudah ada!")
                        return
            
            # Tambahkan kategori ke Category.txt
            with open(category_file, "a") as file:
                file.write(new_category + "\n")
                self.main_window.update_status(f"Kategori '{new_category}' telah ditambahkan!")
            
            # Buat file subkategori baru jika belum ada
            subcategory_file = os.path.join(self.SUB_CATEGORY_DIR, f"{new_category}.txt")
            if not os.path.exists(subcategory_file):
                with open(subcategory_file, "w") as file:
                    pass
            
            # Muat ulang kategori
            self.load_categories()
            self.category_entry.delete(0, tk.END)
            
            # Pilih kategori baru di treeview
            for item in self.category_tree.get_children():
                if self.category_tree.item(item)['values'][0] == new_category:
                    self.category_tree.selection_set(item)
                    self.category_tree.see(item)
                    self.selected_category = new_category
                    # Load content terlebih dahulu
                    self.load_subcategories(new_category)
                    # Kemudian fokus setelah konten dimuat
                    self.focus_text_without_newline()
                    break
            
            # Fokus ke area teks sub-kategori tanpa menambah newline
            if new_category:
                # ...existing code...
                # Modifikasi bagian fokus
                self.focus_text_without_newline()
                # Hapus newline yang mungkin ditambahkan saat focus_set
                content = self.subcategory_text.get("1.0", tk.END)
                if content == '\n':  # Jika hanya berisi newline
                    self.subcategory_text.delete("1.0", tk.END)
        else:
            messagebox.showwarning("Peringatan", "Nama kategori tidak boleh kosong!")

    def delete_category(self):
        if self.selected_category:
            # Tampilkan dialog konfirmasi
            confirm = messagebox.askyesno("Konfirmasi Hapus", f"Apakah yakin ingin menghapus kategori '{self.selected_category}'?")
            if not confirm:
                return

            category_file = os.path.join(self.BASE_DIR, "Category.txt")
            subcategory_file = os.path.join(self.SUB_CATEGORY_DIR, f"{self.selected_category}.txt")
            
            # Hapus kategori dari Category.txt
            with open(category_file, "r") as file:
                categories = file.readlines()
            with open(category_file, "w") as file:
                for category in categories:
                    if category.strip() != self.selected_category:
                        file.write(category)
            
            # Hapus file subkategori
            if os.path.exists(subcategory_file):
                os.remove(subcategory_file)
                deleted_category=self.selected_category
                self.main_window.update_status(f"Kategori '{deleted_category}' telah dihapus!")
            
            # Muat ulang kategori
            self.load_categories()
            self.subcategory_text.delete(1.0, tk.END)
            self.selected_category = None
            self.delete_category_button.config(state=tk.DISABLED)

    def disable_delete_button(self, event):
        self.delete_category_button.config(state=tk.DISABLED)

    def enable_delete_button(self, event):
        if self.category_tree.selection():
            self.delete_category_button.config(state=tk.NORMAL)
        else:
            self.delete_category_button.config(state=tk.DISABLED)

    def rename_current_category(self):
        if not self.selected_category:
            return

        new_name = self.rename_entry.get().strip()
        if not new_name or new_name == self.selected_category:
            return

        # Sanitize the new name
        new_name = self.sanitize_category_text(new_name)

        # Check if new name already exists 
        category_file = os.path.join(self.BASE_DIR, "Category.txt")
        with open(category_file, "r") as file:
            categories = [line.strip() for line in file]
            if new_name in categories:
                messagebox.showwarning("Peringatan", f"Kategori '{new_name}' sudah ada!")
                return

        # Store current subcategory text content and selection
        current_content = self.subcategory_text.get("1.0", tk.END)
        
        # Rename category in Category.txt
        with open(category_file, "r") as file:
            categories = file.readlines()
        with open(category_file, "w") as file:
            for category in categories:
                if category.strip() == self.selected_category:
                    file.write(new_name + "\n")
                else:
                    file.write(category)

        # Rename subcategory file
        old_file = os.path.join(self.SUB_CATEGORY_DIR, f"{self.selected_category}.txt")
        new_file = os.path.join(self.SUB_CATEGORY_DIR, f"{new_name}.txt")
        if os.path.exists(old_file):
            os.rename(old_file, new_file)

        # Update UI
        self.main_window.update_status(f"Kategori '{self.selected_category}' telah diubah menjadi '{new_name}'")
        self.selected_category = new_name
        self.load_categories()
        
        # Pilih kategori yang baru diganti nama
        for item in self.category_tree.get_children():
            if self.category_tree.item(item)['values'][0] == new_name:
                self.category_tree.selection_set(item)
                self.category_tree.see(item)
                break

        # Restore content dulu
        self.subcategory_text.delete("1.0", tk.END)
        self.subcategory_text.insert("1.0", current_content.rstrip('\n'))
        
        # Kemudian set fokus
        self.focus_text_without_newline()
        
        # Select text jika ada konten
        if current_content.strip():
            self.after(100, lambda: (
                self.subcategory_text.tag_add(tk.SEL, "1.0", "end-1c"),
                self.subcategory_text.mark_set(tk.INSERT, "1.0"),
                self.subcategory_text.see("1.0")
            ))

    def get_category_content(self):
        """Get current content of category file"""
        try:
            with open(self.category_file, "r") as file:
                return file.read()
        except FileNotFoundError:
            return ""
        except Exception:
            return ""

    def check_for_updates(self):
        """Optimisasi pengecekan update"""
        try:
            current_content = self.get_category_content()
            if current_content != self.last_content:
                self.last_content = current_content
                currently_selected = None
                if self.category_tree.selection():
                    currently_selected = self.category_tree.item(self.category_tree.selection()[0])['values'][0]
                self.load_categories(preserve_selection=currently_selected)
        except Exception as e:
            if isinstance(e, FileNotFoundError):
                with open(self.category_file, "w") as file:
                    pass
                self.main_window.update_status("File Category.txt tidak ditemukan, membuat file baru!")
                self.last_content = ""
            else:
                messagebox.showerror("Error", f"Terjadi kesalahan: {e}")
        finally:
            self.after(1000, self.check_for_updates)

    def handle_category_entry_return(self):
        """Handle Enter key press in category entry"""
        self.add_category()
        return 'break'
        
    def handle_rename_entry_return(self):
        """Handle Enter key press in rename entry"""
        self.rename_current_category()
        return 'break'

    def handle_text_focus_in(self, event):
        """Handler yang lebih efisien untuk focus in"""
        content = self.subcategory_text.get("1.0", tk.END)
        if content == '\n':
            self.subcategory_text.delete("1.0", tk.END)
        return 'break'

    def focus_text_without_newline(self):
        """Fokus ke text widget dengan cara yang lebih efisien"""
        def safe_focus():
            self.subcategory_text.focus_set()
            content = self.subcategory_text.get("1.0", tk.END)
            if content == '\n':
                self.subcategory_text.delete(1.0, tk.END)
        self.after(10, safe_focus)
        return 'break'