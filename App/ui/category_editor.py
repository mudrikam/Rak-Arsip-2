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
import threading
import time
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

        # Buat LabelFrame kiri untuk "Kategori :"
        self.left_frame = ttk.LabelFrame(self, text="Kategori :", padding=10)
        self.left_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, pady=(10, 0), padx=(0, 5))

        # Tambahkan Entry untuk kategori baru
        self.category_entry = ttk.Entry(self.left_frame, font=("Arial", 12))
        self.category_entry.pack(fill=tk.X, pady=(10, 0))
        self.category_entry.bind("<KeyRelease>", self.sanitize_category_entry)
        self.category_entry.bind("<FocusIn>", self.disable_delete_button)
        self.category_entry.bind("<FocusOut>", self.enable_delete_button)
        self.category_entry.bind("<Return>", lambda event: self.add_category())

        # Tambahkan Tombol untuk menambah kategori baru
        self.add_category_button = ttk.Button(self.left_frame, text="+", command=self.add_category, padding=5)
        self.add_category_button.pack(fill=tk.X, pady=(10, 10))

        # Buat Treeview untuk kategori tanpa heading
        self.category_tree = ttk.Treeview(self.left_frame, columns=("Category"), show="")
        self.category_tree.pack(side=tk.TOP, fill=tk.BOTH, expand=True)
        self.category_tree.bind("<<TreeviewSelect>>", self.on_category_select)

        # Tambahkan Tombol Hapus
        self.delete_category_button = ttk.Button(self.left_frame, text="Hapus", command=self.delete_category, state=tk.DISABLED, padding=5)
        self.delete_category_button.pack(fill=tk.X, pady=(10, 0))

        # Muat kategori dari Category.txt
        self.load_categories()

        # Buat LabelFrame kanan untuk "Sub Kategori :"
        self.right_frame = ttk.LabelFrame(self, text="Sub Kategori :", padding=10)
        self.right_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, pady=(10, 0),padx=(5, 0))

        # Buat widget Text untuk sub-kategori
        self.subcategory_text = scrolledtext.ScrolledText(self.right_frame, wrap=tk.WORD)
        self.subcategory_text.pack(side=tk.TOP, fill=tk.BOTH, expand=True)
        self.subcategory_text.bind("<KeyPress>", self.replace_special_characters)
        self.subcategory_text.bind("<KeyRelease>", self.save_subcategory_text)

        # Variabel untuk menyimpan kategori yang dipilih saat ini
        self.selected_category = None

        # Mulai memonitor Category.txt untuk perubahan
        self.check_for_updates()

    def load_categories(self):
        self.category_tree.delete(*self.category_tree.get_children())  # Hapus kategori yang ada
        if os.path.exists(self.category_file):
            with open(self.category_file, "r") as file:
                categories = file.readlines()
            for category in categories:
                self.category_tree.insert("", tk.END, values=(category.strip(),))

    def on_category_select(self, event):
        selected_item = self.category_tree.selection()
        if selected_item:
            self.selected_category = self.category_tree.item(selected_item[0], "values")[0]
            self.load_subcategories(self.selected_category)
            self.delete_category_button.config(state=tk.NORMAL)
        else:
            self.selected_category = None
            self.delete_category_button.config(state=tk.DISABLED)

    def load_subcategories(self, category):
        subcategory_file = os.path.join(self.BASE_DIR, f"{category}.txt")
        self.subcategory_text.delete(1.0, tk.END)
        if os.path.exists(subcategory_file):
            with open(subcategory_file, "r") as file:
                subcategories = file.read()
            self.subcategory_text.insert(tk.END, subcategories)

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
        if self.selected_category:
            subcategory_file = os.path.join(self.BASE_DIR, f"{self.selected_category}.txt")
            with open(subcategory_file, "w") as file:
                file.write(self.subcategory_text.get(1.0, tk.END))

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
            subcategory_file = os.path.join(self.BASE_DIR, f"{new_category}.txt")
            if not os.path.exists(subcategory_file):
                with open(subcategory_file, "w") as file:
                    pass
            
            # Muat ulang kategori
            self.load_categories()
            self.category_entry.delete(0, tk.END)
        else:
            messagebox.showwarning("Peringatan", "Nama kategori tidak boleh kosong!")


    def delete_category(self):
        if self.selected_category:
            category_file = os.path.join(self.BASE_DIR, "Category.txt")
            subcategory_file = os.path.join(self.BASE_DIR, f"{self.selected_category}.txt")
            
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

    def check_for_updates(self):
        try:
            current_modified_time = os.path.getmtime(self.category_file)
            if current_modified_time != self.last_modified_time:
                self.last_modified_time = current_modified_time
                self.load_categories()
        except FileNotFoundError:
            messagebox.showwarning("Gawat...!", "Waduh databasenya hilang! (o_O)")
            messagebox.showinfo("Hehehe...", "Tenang jangan panik, aku buatin dulu nih")
            self.create_csv_if_not_exists()
            messagebox.showinfo("Tolong diingat...!", "Database mungkin berisi file penting seperti daftar kategori, sub kategori, daftar pustaka dan template. \nBackup Database secara berkala demi keamanan!")
        except Exception as e:
            messagebox.showerror("Error", f"Terjadi kesalahan: {e}")

        # Jadwalkan pemeriksaan berikutnya
        self.after(1000, self.check_for_updates)

    def create_csv_if_not_exists(self):
        if not os.path.exists(self.category_file):
            with open(self.category_file, "w") as file:
                pass