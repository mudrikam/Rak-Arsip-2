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
import sys
import tkinter as tk
from tkinter import ttk
from tkinter import messagebox
from tkinter import scrolledtext
from App.ui.core_scan import forbidden_words

class TemplateCreator(ttk.LabelFrame):
    def __init__(self, parent, BASE_DIR, main_window):
        """
        Inisialisasi kelas TemplateCreator untuk mengelola tampilan file, pengeditan konten, dan pembuatan folder.
        """
        super().__init__(parent, text="Buat template untuk sub folder :", padding=10)
        self.grid(row=0, column=0, padx=10, pady=10, sticky="nsew")
        self.main_window = main_window
        
        # Setup forbidden words and warning system
        self.forbidden_words = forbidden_words if forbidden_words else []
        self.current_warning_level = 0
        self.last_bad_word = None
        self.warning_messages = [
            ("Aduh....!", "Ada kata '{}' di template, kamu yakin itu gak papa?"),
            ("Maaf kalau salah...", "Sebenarnya aku harap kita pakai aplikasi ini secara aman sih..."),
            ("Aku gak yakin nih...","Sepertinya kata '{}' kurang aman kalau mau pakai aplikasi ini"),
            ("Hem...","Sebenernya gapapa sih kalau kamu maksa, tapi kalau bisa tolong pakai kata yang aman saja ya"),
            ("Mending ganti","Aku udah ingetin berkali-kali loh, seriusan aku nggak suka kalau aplikasi ini dipakai untuk hal jelek"),
            ("Seriusan?","Kayanya kamu emang tetep pengen pakai kata '{}' ya?"),
            ("Pliss....","Plis banget pakai kata lain yang lebih aman ya"),
            ("Aku kasih kesempatan","Oke deh untuk kali ini gapapa pakai '{}', tapi ini terakhir ya"),
            ("Maaf nih...","Maaf banget, tapi aku gak bisa toleransi sama kata '{}', kalau belum diubah juga aku pamit undur diri ya"),
            ("Yasudah...","Makasih atas waktunya saya pamit undur diri")
        ]

        # Setup paths
        self.BASE_DIR = os.path.join(BASE_DIR, "Database", "Template")
        os.makedirs(self.BASE_DIR, exist_ok=True)

        self.file_mapping = {}
        self.current_file = None
        self.rename_entry = None

        # Load icons
        self.add_icon = tk.PhotoImage(file=os.path.join(BASE_DIR, "Img", "icon", "ui", "template.png"))
        self.add_icon = self.add_icon.subsample(self.add_icon.width() // 16, self.add_icon.height() // 16)
        
        self.delete_icon = tk.PhotoImage(file=os.path.join(BASE_DIR, "Img", "icon", "ui", "delete.png"))
        self.delete_icon = self.delete_icon.subsample(self.delete_icon.width() // 16, self.delete_icon.height() // 16)
        
        self.rename_icon = tk.PhotoImage(file=os.path.join(BASE_DIR, "Img", "icon", "ui", "rename.png"))
        self.rename_icon = self.rename_icon.subsample(self.rename_icon.width() // 16, self.rename_icon.height() // 16)

        # Create left frame for template list
        self.left_frame = ttk.LabelFrame(self, text="Template :", padding=10)
        self.left_frame.pack(side=tk.LEFT, fill=tk.Y, expand=False, pady=0, padx=(0, 5))
        self.left_frame.configure(width=200)

        # Add template entry and button at top
        self.entry_button_frame = ttk.Frame(self.left_frame)
        self.entry_button_frame.pack(fill=tk.X, pady=(0, 10))  # Changed from 10 to 5

        self.template_entry = ttk.Entry(self.entry_button_frame, font=("Arial", 12))
        self.template_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, pady=(0, 0))  # Removed bottom padding
        self.template_entry.bind("<Return>", lambda e: (self.handle_template_entry_return(), self.focus_text_without_newline()))

        self.add_template_button = ttk.Button(
            self.entry_button_frame,
            image=self.add_icon,
            command=self.save_as_template_and_focus,
            width=1
        )
        self.add_template_button.pack(side=tk.LEFT, padx=(5, 0), pady=(0, 0))  # Removed bottom padding

        # Create treeview frame with minimum height
        self.treeview_frame = ttk.Frame(self.left_frame)
        self.treeview_frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True, pady=(0,5))
        self.treeview_frame.pack_propagate(False)  # Prevent frame from shrinking to fit content
        
        # Set minimum height for frame
        self.treeview_frame.configure(height=100)  # Minimum height of 100 pixels
        
        # Create treeview for templates
        self.template_tree = ttk.Treeview(self.treeview_frame, columns=("Template"), show="")
        self.template_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        # Add scrollbar
        self.tree_scrollbar = ttk.Scrollbar(self.treeview_frame, orient="vertical", command=self.template_tree.yview)
        self.template_tree.configure(yscroll=self.tree_scrollbar.set)
        self.tree_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.template_tree.bind("<<TreeviewSelect>>", self.on_template_select)

        # Add delete button below treeview
        self.delete_button = ttk.Button(self.left_frame, text="Hapus",
                                      command=self.delete_current_file,
                                      image=self.delete_icon, compound=tk.LEFT,
                                      padding=5)
        self.delete_button.pack(fill=tk.X, pady=(10,0))
        self.delete_button.config(state=tk.DISABLED)  # Disable button by default

        # Right side content
        self.right_frame = ttk.Frame(self)
        self.right_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, pady=0, padx=(5,0))

        # Template editor frame with rename controls at top
        self.editor_frame = ttk.LabelFrame(self.right_frame, text="Edit Template:", padding=10)
        self.editor_frame.pack(fill=tk.BOTH, expand=True, padx=0)

        # Rename controls in horizontal layout at top of editor frame
        self.rename_frame = ttk.Frame(self.editor_frame)
        self.rename_frame.pack(fill=tk.X, pady=(0,10))
        self.rename_frame.grid_columnconfigure(0, weight=1)  # Make entry expand

        # Entry fills most of the space with Return binding
        self.rename_entry = ttk.Entry(self.rename_frame, font=("Arial", 12))
        self.rename_entry.grid(row=0, column=0, sticky="ew", padx=(0,5))
        self.rename_entry.bind("<Return>", lambda e: (self.handle_rename_entry_return(), self.focus_text_without_newline()))  # Add Return binding

        # Small rename button on the right
        ttk.Button(self.rename_frame, text="Ganti",
                  command=self.rename_current_file,
                  image=self.rename_icon,
                  compound=tk.LEFT,
                  padding=3,
                  width=8).grid(row=0, column=1)

        # Buat frame untuk text area dan scrollbar
        self.text_frame = ttk.Frame(self.editor_frame)
        self.text_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 0))

        # Gunakan ScrolledText seperti di CategoryEditor
        self.text_area = scrolledtext.ScrolledText(
            self.text_frame, 
            wrap=tk.WORD,
            relief=tk.SUNKEN,
            borderwidth=1
        )
        self.text_area.pack(fill=tk.BOTH, expand=True)

        # Hapus konfigurasi scrollbar manual karena sudah termasuk dalam ScrolledText
        
        # Bind events
        self.text_area.bind("<KeyPress>", self.replace_special_characters)
        self.text_area.bind("<KeyRelease>", self.save_file_content)
        self.text_area.bind("<FocusIn>", self.handle_text_focus_in)

        # Add double-click binding to treeview
        self.template_tree.bind("<Double-1>", self.handle_template_select)
        
        # Load initial templates
        self.load_files()
        
        # Start monitoring for changes
        self.check_for_updates()

    def on_template_select(self, event):
        """Handle template selection"""
        selected_items = self.template_tree.selection()
        if selected_items:
            template_name = self.template_tree.item(selected_items[0])['values'][0]
            self.display_file_content(display_nama=template_name)
            self.rename_entry.delete(0, tk.END)
            self.rename_entry.insert(0, template_name)
            # Hapus fokus otomatis ke rename_entry
            self.delete_button.config(state=tk.NORMAL)
        else:
            self.delete_button.config(state=tk.DISABLED)

    def load_files(self):
        """Load template files into treeview"""
        self.template_tree.delete(*self.template_tree.get_children())
        
        try:
            current_files = [
                f for f in os.listdir(self.BASE_DIR)
                if os.path.isfile(os.path.join(self.BASE_DIR, f)) and f.endswith(".txt")
            ]
            
            # Sort files alphabetically
            current_files.sort()
            
            # Create file mapping and populate treeview
            for file in current_files:
                display_name = os.path.splitext(file)[0]
                self.file_mapping[display_name] = file
                self.template_tree.insert("", tk.END, values=(display_name,))
            
            # Ensure delete button is disabled when no files are loaded
            if not current_files:
                self.delete_button.config(state=tk.DISABLED)
                
        except Exception as e:
            messagebox.showerror("Error", f"Error loading templates: {str(e)}")
            self.delete_button.config(state=tk.DISABLED)

    def check_for_updates(self):
        """Optimisasi pengecekan update template"""
        try:
            current_files = [f for f in os.listdir(self.BASE_DIR)
                           if os.path.isfile(os.path.join(self.BASE_DIR, f)) 
                           and f.endswith(".txt")]

            if not hasattr(self, 'previous_files') or set(current_files) != set(self.previous_files):
                self.previous_files = current_files
                currently_selected = None
                if self.template_tree.selection():
                    currently_selected = self.template_tree.item(
                        self.template_tree.selection()[0])['values'][0]
                self.load_files()
                
                # Restore selection
                if currently_selected:
                    for item in self.template_tree.get_children():
                        if self.template_tree.item(item)['values'][0] == currently_selected:
                            self.template_tree.selection_set(item)
                            break
        except Exception as e:
            if isinstance(e, FileNotFoundError):
                os.makedirs(self.BASE_DIR, exist_ok=True)
                self.previous_files = []
            else:
                self.main_window.update_status(f"Error checking templates: {str(e)}")
        finally:
            self.after(1000, self.check_for_updates)

    def create_template_file(self, file_name):
        """Buat file template kosong di BASE_DIR."""
        template_path = os.path.join(self.BASE_DIR, file_name)
        if not os.path.exists(template_path):
            with open(template_path, "w") as file:
                file.write("")  # Buat file kosong

    def display_file_content(self, display_nama=None):
        """Tampilkan konten file dengan penanganan error yang lebih baik"""
        if display_nama is None:
            return
            
        try:
            full_name = self.file_mapping.get(display_nama)
            if not full_name:
                return

            file_path = os.path.join(self.BASE_DIR, full_name)
            if os.path.exists(file_path):
                with open(file_path, "r") as file:
                    content = file.read().rstrip('\n')
                self.text_area.delete("1.0", tk.END)
                if content:
                    self.text_area.insert(tk.END, content)
                self.current_file = file_path

        except Exception as e:
            self.main_window.update_status(f"Error loading template: {str(e)}")

    def save_file_content(self, event):
        """Simpan konten dengan penanganan error yang lebih baik"""
        if not self.current_file:
            return
            
        try:
            with open(self.current_file, "w") as file:
                file.write(self.text_area.get("1.0", tk.END).rstrip('\n'))
        except Exception as e:
            self.main_window.update_status(f"Error saving template: {str(e)}")

    def save_as_template(self):
        """Simpan konten area teks sebagai file template baru."""
        template_name = self.template_entry.get().strip()
        if not template_name:
            template_name = "template"

        extension = ".txt"
        index = 0
        base_name = template_name

        while True:
            if index > 0:
                file_name = f"{base_name}_{index}{extension}"
            else:
                file_name = f"{base_name}{extension}"
                
            file_path = os.path.join(self.BASE_DIR, file_name)

            if not os.path.exists(file_path):
                with open(file_path, "w") as file:
                    file.write(self.text_area.get("1.0", tk.END).strip())
                self.load_files()
                new_template_name = os.path.splitext(file_name)[0]
                
                # Select the new template in treeview
                for item in self.template_tree.get_children():
                    if self.template_tree.item(item)['values'][0] == new_template_name:
                        self.template_tree.selection_set(item)
                        break
                        
                self.template_entry.delete(0, tk.END)
                self.rename_entry.delete(0, tk.END)
                self.rename_entry.insert(0, new_template_name)
                self.display_file_content(display_nama=new_template_name)
                return

            index += 1

    def save_as_template_and_focus(self):
        """Simpan template dan set fokus dengan benar"""
        self.save_as_template()
        # Gunakan timing yang sama untuk fokus
        self.after(10, lambda: self.focus_text_without_newline())

    def handle_text_focus_in(self, event):
        """Handler yang efisien untuk focus in"""
        content = self.text_area.get("1.0", tk.END)
        if content == '\n':
            self.text_area.delete("1.0", tk.END)
        return 'break'

    def focus_text_without_newline(self):
        """Fokus ke text widget dengan cara yang sama seperti CategoryEditor"""
        def safe_focus():
            self.text_area.focus_set()
            content = self.text_area.get("1.0", tk.END)
            if content == '\n':
                self.text_area.delete(1.0, tk.END)
        # Gunakan delay yang sama dengan CategoryEditor
        self.after(10, safe_focus)
        return 'break'

    def handle_template_entry_return(self):
        """Handle Enter key press in template entry"""
        self.save_as_template()
        return 'break'

    def handle_rename_entry_return(self):
        """Handle Enter key press in rename entry"""
        self.rename_current_file()
        return 'break'

    def handle_template_select(self, event):
        """Handle double-click pada template"""
        self.focus_text_without_newline()

    def replace_special_characters(self, event):
        """Ganti spasi dengan '_' dan tab dengan '\\'."""
        allowed_chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_\\"

        if event.char == " ":  # Jika karakter adalah spasi
            self.text_area.insert(tk.INSERT, "_")
            return "break"
        elif event.keysym == "Tab":  # Jika tombol adalah Tab
            self.text_area.insert(tk.INSERT, "\\")
            return "break"
        elif event.keysym in ("Return", "BackSpace"):  # Izinkan Enter dan Backspace
            return
        elif event.char and event.char not in allowed_chars:  # Blokir karakter yang tidak diizinkan
            return "break"
        
    def rename_current_file(self):
        """Rename file dan set fokus dengan benar"""
        new_name = self.rename_entry.get().strip()
        selected_items = self.template_tree.selection()
        if new_name and selected_items:
            old_name = self.template_tree.item(selected_items[0])['values'][0]
            if self.rename_template(old_name, new_name):
                # Clear entry and immediately focus text area
                self.rename_entry.delete(0, tk.END)
                # Pastikan fokus ke text area terjadi setelah konten dimuat
                self.after(10, lambda: self.focus_text_without_newline())

    def rename_template(self, old_name, new_name):
        """Rename a template file."""
        old_path = os.path.join(self.BASE_DIR, old_name + ".txt")
        new_path = os.path.join(self.BASE_DIR, new_name + ".txt")
        if os.path.exists(old_path):
            os.rename(old_path, new_path)
            self.load_files()
            
            # Select the renamed item and load content
            for item in self.template_tree.get_children():
                if self.template_tree.item(item)['values'][0] == new_name:
                    self.template_tree.selection_set(item)
                    self.template_tree.see(item)
                    self.display_file_content(display_nama=new_name)
                    break
        else:
            messagebox.showerror("Error", f"Template {old_name} does not exist")

    def select_all_text(self, event):
        """Select all text in the entry field when it gains focus."""
        event.widget.select_range(0, tk.END)
        return "break"

    def delete_current_file(self):
        """Delete the currently selected file."""
        selected_items = self.template_tree.selection()
        if selected_items:
            selected_file = self.template_tree.item(selected_items[0])['values'][0]
            full_name = self.file_mapping.get(selected_file)
            if full_name:
                file_path = os.path.join(self.BASE_DIR, full_name)
                if os.path.exists(file_path):
                    confirm = messagebox.askyesno("Konfirmasi Hapus", 
                                                f"Apakah yakin ingin menghapus '{selected_file}'?")
                    if confirm:
                        os.remove(file_path)
                        self.load_files()
                        self.text_area.delete("1.0", tk.END)
                        self.rename_entry.delete(0, tk.END)
                        self.main_window.update_status(f"Template '{selected_file}' berhasil dihapus.")
                    else:
                        self.main_window.update_status(f"Penghapusan '{selected_file}' dibatalkan.")
                else:
                    messagebox.showerror("Error", f"Template {selected_file} tidak ditemukan.")
                    self.main_window.update_status(f"Template {selected_file} tidak ditemukan.")