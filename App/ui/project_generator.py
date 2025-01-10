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
from datetime import date
from tkinter import messagebox
import csv
from colorsys import hsv_to_rgb
from tkinter import colorchooser

class ProjectGenerator(ttk.LabelFrame):
    def __init__(self, parent, BASE_DIR, main_window, selected_disk, root_folder, category, sub_category, date_var, project_name):
        """
        Inisialisasi ProjectGenerator.
        """
        super().__init__(parent, text="Ringkasan :")
        self.grid(row=0, column=0, padx=10, pady=10, sticky="nsew")

        self.BASE_DIR = BASE_DIR
        self.main_window = main_window
        self.selected_disk = selected_disk
        self.root_folder = root_folder
        self.category = category
        self.sub_category = sub_category
        self.date_var = date_var
        self.project_name = project_name
        self.selected_template = tk.StringVar
        self.subfolders = tk.StringVar
        self.subfolder = tk.StringVar
        
        # Simpan semua variabel StringVar dalam sebuah list
        self.variables = [selected_disk, root_folder, category, sub_category, date_var, project_name]

        # Lakukan binding untuk setiap variabel
        for var in self.variables:
            var.trace_add("write", self._create_project_path)

        # Add trace to project_name to update project path in real-time
        self.project_name.trace_add("write", self._create_project_path)

        # Label untuk menampilkan project path
        self.project_label = ttk.Label(self, text="", anchor="w", foreground="blue")
        self.project_label.pack(side=tk.TOP, fill=tk.X, padx=10, pady=10)

        # Tambahkan LabelFrame untuk "Sesuaikan"
        self.adjust_frame = ttk.LabelFrame(self, text="Sesuaikan :")
        self.adjust_frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True, padx=10, pady=0)

        # Frame untuk checkbox (kiri)
        self.checkbox_frame = ttk.Frame(self.adjust_frame)
        self.checkbox_frame.pack(side=tk.LEFT, fill=tk.Y, padx=5, pady=5)

        # Frame untuk input dan dropdown (kanan)
        self.input_dropdown_frame = ttk.Frame(self.adjust_frame)
        self.input_dropdown_frame.pack(side=tk.LEFT, fill=tk.Y, padx=5, pady=5)

        # Tambahkan checkbox untuk menyertakan tanggal
        self.include_date = tk.BooleanVar(value=True)  # Variabel untuk checkbox
        self.checkbox = ttk.Checkbutton(
            self.checkbox_frame, text="Sertakan tanggal", variable=self.include_date, command=self._create_project_path
        )
        self.checkbox.pack(side=tk.TOP, anchor="w", padx=10, pady=5)

        # Tambahkan dropdown combobox untuk folder
        self.folder_label = ttk.Label(self.input_dropdown_frame, text="Lokasi Arsip :")
        self.folder_label.pack(side=tk.TOP, anchor="w", padx=10, pady=5)
        
        self.folder_combobox = ttk.Combobox(self.input_dropdown_frame, textvariable=self.root_folder)
        self.folder_combobox.pack(side=tk.TOP, fill=tk.X, padx=10, pady=5)
        self.folder_combobox.bind("<<ComboboxSelected>>", self._create_project_path)
        self.folder_combobox.bind("<Button-1>", self.start_scanning)
        self.folder_combobox.bind("<FocusOut>", self.stop_scanning)

        # Tambahkan checkbox untuk Markdown
        self.include_markdown = tk.BooleanVar(value=True)  # Default is checked
        self.markdown_checkbox = ttk.Checkbutton(
            self.checkbox_frame, text="Sertakan file Markdown", variable=self.include_markdown
        )
        self.markdown_checkbox.pack(side=tk.TOP, anchor="w", padx=10, pady=5)

        # Tambahkan checkbox untuk membuka explorer
        self.open_explorer = tk.BooleanVar(value=True)
        self.explorer_checkbox = ttk.Checkbutton(
            self.checkbox_frame, text="Buka explorer setelah Arsip dibuat", variable=self.open_explorer
        )
        self.explorer_checkbox.pack(side=tk.TOP, anchor="w", padx=10, pady=5)

        # Tambahkan dropdown untuk template
        self.template_label = ttk.Label(self.input_dropdown_frame, text="Template :")
        self.template_label.pack(side=tk.TOP, anchor="w", padx=10, pady=5)
        
        self.template_var = tk.StringVar()
        self.template_combobox = ttk.Combobox(self.input_dropdown_frame, textvariable=self.template_var, state="readonly")
        self.template_combobox.pack(side=tk.TOP, fill=tk.X, padx=10, pady=5)
        self.template_combobox.bind("<<ComboboxSelected>>", self._update_template_var)

        # Tambahkan Entry untuk jumlah pengulangan
        self.repeat_frame = ttk.Frame(self.input_dropdown_frame)
        self.repeat_frame.pack(side=tk.TOP, fill=tk.X, padx=10, pady=5)
        
        self.repeat_label = ttk.Label(self.repeat_frame, text="Ulang :")
        self.repeat_label.pack(side=tk.LEFT, anchor="w")
        
        self.repeat_entry = ttk.Entry(self.repeat_frame, font=("Arial", 12))
        self.repeat_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)

        # Tambahkan tombol "Buat Arsip"
        self.create_project_button = ttk.Button(self, text="Buat Arsip", command=self.create_project)
        self.create_project_button.pack(side=tk.BOTTOM, fill=tk.X, padx=10, pady=10)
        self.create_project_button.config(style="Custom.TButton")

        # Tambahkan style untuk tombol dengan ukuran font 12
        style = ttk.Style()
        style.configure("Custom.TButton", font=("Arial", 12), padding=10)

        # Tampilkan path awal
        self._create_project_path()

        # Bind selected_disk untuk memperbarui folder_combobox
        self.selected_disk.trace_add("write", self._update_folder_combobox)

        # Panggil load_templates untuk mengisi combobox template
        self.load_templates()  # Memanggil metode untuk memuat template

        # Tambahkan label "Tema markdown"
        self.theme_color = "#000000"  # Warna default
        self.theme_label = ttk.Label(self.checkbox_frame, text="Tema markdown", foreground=self.theme_color)
        self.theme_label.pack(side=tk.TOP, anchor="w", padx=10, pady=5)

        # Tambahkan frame untuk color picker dan tombol acak
        self.picker_frame = ttk.Frame(self.checkbox_frame)
        self.picker_frame.pack(side=tk.TOP, anchor="w", padx=10, pady=5)

        # Tambahkan tombol untuk membuka color picker (kotak kecil berwarna)
        self.color_picker_button = tk.Label(self.picker_frame, background=self.theme_color, width=2, height=1, relief="groove")
        self.color_picker_button.pack(side=tk.LEFT, padx=5)
        self.color_picker_button.bind("<Button-1>", self.open_color_picker)

        # Tambahkan tombol untuk mengacak warna
        self.randomize_button = ttk.Button(self.picker_frame, text="Acak", command=self.enable_random_color)
        self.randomize_button.pack(side=tk.LEFT, padx=5)

        # Bind events untuk mengubah warna label tema dan kotak warna
        self.bind("<Motion>", self._change_theme_color, add="+")  # Ubah warna saat mouse bergerak di atas frame
        self.adjust_frame.bind("<Motion>", self._change_theme_color, add="+")  # Ubah warna saat mouse bergerak di atas frame

        self.folders_to_make = tk.StringVar()  # Variabel untuk menyimpan subfolder dari template

        # Panggil metode untuk melacak perubahan pada combobox template
        self.track_template_changes()

        self.hue = 0  # Initialize hue

        self.initial_root_folder = root_folder.get()  # Save initial root folder value

        # Schedule the check for project_name every 1000ms
        self.check_project_name()
        self.check_sync_project_name()

    def _create_project_path(self, *args):
        """
        Perbarui teks project path berdasarkan kategori dan status checkbox.
        """
        selected_disk_value = self.selected_disk.get()  # Ambil nilai dari selected_disk
        root_folder_value = self.root_folder.get()
        category_value = self.category.get()
        sub_category_value = self.sub_category.get()
        project_name_value = self.project_name.get()

        if self.include_date.get():  # Jika checkbox diaktifkan (sertakan tanggal)
            # Format tanggal dengan bulan dalam bahasa Indonesia
            bulan_indonesia = {
                "January": "Januari", "February": "Februari", "March": "Maret", "April": "April",
                "May": "Mei", "June": "Juni", "July": "Juli", "August": "Agustus",
                "September": "September", "October": "Oktober", "November": "November", "December": "Desember"
            }
            today_date = date.today().strftime("%Y\\%B\\%d")
            for eng, ind in bulan_indonesia.items():
                today_date = today_date.replace(eng, ind)
            project_path = f"{selected_disk_value}\\{root_folder_value}\\{category_value}\\{sub_category_value}\\{today_date}\\{project_name_value}"
        else:  # Jika checkbox tidak diaktifkan (jangan sertakan tanggal)
            project_path = f"{selected_disk_value}\\{root_folder_value}\\{category_value}\\{sub_category_value}\\{project_name_value}"

        self.project_label.config(text=project_path)  # Perbarui label dengan path Arsip

    def _update_folder_combobox(self, *args):
        """
        Memperbarui dropdown combobox dengan folder dari disk yang dipilih,
        mengabaikan $RECYCLE.BIN, folder yang diawali titik (.) atau underscore (_).
        """
        selected_disk_value = self.selected_disk.get()
        if selected_disk_value:
            try:
                # Ambil daftar folder dari disk yang dipilih dan filter out $RECYCLE.BIN, '.' dan '_'
                folders = sorted([
                    f for f in os.listdir(selected_disk_value)
                    if os.path.isdir(os.path.join(selected_disk_value, f)) and 
                    f != "$RECYCLE.BIN" and not f.startswith(('.', '_'))
                ])
                current_selection = self.root_folder.get()  # Save current selection
                self.folder_combobox['values'] = folders
                if current_selection in folders:
                    self.folder_combobox.set(current_selection)  # Restore previous selection if it still exists
                else:
                    self.folder_combobox.set("")  # Reset selection if previous selection no longer exists
            except Exception as e:
                print(f"Error updating folder combobox: {e}")
                self.folder_combobox['values'] = []
                self.folder_combobox.set("")  # Tetap kosong jika ada error

    def start_scanning(self, event):
        """
        Start scanning for external changes when the combobox is clicked.
        """
        self._scan_external_changes()

    def stop_scanning(self, event):
        """
        Stop scanning for external changes when the combobox loses focus.
        """
        if hasattr(self, '_scan_job'):
            self.after_cancel(self._scan_job)

    def _scan_external_changes(self):
        """
        Scan for external changes in the selected disk and refresh the folder combobox if new folders are detected.
        """
        selected_disk_value = self.selected_disk.get()
        if selected_disk_value:
            try:
                # Ambil daftar folder dari disk yang dipilih dan filter out $RECYCLE.BIN, '.' dan '_'
                current_folders = set(
                    f for f in os.listdir(selected_disk_value)
                    if os.path.isdir(os.path.join(selected_disk_value, f)) and 
                    f != "$RECYCLE.BIN" and not f.startswith(('.', '_'))
                )
                previous_folders = set(self.folder_combobox['values'])
                if current_folders != previous_folders:
                    sorted_folders = sorted(current_folders)
                    current_selection = self.root_folder.get()  # Save current selection
                    self.folder_combobox['values'] = sorted_folders
                    if current_selection in sorted_folders:
                        self.folder_combobox.set(current_selection)  # Restore previous selection if it still exists
                    else:
                        self.folder_combobox.set(self.initial_root_folder)  # Restore initial root folder if previous selection no longer exists
            except Exception as e:
                print(f"Error scanning external changes: {e}")

        # Jadwalkan pemeriksaan berikutnya setelah 1000 ms
        self._scan_job = self.after(1000, self._scan_external_changes)

    def create_project(self):
        """
        Metode untuk membuat Arsip berdasarkan input yang diberikan.
        """
        # Validasi input
        if not all([self.selected_disk.get(), self.root_folder.get(), self.category.get(), self.sub_category.get(), self.project_name.get()]):
            messagebox.showinfo("Perhatikan.", "Disk, Nama Arsip, Kategori, Sub Kategori dan Lokasi Arsip harus diisi!")
            return

        base_project_path = self.project_label.cget("text")
        open_explorer = self.open_explorer.get()
        selected_template = self.template_var.get()

        # Ambil nilai dari entry jumlah ulangi
        repeat_count = self.repeat_entry.get()
        try:
            repeat_count = int(repeat_count)
        except ValueError:
            repeat_count = 1  # Default ke 1 jika tidak valid

        last_created_folder = None

        # Implementasi pembuatan Arsip
        for i in range(repeat_count):
            project_folder = base_project_path
            if i > 0:
                project_folder = f"{base_project_path}_{i+1}"
            counter = 1
            while os.path.exists(project_folder):
                project_folder = f"{base_project_path}_{i+1}_{counter}"
                counter += 1

            try:
                os.makedirs(project_folder)
                last_created_folder = project_folder
                print(f"Direktori {project_folder} telah dibuat.")
            except Exception as e:
                messagebox.showerror("Error", f"Gagal membuat direktori:\n\nError:\n\n {project_folder}\n\n {e}\n\nPeriksa kembali nama Arsip.")
                self.main_window.update_status("Karakter seperti [<>:\"/\\|?*] tidak didukung saat membuat nama folder")
                return
            
            # Refresh folder_combobox after creating a new folder
            self._update_folder_combobox()

            # Membuat file Markdown jika diperlukan
            if self.include_markdown.get():
                self.generate_markdown_file(project_folder)

            # Menggunakan template yang dipilih dari combobox
            if selected_template:
                subfolders = self.folders_to_make.get().split("\n")
                for subfolder in subfolders:
                    subfolder = subfolder.strip()  # Remove any leading/trailing whitespace
                    if subfolder:  # Ensure subfolder is not empty
                        subfolder_path = os.path.join(project_folder, subfolder)
                        os.makedirs(subfolder_path, exist_ok=True)
                        print(f"Subfolder {subfolder_path} telah dibuat.")

            # Update CSV file
            self.update_csv(project_folder)

        # Simpan project_name ke clipboard
        self.clipboard_clear()
        self.clipboard_append(self.project_name.get())
        self.update()  # Keep the clipboard content

        # Update status bar in main window
        self.main_window.update_status(f"Folder {self.project_name.get()} berhasil dibuat dan ditambahkan ke daftar pustaka")

        # Membuka explorer jika diperlukan
        if open_explorer and last_created_folder:
            import subprocess
            subprocess.Popen(f'explorer "{last_created_folder}"')
            print(f"Explorer dibuka di {last_created_folder}.")

    def update_csv(self, project_folder):
        """
        Perbarui file CSV dengan detail Arsip baru.
        """
        csv_file_path = os.path.join(self.BASE_DIR, "Database", "Library", "project_library.csv")
        if not os.path.exists(csv_file_path):
            with open(csv_file_path, mode="w", newline="") as file:
                writer = csv.writer(file)
                writer.writerow(["No", "Tanggal", "Nama", "Lokasi"])

        with open(csv_file_path, mode="r", encoding="utf-8") as file:
            reader = csv.reader(file)
            next(reader, None)
            rows = [row for row in reader]
            last_no = int(rows[-1][0]) if rows else 0

        with open(csv_file_path, mode="a", newline="", encoding="utf-8") as file:
            writer = csv.writer(file)
            new_no = last_no + 1
            # Format tanggal dengan bulan dalam bahasa Indonesia
            bulan_indonesia = {
            "January": "Januari", "February": "Februari", "March": "Maret", "April": "April",
            "May": "Mei", "June": "Juni", "July": "Juli", "August": "Agustus",
            "September": "September", "October": "Oktober", "November": "November", "December": "Desember"
            }
            tanggal = date.today().strftime("%d_%B_%Y")
            for eng, ind in bulan_indonesia.items():
                tanggal = tanggal.replace(eng, ind)
            new_row = [new_no, tanggal, self.project_name.get(), project_folder]
            writer.writerow(new_row)

    def rename_template(self, old_name, new_name):
        """
        Rename a template file.
        """
        old_path = os.path.join(self.BASE_DIR, "Database", "Template", old_name + ".txt")
        new_path = os.path.join(self.BASE_DIR, "Database", "Template", new_name + ".txt")
        if os.path.exists(old_path):
            os.rename(old_path, new_path)
            self.load_templates()
            messagebox.showinfo("Success", f"Template renamed from {old_name} to {new_name}")
        else:
            messagebox.showerror("Error", f"Template {old_name} does not exist")

    def load_templates(self):
        """Muat file template ke dalam combobox dan set pilihan default."""
        self.check_and_load_templates()  # Panggil metode untuk memeriksa dan memuat template
        self.main_window.update_status("Memastikan template default ada di database.")  # Update status bar

    def check_and_load_templates(self):
        """Periksa file template, pastikan default_template ada, dan refresh combobox jika default_template hilang."""
        try:
            # Path ke folder Template
            template_folder = os.path.join(self.BASE_DIR, "Database", "Template")

            # Buat folder Template jika belum ada
            os.makedirs(template_folder, exist_ok=True)

            # Ambil daftar file .txt di direktori Template
            files = [
                f for f in os.listdir(template_folder)
                if os.path.isfile(os.path.join(template_folder, f)) and f.endswith(".txt")
            ]

            # Cek apakah default_template.txt ada
            if "default_template.txt" not in files:
                # Jika default_template.txt hilang, buat kembali file default dan refresh combobox
                default_template_path = os.path.join(template_folder, "default_template.txt")
                with open(default_template_path, "w") as default_file:
                    default_file.write("")  # Isi default template
                files.append("default_template.txt")  # Tambahkan default_template ke daftar file
                self.main_window.update_status("Memastikan template default ada di database.") # Update status bar

            # Sembunyikan ekstensi .txt dan buat mapping nama file
            self.file_mapping = {os.path.splitext(f)[0]: f for f in files}  # {display_name: full_name}
            display_names = sorted(list(self.file_mapping.keys()))  # Sort display names alphabetically

            # Simpan pilihan pengguna saat ini
            current_selection = self.template_combobox.get()

            # Tambahkan daftar nama ke combobox template
            self.template_combobox['values'] = display_names

            # Logika untuk refresh combobox
            if current_selection not in display_names:
                # Jika pilihan saat ini tidak ada di daftar (misalnya default_template baru dibuat), pilih default
                default_selection = ""  # Set default selection to empty
                self.template_combobox.set(default_selection)
            else:
                # Jika pilihan masih ada, kembalikan pilihan pengguna
                self.template_combobox.set(current_selection)

        except Exception as e:
            print(f"Error loading templates: {e}")
            messagebox.showerror("Error", f"Failed to load templates: {e}")

        # Jadwalkan pemeriksaan berikutnya setelah 1000 ms
        self.after(1000, self.check_and_load_templates)

    def load_selected_template(self):
        """
        Muat file template yang dipilih ke dalam variabel folders_to_make.
        """
        selected_template = self.template_var.get()
        if selected_template:
            template_file = self.file_mapping.get(selected_template)
            if template_file:
                template_path = os.path.join(self.BASE_DIR, "Database", "Template", template_file)
                try:
                    with open(template_path, "r") as f:
                        subfolders = f.read().splitlines()
                        self.folders_to_make.set("\n".join(subfolders))
                        print(f"Loaded subfolders from {selected_template}: {subfolders}")
                except Exception as e:
                    print(f"Error loading template {selected_template}: {e}")

    def open_color_picker(self, event):
        """Buka color picker dan ambil warna yang dipilih."""
        color_code = colorchooser.askcolor(title="Pilih Warna")[1]
        if color_code:
            self.theme_color = color_code
            self.theme_label.config(foreground=self.theme_color)
            self.color_picker_button.config(background=self.theme_color)
            # Disable motion tracking
            self.unbind("<Motion>")
            self.adjust_frame.unbind("<Motion>")

    def enable_random_color(self):
        """Enable random color changes again."""
        self.bind("<Motion>", self._change_theme_color, add="+")
        self.adjust_frame.bind("<Motion>", self._change_theme_color, add="+")
        print("Random color changes enabled.")

    def _change_theme_color(self, event):
        """Ubah warna tema ke warna dengan hue incremental, tetapi saturasi dan value tetap."""
        # Tetapkan saturasi dan value tetap
        saturation = 0.97
        value = 0.70

        # Increment hue
        self.hue += 0.01
        if self.hue > 1:
            self.hue = 0

        # Konversi dari HSV ke RGB
        r, g, b = hsv_to_rgb(self.hue, saturation, value)
        self.theme_color = "#{:02x}{:02x}{:02x}".format(int(r * 255), int(g * 255), int(b * 255))

        self.theme_label.config(foreground=self.theme_color)
        self.color_picker_button.config(background=self.theme_color)

    def track_template_changes(self):
        """
        Lacak perubahan di combobox template dan cetak variabel folders_to_make.
        """
        current_template = self.template_var.get()
        if current_template != self.template_combobox.get():
            self.template_var.set(self.template_combobox.get())
            self.load_selected_template()
            print(f"Template changed to: {self.template_var.get()}")
            print(f"Folders to make: {self.folders_to_make.get()}")

        # Jadwalkan pemeriksaan berikutnya setelah 1000 ms
        self.after(1000, self.track_template_changes)

    def _update_template_var(self, event):
        """
        Perbarui template_var saat template baru dipilih dari combobox.
        Reset subfolders saat template baru dipilih.
        """
        selected_template = self.template_combobox.get()
        self.template_var.set(selected_template)
        self.subfolders = []  # Reset subfolders
        self.load_selected_template()  # Muat template yang dipilih
        print(f"Selected template: {selected_template}")
        print(f"Folders to make: {self.folders_to_make.get()}")

    def generate_markdown_file(self, project_folder):
        """
        Buat file Markdown di folder Arsip yang ditentukan.
        """
        markdown_file_path = os.path.join(project_folder, f"{self.project_name.get()}.md")
        with open(markdown_file_path, "w") as f:
            f.write(f"""---
Lokasi: "[[{self.root_folder.get()}]]"
Kategori: "[[{self.category.get()}]]"
Sub_Kategori: "[[{self.sub_category.get()}]]"
Tanggal_Buat: {date.today().strftime("%Y-%m-%d")}
Tags:
  - {self.category.get()}
  - {self.sub_category.get()}
  - {self.root_folder.get()}
  - {self.date_var.get()}
  - {self.date_var.get().split('_')[1]}
Selesai: false
---

## <span style="color:{self.theme_color}">Direktori File</span> :

---

```
{project_folder}
```

```
{self.project_name.get()}
```

[Buka Folder]({project_folder})

## <span style="color:{self.theme_color}">Preview</span> :

---

![[{self.project_name.get()}.png]]
""")
        print(f"File Markdown telah dibuat di {markdown_file_path}.")

    def check_project_name(self):
        """
        Check if project_name is empty or only 1 character and update the UI accordingly.
        """
        if len(self.project_name.get()) == 1:
            # Check if project_name in ProjectNameInput is empty
            if not self.main_window.project_name_input.get_project_name():
                self.project_name.set("")  # Clear project_name in ProjectGenerator

        if not self.project_name.get():
            self.create_project_button.config(state=tk.DISABLED)
        else:
            self.create_project_button.config(state=tk.NORMAL)
        
        # Schedule the next check after 1000ms
        self.after(1000, self.check_project_name)

    def update_project_name(self, new_name):
        """
        Update the project_name with the new value.
        """
        self.project_name.set(new_name)
        self._create_project_path()

    def check_sync_project_name(self):
        """
        Ensure project_name in ProjectGenerator and ProjectNameInput are synchronized.
        """
        project_name_input = self.main_window.project_name_input.get_project_name()
        if self.project_name.get() != project_name_input:
            self.project_name.set(project_name_input)
            self._create_project_path()

        # Schedule the next check after 1000ms
        self.after(1000, self.check_sync_project_name)

    def check_update_project_name(self):
        """
        Check if update_project_name needs to be called every 1000ms.
        """
        if not self.project_name.get():
            self.update_project_name("")

        # Schedule the next check after 1000ms
        self.after(1000, self.check_update_project_name)


