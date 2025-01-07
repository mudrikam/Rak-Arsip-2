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
# | Nama Kontributor       | Fitur yang Ditambahkan atau Ubah   |
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
import random
import csv

class ProjectGenerator(ttk.LabelFrame):
    def __init__(self, parent, x, y, width, height, BASE_DIR, main_window, selected_disk, root_folder, category, sub_category, date_var, project_name):
        """
        Inisialisasi ProjectGenerator.
        """
        super().__init__(parent, text="Ringkasan :")
        self.place(x=x, y=y, width=width, height=height)

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
        self.input_dropdown_frame.pack(side=tk.RIGHT, fill=tk.Y, padx=5, pady=5)

        # Tambahkan checkbox untuk menyertakan tanggal
        self.include_date = tk.BooleanVar(value=True)  # Variabel untuk checkbox
        self.checkbox = ttk.Checkbutton(
            self.checkbox_frame, text="Sertakan tanggal", variable=self.include_date, command=self._create_project_path
        )
        self.checkbox.pack(side=tk.TOP, anchor="w", padx=10, pady=5)

        # Tambahkan dropdown combobox untuk folder
        self.folder_label = ttk.Label(self.input_dropdown_frame, text="Pilih lokasi proyek :")
        self.folder_label.pack(side=tk.TOP, anchor="w", padx=10, pady=5)
        
        self.folder_combobox = ttk.Combobox(self.input_dropdown_frame, textvariable=self.root_folder)
        self.folder_combobox.pack(side=tk.TOP, fill=tk.X, padx=10, pady=5)
        self.folder_combobox.bind("<<ComboboxSelected>>", self._create_project_path)

        # Tambahkan checkbox untuk Markdown
        self.include_markdown = tk.BooleanVar(value=True)  # Default is checked
        self.markdown_checkbox = ttk.Checkbutton(
            self.checkbox_frame, text="Sertakan file Markdown", variable=self.include_markdown
        )
        self.markdown_checkbox.pack(side=tk.TOP, anchor="w", padx=10, pady=5)

        # Tambahkan checkbox untuk membuka explorer
        self.open_explorer = tk.BooleanVar(value=True)
        self.explorer_checkbox = ttk.Checkbutton(
            self.checkbox_frame, text="Buka explorer setelah proyek dibuat", variable=self.open_explorer
        )
        self.explorer_checkbox.pack(side=tk.TOP, anchor="w", padx=10, pady=5)

        # Tambahkan dropdown untuk template
        self.template_label = ttk.Label(self.input_dropdown_frame, text="Pilih Template :")
        self.template_label.pack(side=tk.TOP, anchor="w", padx=10, pady=5)
        
        self.template_var = tk.StringVar()
        self.template_combobox = ttk.Combobox(self.input_dropdown_frame, textvariable=self.template_var, state="readonly")
        self.template_combobox.pack(side=tk.TOP, fill=tk.X, padx=10, pady=5)
        self.template_combobox.bind("<<ComboboxSelected>>", self._update_template_var)

        # Tambahkan Entry untuk jumlah pengulangan
        self.repeat_label = ttk.Label(self.input_dropdown_frame, text="Ulangi sebanyak :")
        self.repeat_label.pack(side=tk.TOP, anchor="w", padx=10, pady=5)
        self.repeat_entry = ttk.Entry(self.input_dropdown_frame)
        self.repeat_entry.pack(side=tk.TOP, fill=tk.X, padx=10, pady=5)
        
        # Tambahkan tombol "Buat Proyek"
        self.create_project_button = ttk.Button(self, text="Buat Proyek", command=self.create_project)
        self.create_project_button.pack(side=tk.BOTTOM, fill=tk.X, padx=10, pady=10)
        self.create_project_button.config(style="Custom.TButton")

        # Tambahkan style untuk tombol dengan ukuran font 12
        style = ttk.Style()
        style.configure("Custom.TButton", font=("TkDefaultFont", 12), padding=15)

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

        # Tambahkan kotak warna untuk tema markdown
        self.color_box = tk.Label(self.checkbox_frame, background=self.theme_color, width=20, height=1)
        self.color_box.pack(side=tk.TOP, anchor="w", padx=10, pady=5)

        # Bind events untuk mengubah warna label tema dan kotak warna
        self.theme_label.bind("<Enter>", self._change_theme_color)
        self.theme_label.bind("<Leave>", self._change_theme_color)
        self.theme_label.bind("<ButtonRelease>", self._change_theme_color)
        self.bind("<Motion>", self._change_theme_color)  # Ubah warna saat mouse bergerak di atas frame

        self.folders_to_make = tk.StringVar()  # Variabel untuk menyimpan subfolder dari template

        # Panggil metode untuk melacak perubahan pada combobox template
        self.track_template_changes()

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
            today_date = date.today().strftime("%Y_%B_%d")
            project_path = f"{selected_disk_value}\\{root_folder_value}\\{category_value}\\{sub_category_value}\\{today_date}\\{project_name_value}"
        else:  # Jika checkbox tidak diaktifkan (jangan sertakan tanggal)
            project_path = f"{selected_disk_value}\\{root_folder_value}\\{category_value}\\{sub_category_value}\\{project_name_value}"

        self.project_label.config(text=project_path)  # Perbarui label dengan path proyek

    def _update_folder_combobox(self, *args):
        """
        Memperbarui dropdown combobox dengan folder dari disk yang dipilih,
        mengabaikan $RECYCLE.BIN, folder yang diawali titik (.) atau underscore (_).
        """
        selected_disk_value = self.selected_disk.get()
        if selected_disk_value:
            try:
                # Ambil daftar folder dari disk yang dipilih dan filter out $RECYCLE.BIN, '.' dan '_'
                folders = [
                    f for f in os.listdir(selected_disk_value)
                    if os.path.isdir(os.path.join(selected_disk_value, f)) and 
                    f != "$RECYCLE.BIN" and not f.startswith(('.', '_'))
                ]
                self.folder_combobox['values'] = folders
                # Jangan set nilai default ke folder pertama, biarkan kosong
                self.folder_combobox.set("")  
            except Exception as e:
                print(f"Error updating folder combobox: {e}")
                self.folder_combobox['values'] = []
                self.folder_combobox.set("")  # Tetap kosong jika ada error



    def create_project(self):
        """
        Metode untuk membuat proyek berdasarkan input yang diberikan.
        """
        # Validasi input
        if not all([self.selected_disk.get(), self.root_folder.get(), self.category.get(), self.sub_category.get(), self.project_name.get()]):
            messagebox.showwarning("Peringatan", "Semua variabel harus diisi!")
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

        # Implementasi pembuatan proyek
        for i in range(repeat_count):
            project_folder = base_project_path
            if i > 0:
                project_folder = f"{base_project_path}_{i+1}"
            counter = 1
            while os.path.exists(project_folder):
                project_folder = f"{base_project_path}_{i+1}_{counter}"
                counter += 1

            os.makedirs(project_folder)
            last_created_folder = project_folder
            print(f"Direktori {project_folder} telah dibuat.")

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

        messagebox.showinfo("Sukses", "Proyek telah dibuat dengan sukses!")

    def update_csv(self, project_folder):
        """
        Update the CSV file with the new project details.
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
            new_row = [new_no, date.today().strftime("%Y_%B_%d"), self.project_name.get(), project_folder]
            writer.writerow(new_row)

        
    def load_templates(self):
        """Load template files into the combobox and set a default selection."""
        self.check_and_load_templates()  # Panggil metode untuk memeriksa dan memuat template

    def check_and_load_templates(self):
        """Check for template files, ensure template_0 exists, and refresh combobox if template_0 is missing."""
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

            # Cek apakah template_0.txt ada
            if "template_0.txt" not in files:
                # Jika template_0.txt hilang, buat kembali file default dan refresh combobox
                default_template_path = os.path.join(template_folder, "template_0.txt")
                with open(default_template_path, "w") as default_file:
                    default_file.write("")  # Isi default template
                files.append("template_0.txt")  # Tambahkan template_0 ke daftar file

            # Sembunyikan ekstensi .txt dan buat mapping nama file
            self.file_mapping = {os.path.splitext(f)[0]: f for f in files}  # {display_name: full_name}
            display_names = list(self.file_mapping.keys())

            # Simpan pilihan pengguna saat ini
            current_selection = self.template_combobox.get()

            # Tambahkan daftar nama ke combobox template
            self.template_combobox['values'] = display_names

            # Logika untuk refresh combobox
            if current_selection not in display_names:
                # Jika pilihan saat ini tidak ada di daftar (misalnya template_0 baru dibuat), pilih default
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
        Load the selected template file into the folders_to_make variable.
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

    def _change_theme_color(self, event):
        """Ubah warna tema ke warna acak."""
        self.theme_color = "#{:06x}".format(random.randint(0, 0xFFFFFF))
        self.theme_label.config(foreground=self.theme_color)
        self.color_box.config(background=self.theme_color)

    def track_template_changes(self):
        """
        Track changes in the template combobox and print the folders_to_make variable.
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
        Update template_var when a new template is selected from the combobox.
        Reset subfolders when a new template is selected.
        """
        selected_template = self.template_combobox.get()
        self.template_var.set(selected_template)
        self.subfolders = []  # Reset subfolders
        self.load_selected_template()  # Load the selected template
        print(f"Selected template: {selected_template}")
        print(f"Folders to make: {self.folders_to_make.get()}")

    def generate_markdown_file(self, project_folder):
        """
        Generate a Markdown file in the specified project folder.
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


