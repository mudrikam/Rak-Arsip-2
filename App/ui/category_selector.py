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

import tkinter as tk
from tkinter import ttk
import os
from tkinter import messagebox

class CategorySelector(ttk.LabelFrame):
    def __init__(self, parent, x, y, width, height, BASE_DIR, main_window):
        """
        Initialize the CategorySelector.
        """
        super().__init__(parent, text="Pilih Kategori :")  # LabelFrame as the parent widget
        self.place(x=x, y=y, width=width, height=height)  # Set position and size
        self.BASE_DIR = BASE_DIR
                
        self.main_window = main_window
                
        self.category_value = tk.StringVar()
        self.new_category_value = tk.StringVar()
        self.categories = []
        self._load_categories()

        # Create the LabelFrames for categories and subcategories
        self.category_label_frame = ttk.LabelFrame(self, text="Kategori :", padding="10")
        self.category_label_frame.pack(fill="x", padx=10, pady=5)

        self.subcategory_label_frame = ttk.LabelFrame(self, text="Sub Kategori :", padding="10")
        self.subcategory_label_frame.pack(fill="x", padx=10, pady=5)

        # Add category dropdown and input fields
        self._add_category_dropdown(self.category_label_frame)
        self._add_category_input(self.category_label_frame)

        # Add subcategory dropdown and input fields
        self._add_subcategory_dropdown(self.subcategory_label_frame)
        self._add_subcategory_input(self.subcategory_label_frame)

        # Reset button placed below subcategory frame
        self.reset_button = ttk.Button(self, text="Reset Kategori", command=self._reset, state=tk.DISABLED)
        self.reset_button.pack(fill=tk.X, padx=10, pady=5)  # Pack it after subcategory frame

        # Initialize last modified time for Category.txt
        self.category_file_path = os.path.join(self.BASE_DIR, "Database", "Category.txt")
        try:
            self.last_modified_time = os.path.getmtime(self.category_file_path)
        except FileNotFoundError:
            self.last_modified_time = None

        # Initialize last modified time for the selected subcategory file
        self.selected_subcategory_file_path = None
        self.last_subcategory_modified_time = None

        # Start monitoring Category.txt for changes
        self.check_for_updates()

    def _load_categories(self):
        """
        Load categories from the Category.txt file if it exists.
        """
        category_file_path = os.path.join(self.BASE_DIR, "Database", "Category.txt")
        try:
            with open(category_file_path, "r") as file:
                self.categories = [line.strip() for line in file if line.strip()]
        except FileNotFoundError:
            print("Category.txt not found. Starting with an empty category list.")
            self.categories = ["Tambahkan Kategori Baru"]  # Default if file not found

    def _add_category_dropdown(self, parent_frame):
        """
        Create and place the category dropdown (ComboBox).
        """
        # Create the dropdown (ComboBox) for categories
        self.category_dropdown = ttk.Combobox(
            parent_frame,
            textvariable=self.category_value,
            font=("Arial", 10),
            state="readonly",  # Make dropdown read-only
        )
        self.category_dropdown["values"] = self.categories
        self.category_dropdown.pack(fill=tk.X, pady=(10, 0))  # Place the dropdown with padding

        # Set the default category to None (empty) initially
        self.category_value.set("")  # Make sure no default selection is made

        # Bind event <ComboboxSelected> to trigger the category selection action
        self.category_dropdown.bind("<<ComboboxSelected>>", self._on_category_selected)

    def _add_category_input(self, parent_frame):
        """
        Add input field and button to add a new category.
        """
        # Create a new StringVar specifically for the category input
        self.new_category_value = tk.StringVar()

        # Entry for a new category with input validation
        self.new_category_entry = ttk.Entry(parent_frame, textvariable=self.new_category_value, font=("Arial", 10))
        self.new_category_entry.pack(fill=tk.X, pady=(10, 0))
        self.new_category_entry.bind("<Return>", lambda event: self._add_new_category())

        # Bind event to replace spaces with underscores automatically
        def on_key_release(event):
            current_value = self.new_category_value.get()

            if event.keysym not in ['BackSpace', 'Delete']:
                # Filter karakter yang diizinkan (huruf, angka, underscore, dan spasi)
                filtered_value = ''.join(char for char in current_value if char.isalnum() or char == '_' or char == ' ')

                # Ganti spasi dengan underscore
                updated_value = filtered_value.replace(" ", "_")

                self.new_category_value.set(updated_value)

        self.new_category_entry.bind("<KeyRelease>", on_key_release)

        # Button to add new category
        add_button = ttk.Button(parent_frame, text="Tambah", command=self._add_new_category)
        add_button.pack(fill=tk.X, pady=(10, 0))

    def _add_new_category(self):
        """
        Add a new category to the file and update the dropdown.
        """
        new_category = self.new_category_value.get().strip()
        new_category = new_category.replace(" ", "_")  # Replace spaces with underscores
        
        if new_category:
            category_file_path = os.path.join(self.BASE_DIR, "Database", "Category.txt")
            
            # Check if the category already exists in the file
            if os.path.exists(category_file_path):
                with open(category_file_path, "r") as file:
                    existing_categories = [line.strip() for line in file if line.strip()]
                    if new_category in existing_categories:
                        messagebox.showwarning("Peringatan", "Kategori sudah ada!")
                        self.new_category_entry.delete(0, tk.END)  # Reset input field
                        return
            
            # Create the file if it doesn't exist
            if not os.path.exists(category_file_path):
                with open(category_file_path, "w") as file:
                    print(f"Created new file: {category_file_path}")

            # Append the new category to the file
            with open(category_file_path, "a") as file:
                file.write(f"{new_category}\n")

            # Update the category dropdown
            self.categories.append(new_category)
            self.category_dropdown["values"] = self.categories
            self.category_value.set(new_category)  # Set new category as default
            print(f"New category added: {new_category}")

            # Clear the entry field
            self.new_category_entry.delete(0, tk.END)
        else:
            print("Invalid input. Category name cannot be empty.")
            messagebox.showwarning("Peringatan", "Kategori tidak boleh kosong!")

    def _add_subcategory(self):
        """
        Add a new subcategory to the selected category's subcategory file.
        """
        selected_category = self.category_value.get()
        new_subcategory = self.new_subcategory_value.get().strip()  # Use the new StringVar for input

        if new_subcategory:
            subcategory_file_path = os.path.join(self.BASE_DIR, "Database", f"{selected_category}.txt")
            with open(subcategory_file_path, "a") as file:
                file.write(f"{new_subcategory}\n")
            print(f"Added new subcategory: {new_subcategory}")
            # Reload subcategories
            self._on_category_selected(None)  # Trigger reloading of the list

            # Clear the entry field
            self.new_subcategory_entry.delete(0, tk.END)
        else:
            print("Invalid input. Subcategory name cannot be empty.")
            messagebox.showwarning("Peringatan", "Sub Kategori tidak boleh kosong!")

    def _on_category_selected(self, event):
        """
        Event handler for the category selection.
        This will create the SubCategorySelector based on the selected category.
        """
        selected_category = self.category_value.get()  # Get selected category
        self.main_window.update_value("category", selected_category)  # Update category in MainWindow
        # Update status bar with the selected category
        
        self.main_window.update_status(f"Kategori utama: {selected_category}")
        print(f"Selected Category: {selected_category}")  # Print selected category to console
        
        self.reset_button.config(state=tk.NORMAL)

        # Construct the path to the corresponding subcategory file
        subcategory_file_path = os.path.join(self.BASE_DIR, "Database", f"{selected_category}.txt")

        # Check if the file exists
        if os.path.exists(subcategory_file_path):
            try:
                with open(subcategory_file_path, "r") as file:
                    subcategories = [line.strip() for line in file if line.strip()]
                    if subcategories:
                        self.subcategory_dropdown["values"] = subcategories
                        self.subcategory_value.set(subcategories[0])  # Set the default subcategory from the list
                    else:
                        print(f"The file {subcategory_file_path} is empty.")
                        self.subcategory_dropdown["values"] = [""]
            except Exception as e:
                print(f"Error reading {subcategory_file_path}: {e}")
        else:
            print(f"File {subcategory_file_path} not found.")
            # Create the file with a default list or allow adding new subcategories
            self.subcategory_dropdown["values"] = ["Tambah"]

        # Reset the subcategory input field to an empty state
        self.subcategory_value.set("")  # Clear the subcategory input field

        # Update the last modified time for the selected subcategory file
        self.selected_subcategory_file_path = subcategory_file_path
        try:
            self.last_subcategory_modified_time = os.path.getmtime(subcategory_file_path)
        except FileNotFoundError:
            self.last_subcategory_modified_time = None

    def _add_subcategory_dropdown(self, parent_frame):
        """
        Create and place the subcategory dropdown (ComboBox).
        """
        self.subcategory_value = tk.StringVar()
        self.subcategory_dropdown = ttk.Combobox(
            parent_frame,
            textvariable=self.subcategory_value,
            font=("Arial", 10),
            state="readonly",  # Make dropdown read-only
        )
        self.subcategory_dropdown.pack(fill=tk.X, pady=(10, 0))  # Place the dropdown with padding

        # Set the default subcategory (or any default value)
        self.subcategory_value.set("Pilih kategori dulu")

        # Bind event <ComboboxSelected> to load the corresponding subcategory list
        self.subcategory_dropdown.bind("<<ComboboxSelected>>", self._on_subcategory_selected)

    def _add_subcategory_input(self, parent_frame):
        """
        Add input field and button to add a new subcategory.
        """
        # Create a new StringVar specifically for the subcategory input
        self.new_subcategory_value = tk.StringVar()

        # Entry for a new subcategory with input validation
        self.new_subcategory_entry = ttk.Entry(parent_frame, textvariable=self.new_subcategory_value, font=("Arial", 10))
        self.new_subcategory_entry.pack(fill=tk.X, pady=(10, 0))
        self.new_subcategory_entry.bind("<Return>", lambda event: self._add_subcategory())

        # Bind event to replace spaces with underscores automatically
        def on_key_release(event):
            current_value = self.new_subcategory_value.get()

            if event.keysym not in ['BackSpace', 'Delete']:
                # Filter karakter yang diizinkan (huruf, angka, underscore, dan spasi)
                filtered_value = ''.join(char for char in current_value if char.isalnum() or char == '_' or char == ' ')

                # Ganti spasi dengan underscore
                updated_value = filtered_value.replace(" ", "_")

                self.new_subcategory_value.set(updated_value)

        self.new_subcategory_entry.bind("<KeyRelease>", on_key_release)  # Bind the key release event

        # Button to add new subcategory
        add_subcategory_button = ttk.Button(parent_frame, text="Tambah", command=self._add_subcategory)
        add_subcategory_button.pack(fill=tk.X, pady=(10, 0))

    def _on_subcategory_selected(self, event):
        """
        Event handler for subcategory selection.
        """
        selected_category = self.category_value.get()  # Get the selected category
        selected_subcategory = self.subcategory_value.get()  # Get the selected subcategory
        selected_subcategory = self.subcategory_value.get()  # Get the selected subcategory
        self.main_window.update_value("sub_category", selected_subcategory)
        # Update status bar with the selected category and subcategory
        self.main_window.update_status(f"Kategori dipilih: {selected_category}\\{selected_subcategory}")
        print(f"Selected Subcategory: {selected_subcategory}")  # Print selected subcategory to console

    def _reset(self):
        """
        Reset all values to their initial state.
        """
        self.category_value.set("")
        self.new_category_value.set("")
        self.subcategory_value.set("")
        self.new_subcategory_value.set("")
        self.reset_button.config(state=tk.DISABLED)
        self.main_window.update_value("category", "")
        self.main_window.update_value("sub_category", "")
        self.main_window.update_status(f"Silakan pilih kategori.")

        # Reset category dropdown if needed (consider logic based on implementation)
        self.category_dropdown["values"] = self.categories

        # Reset subcategory dropdown if needed (consider logic based on implementation)
        self.subcategory_dropdown["values"] = ["Pilih kategori dulu"]

        # Print message for confirmation (optional)
        print("Semua nilai kategori telah direset.")

    def check_for_updates(self):
        """
        Check for updates in Category.txt and reload categories if modified.
        """
        try:
            current_modified_time = os.path.getmtime(self.category_file_path)
            if current_modified_time != self.last_modified_time:
                self.last_modified_time = current_modified_time
                self._load_categories()
                self.category_dropdown["values"] = self.categories
                self.category_value.set("")  # Reset selected category
                self.subcategory_dropdown["values"] = ["Pilih kategori dulu"]  # Reset subcategory dropdown
                self.subcategory_value.set("")  # Reset selected subcategory
        except FileNotFoundError:
            messagebox.showwarning("Gawat...!", "Waduh databasenya hilang! (o_O)")
            messagebox.showinfo("Hehehe...", "Tenang jangan panik, aku buatin dulu nih")
            self.create_csv_if_not_exists()
            messagebox.showerror("Tolong diingat...!", "Baiklah database sudah aku buatin, jangan dihapus lagi, aku tau kamu sengaja!")
        except Exception as e:
            messagebox.showerror("Error", f"Terjadi kesalahan: {e}")

        # Check for updates in the selected subcategory file if it exists
        if self.selected_subcategory_file_path:
            try:
                current_subcategory_modified_time = os.path.getmtime(self.selected_subcategory_file_path)
                if current_subcategory_modified_time != self.last_subcategory_modified_time:
                    self.last_subcategory_modified_time = current_subcategory_modified_time
                    self._on_category_selected(None)  # Reload subcategories
            except FileNotFoundError:
                # If the file is deleted, reset subcategory dropdown
                self.subcategory_dropdown["values"] = ["Pilih kategori dulu"]
                self.subcategory_value.set("")
            except Exception as e:
                messagebox.showerror("Error", f"Terjadi kesalahan: {e}")

        # Schedule the next check
        self.after(1000, self.check_for_updates)

    def create_csv_if_not_exists(self):
        """
        Create Category.txt if it does not exist.
        """
        if not os.path.exists(self.category_file_path):
            with open(self.category_file_path, "w") as file:
                pass