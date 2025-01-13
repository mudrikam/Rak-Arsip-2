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

# Launcher ini berfungsi untuk memulai aplikasi Rak Arsip 2.0 dengan menginisialisasi
# dan menjalankan instance dari kelas MainWindow yang terdapat di dalam modul App.window.

import logging
import random
import sys
import os
import json
from typing import Dict, Any, Optional
from urllib.request import urlopen
import tkinter as tk
from tkinter import ttk
from tkinter import messagebox

from App.config import CURRENT_VERSION, GITHUB_REPO
from App.window import MainWindow

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('launcher.log'),
        logging.StreamHandler()
    ]
)

# Dapatkan lokasi folder "App"
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
APP_DIR = os.path.join(BASE_DIR, "App")

# Tambahkan folder "App" ke sys.path
sys.path.insert(0, APP_DIR)

# Load release messages
def load_release_messages() -> Dict[str, Any]:
    """Load and validate release messages from JSON file."""
    message_file = os.path.join(BASE_DIR, "App", "release_message.json")
    try:
        with open(message_file, 'r', encoding='utf-8') as f:
            messages = json.load(f)
            required_keys = ['greetings', 'facts', 'version_messages', 
                           'current_version_messages', 'release_titles',
                           'later_messages', 'update_messages', 'countdown_messages']
            
            missing_keys = [key for key in required_keys if key not in messages]
            if missing_keys:
                raise KeyError(f"Missing required keys: {', '.join(missing_keys)}")
                
            return messages
    except Exception as e:
        logging.error(f"Failed to load release messages: {str(e)}")
        messagebox.showerror("Error", "Failed to load application messages. The application will exit.")
        sys.exit(1)

def create_countdown_dialog(message: str, timeout: int = 30, 
                          latest_version: Optional[str] = None, 
                          current_version: Optional[str] = None, 
                          release_notes: Optional[str] = None) -> bool:
    """Create update notification dialog with countdown."""
    try:
        dialog = tk.Toplevel()
        dialog.withdraw()
        
        # Set protocol sekali di awal dan jangan pernah diubah
        dialog.protocol("WM_DELETE_WINDOW", lambda: None)
        
        DIALOG_WIDTH = 480
        
        style = ttk.Style()
        style.theme_use('vista')
        
        # Configure custom styles
        style.configure('Action.TButton', font=('Segoe UI', 11), padding=5)
        style.configure('Later.TButton', font=('Segoe UI', 10), padding=5)
        style.configure('Title.TLabel', font=('Segoe UI', 12, 'bold'), background='white', foreground='#ff7d19')
        style.configure('Heading.TLabel', font=('Segoe UI', 12), background='white')
        style.configure('Body.TLabel', font=('Segoe UI', 10), background='white')
        style.configure('Small.TLabel', font=('Segoe UI', 9), background='white', foreground='#666666')
        style.configure('Custom.TLabel', font=('Segoe UI', 10), background='white')
        
        # Tambahkan style baru untuk centered text
        style.configure('Centered.TLabel', 
                       font=('Segoe UI', 10), 
                       background='white',
                       justify='center',
                       anchor='center')
        
        dialog.configure(bg='white')
        dialog.resizable(False, False)
        
        icon_path = os.path.join(BASE_DIR, "App", "img", "Icon", "rakikon.ico")
        if os.path.exists(icon_path):
            dialog.iconbitmap(icon_path)
        
        result = {'value': None, 'after_id': None}
        
        # Load messages from JSON - sekarang akan selalu berhasil atau keluar
        messages = load_release_messages()

        # Simpan referensi untuk binding cleanup
        dialog_refs = {
            'canvas': None,
            'scrollable_frame': None
        }

        def create_content():
            main_container = ttk.Frame(dialog, style='Custom.TLabel')
            main_container.pack(fill='both', expand=True)
            
            container = ttk.Frame(main_container, style='Custom.TLabel')
            container.pack(fill='both', expand=True, padx=20, pady=(15,5))
            
            # Center align greeting
            greeting = random.choice(messages['greetings'])
            greeting_label = ttk.Label(container, text=greeting, style='Title.TLabel')
            greeting_label.pack(fill='x', pady=(0,10))
            greeting_label.configure(anchor='center', justify='center')
            
            # Version info dengan alignment center
            version_frame = ttk.Frame(container, style='Custom.TLabel')
            version_frame.pack(fill='x', pady=5)
            
            version_msg = random.choice(messages['version_messages']).format(version=latest_version)
            current_version_msg = random.choice(messages['current_version_messages']).format(version=current_version)
            
            version_label = ttk.Label(version_frame, text=version_msg, style='Heading.TLabel')
            version_label.pack(fill='x')
            version_label.configure(anchor='center', justify='center')
            
            current_version_label = ttk.Label(version_frame, text=current_version_msg, style='Small.TLabel')
            current_version_label.pack(fill='x', pady=(2,0))
            current_version_label.configure(anchor='center', justify='center')
            
            # Center align fact
            fact_label = ttk.Label(container, text=random.choice(messages['facts']), 
                                  style='Small.TLabel', wraplength=DIALOG_WIDTH-60)
            fact_label.pack(fill='x', pady=(0,10))
            fact_label.configure(anchor='center', justify='center')
            
            if release_notes:
                notes_frame = ttk.Frame(container, style='Custom.TLabel')
                notes_frame.pack(fill='both', expand=True, pady=10)
                
                # Title centered
                title_label = ttk.Label(notes_frame, 
                                      text=random.choice(messages['release_titles']), 
                                      style='Heading.TLabel')
                title_label.pack(fill='x')
                title_label.configure(anchor='center', justify='center')
                
                # Canvas dan scrollbar untuk release notes
                canvas = tk.Canvas(notes_frame, bg='white', highlightthickness=0, height=200)  # Tambah height default
                scrollbar = ttk.Scrollbar(notes_frame, orient="vertical", command=canvas.yview)
                scrollable_frame = ttk.Frame(canvas, style='Custom.TLabel')
                
                scrollable_frame.bind(
                    "<Configure>",
                    lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
                )
                
                canvas.create_window((0, 0), window=scrollable_frame, anchor="nw", width=DIALOG_WIDTH-80)
                canvas.configure(yscrollcommand=scrollbar.set)
                
                # Release notes content dalam scrollable frame
                notes_label = ttk.Label(scrollable_frame, 
                                      text=release_notes,
                                      wraplength=DIALOG_WIDTH-85,
                                      justify='left',
                                      style='Body.TLabel')
                notes_label.pack(fill='x', pady=(5,0))
                notes_label.configure(anchor='w')
                
                # Pack canvas dan scrollbar
                canvas.pack(side="left", fill="both", expand=True, pady=(5,0))
                scrollbar.pack(side="right", fill="y", pady=(5,0))
                
                # Perbaikan binding mouse wheel
                def _on_mousewheel(event):
                    canvas.yview_scroll(int(-1*(event.delta/120)), "units")
                
                # Bind ke canvas dan scrollable_frame
                canvas.bind_all("<MouseWheel>", _on_mousewheel)
                scrollable_frame.bind("<MouseWheel>", _on_mousewheel)
                
                # Tambahkan binding untuk fokus
                def _on_enter(event):
                    canvas.bind_all("<MouseWheel>", _on_mousewheel)
                
                def _on_leave(event):
                    canvas.unbind_all("<MouseWheel>")
                
                # Bind mouse enter/leave events
                canvas.bind("<Enter>", _on_enter)
                canvas.bind("<Leave>", _on_leave)
                scrollable_frame.bind("<Enter>", _on_enter)
                scrollable_frame.bind("<Leave>", _on_leave)

                # Simpan referensi
                dialog_refs['canvas'] = canvas
                dialog_refs['scrollable_frame'] = scrollable_frame

                # Update cleanup binding
                def cleanup_binding():
                    try:
                        canvas.unbind_all("<MouseWheel>")
                        canvas.unbind("<Enter>")
                        canvas.unbind("<Leave>")
                        scrollable_frame.unbind("<Enter>")
                        scrollable_frame.unbind("<Leave>")
                    except:
                        pass
            
            return main_container

        def update_countdown(count):
            if result['after_id']:
                dialog.after_cancel(result['after_id'])
                result['after_id'] = None

            try:
                if not dialog.winfo_exists():
                    return
                    
                if count >= 0 and result['value'] is None:
                    if not hasattr(countdown_label, 'base_message'):
                        countdown_label.base_message = random.choice(messages['countdown_messages'])
                    message = countdown_label.base_message.format(count=count)
                    countdown_label.config(text=message)
                    result['after_id'] = dialog.after(1000, lambda: update_countdown(count - 1))
                elif result['value'] is None:
                    cleanup_bindings()
                    dialog.destroy()
                    result['value'] = False
            except tk.TclError:
                return

        def cleanup_resources():
            """Clean up all resources and bindings."""
            if result['after_id']:
                dialog.after_cancel(result['after_id'])
            cleanup_bindings()
            try:
                dialog.destroy()
            except tk.TclError:
                pass

        def cleanup_bindings():
            try:
                if dialog_refs['canvas']:
                    dialog_refs['canvas'].unbind_all("<MouseWheel>")
                    dialog_refs['canvas'].unbind("<Enter>")
                    dialog_refs['canvas'].unbind("<Leave>")
                if dialog_refs['scrollable_frame']:
                    dialog_refs['scrollable_frame'].unbind("<Enter>")
                    dialog_refs['scrollable_frame'].unbind("<Leave>")
                dialog.unbind_all("<MouseWheel>")
            except:
                pass

        dialog.title("Pembaruan Tersedia")
        
        content = create_content()
        
        countdown_label = ttk.Label(dialog, style='Small.TLabel')
        countdown_label.pack(pady=5)
        
        ttk.Separator(dialog, orient='horizontal').pack(fill='x')
        button_frame = ttk.Frame(dialog, style='Custom.TLabel')
        button_frame.pack(fill='x', padx=20, pady=15)
        
        button_frame.grid_columnconfigure(1, weight=1)
        
        later_btn = ttk.Button(button_frame, 
                              text=random.choice(messages['later_messages']), 
                              command=lambda: (cleanup_resources(), 
                                             result.update({'value': False})),
                              style='Later.TButton')
        later_btn.grid(row=0, column=0, padx=(0,10))
        later_btn.state(['disabled'])  # Disable tombol saat pertama muncul
        
        update_btn = ttk.Button(button_frame, 
                               text=random.choice(messages['update_messages']), 
                               command=lambda: (cleanup_resources(),
                                              result.update({'value': True})),
                               style='Action.TButton')
        update_btn.grid(row=0, column=2)

        # Fungsi untuk mengaktifkan tombol later setelah 5 detik
        def enable_later_button():
            later_btn.state(['!disabled'])
            
        # Set timer untuk mengaktifkan tombol
        dialog.after(5000, enable_later_button)

        dialog.update_idletasks()
        dialog.geometry(f"{DIALOG_WIDTH}x{dialog.winfo_height()}")
        
        screen_width = dialog.winfo_screenwidth()
        screen_height = dialog.winfo_screenheight()
        x = screen_width/2 - DIALOG_WIDTH/2
        y = screen_height/2 - dialog.winfo_height()/2
        dialog.geometry(f"+{int(x)}+{int(y)}")  # Hapus tanda + ekstra di akhir
        
        dialog.update_idletasks()
        
        required_height = content.winfo_reqheight() + countdown_label.winfo_reqheight() + \
                         button_frame.winfo_reqheight() + 50
        
        max_height = int(dialog.winfo_screenheight() * 0.8)
        final_height = min(required_height, max_height)
        
        dialog.geometry(f"{DIALOG_WIDTH}x{int(final_height)}")
        
        screen_width = dialog.winfo_screenwidth()
        screen_height = dialog.winfo_screenheight()
        x = int(screen_width/2 - DIALOG_WIDTH/2)
        y = int(screen_height/2 - final_height/2)
        dialog.geometry(f"+{x}+{y}")
        
        dialog.deiconify()
        update_countdown(timeout)
        dialog.grab_set()
        dialog.wait_window()
        
        if result['after_id']:
            try:
                dialog.after_cancel(result['after_id'])
            except tk.TclError:
                pass

        return result['value']
    except Exception as e:
        logging.error(f"Error creating update dialog: {str(e)}")
        return False

def check_for_updates(parent_window: Optional[tk.Tk] = None) -> None:
    """Check for updates and show dialog if update is available."""
    try:
        api_url = f"https://api.github.com/repos/{GITHUB_REPO}/releases/latest"
        with urlopen(api_url) as response:
            data = json.loads(response.read())
            latest_version = data['tag_name'].lstrip('v')
            release_notes = data.get('body', '').strip()
            
            if latest_version > CURRENT_VERSION:
                logging.info(f"Update available: {latest_version}")
                if create_countdown_dialog(
                    message="",
                    latest_version=latest_version,
                    current_version=CURRENT_VERSION,
                    release_notes=release_notes
                ):
                    import webbrowser
                    webbrowser.open(f"https://github.com/{GITHUB_REPO}/releases/latest")
    except Exception as e:
        logging.error(f"Failed to check for updates: {str(e)}")

# Jalankan aplikasi
def main():
    """Main application entry point."""
    try:
        app = MainWindow()
        app.after(1000, lambda: check_for_updates(app))
        app.mainloop()
    except Exception as e:
        logging.error(f"Application error: {str(e)}")
        messagebox.showerror("Error", "An unexpected error occurred. Check launcher.log for details.")
        sys.exit(1)

if __name__ == "__main__":
    main()
