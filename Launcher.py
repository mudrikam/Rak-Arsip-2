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

import sys
import os
import json
from urllib.request import urlopen
import tkinter as tk
from tkinter import messagebox

from App.window import MainWindow

# Version constant
CURRENT_VERSION = "2.0.0"  # Update this when releasing new versions
GITHUB_REPO = "mudrikam/Rak-Arsip-2"

# Dapatkan lokasi folder "App"
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
APP_DIR = os.path.join(BASE_DIR, "App")

# Tambahkan folder "App" ke sys.path
sys.path.insert(0, APP_DIR)

def check_for_updates():
    try:
        # Get latest release info from GitHub API
        api_url = f"https://api.github.com/repos/{GITHUB_REPO}/releases/latest"
        with urlopen(api_url) as response:
            data = json.loads(response.read())
            latest_version = data['tag_name'].lstrip('v')
            
            if latest_version > CURRENT_VERSION:
                message = f"Versi baru ({latest_version}) tersedia!\n\n" \
                         f"Versi Anda saat ini: {CURRENT_VERSION}\n" \
                         f"Kunjungi: https://github.com/{GITHUB_REPO}/releases"
                         
                root = tk.Tk()
                root.withdraw()  # Hide the main window
                if messagebox.askyesno("Pembaruan Tersedia", message + "\n\nBuka halaman unduhan?"):
                    import webbrowser
                    webbrowser.open(f"https://github.com/{GITHUB_REPO}/releases/latest")
                root.destroy()
    except Exception as e:
        print(f"Gagal memeriksa pembaruan: {e}")

# Jalankan aplikasi
def main():
    check_for_updates()
    app = MainWindow()
    app.mainloop()

if __name__ == "__main__":
    main()
