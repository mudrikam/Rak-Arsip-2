# Panduan Kontribusi

Terima kasih sudah tertarik untuk berkontribusi pada proyek Rak Arsip 2! Berikut adalah panduan untuk membantu dalam proses kontribusi.

## Cara Memulai

1. **Fork Repository**: Mulai dengan melakukan fork repository ini ke akun GitHub.
2. **Clone Repository**: Clone hasil fork ke komputer lokal.
    ```bash
    git clone https://github.com/mudrikam/Rak-Arsip-2.git
    ```
3. **Buat Branch Baru**: Buat branch baru untuk mengerjakan fitur atau perbaikan.
    ```bash
    git checkout -b nama-branch-baru
    ```

## Membuat Perubahan

1. **Pastikan Kode Berjalan**: Sebelum membuat perubahan, pastikan kode yang ada berjalan dengan baik.
    ```bash
    python "Direktori Rak Arsip 2/Launcher.py"
    ```
2. **Lakukan Perubahan**: Lakukan perubahan yang diperlukan pada kode.
3. **Uji Perubahan**: Setelah melakukan perubahan, uji kembali untuk memastikan tidak ada yang rusak.
    ```bash
    python "Direktori Rak Arsip 2/Launcher.py"
    ```

## Commit dan Push

1. **Commit Perubahan**: Commit perubahan dengan pesan yang jelas dan deskriptif.
    ```bash
    git add .
    git commit -m "Deskripsi perubahan yang dilakukan"
    ```
2. **Push ke Repository**: Push perubahan ke repository fork.
    ```bash
    git push origin nama-branch-baru
    ```

## Membuat Pull Request

1. **Buka Pull Request**: Buka pull request dari repository fork ke repository utama.
2. **Deskripsikan Perubahan**: Jelaskan secara detail perubahan yang dilakukan dan alasan di balik perubahan tersebut.

## Tips Tambahan

- **Ikuti Gaya Kode**: Usahakan untuk mengikuti gaya penulisan kode yang sudah ada.
- **Periksa Kembali**: Sebelum membuka pull request, periksa kembali perubahan yang dilakukan untuk menghindari kesalahan.

Terima kasih atas kontribusinya! Jika ada pertanyaan, jangan ragu untuk membuka issue atau menghubungi melalui diskusi di repository ini.
