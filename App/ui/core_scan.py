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

forbidden_words = [
    "bokep", "ngewe", "ngentot", "ngesex", "ngeseks", "bersetubuh", "persetubuhan", "berzina", "perzinaan",
    "cumbu", "bercumbu", "oral", "anal", "masturbasi", "onani", "coli", "colmek", "sange", "sagne",
    "desah", "mendesis", "ejakulasi", "sperma", "mani", "lendir", "basah", "kelamin", "vagina", "penis",
    "kontol", "memek", "pepek", "tempik", "itil", "toket", "tobrut", "pentil", "jembut", "puki", "pukimak",
    "picek", "ngaceng", "horny", "nafsu", "birahi", "rangsang", "terangsang", "orgasme", "klimaks",
    "asu", "anjing", "bajingan", "brengsek", "jancok", "bangsat", "keparat", "bedebah", "berengsek",
    "setan", "syaitan", "iblis", "laknat", "terkutuk", "sialan", "sial", "kampret", "goblok", "tolol",
    "idiot", "bego", "dungu", "bebal", "bodoh", "cacat", "cacat mental", "sampah", "kotoran", "najis",
    "butut", "jorok", "buruk", "jelek", "buruk rupa", "pecundang", "penipu", "penjahat", "maling",
    "begundal", "preman", "berandal", "bandit", "bajingan tengik", "monyet", "babi", "onta", "udik",
    "ndeso", "gaptek", "kamseupay", "alay", "tai",
    "pelacur", "sundal", "sundel", "pelacuran", "prostitusi", "porno", "pornografi", "cabul", "hidung belang",
    "main belakang", "balapan liar", "film biru", "adegan ranjang", "esek esek", "lendir",
    "judi", "judi online", "online casino", "taruhan", "slot", "roulette", "poker", "sabung ayam",
    "betting", "togel", "bandar togel", "pasang taruhan", "jackpot", "win big", "gambling", "kartu remi",
    "poker online", "poker uang asli", "uang taruhan", "deposit judi", "domino qq", "dadu online",
    "pemain judi", "online betting", "live casino", "betting site", "casino online", "tangkasnet",
    "penipu judi", "kredit pinjol", "pinjaman online", "pinjol ilegal", "bunga pinjaman", "pinjaman tanpa agunan",
    "bunga tinggi", "penipuan pinjaman", "utang cepat", "pinjaman instan", "tanya pinjol",
    "pinjaman segera cair", "cair tanpa syarat", "pinjaman cepat", "pinjaman pribadi", "utang online",
    "cair cepat", "pendanaan online", "pinjaman uang cepat", "pinjol resmi", "pinjaman ilegal",
    "narkoba", "narkotik", "obat terlarang", "ganja", "sabu", "ekstasi", "heroin", "kokain", "morfin",
    "putau", "pil koplo", "kurang ajar", "biadab", "terkutuk", "terlaknat", "penghianat",
    "perusak", "penghancur", "perusak dunia", "pengacau", "penyimpangan",
    "keji", "jahat", "jahat sekali", "kejam", "kekerasan", "pemerkosaan",
    "pencurian", "perampokan", "penyerangan", "permusuhan", "konflik", "pertengkaran",
    "perkelahian", "pertempuran", "peperangan", "kekacauan", "kerusakan",
    "kecelakaan", "musibah", "bencana", "tragedi", "kematian", "pembunuhan",
    "bunuh diri", "pembunuh", "pembantaian", "penyiksaan", "penyiksaan kejam",
    "teroris", "terorisme", "radikal", "radikalisme", "ekstrimis", "ekstrimisme",
    "komplotan", "komplotan kejam", "tindakan kejam", "jebakan", "jebak",
    "tipu", "tukang tipu", "penipuan", "kecurangan", "pembohong", "kebohongan",
    "mencuri", "rampas", "perampas", "perampasan", "maling",
    "stres", "stres berat", "tekanan mental", "depresi", "kecemasan",
    "gila", "gila gilaan", "sinting", "edan", "sarap", "gendeng",
    "abnormal", "kelainan", "penyakit mental", "gangguan jiwa",
    "haram", "maksiat", "dosa", "nista", "menista", "penistaan",
    "zalim", "aniaya", "menganiaya", "penindasan", "penyiksaan",
    "mencurigakan", "berbahaya", "mengancam", "ancaman", "mengintimidasi",
    "permainan", "permainan kotor", "licik", "curang", "muslihat",
    "feodal", "kolot", "terbelakang", "primitif", "kuno", "tradisional",
    "bebal", "bodoh", "dungu", "tolol", "idiot", "goblok", "otak udang",
    "pecundang", "kalah", "kekalahan", "gagal", "kegagalan", "putus asa",
    "parasit", "benalu", "pengganggu", "perusak", "penghancur",
    "hidung belang", "playboy", "mata keranjang", "genit", "cabul",
    "gerandong", "basah", "celana dalam", "blonjo", "penjara",
    "terjebak", "lapar", "jongkok", "ambruk", "nahan", "guling", "hancur", "lempar", "gebuk", "rebutan", "lepas",
    "kacau", "kambing", "hidung keriput", "buaya darat", "jengkol",
    "gulat", "main belakang", "garuk", "colmek", "binal",
    "kolam", "panjat", "narkotika", "minuman keras", "tutup mulut", "masalah",
    "teriak", "ajak ajakan", "buang", "penghancur", "beruk", "babi ngepet",
    "tersembunyi", "orang bodoh", "gerombolan", "bengkok", "kehilangan",
    "ngaco", "dilarang", "buruh", "banjir", "badut", "sembunyi", "robek",
    "debu", "cabut", "kolam renang", "kurang ajar", "biadab", "terkutuk", "terlaknat", "penghianat", "perusak", "penghancur", "perusak dunia",
    "pengacau", "penyimpangan", "keji", "jahat", "jahat sekali", "kejam", "kekerasan", "pemerkosaan",
    "pencurian", "perampokan", "penyerangan", "permusuhan", "konflik", "pertengkaran", "perkelahian",
    "pertempuran", "peperangan", "kekacauan", "kerusakan", "kecelakaan", "musibah", "bencana", "tragedi",
    "kematian", "pembunuhan", "bunuh diri", "pembunuh", "pembantaian", "penyiksaan", "penyiksaan kejam",
    "teroris", "terorisme", "radikal", "radikalisme", "ekstrimis", "ekstrimisme", "komplotan",
    "komplotan kejam", "tindakan kejam", "jebakan", "jebak", "tipu", "tukang tipu", "penipuan",
    "kecurangan", "pembohong", "kebohongan", "mencuri", "rampas", "perampas", "perampasan",
    "stres", "stres berat", "tekanan mental", "depresi", "kecemasan", "gila", "gila gilaan", "sinting",
    "edan", "sarap", "gendeng", "abnormal", "kelainan", "penyakit mental", "gangguan jiwa", "haram",
    "maksiat", "dosa", "nista", "menista", "penistaan", "zalim", "aniaya", "menganiaya", "penindasan",
    "mencurigakan", "berbahaya", "mengancam", "ancaman", "mengintimidasi", "permainan", "permainan kotor",
    "licik", "curang", "muslihat", "feodal", "kolot", "terbelakang", "primitif", "kuno", "tradisional",
    "otak udang", "kalah", "kekalahan", "gagal", "kegagalan", "putus asa", "benalu", "pengganggu",
    "playboy", "mata keranjang", "lendir", "gerandong", "celana dalam", "blonjo", "penjara", "terjebak",
    "lapar", "jongkok", "ambruk", "nahan", "guling", "hancur", "lempar", "gebuk", "rebutan", "lepas",
    "kacau", "kambing", "hidung keriput", "buaya darat", "jengkol", "gulat", "main belakang", "garuk",
    "binal", "kolam", "panjat", "minuman keras", "tutup mulut", "masalah", "teriak", "ajak ajakan",
    "buang", "beruk", "babi ngepet", "tersembunyi", "gerombolan", "bengkok", "kehilangan", "ngaco",
    "dilarang", "buruh", "banjir", "badut", "sembunyi", "robek", "debu", "cabut", "kolam renang",
    "padam", "tercecer", "pecat", "mengecewakan", "hakim", "tersangka", "benar benar rusak", "guncangan",
    "masalah sosial", "teman palsu", "sekolah gelap", "penyalahgunaan", "masalah berat",
    "sama sama cacat", "tega", "berdarah", "lawan", "penjahat dunia", "terselubung", "pukul",
    "lempar batu", "tangkap", "bulutangkis", "jelek", "ngatuk", "kenalan buruk", "melekat", "serangan",
    "pelabuhan", "bersentuhan", "tumbuh", "melarikan diri", "kirim", "kabur lagi", "ramuan",
    "pentil", "toket", "tobrut", "sagne", "harem", "cok", "gacor", "maxwin", "win uang", "bonus taruhan",
    "judi haram", "pinjaman bunga tinggi", "pinjaman jangka pendek", "utang berbunga tinggi",
    "aplikasi judi", "pinjaman tanpa jaminan", "pembusukan", "liar", "penyimpangan",
    "orang bodoh", "buruk", "narkotika", "kotor", "gelap", "perusakan", "mencuri",
    "terkutuk", "buruk rupa", "stres berat", "kelainan", "permainan kotor",
    "komplotan kejam", "tindakan kejam", "perusak dunia", "obat terlarang", "terselubung", "kerusakan",
    "kenalan buruk", "melekat", "melarikan diri", "kabur lagi", "ramuan", "tersembunyi", "orang bodoh",
    "gerombolan", "bengkok", "kehilangan", "ngaco", "dilarang", "buruh", "banjir", "badut", "sembunyi",
    "robek", "debu", "cabut", "kolam renang", "padam", "tercecer", "pecat", "mengecewakan", "hakim",
    "tersangka", "benar benar rusak", "guncangan", "masalah sosial", "teman palsu", "sekolah gelap",
    "penyalahgunaan", "masalah berat", "sama sama cacat", "tega", "berdarah", "lawan", "penjahat dunia",
    "pukul", "lempar batu", "tangkap", "bulutangkis", "jelek", "ngatuk", "serangan", "pelabuhan",
    "bersentuhan", "tumbuh", "kirim", "pentil", "toket", "tobrut", "sagne", "harem", "cok", "gacor",
    "maxwin", "win uang", "bonus taruhan", "judi haram", "pinjaman bunga tinggi", "pinjaman jangka pendek",
    "utang berbunga tinggi", "aplikasi judi", "pinjaman tanpa jaminan", "pembusukan", "liar",
    "orang bodoh", "buruk", "narkotika", "kotor", "gelap", "perusakan", "mencuri", "terkutuk",
    "buruk rupa", "stres berat", "kelainan", "komplotan kejam", "tindakan kejam", "obat terlarang",
    "terselubung", "kerusakan", "kenalan buruk", "melekat", "melarikan diri", "kabur lagi", "ramuan",
    "tersembunyi", "gerombolan", "bengkok", "kehilangan", "ngaco", "dilarang", "buruh", "banjir",
    "badut", "sembunyi", "robek", "debu", "cabut", "kolam renang", "padam", "tercecer", "pecat",
    "mengecewakan", "hakim", "tersangka", "benar benar rusak", "guncangan", "masalah sosial",
    "bencong", "waria", "bispak", "lesbi", "homo", "gay", "transgender", "cowo", "cewe", "pacar", "selingkuh",
    "selingkuhan", "kawin", "nikah", "cerai", "janda", "duda", "mertua", "iparmu", "besan", "tetangga",
    "kampung", "kota", "pulau", "negara", "dunia", "akhirat", "surga", "neraka", "malaikat", "setan",
    "jin", "hantu", "iblis", "setan gundul", "pocong", "kuntilanak", "genderuwo", "tuyul", "babi ngepet",
    "pesugihan", "santet", "guna-guna", "teluh", "sihir", "mistis", "gaib", "klenik", "tahayul", "mitos",
    "legenda", "dongeng", "cerita", "kisah", "sejarah", "peristiwa", "kejadian", "musibah", "bencana",
    "tragedi", "kematian", "pembunuhan", "bunuh diri", "pembunuh", "pembantaian", "penyiksaan",
    "penyiksaan kejam", "teroris", "terorisme", "radikal", "radikalisme", "ekstrimis", "ekstrimisme",
    "komplotan", "komplotan kejam", "tindakan kejam", "jebakan", "jebak", "tipu", "tukang tipu",
    "penipuan", "kecurangan", "pembohong", "kebohongan", "mencuri", "rampas", "perampas", "perampasan",
    "stres", "stres berat", "tekanan mental", "depresi", "kecemasan", "gila", "gila gilaan", "sinting",
    "edan", "sarap", "gendeng", "abnormal", "kelainan", "penyakit mental", "gangguan jiwa", "haram",
    "maksiat", "dosa", "nista", "menista", "penistaan", "zalim", "aniaya", "menganiaya", "penindasan",
    "mencurigakan", "berbahaya", "mengancam", "ancaman", "mengintimidasi", "permainan", "permainan kotor",
    "licik", "curang", "muslihat", "feodal", "kolot", "terbelakang", "primitif", "kuno", "tradisional",
    "otak udang", "kalah", "kekalahan", "gagal", "kegagalan", "putus asa", "parasit", "benalu",
    "pengganggu", "playboy", "mata keranjang", "lendir", "gerandong", "celana dalam", "blonjo",
    "penjara", "terjebak", "lapar", "jongkok", "ambruk", "nahan", "guling", "hancur", "lempar",
    "gebuk", "rebutan", "lepas", "kacau", "kambing", "hidung keriput", "buaya darat", "jengkol",
    "gulat", "main belakang", "garuk", "binal", "kolam", "panjat", "minuman keras", "tutup mulut",
    "masalah", "teriak", "ajak ajakan", "buang", "beruk", "babi ngepet", "tersembunyi", "gerombolan",
    "bengkok", "kehilangan", "ngaco", "dilarang", "buruh", "banjir", "badut", "sembunyi", "robek",
    "debu", "cabut", "kolam renang", "padam", "tercecer", "pecat", "mengecewakan", "hakim", "tersangka",
    "benar benar rusak", "guncangan", "masalah sosial", "teman palsu", "sekolah gelap", "penyalahgunaan",
    "masalah berat", "sama sama cacat", "tega", "berdarah", "lawan", "penjahat dunia", "pukul",
    "lempar batu", "tangkap", "bulutangkis", "jelek", "ngatuk", "serangan", "pelabuhan",
    "bersentuhan", "tumbuh", "melarikan diri", "kirim", "kabur lagi", "ramuan",
    "pentil", "toket", "tobrut", "sagne", "harem", "cok", "gacor", "maxwin", "win uang", "bonus taruhan",
    "judi haram", "pinjaman bunga tinggi", "pinjaman jangka pendek", "utang berbunga tinggi",
    "aplikasi judi", "pinjaman tanpa jaminan", "pembusukan", "liar", "orang bodoh", "buruk", "narkotika",
    "kotor", "gelap", "perusakan", "mencuri", "terkutuk", "buruk rupa", "stres berat", "kelainan",
    "komplotan kejam", "tindakan kejam", "obat terlarang", "terselubung", "kerusakan", "kenalan buruk",
    "melekat", "melarikan diri", "kabur lagi", "ramuan", "tersembunyi", "gerombolan", "bengkok",
    "kehilangan", "ngaco", "dilarang", "buruh", "banjir", "badut", "sembunyi", "robek", "debu",
    "cabut", "kolam renang", "padam", "tercecer", "pecat", "mengecewakan", "hakim", "tersangka",
    "benar benar rusak", "guncangan", "masalah sosial", "teman palsu", "sekolah gelap", "penyalahgunaan",
    "masalah berat", "sama sama cacat", "tega", "berdarah", "lawan", "penjahat dunia", "pukul",
    "lempar batu", "tangkap", "bulutangkis", "jelek", "ngatuk", "serangan", "pelabuhan",
    "bersentuhan", "tumbuh", "kirim", "sange", "sagne", "itil", "toket", "tobrut", "pentil", "jembut", "puki", "pukimak",
    "picek", "ngaceng", "horny", "nafsu", "birahi", "rangsang", "terangsang", "orgasme", "klimaks",
    "lendir", "gerandong", "celana dalam", "blonjo", "penjara", "terjebak", "lapar", "jongkok", "ambruk",
    "nahan", "guling", "hancur", "lempar", "gebuk", "rebutan", "lepas", "kacau", "kambing", "hidung keriput",
    "buaya darat", "jengkol", "gulat", "main belakang", "garuk", "binal", "kolam", "panjat", "minuman keras",
    "tutup mulut", "masalah", "teriak", "ajak ajakan", "buang", "beruk", "babi ngepet", "tersembunyi",
    "gerombolan", "bengkok", "kehilangan", "ngaco", "dilarang", "buruh", "banjir", "badut", "sembunyi",
    "robek", "debu", "cabut", "kolam renang", "padam", "tercecer", "pecat", "mengecewakan", "hakim"
]