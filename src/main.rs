use clap::Parser;
use secp256k1::{Secp256k1, PublicKey, SecretKey};
use ripemd::Ripemd160;
use sha2::{Sha256, Digest};
use base58::ToBase58;
use bech32::{self, ToBase32};
use serde::{Deserialize, Serialize};
use rand::Rng;
use rand::rngs::OsRng;
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{BufRead, BufReader, Read, Write};
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;
use std::time::{Duration, Instant};
use crossbeam_channel::{unbounded, Receiver, Sender, select};
use anyhow::{bail, Result};
use primitive_types::U256;
use chrono::Utc;

// ========================== config ==========================

#[derive(Parser, Debug, Clone)]
#[command(author, version, about, long_about = None)]
struct Config {
    /// Диапазон в процентах, например "0-0.01", "0.5-100", "99.99-100"
    #[arg(long, value_parser = parse_range_percent)]
    range_percent: (u32, u32),

    /// Количество потоков (по умолчанию все логические ядра)
    #[arg(short, long, default_value_t = num_cpus::get())]
    threads: usize,

    /// Файл с RIPEMD-160 хешами в текстовом формате (hex по одному на строку)
    #[arg(long)]
    hash_file: Option<String>,

    /// Файл с RIPEMD-160 хешами в бинарном формате (20 байт на хеш)
    #[arg(long)]
    hash_bin: Option<String>,

    /// Файл для сохранения результатов (если не указан, вывод в stdout)
    #[arg(short, long)]
    output: Option<String>,

    /// Флаг продолжения с сохранённого состояния (только для последовательного режима)
    #[arg(long)]
    resume: bool,

    /// Режим случайного перебора (прогресс не сохраняется)
    #[arg(long)]
    random: bool,
}

fn parse_range_percent(s: &str) -> Result<(u32, u32)> {
    let parts: Vec<&str> = s.split('-').collect();
    if parts.len() != 2 {
        bail!("Формат должен быть 'start-end', например 0-0.01");
    }
    let start = parse_centipercent(parts[0])?;
    let end = parse_centipercent(parts[1])?;
    if start > end {
        bail!("Начальный процент не может быть больше конечного");
    }
    if start > 10000 || end > 10000 {
        bail!("Проценты должны быть в диапазоне 0.00 .. 100.00");
    }
    Ok((start, end))
}

fn parse_centipercent(s: &str) -> Result<u32> {
    if s.is_empty() {
        bail!("Пустое значение");
    }
    let parts: Vec<&str> = s.split('.').collect();
    match parts.len() {
        1 => {
            let int: u32 = s.parse()?;
            if int > 100 {
                bail!("Процент не может превышать 100");
            }
            Ok(int * 100)
        }
        2 => {
            let int: u32 = parts[0].parse()?;
            if int > 100 {
                bail!("Процент не может превышать 100");
            }
            let frac_part = parts[1];
            if frac_part.len() > 2 {
                bail!("Дробная часть не может быть длиннее двух цифр");
            }
            let frac: u32 = frac_part.parse()?;
            let multiplier = 10u32.pow(2 - frac_part.len() as u32);
            let frac_scaled = frac * multiplier;
            Ok(int * 100 + frac_scaled)
        }
        _ => bail!("Неверный формат числа"),
    }
}

// ========================== state ==========================

#[derive(Serialize, Deserialize, Debug, Clone)]
struct State {
    range_start: U256,
    range_end: U256,
    thread_positions: Vec<U256>,
    total_attempts: u64,
    total_found: u32,
    timestamp: chrono::DateTime<chrono::Utc>,
}

type StateMap = HashMap<String, State>;

// ========================== crypto ==========================

fn u256_to_bytes(key: U256) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    key.to_big_endian(&mut bytes);
    bytes
}

fn hash160(data: &[u8]) -> [u8; 20] {
    let sha = Sha256::digest(data);
    let mut hasher = Ripemd160::new();
    hasher.update(&sha);
    let rip = hasher.finalize();
    rip.into()
}

fn generate_addresses(priv_key: &[u8; 32]) -> Result<(String, String, String, String, String, String, String)> {
    let secp = Secp256k1::new();
    let secret_key = SecretKey::from_slice(priv_key)?;
    let pub_key = PublicKey::from_secret_key(&secp, &secret_key);

    let uncompressed = pub_key.serialize_uncompressed();
    let compressed = pub_key.serialize();

    let hash160_uncompressed = hash160(&uncompressed);
    let hash160_compressed = hash160(&compressed);

    fn legacy_address(hash: &[u8; 20]) -> String {
        let mut payload = vec![0x00];
        payload.extend_from_slice(hash);
        let checksum = Sha256::digest(&Sha256::digest(&payload));
        payload.extend_from_slice(&checksum[0..4]);
        payload.to_base58()
    }

    let legacy_uncompressed = legacy_address(&hash160_uncompressed);
    let legacy_compressed = legacy_address(&hash160_compressed);

    fn p2sh_address(inner_hash: &[u8; 20]) -> String {
        let witness_program = [0x00, 0x14];
        let mut script = Vec::with_capacity(22);
        script.extend_from_slice(&witness_program);
        script.extend_from_slice(inner_hash);
        let script_hash = hash160(&script);
        let mut payload = vec![0x05];
        payload.extend_from_slice(&script_hash);
        let checksum = Sha256::digest(&Sha256::digest(&payload));
        payload.extend_from_slice(&checksum[0..4]);
        payload.to_base58()
    }

    let p2sh_uncompressed = p2sh_address(&hash160_uncompressed);
    let p2sh_compressed = p2sh_address(&hash160_compressed);

    fn bech32_address(hash: &[u8; 20]) -> String {
        let hrp = "bc";
        let mut bytes = Vec::with_capacity(21);
        bytes.push(0u8);
        bytes.extend_from_slice(hash);
        let data = bytes.to_base32();
        bech32::encode(hrp, data, bech32::Variant::Bech32).unwrap()
    }

    let bech32 = bech32_address(&hash160_compressed);

    let priv_hex = hex::encode(priv_key);
    let ripemd_hex = hex::encode(hash160_compressed);

    Ok((
        priv_hex,
        ripemd_hex,
        legacy_uncompressed,
        legacy_compressed,
        p2sh_uncompressed,
        p2sh_compressed,
        bech32,
    ))
}

// ========================== worker ==========================

#[derive(Debug)]
enum WorkerMessage {
    Stats(usize, u64, u32),
    Match(usize, [u8; 32], [u8; 20], String),
    MinMax(usize, U256, U256),
    Finished(usize),
}

fn update_minmax(key: U256, min: &mut Option<U256>, max: &mut Option<U256>) {
    *min = Some(min.map_or(key, |m| if key < m { key } else { m }));
    *max = Some(max.map_or(key, |m| if key > m { key } else { m }));
}

fn worker_main(
    thread_id: usize,
    start_key: U256,
    end_key: U256,
    step: U256,
    running: Arc<AtomicBool>,
    tx: Sender<WorkerMessage>,
    target_hashes: Arc<HashSet<[u8; 20]>>,
    random_mode: bool,
) {
    let report_interval = 1_000_000;
    let secp = Secp256k1::new();
    let mut local_attempts = 0u64;
    let mut local_found = 0u32;
    let mut last_minmax_report = Instant::now();
    let mut local_min: Option<U256> = None;
    let mut local_max: Option<U256> = None;

    if random_mode {
        let mut rng = OsRng;
        let range_width = end_key - start_key + U256::from(1u64);
        while running.load(Ordering::SeqCst) {
            let rand_offset = if range_width > U256::from(u64::MAX) {
                let mut bytes = [0u8; 32];
                rng.fill(&mut bytes);
                U256::from_big_endian(&bytes) % range_width
            } else {
                U256::from(rng.gen_range(0..range_width.low_u64()))
            };
            let current = start_key + rand_offset;

            update_minmax(current, &mut local_min, &mut local_max);

            let key_bytes = u256_to_bytes(current);
            let secret = match SecretKey::from_slice(&key_bytes) {
                Ok(s) => s,
                Err(_) => {
                    local_attempts += 1;
                    continue;
                }
            };
            let pub_key = PublicKey::from_secret_key(&secp, &secret);

            let uncompressed = pub_key.serialize_uncompressed();
            let compressed = pub_key.serialize();

            let h160_uncompressed = hash160(&uncompressed);
            let h160_compressed = hash160(&compressed);

            if target_hashes.contains(&h160_uncompressed) {
                local_found += 1;
                let _ = tx.send(WorkerMessage::Match(thread_id, key_bytes, h160_uncompressed, "uncompressed".into()));
            }
            if target_hashes.contains(&h160_compressed) {
                local_found += 1;
                let _ = tx.send(WorkerMessage::Match(thread_id, key_bytes, h160_compressed, "compressed".into()));
            }

            local_attempts += 1;
            if local_attempts % report_interval == 0 {
                let _ = tx.send(WorkerMessage::Stats(thread_id, local_attempts, local_found));
            }

            if last_minmax_report.elapsed() >= Duration::from_secs(60) {
                if let (Some(min), Some(max)) = (local_min, local_max) {
                    let _ = tx.send(WorkerMessage::MinMax(thread_id, min, max));
                }
                local_min = None;
                local_max = None;
                last_minmax_report = Instant::now();
            }
        }
    } else {
        let mut current = start_key;
        while running.load(Ordering::SeqCst) && current <= end_key {
            update_minmax(current, &mut local_min, &mut local_max);

            let key_bytes = u256_to_bytes(current);
            let secret = match SecretKey::from_slice(&key_bytes) {
                Ok(s) => s,
                Err(_) => {
                    current += step;
                    local_attempts += 1;
                    continue;
                }
            };
            let pub_key = PublicKey::from_secret_key(&secp, &secret);

            let uncompressed = pub_key.serialize_uncompressed();
            let compressed = pub_key.serialize();

            let h160_uncompressed = hash160(&uncompressed);
            let h160_compressed = hash160(&compressed);

            if target_hashes.contains(&h160_uncompressed) {
                local_found += 1;
                let _ = tx.send(WorkerMessage::Match(thread_id, key_bytes, h160_uncompressed, "uncompressed".into()));
            }
            if target_hashes.contains(&h160_compressed) {
                local_found += 1;
                let _ = tx.send(WorkerMessage::Match(thread_id, key_bytes, h160_compressed, "compressed".into()));
            }

            local_attempts += 1;
            if local_attempts % report_interval == 0 {
                let _ = tx.send(WorkerMessage::Stats(thread_id, local_attempts, local_found));
            }

            current += step;

            if last_minmax_report.elapsed() >= Duration::from_secs(60) {
                if let (Some(min), Some(max)) = (local_min, local_max) {
                    let _ = tx.send(WorkerMessage::MinMax(thread_id, min, max));
                }
                local_min = None;
                local_max = None;
                last_minmax_report = Instant::now();
            }
        }
    }

    let _ = tx.send(WorkerMessage::Stats(thread_id, local_attempts, local_found));
    let _ = tx.send(WorkerMessage::Finished(thread_id));
}

// ========================== model ==========================

fn max_key() -> U256 {
    U256::from_str_radix("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364140", 16).unwrap()
}

fn min_key() -> U256 {
    U256::from(1u64)
}

#[derive(Default, Clone)]
struct ThreadStats {
    attempts: u64,
    found: u32,
}

struct SearchModel {
    config: Config,
    target_hashes: Arc<HashSet<[u8; 20]>>,
    found_keys: Arc<std::sync::Mutex<HashSet<[u8; 32]>>>,
    start_key: U256,
    end_key: U256,
    step: U256,
    running: Arc<AtomicBool>,
    stop_rx: Receiver<()>,
    tx: Sender<WorkerMessage>,
    rx: Receiver<WorkerMessage>,
    handles: Vec<thread::JoinHandle<()>>,
    thread_stats: Vec<ThreadStats>,
    total_attempts: u64,
    total_found: u32,
    state_path: PathBuf,
    last_state_save: Instant,
    range_key: String,
    random_mode: bool,
}

impl SearchModel {
    fn new(config: Config, stop_rx: Receiver<()>) -> Result<Self> {
        let target_hashes = if let Some(bin_path) = &config.hash_bin {
            Self::load_hashes_bin(bin_path)?
        } else if let Some(txt_path) = &config.hash_file {
            Self::load_hashes_text(txt_path)?
        } else {
            bail!("Не указан файл с хешами: используйте --hash-file или --hash-bin");
        };

        let target_hashes = Arc::new(target_hashes);

        let found_keys = Arc::new(std::sync::Mutex::new(HashSet::new()));
        if let Some(ref path) = config.output {
            if let Ok(file) = File::open(path) {
                let reader = BufReader::new(file);
                for line in reader.lines() {
                    let line = line?;
                    let parts: Vec<&str> = line.split('\t').collect();
                    if parts.len() >= 1 {
                        if let Ok(key_bytes) = hex::decode(parts[0]) {
                            if key_bytes.len() == 32 {
                                let mut arr = [0u8; 32];
                                arr.copy_from_slice(&key_bytes);
                                found_keys.lock().unwrap().insert(arr);
                            }
                        }
                    }
                }
                eprintln!("Загружено {} уже найденных ключей из {}", found_keys.lock().unwrap().len(), path);
            }
        }

        let total_keys = max_key() - min_key() + U256::from(1u64);
        let (start_centi, end_centi) = config.range_percent;

        let total_minus_1 = total_keys - U256::from(1u64);
        let divisor = U256::from(10000u64);
        let q = total_minus_1 / divisor;
        let r = total_minus_1 % divisor;

        let start_offset = q * U256::from(start_centi) + (r * U256::from(start_centi)) / divisor;
        let end_offset = q * U256::from(end_centi) + (r * U256::from(end_centi)) / divisor;

        let start_key = min_key() + start_offset;
        let end_key = min_key() + end_offset;

        if start_key > end_key {
            bail!("Внутренняя ошибка: start_key > end_key");
        }

        let range_key = format!("{}-{}", start_centi, end_centi);
        let state_path = PathBuf::from("state.json");
        let running = Arc::new(AtomicBool::new(true));
        let (tx, rx) = unbounded();

        let threads = config.threads;
        let random_mode = config.random;

        Ok(Self {
            config,
            target_hashes,
            found_keys,
            start_key,
            end_key,
            step: U256::from(threads),
            running,
            stop_rx,
            tx,
            rx,
            handles: Vec::new(),
            thread_stats: Vec::new(),
            total_attempts: 0,
            total_found: 0,
            state_path,
            last_state_save: Instant::now(),
            range_key,
            random_mode,
        })
    }

    fn load_hashes_text(path: &str) -> Result<HashSet<[u8; 20]>> {
        let file = File::open(path)?;
        let reader = BufReader::new(file);
        let mut set = HashSet::new();
        let mut lines = 0;
        for line in reader.lines() {
            let line = line?.trim().to_string();
            if line.is_empty() {
                continue;
            }
            if line.len() != 40 {
                bail!("Неверная длина хеша: {} в файле {}", line, path);
            }
            let bytes = hex::decode(&line)?;
            let mut arr = [0u8; 20];
            arr.copy_from_slice(&bytes);
            set.insert(arr);
            lines += 1;
        }
        eprintln!("Загружено {} хешей из текстового файла {}", lines, path);
        Ok(set)
    }

    fn load_hashes_bin(path: &str) -> Result<HashSet<[u8; 20]>> {
        let mut file = File::open(path)?;
        let metadata = file.metadata()?;
        let file_size = metadata.len();
        if file_size % 20 != 0 {
            bail!("Размер бинарного файла {} не кратен 20 байтам", path);
        }
        let num_hashes = (file_size / 20) as usize;
        let mut set = HashSet::with_capacity(num_hashes);
        let mut buffer = vec![0u8; file_size as usize];
        file.read_exact(&mut buffer)?;
        for chunk in buffer.chunks_exact(20) {
            let mut arr = [0u8; 20];
            arr.copy_from_slice(chunk);
            set.insert(arr);
        }
        eprintln!("Загружено {} хешей из бинарного файла {}", num_hashes, path);
        Ok(set)
    }

    fn load_state_for_current_range(&self) -> Result<Option<State>> {
        if !self.state_path.exists() {
            return Ok(None);
        }
        let file = File::open(&self.state_path)?;
        let map: StateMap = serde_json::from_reader(file)?;
        Ok(map.get(&self.range_key).cloned())
    }

    fn save_state(&self) -> Result<()> {
        if self.random_mode {
            return Ok(());
        }
        let mut map: StateMap = if self.state_path.exists() {
            let file = File::open(&self.state_path)?;
            serde_json::from_reader(file).unwrap_or_default()
        } else {
            HashMap::new()
        };

        let num_threads = self.config.threads;
        let mut next_positions = Vec::with_capacity(num_threads);
        for i in 0..num_threads {
            let attempts = self.thread_stats.get(i).map(|s| s.attempts).unwrap_or(0);
            let start_for_thread = self.start_key + U256::from(i);
            let next_key = start_for_thread + U256::from(attempts) * self.step;
            next_positions.push(next_key);
        }

        let state = State {
            range_start: self.start_key,
            range_end: self.end_key,
            thread_positions: next_positions,
            total_attempts: self.total_attempts,
            total_found: self.total_found,
            timestamp: Utc::now(),
        };

        map.insert(self.range_key.clone(), state);

        let file = File::create(&self.state_path)?;
        serde_json::to_writer_pretty(file, &map)?;
        Ok(())
    }

    fn run(&mut self) -> Result<()> {
        let num_threads = self.config.threads;
        let mut thread_positions = Vec::with_capacity(num_threads);

        if self.random_mode {
            if self.config.resume {
                eprintln!("Предупреждение: флаг --resume игнорируется в случайном режиме.");
            }
            eprintln!("Запущен случайный перебор ключей в диапазоне [{}, {}]", self.start_key, self.end_key);
            for _ in 0..num_threads {
                thread_positions.push(self.start_key);
            }
        } else {
            if self.config.resume {
                if let Some(state) = self.load_state_for_current_range()? {
                    if state.range_start != self.start_key || state.range_end != self.end_key {
                        eprintln!("Предупреждение: сохранённый диапазон не совпадает с текущим. Начинаем сначала.");
                        for i in 0..num_threads {
                            thread_positions.push(self.start_key + U256::from(i));
                        }
                    } else {
                        self.total_attempts = state.total_attempts;
                        self.total_found = state.total_found;

                        if state.thread_positions.len() == num_threads {
                            thread_positions = state.thread_positions;
                            eprintln!("Восстановлено состояние: проверено {} ключей, найдено {} совпадений",
                                      self.total_attempts, self.total_found);
                        } else {
                            let min_pos = state.thread_positions.iter().min().unwrap_or(&self.start_key).clone();
                            eprintln!(
                                "Предупреждение: сохранённое состояние использует {} поток(а), а текущее — {}.\n\
                                 Продолжаем с минимального сохранённого ключа: {}. Это может привести к повторной проверке некоторых ключей. Дубликаты не будут записаны.",
                                state.thread_positions.len(), num_threads, min_pos
                            );
                            for i in 0..num_threads {
                                thread_positions.push(min_pos + U256::from(i));
                            }
                            self.total_attempts = 0;
                        }
                    }
                } else {
                    eprintln!("Предупреждение: нет сохранённого состояния для текущего диапазона. Начинаем сначала.");
                    for i in 0..num_threads {
                        thread_positions.push(self.start_key + U256::from(i));
                    }
                }
            } else {
                for i in 0..num_threads {
                    thread_positions.push(self.start_key + U256::from(i));
                }
            }
        }

        for i in 0..num_threads {
            let start = if self.random_mode {
                self.start_key
            } else {
                thread_positions[i]
            };
            let end = self.end_key;
            let step = self.step;
            let running = self.running.clone();
            let tx = self.tx.clone();
            let target_hashes = self.target_hashes.clone();
            let random_mode = self.random_mode;

            let handle = thread::spawn(move || {
                worker_main(i, start, end, step, running, tx, target_hashes, random_mode);
            });
            self.handles.push(handle);
            self.thread_stats.push(ThreadStats::default());
        }

        let start_time = Instant::now();
        let mut last_report = Instant::now();
        let mut last_minmax_display = Instant::now();
        self.last_state_save = Instant::now();

        let mut global_min: Option<U256> = None;
        let mut global_max: Option<U256> = None;
        let mut period_attempts: u64 = 0;

        loop {
            select! {
                recv(self.rx) -> msg => {
                    match msg {
                        Ok(WorkerMessage::Stats(thread_id, attempts, found)) => {
                            let old_attempts = self.thread_stats[thread_id].attempts;
                            self.thread_stats[thread_id].attempts = attempts;
                            self.thread_stats[thread_id].found = found;
                            period_attempts += attempts - old_attempts;
                            self.recalc_totals();
                        }
                        Ok(WorkerMessage::Match(thread_id, key_bytes, hash160, addr_type)) => {
                            let mut found_keys = self.found_keys.lock().unwrap();
                            if !found_keys.contains(&key_bytes) {
                                found_keys.insert(key_bytes);
                                drop(found_keys);

                                if let Ok(addresses) = generate_addresses(&key_bytes) {
                                    if let Err(e) = self.save_match(&addresses) {
                                        eprintln!("Ошибка сохранения совпадения: {}", e);
                                    }
                                }
                                self.total_found += 1;
                                self.thread_stats[thread_id].found += 1;
                                println!(
                                    "\nНайден новый ключ: {} (тип: {}, хеш: {})",
                                    hex::encode(key_bytes),
                                    addr_type,
                                    hex::encode(hash160)
                                );
                            } else {
                                println!(
                                    "\n[Повтор] Ключ {} уже найден, пропускаем запись.",
                                    hex::encode(key_bytes)
                                );
                            }
                        }
                        Ok(WorkerMessage::MinMax(_thread_id, min_key, max_key)) => {
                            global_min = Some(global_min.map_or(min_key, |g| if min_key < g { min_key } else { g }));
                            global_max = Some(global_max.map_or(max_key, |g| if max_key > g { max_key } else { g }));
                        }
                        Ok(WorkerMessage::Finished(_thread_id)) => {}
                        Err(_) => break,
                    }
                }
                recv(self.stop_rx) -> _ => {
                    self.running.store(false, Ordering::SeqCst);
                    eprintln!("\nОстанавливаем потоки...");
                    break;
                }
            }

            if !self.running.load(Ordering::SeqCst) {
                break;
            }

            if last_report.elapsed() >= Duration::from_secs(13) {
                self.print_stats(start_time.elapsed());
                last_report = Instant::now();
            }

            if !self.random_mode && self.last_state_save.elapsed() >= Duration::from_secs(10) {
                if let Err(e) = self.save_state() {
                    eprintln!("Ошибка сохранения состояния: {}", e);
                }
                self.last_state_save = Instant::now();
            }

            if last_minmax_display.elapsed() >= Duration::from_secs(60) {
                if let (Some(min), Some(max)) = (global_min, global_max) {
                    println!(
                        "\n📊 Статистика за минуту:\n   Минимальный ключ: {}\n   Максимальный ключ: {}\n   Всего ключей за минуту: {}",
                        hex::encode(u256_to_bytes(min)),
                        hex::encode(u256_to_bytes(max)),
                        period_attempts
                    );
                } else {
                    println!("\n📊 Статистика за минуту: нет данных (возможно, мало ключей)");
                }
                global_min = None;
                global_max = None;
                period_attempts = 0;
                last_minmax_display = Instant::now();
            }
        }

        for handle in self.handles.drain(..) {
            handle.join().unwrap();
        }

        if !self.random_mode {
            self.save_state()?;
        }
        self.print_final_stats(start_time.elapsed());

        Ok(())
    }

    fn recalc_totals(&mut self) {
        self.total_attempts = self.thread_stats.iter().map(|s| s.attempts).sum();
        self.total_found = self.thread_stats.iter().map(|s| s.found).sum();
    }

    fn print_stats(&self, elapsed: Duration) {
        let speed = if elapsed.as_secs() > 0 {
            self.total_attempts as f64 / elapsed.as_secs_f64()
        } else {
            0.0
        };
        let mode = if self.random_mode { "случайный" } else { "последовательный" };
        println!(
            "\r[{}] {} режим. Ключей: {}, Найдено: {}, Скорость: {:.0} к/с",
            humantime::format_duration(elapsed),
            mode,
            self.total_attempts,
            self.total_found,
            speed
        );
    }

    fn print_final_stats(&self, elapsed: Duration) {
        let speed = if elapsed.as_secs() > 0 {
            self.total_attempts as f64 / elapsed.as_secs_f64()
        } else {
            0.0
        };
        let mode = if self.random_mode { "случайный" } else { "последовательный" };
        println!("\nЗавершено ({}). Всего ключей: {}, Найдено: {}, Время: {}, Ср. скорость: {:.0} к/с",
                 mode, self.total_attempts, self.total_found, humantime::format_duration(elapsed), speed);
    }

    fn save_match(&self, addresses: &(String, String, String, String, String, String, String)) -> Result<()> {
        let line = format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            addresses.0, addresses.1, addresses.2, addresses.3, addresses.4, addresses.5, addresses.6
        );
        if let Some(ref output_path) = self.config.output {
            let mut file = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(output_path)?;
            file.write_all(line.as_bytes())?;
        } else {
            print!("{}", line);
        }
        Ok(())
    }
}

// ========================== main ==========================

fn main() -> Result<()> {
    let config = Config::parse();

    let (stop_tx, stop_rx) = crossbeam_channel::bounded(1);
    let r = stop_tx.clone();
    ctrlc::set_handler(move || {
        let _ = r.send(());
        eprintln!("\nПолучен сигнал завершения, сохраняем состояние...");
    })?;

    let mut model = SearchModel::new(config, stop_rx)?;

    let model_handle = thread::spawn(move || {
        if let Err(e) = model.run() {
            eprintln!("Ошибка выполнения: {}", e);
        }
    });

    model_handle.join().unwrap();
    Ok(())
}