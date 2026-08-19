fn main() {
    let arg: usize = std::env::args().nth(1).unwrap().parse().unwrap();
    let q = format!(
        "module d {{ impl fn f() -> u32 effects {{ pure }} costs <= 1 ops {{ return {}1{}; }} }}",
        "(".repeat(arg), ")".repeat(arg));
    // 2 MiB -- der Vorgabewert eines Rust-Testfadens.
    let h = std::thread::Builder::new().stack_size(2 * 1024 * 1024)
        .spawn(move || { let _ = gabbro_syntax::lies("probe.gab", &q); })
        .unwrap();
    h.join().unwrap();
    println!("{arg} ok");
}
