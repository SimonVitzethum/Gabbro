//! **Wie tief darf eine Schachtelung sein, bevor der Stapel reisst?**
//!
//! *Der erste Anlauf mass `gabbro_syntax::lies` -- also den PARSER ALLEIN* -- und kam auf
//! 384/512. Die Giftprobe faellt aber durch `pruefe-beweise`s Testlaeufer, und der fuehrt
//! **Parser UND Pruefer**: jeder Pass steigt noch einmal ueber denselben Baum. Bei 128 starb
//! er. *Ein Messwerkzeug, das die halbe Kette misst, misst die falsche Zahl.*
//!
//! Gemessen wird deshalb hier, was der Test tut, auf dem Stapel, den der Test hat.
fn main() {
    let arg: usize = std::env::args().nth(1).unwrap().parse().unwrap();
    let kib: usize = std::env::args().nth(2).map(|s| s.parse().unwrap()).unwrap_or(2048);
    let q = format!(
        "module d {{ impl fn f() -> u32 effects {{ pure }} costs <= 1 ops {{ return {}1{}; }} }}",
        "(".repeat(arg), ")".repeat(arg));
    // 2 MiB ist der Vorgabewert eines Rust-Testfadens -- der kleinste Stapel, auf dem der
    // Pruefer laufen soll.
    let h = std::thread::Builder::new().stack_size(kib * 1024)
        .spawn(move || {
            let (baum, mut absagen) = gabbro_syntax::lies("probe.gab", &q);
            let _ = gabbro_check::pruefe(&baum, &mut absagen);
        })
        .unwrap();
    h.join().unwrap();
    println!("{arg} @ {kib} KiB ok");
}
