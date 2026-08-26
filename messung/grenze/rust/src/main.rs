//! **Der Grenzdurchstich.** Rust ruft eine Gabbro-Einheit ueber `extern "C"`.
//!
//! Vier Fragen, jede mit einem Lauf. Die vierte ist der Pruefstein: Gabbros Rangordnung
//! gibt Verklemmungsfreiheit DURCH KONSTRUKTION, und die Praemisse des Satzes
//! `Passlogik/Rang.lean::keine_verklemmung` lautet
//!
//! ```text
//! rangdisziplin r Z := ∀ t A B, Z.wartet t = some A → Z.haelt t B → r B < r A
//! ```
//!
//! **`∀ t` -- ueber ALLE Faeden.** Gabbro prueft die Faeden, deren Rumpf es sieht. Dieser
//! Pruefstand stellt einen daneben, den es nicht sieht.
#![allow(clippy::missing_safety_doc)]

use std::sync::atomic::{AtomicU64, Ordering};

// ------------------------------------------------------- die Gabbro-Seite, wie sie steht
//
// `pub impl fn` bekommt in C aeussere Bindung; `gabbro abi` schreibt genau diese Koepfe.
// Die Rust-Deklarationen daneben sind VON HAND -- und das ist der erste Befund.

/// Der Verbund, wie der Erzeuger ihn schreibt:
/// `typedef struct { uint32_t marke; bool gueltig; uint64_t breit; uint8_t schmal; } Fach_slot;`
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct FachSlot {
    pub marke: u32,
    pub gueltig: bool,
    pub breit: u64,
    pub schmal: u8,
}

pub const NFAECHER: usize = 8;

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct Fach {
    pub slots: [FachSlot; NFAECHER],
}

extern "C" {
    // aus grenze.gab
    fn rangtreu(i: u32, w: u32);
    fn fremd_schreiben(f: *mut Fach, i: u32, w: u32) -> u32;
    fn lies_marke(f: *const Fach, i: u32) -> u32;
    fn misch(a: *mut Fach, b: *mut Fach, i: u32) -> u32;
    // die Sperren -- vom Erzeuger DEKLARIERT, von der Schale definiert
    fn A_nimm();
    fn A_gib();
    fn B_nimm();
    fn B_gib();
    // aus schale.c
    fn schale_masse(was: i32) -> u64;
    fn schale_merke(f: *mut Fach);
    fn schale_schreibe_gemerkt(i: u32, w: u32);
    fn schale_durch_c_rahmen(zurueck: extern "C" fn()) -> i32;
    fn schale_rendezvous_an();
}

// **Die DRIFTPROBE.** Dieselben vier Felder, zwei vertauscht -- so, wie eine Hand sie
// abschreibt, die die `.gabi` nicht daneben liegen hat. **Nichts im Bau widerspricht:**
// `gabbro abi` schreibt Gabbro-Quelltext, kein Rust; `cc` sieht die Rust-Seite nie; der
// Binder vergleicht Namen, keine Typen. *Der Vertrag ueber die Grenze wird von KEINEM
// Werkzeug gehalten.*
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub struct FachSlotFalsch {
    pub breit: u64,   // <- in der `.gab` steht dieses Feld an DRITTER Stelle
    pub marke: u32,
    pub gueltig: bool,
    pub schmal: u8,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct FachFalsch {
    pub slots: [FachSlotFalsch; NFAECHER],
}

fn driftprobe() -> bool {
    kopf("DRIFTPROBE -- die Rust-Deklaration wird von NICHTS geprueft");
    println!("  C:    sizeof Fach_slot = {}", unsafe { schale_masse(0) });
    println!("  Rust: size_of FachSlotFalsch = {}", std::mem::size_of::<FachSlotFalsch>());
    let mut f = FachFalsch { slots: [FachSlotFalsch::default(); NFAECHER] };
    f.slots[3].marke = 0xDEAD_BEEF;
    // Derselbe Ruf wie in Frage 1 -- nur mit dem falsch abgeschriebenen Verbund.
    let gelesen = unsafe { lies_marke(&f as *const FachFalsch as *const Fach, 3) };
    println!("  Gabbro liest .marke bei Fach 3: {gelesen:#x} (hingelegt: 0xdeadbeef)");
    if gelesen == 0xDEAD_BEEF {
        println!("  zufaellig gleich -- die Feldlage von `.marke` hat sich nicht verschoben");
    } else {
        println!("  **ANDERE ZAHL.** Uebersetzt, gebunden, gelaufen -- und still falsch.");
    }
    println!("  Beide Seiten uebersetzen ohne eine einzige Warnung.");
    true
}

fn kopf(s: &str) {
    println!("\n=================== {s} ===================");
}

// =========================================================================== FRAGE 1
// Reist ein Verbund unveraendert? Groesse, Ausrichtung UND Feldlagen -- beidseitig.

fn frage1() -> bool {
    kopf("FRAGE 1 -- #[repr(C)] auf beiden Seiten");
    let c = |n: i32| unsafe { schale_masse(n) };
    let zeilen: [(&str, u64, u64); 8] = [
        ("sizeof  Fach_slot", c(0), std::mem::size_of::<FachSlot>() as u64),
        ("alignof Fach_slot", c(1), std::mem::align_of::<FachSlot>() as u64),
        ("sizeof  Fach", c(2), std::mem::size_of::<Fach>() as u64),
        ("alignof Fach", c(3), std::mem::align_of::<Fach>() as u64),
        ("offset  .marke", c(4), std::mem::offset_of!(FachSlot, marke) as u64),
        ("offset  .gueltig", c(5), std::mem::offset_of!(FachSlot, gueltig) as u64),
        ("offset  .breit", c(6), std::mem::offset_of!(FachSlot, breit) as u64),
        ("offset  .schmal", c(7), std::mem::offset_of!(FachSlot, schmal) as u64),
    ];
    let mut gut = true;
    println!("  {:<20} {:>8} {:>8}   {}", "", "C", "Rust", "");
    for (name, a, b) in zeilen {
        let ok = a == b;
        gut &= ok;
        println!("  {:<20} {:>8} {:>8}   {}", name, a, b, if ok { "gleich" } else { "VERSCHIEDEN" });
    }
    println!("  NFAECHER (C) = {}, (Rust) = {}", c(8), NFAECHER);
    gut &= c(8) == NFAECHER as u64;

    // **Und nicht nur gerechnet, sondern GELESEN.** Rust legt einen Wert hin, Gabbro liest
    // ihn zurueck -- wer die Feldlage falsch haette, bekaeme hier eine andere Zahl.
    let mut f = Fach { slots: [FachSlot::default(); NFAECHER] };
    f.slots[3].marke = 0xDEAD_BEEF;
    f.slots[3].breit = 0x0102_0304_0506_0708;
    f.slots[3].schmal = 0x7F;
    let gelesen = unsafe { lies_marke(&f as *const Fach, 3) };
    let ok = gelesen == 0xDEAD_BEEF;
    gut &= ok;
    println!("  Rueckgelesen: Gabbro sieht .marke = {:#x} ({})", gelesen,
             if ok { "wie hingelegt" } else { "ANDERS" });
    println!("  --> {}", if gut { "der Verbund reist unveraendert" } else { "ER REIST NICHT" });
    gut
}

// =========================================================================== FRAGE 2
// Wem gehoert die Struktur?

extern "C" fn nichts() {}

fn frage2() -> bool {
    kopf("FRAGE 2 -- wem gehoert die Struktur");
    let mut gut = true;

    // (a) Das saubere Muster: Rust besitzt, gibt einen ROHEN Zeiger heraus, haelt waehrend
    //     des Rufes keine Referenz. Das ist der Fall, der halten MUSS.
    let mut f = Fach { slots: [FachSlot::default(); NFAECHER] };
    let zurueck = unsafe { fremd_schreiben(&mut f as *mut Fach, 1, 4711) };
    let ok_a = zurueck == 4711 && f.slots[1].marke == 4711;
    gut &= ok_a;
    println!("  (a) Rust besitzt, C schreibt durch einen rohen Zeiger:");
    println!("      Rueckgabe {zurueck}, Rust liest {} -- {}", f.slots[1].marke,
             if ok_a { "ok" } else { "FALSCH" });

    // (b) `misch` nimmt ZWEI Zeiger desselben Traegertyps. Der Erzeuger schreibt dort
    //     BEWUSST kein `restrict` (`emit.rs::darf_restrict`, H2a). Rust darf also aliasen.
    let mut g = Fach { slots: [FachSlot::default(); NFAECHER] };
    let p = &mut g as *mut Fach;
    let r = unsafe { misch(p, p, 2) };
    let ok_b = r == 2 && g.slots[2].marke == 2;
    gut &= ok_b;
    println!("  (b) derselbe Zeiger zweimal an `misch` (kein `restrict` emittiert):");
    println!("      Rueckgabe {r}, Speicher {} -- {}", g.slots[2].marke,
             if ok_b { "wie C es vorschreibt" } else { "ABWEICHEND" });

    // (c) **Der Fall, der schiefgeht.** C merkt sich den Zeiger; Rust haelt danach ein
    //     `&mut` auf dasselbe Objekt und ruft C. `&mut` traegt in LLVM `noalias`.
    println!("  (c) C merkt sich den Zeiger, Rust haelt danach ein `&mut`:");
    static mut ABLAGE: Fach = Fach { slots: [FachSlot { marke: 0, gueltig: false, breit: 0, schmal: 0 }; NFAECHER] };
    let roh = std::ptr::addr_of_mut!(ABLAGE);
    unsafe { schale_merke(roh) };
    #[inline(never)]
    fn durch_mut(f: &mut Fach) -> (u32, u32) {
        let vor = f.slots[0].marke;
        // Der Schreibzugriff geht durch den Zeiger, den C sich GEMERKT hat -- er ist
        // NICHT aus `f` abgeleitet. Genau das verbietet `noalias`.
        unsafe { schale_schreibe_gemerkt(0, 0xABCD) };
        let nach = f.slots[0].marke;
        (vor, nach)
    }
    let (vor, nach) = durch_mut(unsafe { &mut *roh });
    println!("      vor dem Ruf {vor:#x}, danach {nach:#x}");
    if nach == 0xABCD {
        println!("      diesmal hat der Uebersetzer NICHT zwischengespeichert --");
        println!("      und das ist kein Beleg, dass er es nicht darf.");
    } else {
        println!("      **DER WERT IST ALT.** `&mut` hiess `noalias`, und der fremde");
        println!("      Schreibzugriff war fuer den Uebersetzer nicht da.");
    }
    // Kein Urteil: beide Ausgaenge sind mit undefiniertem Verhalten vertraeglich.
    println!("      (kein Tor -- der Befund ist die Frage, nicht die Zahl)");

    unsafe { schale_durch_c_rahmen(nichts) };
    gut
}

// =========================================================================== FRAGE 3
// Panik durch einen C-Rahmen.

extern "C" fn platzt() {
    panic!("Rust platzt in einem C-Rahmen");
}

fn frage3() -> bool {
    kopf("FRAGE 3 -- Panik durch einen C-Rahmen");
    println!("  Strategie dieses Baus: {}", if cfg!(panic = "abort") { "abort" } else { "unwind" });
    let r = unsafe { schale_durch_c_rahmen(platzt) };
    println!("  [Rust] zurueck aus dem C-Rahmen, Marke {r:#x}");
    println!("  **DER RAHMEN WURDE VERLASSEN** -- die Panik ist durchgekommen.");
    true
}

// =========================================================================== FRAGE 4
// Die Sperrdisziplin. Der Pruefstein.

static RUNDEN_G: AtomicU64 = AtomicU64::new(0);
static RUNDEN_R: AtomicU64 = AtomicU64::new(0);

/// Der Faden, den Gabbro GESCHRIEBEN hat: `locks A { locks B { … } }`, Rang 1 vor Rang 2.
fn faden_gabbro(n: u64) {
    for i in 0..n {
        unsafe { rangtreu((i % NFAECHER as u64) as u32, i as u32) };
        RUNDEN_G.fetch_add(1, Ordering::Relaxed);
    }
}

/// **Der Faden, den Gabbro NICHT sieht.** Dieselben zwei Sperren, dieselben zwei Symbole.
/// Kein Pass hat diese acht Zeilen je angesehen.
///
/// `rangtreu = false` nimmt sie in der FALSCHEN Reihenfolge -- das ist die Probe.
/// `rangtreu = true` nimmt sie in der richtigen -- das ist die GEGENPROBE, ohne die
/// „verklemmt" nur eine Eigenschaft dieses Pruefstands waere und keine der Grenze.
fn faden_fremd(n: u64, rangtreu_auch: bool) {
    for _ in 0..n {
        unsafe {
            if rangtreu_auch {
                A_nimm();
                B_nimm();
                B_gib();
                A_gib();
            } else {
                B_nimm();
                A_nimm();
                A_gib();
                B_gib();
            }
        }
        RUNDEN_R.fetch_add(1, Ordering::Relaxed);
    }
}

fn frage4(gesteuert: bool, fremd_rangtreu: bool) -> bool {
    kopf(match (gesteuert, fremd_rangtreu) {
        (_, true) => "FRAGE 4c -- GEGENPROBE: der fremde Faden haelt die Rangordnung mit",
        (true, _) => "FRAGE 4b -- die Rangordnung, GESTEUERT (Rendezvous erzwingt die Verschraenkung)",
        (false, _) => "FRAGE 4a -- die Rangordnung, UNGESTEUERT (zwei Faeden, freier Lauf)",
    });
    println!("  Gabbro-Faden: locks A (rank 1) -> locks B (rank 2)   [rangtreu, H006 gruen]");
    if fremd_rangtreu {
        println!("  Fremd-Faden:  A_nimm()        -> B_nimm()            [dieselbe Ordnung]");
    } else {
        println!("  Fremd-Faden:  B_nimm()        -> A_nimm()            [Gabbro sieht ihn nicht]");
    }
    if gesteuert {
        unsafe { schale_rendezvous_an() };
    }
    let n = if gesteuert { 1 } else { 2_000_000 };
    let g = std::thread::spawn(move || faden_gabbro(n));
    let r = std::thread::spawn(move || faden_fremd(n, fremd_rangtreu));

    let start = std::time::Instant::now();
    let frist = std::time::Duration::from_secs(5);
    let mut letzte = (0u64, 0u64);
    let mut still_seit = std::time::Instant::now();
    loop {
        std::thread::sleep(std::time::Duration::from_millis(50));
        let jetzt = (RUNDEN_G.load(Ordering::Relaxed), RUNDEN_R.load(Ordering::Relaxed));
        if g.is_finished() && r.is_finished() {
            println!("  beide Faeden fertig nach {:?} -- G {} Runden, R {} Runden",
                     start.elapsed(), jetzt.0, jetzt.1);
            println!("  --> KEINE VERKLEMMUNG in diesem Lauf. Das ist kein Beweis, dass");
            println!("      keine moeglich ist -- nur, dass sie diesmal nicht eintrat.");
            return true;
        }
        if jetzt != letzte {
            letzte = jetzt;
            still_seit = std::time::Instant::now();
        } else if still_seit.elapsed() > std::time::Duration::from_millis(500) {
            println!("  **VERKLEMMT** nach {:?}", start.elapsed());
            println!("  G stand bei {} Runden, R bei {} -- seither ruehrt sich nichts.",
                     jetzt.0, jetzt.1);
            println!("  Gabbro-Faden haelt A und wartet auf B; Fremd-Faden haelt B und wartet auf A.");
            println!("  --> Der Zyklus, den `keine_verklemmung` ausschliesst. Die Praemisse");
            println!("      `∀ t` gilt fuer den zweiten Faden nicht, und niemand hat es gesagt.");
            return false;
        }
        if start.elapsed() > frist {
            println!("  Frist abgelaufen ohne Stillstand und ohne Ende: G {} / R {}",
                     jetzt.0, jetzt.1);
            return true;
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let was = args.first().map(String::as_str).unwrap_or("alle");
    match was {
        "f1" => { std::process::exit(if frage1() { 0 } else { 1 }); }
        "f2" => { std::process::exit(if frage2() { 0 } else { 1 }); }
        "f3" => { frage3(); std::process::exit(0); }
        "f4a" => { let ok = frage4(false, false); std::process::exit(if ok { 0 } else { 9 }); }
        "f4b" => { let ok = frage4(true, false); std::process::exit(if ok { 0 } else { 9 }); }
        "drift" => { driftprobe(); std::process::exit(0); }
        "f4c" => { let ok = frage4(false, true); std::process::exit(if ok { 0 } else { 9 }); }
        _ => {
            let a = frage1();
            let b = frage2();
            println!("\nFrage 1 {}, Frage 2 {}", if a { "ok" } else { "GEFALLEN" },
                     if b { "ok" } else { "GEFALLEN" });
        }
    }
}
