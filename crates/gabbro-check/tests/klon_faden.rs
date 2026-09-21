//! **The `child` path as its own thread** (fix lane F3, review G11 F2-F4, 2026-09-21).
//!
//! Poison and positive twins for the four repairs:
//!
//! * `N456` -- a child holds nothing the parent holds (no `child` under `locks`,
//!   `observes`, `breaking` or a signature-held lock), and the held-set walkers start
//!   the child empty (`H007` fires on the review's scenario);
//! * `N457` -- the child path is a thread for race freedom (touched carriers that
//!   anyone writes are guarded, atomic or per-core), through calls too;
//! * `N451` -- the spill read set is exhaustive (`grow … else`, lock places);
//! * `N450` -- one dominating gate call per region.
//!
//! And the pin for the lowering lane (258): `C185` carries the "child entered by
//! jump" assumption, and the day a lowering lifts it this file asks for the
//! assumption to be kept or re-checked.

use gabbro_syntax::diag::Stufe;

const KOPF: &str = r#"reason UebergabeFehler {
    KeinStapel = 1 "no stack was handed"
    exhaustive
}

assume faden_start_vertrag
    "The starter keeps its contract on this machine."
    falsifier sonde_faden_start;

syscall roher_start(art : u64, stapel : u64) -> u64 or UebergabeFehler
    abi linux arch x86_64 number 1000
    regs in { rdi = art, rsi = stapel }
    regs out { rax }
    stack rsi
    clobbers { rcx, r11 }
    errors { NSTACK => KeinStapel }
    effects { pure }
    costs <= 64 ops
    assume faden_start_vertrag falsifier sonde_faden_start;

extern fn ausgang(code : u64) -> never effects { diverges } costs <= 1 ops;"#;

fn codes(rumpf: &str) -> Vec<String> {
    let quelle = format!("module t {{\n{KOPF}\n{rumpf}\n}}\n");
    let (baum, mut absagen) = gabbro_syntax::lies("klon_faden", &quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect()
}

fn faellt(rumpf: &str, code: &str) {
    let c = codes(rumpf);
    assert!(c.iter().any(|x| x == code), "expected {code}, fell with {c:?}");
}

fn sauber(rumpf: &str) {
    let c = codes(rumpf);
    assert!(c.is_empty(), "the positive twin must check clean, fell with {c:?}");
}

const SPERRE: &str = "static mut g : u64 = 0;\nlock L protects { g } rank 0 held <= 100 ops;\n";

// ---- N456 / H007: the child holds nothing ----------------------------------------

#[test]
fn n456_kind_unter_locks_faellt_und_h007_sieht_den_kindpfad() {
    let r = format!(
        "{SPERRE}
impl fn starter(art : u64, stapel : u64) -> u64
    effects {{ writes g, locks L, diverges }}
{{
    let v = roher_start(art, stapel) else (e) {{ return 999; }}
    locks L {{
        g = 1;
        child {{
            g = 2;
            ausgang(0);
        }}
    }}
    return v;
}}"
    );
    faellt(&r, "N456");
    faellt(&r, "H007");
}

#[test]
fn n456_kind_unter_signatursperre_faellt() {
    faellt(
        &format!(
            "{SPERRE}
impl fn starter(art : u64, stapel : u64) -> u64
    requires Held(L)
    effects {{ reads g, diverges }}
{{
    let v = roher_start(art, stapel) else (e) {{ return 999; }}
    if v == 0 {{
        child {{ ausgang(0); }}
    }}
    return g;
}}"
        ),
        "N456",
    );
}

/// **The `effects { locks L }` line is no cover on the child path.** No `N456` here
/// (the line is no holding context), but `H007` must see the unguarded child write.
#[test]
fn h007_effects_zeile_deckt_den_kindpfad_nicht() {
    let c = codes(&format!(
        "{SPERRE}
impl fn starter(art : u64, stapel : u64) -> u64
    effects {{ writes g, locks L, diverges }}
{{
    let v = roher_start(art, stapel) else (e) {{ return 999; }}
    if v == 0 {{
        child {{
            g = 2;
            ausgang(0);
        }}
    }}
    locks L {{ g = 1; }}
    return v;
}}"
    ));
    assert!(c.iter().any(|x| x == "H007"), "fell with {c:?}");
    assert!(!c.iter().any(|x| x == "N456"), "fell with {c:?}");
}

/// Positive twin of all three above: the child takes the lock ITSELF.
#[test]
fn kind_mit_eigener_sperre_ist_sauber() {
    sauber(&format!(
        "{SPERRE}
impl fn starter(art : u64, stapel : u64) -> u64
    effects {{ writes g, locks L, diverges }}
{{
    let v = roher_start(art, stapel) else (e) {{ return 999; }}
    if v == 0 {{
        child {{
            locks L {{ g = stapel; }}
            ausgang(0);
        }}
    }}
    locks L {{ g = 1; }}
    return v;
}}"
    ));
}

// ---- N457: the child is a thread for race freedom ---------------------------------

#[test]
fn n457_kind_schreibt_ungeschuetzt() {
    faellt(
        "static mut g : u64 = 0;
impl fn starter(art : u64, stapel : u64) -> u64
    effects { writes g, diverges }
{
    let v = roher_start(art, stapel) else (e) { return 999; }
    if v == 0 {
        child { g = 2; ausgang(0); }
    }
    g = 3;
    return v;
}",
        "N457",
    );
}

#[test]
fn n457_kind_schreibt_durch_einen_ruf() {
    faellt(
        "static mut g : u64 = 0;
impl fn setze(x : u64) effects { writes g } { g = x; }
impl fn starter(art : u64, stapel : u64) -> u64
    effects { writes g, diverges }
{
    let v = roher_start(art, stapel) else (e) { return 999; }
    if v == 0 {
        child { setze(2); ausgang(0); }
    }
    return v;
}",
        "N457",
    );
}

#[test]
fn n457_kind_liest_was_der_elter_schreibt() {
    faellt(
        "static mut g : u64 = 0;
impl fn starter(art : u64, stapel : u64) -> u64
    effects { reads g, writes g, diverges }
{
    let v = roher_start(art, stapel) else (e) { return 999; }
    if v == 0 {
        child { ausgang(g); }
    }
    g = 3;
    return v;
}",
        "N457",
    );
}

/// Positive twin: a carrier NOBODY writes is read-only and races with nothing.
#[test]
fn kind_liest_ungeschriebenes_ist_sauber() {
    sauber(
        "static mut g : u64 = 7;
impl fn starter(art : u64, stapel : u64) -> u64
    effects { reads g, diverges }
{
    let v = roher_start(art, stapel) else (e) { return 999; }
    if v == 0 {
        child { ausgang(g); }
    }
    return v;
}",
    );
}

// ---- N451: the exhaustive read set ------------------------------------------------

#[test]
fn n451_grow_sonst_liest_die_torantwort() {
    faellt(
        "arena A capacity 2 .. 8 max 16 of u16;
impl fn starter(art : u64, stapel : u64) -> u64
    effects { writes A, diverges }
{
    let v = roher_start(art, stapel) else (e) { return 999; }
    if v == 0 {
        child {
            grow A by 1 else { ausgang(v); };
            ausgang(0);
        }
    }
    return v;
}",
        "N451",
    );
}

#[test]
fn n451_sperrindex_liest_einen_aufruferlet() {
    faellt(
        "impl fn starter(art : u64, stapel : u64) -> u64
    effects { diverges }
{
    let w = art;
    let v = roher_start(art, stapel) else (e) { return 999; }
    if v == 0 {
        child {
            locks S[w] { ausgang(1); }
        }
    }
    return v;
}",
        "N451",
    );
}

// ---- N450: one dominating gate call per region ------------------------------------

#[test]
fn n450_tor_in_einer_anderen_funktion() {
    faellt(
        "impl fn vorbereiten(art : u64, stapel : u64) -> u64 effects { pure }
{
    let v = roher_start(art, stapel) else (e) { return 999; }
    return v;
}
impl fn starter(art : u64) -> u64
    effects { diverges }
{
    if art == 0 { child { ausgang(0); } }
    return 1;
}",
        "N450",
    );
}

#[test]
fn n450_zwei_regionen_in_geschwisterzweigen() {
    faellt(
        "impl fn starter(art : u64, stapel : u64) -> u64
    effects { diverges }
{
    let v = roher_start(art, stapel) else (e) { return 999; }
    if v == 0 {
        child { ausgang(0); }
    } else {
        child { ausgang(1); }
    }
    return v;
}",
        "N450",
    );
}

/// Positive twin: two regions, each behind its own call; the second call hands the
/// first answer's slot (`v`), so the second region may read it.
#[test]
fn zwei_regionen_je_mit_eigenem_ruf_sind_sauber() {
    sauber(
        "impl fn starter(art : u64, stapel : u64) -> u64
    effects { diverges }
{
    let v = roher_start(art, stapel) else (e) { return 999; }
    if v == 0 {
        child { ausgang(0); }
    }
    let w = roher_start(art, v) else (e) { return 998; }
    if w == 0 {
        child { ausgang(v); }
    }
    return v;
}",
    );
}

// ---- The lowering assumption, pinned ------------------------------------------------

/// **The pin for lane 258.** `C185` refuses every `child` block and its message
/// carries the assumption the checker's reading rests on: the child is entered by
/// jump AT the region, and the statements between the gate call and the region never
/// run on the child's stack. A lowering that lifts `C185` turns this test red -- and
/// must then keep that reading, or re-check the gap the reading leaves unchecked
/// (SATZKARTE §39).
#[test]
fn c185_traegt_die_sprungannahme() {
    let quelle = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../beispiele/155-kind-uebergabe.gab"
    ))
    .expect("example 155 is readable");
    let (baum, mut absagen) = gabbro_syntax::lies("155", &quelle);
    let _ = gabbro_check::emit::emittiere(&baum, &mut absagen);
    let c185: Vec<String> = absagen
        .absagen
        .iter()
        .filter(|a| a.code == "C185")
        .map(|a| a.text.clone())
        .collect();
    assert_eq!(c185.len(), 1, "every child block falls at C185 by name: {c185:?}");
    assert!(
        c185[0].contains("ASSUMES that jump")
            && c185[0].contains("never run on the child's stack"),
        "C185 must carry the jump assumption: {}",
        c185[0]
    );
}
