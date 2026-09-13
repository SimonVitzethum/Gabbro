//! **Device carriers (`depends`, lane 140) in both directions.**
//!
//! The file-level twin of the gift probes: `beispiele/gift/925`-`929` pin the
//! fall over files, what stands here pins it over snippets -- poison and
//! positive twin side by side, so a rule that goes silent fails here even
//! where the gift corpus has no file for the shape. The locks-block shape
//! (`locks Sperre { … }` without `requires Held`) has no gift file of its
//! own: it lives here, beside the rule whose signature-only reading it pins.

use gabbro_syntax::diag::Stufe;

fn fehler(quelle: &str) -> Vec<String> {
    let (baum, mut absagen) = gabbro_syntax::lies("geraetetraeger", quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect()
}

const KOPF: &str = "module test::geraetetraeger {\n\
    table Zustand count 4 {\n\
        slot { bereit : u32, }\n\
    }\n\
    lock Sperre protects { Zustand } rank 0;\n\
    device Geraet(basis : u64) at mmio {\n";

const SCHREIBER: &str = "    }\n\
    impl fn lesen(d : Geraet) -> u32\n\
        REQUIRES\n\
        effects { reads d }\n\
        costs <= 8 ops\n\
    {\n\
        let stand = d.ST;\n\
        return stand;\n\
    }\n\
    impl fn schreiben(i : index into Zustand, w : u32) -> u32\n\
        requires Held(Sperre)\n\
        effects { writes Zustand }\n\
        costs <= 8 ops\n\
    {\n\
        Zustand.slots[i].bereit = w;\n\
        return 0;\n\
    }\n\
    }\n";

fn einheit(regzeile: &str, requires: &str) -> String {
    format!(
        "{KOPF}\
        reg ST : u32 @0x00 class r{regzeile}\n\
        {SCHREIBER}",
    )
    .replace("REQUIRES", requires)
}

#[test]
fn n255_faellt_allein() {
    let codes = einheit(
        " depends { gibt_es_nicht }",
        "requires Held(Sperre)",
    );
    assert_eq!(
        fehler(&codes),
        vec!["N255"],
        "an unknown carrier draws exactly N255"
    );
}

#[test]
fn n257_faellt_allein() {
    let codes = einheit(" depends { Sperre }", "requires Held(Sperre)");
    assert_eq!(
        fehler(&codes),
        vec!["N257"],
        "a declared non-carrier draws exactly N257"
    );
}

#[test]
fn n258_faellt_allein() {
    let codes = einheit(" depends { Zustand.bereit }", "requires Held(Sperre)");
    assert_eq!(
        fehler(&codes),
        vec!["N258"],
        "a slot draws exactly N258, never a silent widening"
    );
}

#[test]
fn n256_ohne_wache_faellt_allein() {
    let codes = einheit(" depends { Zustand }", "");
    assert_eq!(
        fehler(&codes),
        vec!["N256"],
        "a reader with no guard draws exactly N256"
    );
}

#[test]
fn n256_falsche_wache_faellt() {
    let q = "module test::geraetefalsch {\n\
        table Zustand count 4 {\n\
            slot { bereit : u32, }\n\
        }\n\
        table Fremd count 2 {\n\
            slot { x : u32, }\n\
        }\n\
        lock Sperre protects { Zustand } rank 0;\n\
        lock Anderes protects { Fremd } rank 1;\n\
        device Geraet(basis : u64) at mmio {\n\
            reg ST : u32 @0x00 class r depends { Zustand }\n\
        }\n\
        impl fn lesen(d : Geraet) -> u32\n\
            requires Held(Anderes)\n\
            effects { reads d }\n\
            costs <= 8 ops\n\
        {\n\
            let stand = d.ST;\n\
            return stand;\n\
        }\n\
        impl fn schreiben(i : index into Zustand, w : u32) -> u32\n\
            requires Held(Sperre)\n\
            effects { writes Zustand }\n\
            costs <= 8 ops\n\
        {\n\
            Zustand.slots[i].bereit = w;\n\
            return 0;\n\
        }\n\
        }\n";
    assert_eq!(
        fehler(q),
        vec!["N256"],
        "a guard over the wrong carrier is no guard"
    );
}

#[test]
fn n256_sieht_keinen_locks_block() {
    // A lock taken in a `locks` block does not count: the repaired machine
    // has no bare lock steps, so only `requires Held(L)` holds the reader.
    // The effects line declares the taking, so nothing else speaks.
    let q = "module test::geraeteblock {\n\
        table Zustand count 4 {\n\
            slot { bereit : u32, }\n\
        }\n\
        lock Sperre protects { Zustand } rank 0;\n\
        device Geraet(basis : u64) at mmio {\n\
            reg ST : u32 @0x00 class r depends { Zustand }\n\
        }\n\
        impl fn lesen(d : Geraet) -> u32\n\
            effects { reads d, locks Sperre }\n\
            costs <= 8 ops\n\
        {\n\
            locks Sperre {\n\
                let stand = d.ST;\n\
                return stand;\n\
            }\n\
        }\n\
        impl fn schreiben(i : index into Zustand, w : u32) -> u32\n\
            requires Held(Sperre)\n\
            effects { writes Zustand }\n\
            costs <= 8 ops\n\
        {\n\
            Zustand.slots[i].bereit = w;\n\
            return 0;\n\
        }\n\
        }\n";
    let codes = fehler(q);
    assert_eq!(
        codes,
        vec!["N256"],
        "a locks-block-only reader still falls with N256 alone"
    );
}

#[test]
fn bewachter_leser_schweigt() {
    let codes = fehler(&einheit(" depends { Zustand }", "requires Held(Sperre)"));
    assert!(
        codes.is_empty(),
        "a signature-held guard over a written carrier stays silent: {codes:?}"
    );
}

#[test]
fn unbeschriebener_traeger_schweigt_ohne_wache() {
    // No function writes `Zustand`: the unwritten disjunct holds, no `Held`
    // owed. The writer is gone, so the lock stands untaken -- and an untaken
    // lock is a hint (`H008`), never an error.
    let q = "module test::geraeteruhig {\n\
        table Zustand count 4 {\n\
            slot { bereit : u32, }\n\
        }\n\
        lock Sperre protects { Zustand } rank 0;\n\
        device Geraet(basis : u64) at mmio {\n\
            reg ST : u32 @0x00 class r depends { Zustand }\n\
        }\n\
        impl fn lesen(d : Geraet) -> u32\n\
            effects { reads d }\n\
            costs <= 8 ops\n\
        {\n\
            let stand = d.ST;\n\
            return stand;\n\
        }\n\
        }\n";
    assert!(
        fehler(q).is_empty(),
        "an unwritten carrier needs no guard: {:?}",
        fehler(q)
    );
}
