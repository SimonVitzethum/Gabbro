//! **Bau integration tests live here, not in `bau.rs`.**
//!
//! The unit tests inside `bau.rs` cover the pure half (`schritt_bis`,
//! `pruefe_ungeteilt`, the split round-trips) over hand-built `Bau` values.
//! What stands here is the wired half: `erhebe` over a parsed unit, the
//! Tab/Glob tag over its world members, and the agreement between the W5
//! answer beside `H013` and the `H013` refusal itself. The Bau emits nothing,
//! so these tests assert on the returned value, never on diagnostics -- except
//! the agreement test, which reads the `H013` code the pipeline reports.
use gabbro_check::geteilt::bau;

const ZWEI_FAEDEN: &str = "module test::bausplit {\n\
    static mut z : u32 = 0;\n\
    table T count 4 {\n\
        slot {\n\
            v : u32,\n\
        }\n\
    }\n\
    lock L protects { T } rank 0 held <= 100 ops;\n\
    impl fn tief() effects { writes z } costs <= 4 ops { z = 1; }\n\
    impl fn mitte() effects { writes z } costs <= 8 ops { tief(); }\n\
    impl fn seite() effects { writes z } costs <= 4 ops { z = 2; }\n\
    entry syscall_a vector 0x80 arch x86_64 {\n\
        regs in  { }\n\
        regs out { }\n\
        preserves { rbx }\n\
        clobbers  { rcx }\n\
        stack ka per cpu nested never\n\
        dispatch test::bausplit::mitte;\n\
    }\n\
    entry syscall_b vector 0x81 arch x86_64 {\n\
        regs in  { }\n\
        regs out { }\n\
        preserves { rbx }\n\
        clobbers  { rcx }\n\
        stack kb per cpu nested never\n\
        dispatch test::bausplit::seite;\n\
    }\n\
    }\n";

const RUHIG: &str = "module test::bauruhig {\n\
    table T count 4 {\n\
        slot {\n\
            v : u32,\n\
        }\n\
    }\n\
    lock L protects { T } rank 0 held <= 100 ops;\n\
    impl fn ruhig(j : index into T, m : index into T)\n\
        effects { writes T.slots, locks L }\n\
        costs <= 16 ops\n\
    {\n\
        locks L {\n\
            T.slots[j].v = 0;\n\
            T.slots[m].v = 1;\n\
        }\n\
    }\n\
    entry syscall_a vector 0x80 arch x86_64 {\n\
        regs in  { }\n\
        regs out { }\n\
        preserves { rbx }\n\
        clobbers  { rcx }\n\
        stack ka per cpu nested never\n\
        dispatch test::bauruhig::ruhig;\n\
    }\n\
    }\n";

/// The world as the `H013` section of `geteilt.rs` hands it in: every mutable
/// world member, the guarded places, and the table roots among them (the Tab
/// half of the split; `z` is the Glob half).
fn welt() -> (Vec<String>, Vec<String>, Vec<String>) {
    (
        vec!["z".to_string(), "T".to_string()],
        vec!["T".to_string()],
        vec!["T".to_string()],
    )
}

fn erhebe_aus(quelle: &str, name: &str) -> bau::Bau {
    let (baum, _) = gabbro_syntax::lies(name, quelle);
    let u = gabbro_check::umgebung::Umgebung::sammle(&baum);
    let g = gabbro_check::aufrufgraph::erhebe_mit(&baum, &u);
    let kontexte = gabbro_check::kontexte::erhebe(&baum);
    let (welt, geschuetzt, tabellen) = if name == "bau-zwei-faeden" {
        welt()
    } else {
        (
            vec!["T".to_string()],
            vec!["T".to_string()],
            vec!["T".to_string()],
        )
    };
    bau::erhebe(&baum, &u, &g, &kontexte, &welt, &geschuetzt, &tabellen)
}

#[test]
fn tab_roots_are_tab_globals_are_glob() {
    let b = erhebe_aus(ZWEI_FAEDEN, "bau-zwei-faeden");
    let mut traeger = b.traeger.clone();
    traeger.sort();
    assert_eq!(traeger, ["T", "z"]);
    assert_eq!(b.ist_tab.get("T"), Some(&true));
    assert_eq!(b.ist_tab.get("z"), Some(&false));
}

#[test]
fn split_folds_back_over_every_carrier() {
    let b = erhebe_aus(ZWEI_FAEDEN, "bau-zwei-faeden");
    for c in &b.traeger {
        assert_eq!(bau::falte(&bau::teile(&b, c)), c.as_str());
    }
    assert_eq!(bau::teile(&b, "T"), bau::Seite::Tab("T".to_string()));
    assert_eq!(bau::teile(&b, "z"), bau::Seite::Glob("z".to_string()));
}

#[test]
fn call_edges_and_footprints_come_from_the_bodies() {
    let b = erhebe_aus(ZWEI_FAEDEN, "bau-zwei-faeden");
    assert_eq!(
        b.eintritt,
        vec![
            "test::bausplit::mitte".to_string(),
            "test::bausplit::seite".to_string()
        ]
    );
    // The transitive edge: `mitte` reaches `z` only through `tief`.
    assert_eq!(
        b.ruft.get("test::bausplit::mitte"),
        Some(&vec!["test::bausplit::tief".to_string()])
    );
    assert_eq!(
        b.schreibt_fn.get("test::bausplit::tief"),
        Some(&vec!["z".to_string()])
    );
    assert!(!b.geteilt["z"]);
    assert!(b.geteilt["T"]);
}

#[test]
fn w5_names_the_carrier_h013_refuses() {
    let b = erhebe_aus(ZWEI_FAEDEN, "bau-zwei-faeden");
    // Both entries reach the unshared `z`; the shared `T` never appears.
    assert_eq!(bau::pruefe_ungeteilt(&b, bau::sattigung(&b)), ["z"]);
    let (baum, mut absagen) = gabbro_syntax::lies("bau-zwei-faeden", ZWEI_FAEDEN);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    assert!(
        absagen
            .absagen
            .iter()
            .any(|a| a.code == "H013" && a.text.contains("`z`")),
        "H013 must refuse the same carrier the W5 answer names"
    );
}

#[test]
fn guarded_single_thread_carrier_stays_silent() {
    let b = erhebe_aus(RUHIG, "bau-ruhig");
    assert!(bau::pruefe_ungeteilt(&b, bau::sattigung(&b)).is_empty());
    let (baum, mut absagen) = gabbro_syntax::lies("bau-ruhig", RUHIG);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    assert!(
        !absagen.absagen.iter().any(|a| a.code == "H013"),
        "a guarded carrier under one entry draws neither answer"
    );
}
