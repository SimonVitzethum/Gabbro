//! **R14 fuer den Aufrufgraphen: er beweist zuerst, dass er messen kann.**
//!
//! Vor der ersten abgeleiteten Zahl: (a) die Aufloesung findet, was sie finden soll, und
//! (b) jede Zusicherung haengt nachweislich am Pruefling -- aendert man den Gerufenen, kippt
//! sie. Ohne (b) ist eine gruene Probe nur ein gruener Bildschirm.

use gabbro_check::aufrufgraph;

fn graph(q: &str) -> aufrufgraph::Graph {
    aufrufgraph::erhebe(&gabbro_syntax::lies("probe.gab", q).0)
}

#[test]
fn die_huelle_schliesst_die_wirkungen_der_gerufenen_ein() {
    let q = "module t {
extern fn tief(p : ptr<normal, rw> T) effects { writes p.slots } costs <= 1 ops;
impl fn mitte(p : ptr<normal, rw> T) effects { writes p.slots } costs <= 4 ops { tief(p); }
impl fn oben(p : ptr<normal, rw> T) effects { writes p.slots } costs <= 8 ops { mitte(p); }
}";
    let h = graph(q).huelle("oben");
    assert!(h.wirkungen.contains("writes p.slots"), "{:?}", h.wirkungen);
    assert!(h.unvollstaendig.is_none(), "kein Zyklus, keine Luecke: {:?}", h.unvollstaendig);
}

#[test]
fn eine_wirkung_zwei_ebenen_tiefer_kommt_oben_an() {
    // **Die Probe haengt am Pruefling** (R14b): nur der GERUFENE nennt `masks`, der Rufer
    // nicht. Faellt die Hülle auf die erste Ebene zurück, verschwindet die Wirkung.
    let q = "module t {
extern fn ganz_tief() effects { masks IRQ } costs <= 1 ops;
impl fn mitte() effects { pure } costs <= 4 ops { ganz_tief(); }
impl fn oben() effects { pure } costs <= 8 ops { mitte(); }
}";
    let h = graph(q).huelle("oben");
    assert!(
        h.wirkungen.contains("masks IRQ"),
        "zwei Ebenen tiefer und trotzdem sichtbar -- sonst deckt `effects` nur die erste: {:?}",
        h.wirkungen
    );
}

#[test]
fn ein_zyklus_endet_und_sagt_dass_er_einer_war() {
    let q = "module t {
impl fn a() effects { pure } costs <= 4 ops { b(); }
impl fn b() effects { pure } costs <= 4 ops { a(); }
}";
    let h = graph(q).huelle("a");
    assert!(
        h.unvollstaendig.as_deref().is_some_and(|s| s.contains("Zyklus")),
        "ein Zyklus liefert eine UNTERE SCHRANKE und heisst so: {:?}",
        h.unvollstaendig
    );
}

#[test]
fn ein_gerufener_ohne_effects_macht_die_menge_zur_unteren_schranke() {
    let q = "module t {
spec fn stumm() -> bool { true }
impl fn oben() effects { pure } costs <= 4 ops { stumm(); }
}";
    let h = graph(q).huelle("oben");
    assert!(
        h.unvollstaendig.is_some(),
        "ohne `effects` beim Gerufenen ist nichts ableitbar -- das muss dastehen"
    );
}

#[test]
fn held_wird_mit_seiner_staerke_erkannt() {
    let q = "module t {
lock L protects { a } rank 0 held <= 8 ops shared held <= 8 ops;
impl fn exklusiv(p : ptr<normal, rw> T) requires Held(L) effects { writes p.slots } costs <= 1 ops { }
impl fn geteilt(p : ptr<normal, r> T) requires Held(L, shared) effects { reads p.slots } costs <= 1 ops { }
}";
    let g = graph(q);
    assert_eq!(g.verlangt("exklusiv"), &[("L".to_string(), false)][..], "exklusiv");
    assert_eq!(g.verlangt("geteilt"), &[("L".to_string(), true)][..], "geteilt");
}

#[test]
fn ein_zyklus_bestaetigt_pure_nicht_still() {
    // **Die gefaehrlichste Stelle des ganzen Passes.** Beide Funktionen erklaeren `pure` und
    // rufen transitiv etwas Schreibendes -- ueber einen Zyklus. Aus einer unteren Schranke
    // wird nicht abgesagt (R16); wuerde sie deshalb still DURCHGELASSEN, waere das die
    // Ausweg-Zusicherung aus R15 durch die Hintertuer: erfuellt, weil nichts passiert ist.
    //
    // Der ehrliche dritte Zustand heisst `E009` und ist sichtbar, nicht gruen.
    let q = "module t {
extern fn schreibt(p : ptr<normal, rw> T) effects { writes p.slots } costs <= 1 ops;
impl fn a(p : ptr<normal, rw> T) effects { pure } costs <= 99 ops { b(p); }
impl fn b(p : ptr<normal, rw> T) effects { pure } costs <= 99 ops { a(p); schreibt(p); }
}";
    let mut absagen = gabbro_syntax::diag::Absagen::neu("probe.gab");
    gabbro_check::pruefe(&gabbro_syntax::lies("probe.gab", q).0, &mut absagen);
    let text = absagen.zeige(q);
    assert!(
        text.contains("E009"),
        "eine `pure`-Zusage hinter einem Zyklus darf nicht still durchgehen:\n{text}"
    );
    assert!(
        text.contains("unentscheidbar"),
        "der dritte Zustand muss beim Namen genannt werden:\n{text}"
    );
}

#[test]
fn ein_uebergang_ist_ein_gerufener_mit_wirkungen() {
    // Ohne diese Kante meldete der Graph `unbekannt` und der dritte Zustand feuerte an einer
    // Stelle, an der alles erklaert war -- eine Luecke im GRAPHEN, nicht im Programm.
    let q = "module t {
device D(basis : u64) at mmio {
    reg G : u32 @0x0 class rw fields { TE @31, }
    transition an { G.TE: 0 -> 1 } effects { writes G }
}
impl fn schalte(d : ptr<mmio, rw> D) effects { writes d.G } costs <= 4 ops { an(d); }
}";
    let h = graph(q).huelle("schalte");
    assert!(h.unvollstaendig.is_none(), "der Uebergang ist bekannt: {:?}", h.unvollstaendig);
    assert!(h.wirkungen.contains("writes G"), "seine Wirkung kommt an: {:?}", h.wirkungen);
}
