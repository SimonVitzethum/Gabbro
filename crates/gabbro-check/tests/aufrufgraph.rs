//! **R14 fuer den Aufrufgraphen: er beweist zuerst, dass er messen kann.**
//!
//! Vor der ersten abgeleiteten Zahl: (a) die Aufloesung findet, was sie finden soll, und
//! (b) jede Zusicherung haengt nachweislich am Pruefling -- aendert man den Gerufenen, kippt
//! sie. Ohne (b) ist eine gruene Probe nur ein gruener Bildschirm.

use gabbro_check::aufrufgraph;

/// **Die Schluessel sind qualifiziert** (2026-08-19). Ein Test, der `huelle("oben")` sagt,
/// misst nicht mehr, was er zu messen glaubt -- `t::oben` ist der Name.
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
    let h = graph(q).huelle("t::oben");
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
    let h = graph(q).huelle("t::oben");
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
    let h = graph(q).huelle("t::a");
    assert!(
        h.unvollstaendig.as_deref().is_some_and(|s| s.contains("cycle")),
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
    let h = graph(q).huelle("t::oben");
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
    assert_eq!(g.verlangt("t::exklusiv"), &[("L".to_string(), false)][..], "exklusiv");
    assert_eq!(g.verlangt("t::geteilt"), &[("L".to_string(), true)][..], "geteilt");
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
        text.contains("undecidable"),
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
    let h = graph(q).huelle("t::schalte");
    assert!(h.unvollstaendig.is_none(), "der Uebergang ist bekannt: {:?}", h.unvollstaendig);
    assert!(h.wirkungen.contains("writes G"), "seine Wirkung kommt an: {:?}", h.wirkungen);
}

// -- Die Sammelseite: sechs Anweisungsklassen, und keine war je angesehen ----------------
//
// **`huelle` war gepruft, `sammle_rufe` nicht.** Die sieben Proben oben rufen ausschliesslich
// auf der obersten Rumpfebene. Ein Ruf in einem `match`-Zweig, in einem `locks`-Block oder in
// einem Schleifenrumpf haette stillschweigend fehlen koennen -- und dann deckt `effects` genau
// die Aufrufe, die niemand versteckt hat.
//
// *Genau diese Form steht im Korpus:* `delete_leaf` ruft `free_region`, `push_dma` und
// `push_reply` in drei `match`-Zweigen (`FRAGMENTE.md`:277-279).

#[test]
fn ein_ruf_im_match_zweig_kommt_in_der_huelle_an() {
    let q = "module t {
tagged type A = { Eins(u32), Zwei(u32) };
extern fn tief(p : ptr<normal, rw> T) effects { masks IRQ } costs <= 1 ops;
impl fn oben(p : ptr<normal, rw> T, a : A) effects { pure } costs <= 8 ops
{ match a { Eins(x) => { tief(p); } Zwei(y) => { } } }
}";
    let h = graph(q).huelle("t::oben");
    assert!(
        h.wirkungen.contains("masks IRQ"),
        "ein Ruf in einem `match`-Zweig ist ein Ruf: {:?}",
        h.wirkungen
    );
}

#[test]
fn ein_ruf_unter_locks_und_in_einer_schleife_kommt_an() {
    let q = "module t {
lock L protects { a } rank 0 held <= 8 ops;
extern fn tief(p : ptr<normal, rw> T) effects { masks IRQ } costs <= 1 ops;
impl fn oben(p : ptr<normal, rw> T) effects { pure } costs <= 8 ops
{ locks L { traverse s over slots of p by unvisited { tief(p); } } }
}";
    let h = graph(q).huelle("t::oben");
    assert!(
        h.wirkungen.contains("masks IRQ"),
        "weder ein `locks`-Block noch ein Schleifenrumpf versteckt einen Ruf: {:?}",
        h.wirkungen
    );
}

#[test]
fn some_und_none_sind_konstruktoren_und_keine_gerufenen() {
    // «B35»: `option` hatte keinen Konstruktor, und der Bestand schreibt ihn seit jeher.
    // Zaehlt der Graph `Some` als Ruf, ist er dem Graphen unbekannt -- und JEDE Huelle ueber
    // einer Tabelle mit `option`-Feld wird zur unteren Schranke. Eine Luecke im GRAPHEN,
    // nicht im Programm, und zwar dieselbe Klasse wie beim `transition`.
    let q = "module t {
table T count 8 { slot { eltern : option index into T, } }
impl fn setze(p : ptr<normal, rw> T, i : index into T) effects { writes p.slots } costs <= 4 ops
{ p.slots[i].eltern = None; }
}";
    let h = graph(q).huelle("t::setze");
    assert!(
        h.unvollstaendig.is_none(),
        "`None` ist ein Konstruktor, kein unbekannter Gerufener: {:?}",
        h.unvollstaendig
    );
}

#[test]
fn zwei_gleichnamige_in_zwei_modulen_sind_zwei_funktionen() {
    // **Der Fund vom 2026-08-19, als Probe.** Bis dahin war der Schluessel der KURZE Name:
    // `boese::hilf` und `harmlos::hilf` waren EIN Knoten, und welcher gewann, entschied die
    // Reihenfolge im Quelltext. Gemessen ergab dieselbe Datei einmal 0 Fehler fuer ein
    // `pure`, das etwas Schreibendes ruft, und einmal drei -- davon einer an der FALSCHEN
    // Funktion.
    let q = "module boese {
impl fn hilf() effects { masks IRQ } costs <= 900 ops { }
}
module harmlos {
impl fn hilf() effects { pure } costs <= 1 ops { }
impl fn ruft() effects { pure } costs <= 8 ops { hilf(); }
}";
    let g = graph(q);
    // Beide stehen im Graphen, unter ihren eigenen Namen.
    assert!(g.knoten.contains_key("boese::hilf"), "{:?}", g.knoten.keys());
    assert!(g.knoten.contains_key("harmlos::hilf"), "{:?}", g.knoten.keys());
    // Und der Ruf im HARMLOSEN Modul trifft den harmlosen Nachbarn.
    let h = g.huelle("harmlos::ruft");
    assert!(
        !h.wirkungen.contains("masks IRQ"),
        "ein `hilf` im eigenen Modul ist naeher als ein gleichnamiges in einem fremden: {:?}",
        h.wirkungen
    );
    // **Die Gegenprobe, sonst ist gruen nur gruen** (R14b): der QUALIFIZIERTE Ruf trifft.
    let q2 = q.replace("{ hilf(); }", "{ boese::hilf(); }");
    let h2 = graph(&q2).huelle("harmlos::ruft");
    assert!(
        h2.wirkungen.contains("masks IRQ"),
        "wer `boese::hilf` schreibt, ruft `boese::hilf`: {:?}",
        h2.wirkungen
    );
}
