//! **Die Stellen, an denen der Pruefer RECHNET statt abzusagen.**
//!
//! Der erzeugte Mutationslauf vom 2026-08-15 fand fuenfzehn Regelluecken und zeigte, wo sie
//! sitzen: nicht bei den Absagen, sondern bei den **Zahlen**. Sieben sind mit den
//! Wertetabellen in `typen.rs`/`umgebung.rs` geschlossen; diese Datei nimmt sechs weitere,
//! die keine Bereichsarithmetik sind, sondern **Berichte und Modulaufloesung**.
//!
//! Zwei der urspruenglichen fuenfzehn bleiben offen und sind es zu Recht — sie sind
//! **beweisbar aequivalente Mutanten**, s. `typen.rs`, Modul `wertetabellen`.

use gabbro_check::{kbedingung, kosten, schablonen};

fn baum(quelle: &str) -> gabbro_syntax::ast::Programm {
    gabbro_syntax::lies("probe.gab", quelle).0
}

/// Kosten eines Rumpfes, aus dem Bericht abgelesen -- die Zahl, die `gabbro kosten` druckt.
fn gerechnet(quelle: &str, funktion: &str) -> i128 {
    let bericht = kosten::bericht(&baum(quelle));
    for zeile in bericht.lines() {
        let mut sp = zeile.split('\t');
        if sp.next() == Some(funktion) {
            if let Some(n) = sp.next() {
                return n.parse().unwrap_or(-1);
            }
        }
    }
    -1
}

#[test]
fn ein_let_else_kostet_eine_op_plus_ruf_plus_zweig() {
    // Die Kante: die EINE op des `let … else` selbst. Ohne sie waere die Zusage um genau
    // eins zu klein -- und eine Kostenzahl, die um eins danebenliegt, faellt in keinem
    // Beispiel auf, solange sie unter der Zusage bleibt.
    let q = "module t {
extern fn hol() -> u32 effects { pure } costs <= 5 ops;
extern fn weg() -> never effects { diverges } costs <= 0 ops;
impl fn f() -> u32 effects { pure } costs <= 99 ops {
    let x = hol() else (e) { weg(); }
    return x;
}
}";
    // 1 (let-else) + 5 (hol) + 0 (weg) + 1 (return) = 7
    assert_eq!(gerechnet(q, "f"), 7, "das `let … else` selbst kostet genau 1 op");
}

#[test]
fn ein_exchange_update_kostet_eine_op_plus_rumpf() {
    let q = "module t {
const EINS : u32 = 1;
atomic z : u32 publishes nothing relaxed;
impl fn f() effects { writes z } costs <= 99 ops {
    let alt = z exchange update (v) { z = EINS; };
}
}";
    let n = gerechnet(q, "f");
    // 1 (der Tausch selbst) + 1 (die Zuweisung im Rumpf) = 2. Die Kante ist die EINE op
    // des Tausches: ohne sie kaeme 1 heraus, und das faellt in keinem Beispiel auf.
    assert_eq!(n, 2, "Tausch (1) + Rumpf (1) -- der Tausch selbst kostet genau 1 op");
}

#[test]
fn der_schablonenbericht_zaehlt_ab_eins_und_deckt_jeden_eintrag() {
    let t = schablonen::zeige();
    assert!(t.contains("S1\t"), "die erste Schablone heisst S1, nicht S0 oder S2");
    let letzte = format!("S{}\t", schablonen::SCHABLONEN.len());
    assert!(
        t.contains(&letzte),
        "die letzte Schablone traegt die Nummer der Listenlaenge: {letzte}"
    );
    assert!(!t.contains("S0\t"), "es gibt keine Schablone S0");
}

#[test]
fn der_k_bedingungsbericht_zaehlt_bei_null_an() {
    // Ein Baum ohne jede Tabelle: null Traeger, null mal haelt K, null mal faellt sie.
    let t = kbedingung::zeige(&kbedingung::erhebe(&baum("module t { }")));
    assert!(
        t.contains("0 carriers: K holds 0 times, falls 0 times"),
        "ohne Tabellen sind ALLE drei Zahlen null -- ein Startwert != 0 faellt hier:\n{t}"
    );
    // Und mit genau einer Tabelle ohne `ops` faellt K genau einmal.
    let q = "module t { table T count 4 { slot { a : bool, } } }";
    let t = kbedingung::zeige(&kbedingung::erhebe(&baum(q)));
    assert!(
        t.contains("1 carriers: K holds 0 times, falls 1 times"),
        "eine Tabelle ohne `ops`: K faellt genau einmal:\n{t}"
    );
}

#[test]
fn ein_unaufloesbarer_index_faellt_auf_die_volle_breite_und_nicht_daneben() {
    // `index into T` ohne auffindbares `T`: der Rueckfall ist die VOLLE 32-Bit-Breite.
    // Waere er 33 Bit oder vorzeichenbehaftet, passte plötzlich mehr durch M1 -- und
    // genau das faellt in keinem Beispiel auf, weil kein Beispiel den Rueckfall trifft.
    let q = "module t {
impl fn f(i : index into Unbekannt) -> u32 effects { pure } costs <= 4 ops {
    return i;
}
}";
    // **Kein `|| text.is_empty()`.** Meine erste Fassung hatte den Zusatz und war damit
    // leer: sie war erfuellt, sobald der Pruefer gar nichts sagte. Eine Zusicherung mit
    // einem Ausweg ist keine.
    let n = gerechnet(q, "f");
    assert_eq!(n, 1, "der Rumpf ist ein `return` -- 1 op");
    // Der Rueckfall muss die VOLLE 32-Bit-Breite sein. Waere er schmaler, passte `i` nicht
    // mehr in `u32` und M1 saehe eine Absage; waere er breiter oder vorzeichenbehaftet,
    // ebenso. Genau ein Bereich laesst diesen Rumpf durch, und das ist die Kante.
    let mut absagen = gabbro_syntax::diag::Absagen::neu("probe.gab");
    gabbro_check::pruefe(&baum(q), &mut absagen);
    assert_eq!(
        absagen.fehler_zahl(),
        0,
        "`index into Unbekannt` faellt auf volles u32 zurueck und passt damit in u32:\n{}",
        absagen.zeige(q)
    );
}

#[test]
fn ein_use_entscheidet_zwischen_zwei_gleichnamigen_konstanten() {
    // **Die Probe muss vom WERT abhaengen, nicht nur von der Fehlerzahl.** Meine erste
    // Fassung pruefte „null Fehler" -- und das gilt fuer 7 wie fuer 99. Sie konnte die
    // Aufloesung gar nicht messen.
    //
    // Jetzt entscheidet der Wert ueber die Tabellengroesse, und ein Index von 50 passt in
    // `c::N` (99), aber nicht in `a::N` (7). Nur die richtige `use`-Aufloesung sagt `M103`.
    let q = "module a { pub const N : u32 = 7; }
module c { pub const N : u32 = 99; }
module b {
use a::N;
table T count N { slot { x : bool, } }
impl fn f(t : ptr<normal, r> T) -> bool
    effects { reads t.slots } costs <= 4 ops
{
    return t.slots[50].x;
}
}";
    let mut absagen = gabbro_syntax::diag::Absagen::neu("probe.gab");
    gabbro_check::pruefe(&baum(q), &mut absagen);
    let text = absagen.zeige(q);
    assert!(
        text.contains("M103") || text.contains("M101"),
        "`use a::N;` waehlt 7, nicht 99 -- Index 50 liegt dann AUSSERHALB:\n{text}"
    );
}

// -- Die Emission ---------------------------------------------------------------------

/// **Der Erzeuger, mechanisch gepruefte Haelfte.** Der volle Differenztest steht in
/// `pruefe-emission.sh` (er braucht `cc`); dieser Test haelt fest, was ohne C-Uebersetzer
/// pruefbar ist -- und er ist der Grund, warum eine Mutation im Erzeuger ueberhaupt gefangen
/// werden kann.
#[test]
fn der_erzeuger_senkt_die_formen_dieses_fragments_ab() {
    let quelle = std::fs::read_to_string("../../beispiele/16-by-ops-am-feld.gab").unwrap();
    let mut absagen = gabbro_syntax::Absagen::neu("16.gab");
    let (baum, _) = gabbro_syntax::lies("16.gab", &quelle);
    let c = gabbro_check::emit::emittiere(&baum, &mut absagen);

    assert_eq!(absagen.fehler_zahl(), 0, "{}", absagen.zeige(&quelle));

    // Die Lizenzbedingung aus LIZENZ-ZUSATZ.md -- eine Bedingung, die niemand prueft, ist
    // eine Bitte.
    assert!(c.contains("Generated by Gabbro"), "{c}");

    // `count N` wird zur festen Feldlaenge. **Ohne sie waere die Absenkung ein Zeiger plus
    // Laenge** -- genau die Form, gegen die Gabbro gebaut ist.
    assert!(c.contains("Objekte_slot slots[N]"), "{c}");

    // Ein Pfad, der eine TABELLE nennt, IST die Struktur. Die erste Fassung senkte ihn zu
    // `uint32_t` ab und nannte das eine Vergroeberung in die sichere Richtung -- sie war
    // nicht grob, sie war falsch.
    // **Und `restrict` steht dabei** («OPT1», 2026-08-19): `o` ist der einzige Zeiger auf
    // einen `Objekte`-Traeger in dieser Signatur, und ein Zeiger auf die GLOBALE Tabelle
    // laesst sich in Gabbro nicht bilden (kein `cast` -- G9 --, kein Adressoperator). Das
    // ist die Angabe, die C fehlt: fuer den C-Uebersetzer koennen `Objekte *o` und das
    // globale `Objekte`-Objekt dasselbe sein.
    assert!(c.contains("const Objekte *restrict o"), "{c}");
    assert!(c.contains("uint32_t stand("), "{c}");

    // `r` ohne `w` wird `const`; `rw` nicht. Die Rechte am Zeiger stehen im C.
    assert!(c.contains("void belegen(Objekte *restrict o"), "{c}");

    // Der benannte Bereichstyp senkt zu seinem Traeger ab; der Bereich bleibt M1-Sache.
    assert!(c.contains("uint32_t zaehler;"), "{c}");
}

/// **Die Geistloeschung -- F7, und sie muss an DREI Orten gleichzeitig halten.**
///
/// `BootPhase` ist ein `linear ghost type`: er traegt das ganze Sicherheitsargument des
/// Fragments (die Marke entsteht einmal, wandert durch die Strecke, wird verbraucht) und darf
/// zur Laufzeit **nicht existieren**. Die Loeschung sitzt in der Signatur, am Rufort und an
/// der `let`-Bindung -- und **zwei der drei Fehlformen sind still**.
///
/// > *Die gefaehrlichste ist die dritte:* laesst man die ganze `let`-Anweisung verschwinden
/// > statt nur ihrer Bindung, uebersetzt das C anstandslos und **der Bootschritt findet nicht
/// > statt.** `pruefe-emission.sh` misst genau das und bekam in der Gegenprobe `6` statt
/// > `123456` -- fuenf von sechs Schritten lautlos weg.
#[test]
fn der_erzeuger_loescht_den_geist_und_nicht_den_ruf() {
    let quelle = "module t {
linear ghost type BootPhase;
extern fn melde_roh(text : ptr<code, r> Text) -> u32
    requires Held(PHASE_ROH) effects { reads text } costs <= 64 ops;
extern fn mmu_an(p : BootPhase) -> BootPhase
    effects { consumes p, writes mmu } costs <= 4096 ops;
extern fn root_task_starten(p : BootPhase)
    effects { consumes p, writes faeden } costs <= 8192 ops;
impl fn hochlauf(p : BootPhase) effects { consumes p, writes mmu, writes faeden }
    costs <= 32768 ops
{
    let p1 = mmu_an(p);
    root_task_starten(p1);
}
}";
    let mut absagen = gabbro_syntax::Absagen::neu("f7.gab");
    let (baum, _) = gabbro_syntax::lies("f7.gab", quelle);
    let c = gabbro_check::emit::emittiere(&baum, &mut absagen);
    assert_eq!(absagen.fehler_zahl(), 0, "{}", absagen.zeige(quelle));

    // **Erstens: der Geisttyp selbst erzeugt NICHTS.** Kein `typedef`, keine Struktur.
    assert!(!c.contains("BootPhase"), "ein Geist hat keine Darstellung:\n{c}");

    // **Zweitens: die Signatur.** Ein Geistparameter faellt weg, der Geistrueckgabetyp wird
    // `void`. Bleibt eines von beiden stehen, weigert sich `ctyp` -- laut, nicht still.
    assert!(c.contains("void mmu_an(void);"), "Signatur und Rueckgabe geloescht:\n{c}");
    assert!(c.contains("void root_task_starten(void);"), "{c}");
    assert!(c.contains("void hochlauf(void) {"), "{c}");

    // **Drittens, und hier ist die stille Stelle: die Bindung geht, der RUF bleibt.**
    assert!(c.contains("    mmu_an();"), "der Bootschritt muss stattfinden:\n{c}");
    assert!(!c.contains("p1"), "die Bindung an einen Geist hat keine Entsprechung:\n{c}");
    assert!(c.contains("    root_task_starten();"), "{c}");

    // **Und der fremde Typ:** `Text` wird hier genannt und nirgends erklaert. C traegt dafuer
    // bereits eine Form -- unvollstaendig, hinter einem Zeiger erlaubt, und jede Benutzung,
    // die das Layout braucht, ist ein Uebersetzungsfehler. *Die Absage ist delegiert, nicht
    // fallengelassen.* Der Tag muss VOR der Parameterliste stehen, sonst reicht seine
    // Sichtbarkeit nur bis zum Semikolon -- und `-Wall` sagt das zu Recht.
    let vorwaerts = c.find("struct Text;").expect("Vorwaertsdeklaration fehlt");
    let benutzung = c.find("const struct Text *text").expect("Zeigerparameter fehlt");
    assert!(vorwaerts < benutzung, "der Tag muss VOR seiner Benutzung stehen:\n{c}");
}

/// **Der Erzeuger fiel an drei Stellen OFFEN aus — gefunden 2026-08-17 am Korpus.**
///
/// Sein ganzer Entwurf ist *„weigere dich beim Namen, statt etwas Plausibles auszugeben"*, und
/// genau davon gab es drei Ausnahmen. Alle drei uebersetzen, und zwei von ihnen rechnen still
/// etwas anderes:
///
/// | Stelle | alte Ausgabe | warum sie falsch ist |
/// |---|---|---|
/// | `option index into T` | `uint32_t` | **jeder Wert 0..<N ist ein gueltiger Index** — es bleibt kein Bitmuster fuer *abwesend* |
/// | unbekannte Ausdrucksform | `/* NOT LOWERED */ 0` | uebersetzt und **liefert null** |
/// | `Some`/`None` | `None()` | ein impliziter Ruf; dass `-Werror` ihn faengt, ist Glueck, keine Absage |
///
/// *Dieselbe Klasse wie der Tabellenzeiger vom Vortag, und mit derselben Methode gefunden:
/// den Erzeuger gegen den Korpus laufen lassen.*
#[test]
fn der_erzeuger_weigert_sich_statt_offen_auszufallen() {
    fn absagen_von(q: &str) -> Vec<String> {
        // Die Absagen des Parsers gehoeren dazu -- sonst liest sich eine Probe, die gar
        // nicht parst, wie ein Erzeuger ohne Beanstandung.
        let (baum, mut a) = gabbro_syntax::lies("p.gab", q);
        assert_eq!(a.fehler_zahl(), 0, "die Probe selbst parst nicht:\n{}", a.zeige(q));
        let _ = gabbro_check::emit::emittiere(&baum, &mut a);
        a.absagen.iter().map(|x| x.text.clone()).collect()
    }
    fn c_von(q: &str) -> (String, Vec<String>) {
        let (baum, mut a) = gabbro_syntax::lies("p.gab", q);
        assert_eq!(a.fehler_zahl(), 0, "die Probe selbst parst nicht:\n{}", a.zeige(q));
        let c = gabbro_check::emit::emittiere(&baum, &mut a);
        (c, a.absagen.iter().map(|x| x.text.clone()).collect())
    }

    // **1. `option` wurde am selben Tag entschieden, und der Test wird im Gleichschritt
    // nachgezogen.** Beim Fund war die Absage die ehrliche Antwort -- die Darstellung war
    // offen. Seit F8 traegt sie den Sonderwert `N`, und `der_erzeuger_gibt_die_sperre_auf_
    // jedem_pfad` prueft ihn. *Was hier bleibt, ist die Richtung: der Sonderwert darf nicht
    // null sein, sonst kollidiert er mit Slot 0.*
    let mit_option = absagen_von(
        "module t { table T count 8 { slot { eltern : option index into T, } } }",
    );
    assert!(mit_option.is_empty(), "`option` traegt seit dem Sonderwert: {mit_option:?}");

    // Der pflichtige Index senkt sich ebenso ab -- die Schranke kommt aus `count N` und ist
    // eine M1-Tatsache.
    let ohne_option = absagen_von(
        "module t { table T count 8 { slot { eltern : index into T, } } }",
    );
    assert!(ohne_option.is_empty(), "ein pflichtiger Index traegt: {ohne_option:?}");

    // **2. Eine unbekannte Ausdrucksform wird abgelehnt, nicht zu null.**
    //
    // *Hier stand bis zum 2026-08-20 ein `!`* -- und die Verneinung ist seit Stufe 4 gebaut,
    // weil ein Programm sie gebraucht hat (`messung/netz/udp-echo.gab`). Der Sammelzweig
    // bleibt trotzdem geprueft, jetzt an `old(place)` in einem RUMPF: `SPRACHE.md` §6 sagt
    // *„`old(place)` only in `ensures`"*, **und kein Pass haelt die Zeile** -- nur der
    // Erzeuger faellt. Dieselbe Klasse wie das `!` davor.
    let unbekannt = absagen_von(
        "module t { table T count 8 { slot { benutzt : bool, } }\n \
         impl fn f(t : ptr<normal, r> T, i : index into T) -> bool \
         effects { reads t.slots } costs <= 4 ops { return old(t.slots[i].benutzt); } }",
    );
    // **Und seit dem 2026-08-21 wird die Absage SCHAERFER geprueft.** Hier stand
    // `contains("expression form")` -- der Text des Sammelzweiges, der alle drei
    // uebriggebliebenen Formen (`sizeof`/`lenof`/`aligned`, `old(…)`, `result`) unter EINEM
    // Satz zusammenzog. *Ein Zeugnis, das „expression form" sagt, nennt die Form nicht.*
    // Der Sammelzweig ist ausgeschrieben, und die Probe verlangt jetzt, dass die Absage die
    // Form beim Namen nennt.
    assert!(
        unbekannt.iter().any(|s| s.contains("`old(place)`")),
        "eine unbekannte Ausdrucksform muss beim NAMEN abgelehnt werden: {unbekannt:?}"
    );

    // **2b. Die Verneinung SENKT AB, das unaere Minus nicht -- und der Unterschied ist
    // begruendet, nicht bequem** (2026-08-20, Regel A).
    let (c, verneint) = c_von(
        "module t { table T count 8 { slot { benutzt : bool, } }\n \
         impl fn f(t : ptr<normal, r> T, i : index into T) -> bool \
         effects { reads t.slots } costs <= 4 ops { return !t.slots[i].benutzt; } }",
    );
    assert!(verneint.is_empty(), "`!` ist gebaut, weil ein Programm es brauchte: {verneint:?}");
    // **Und das `!` muss im erzeugten C ANKOMMEN.** Die erste Fassung pruefte nur, dass keine
    // Absage faellt -- und die Mutation `verneinung-verschwindet` ueberlebte: ohne das `!`
    // faellt auch keine Absage, jede Bedingung ist nur umgedreht. *Zum zweiten Mal an einem
    // Tag: eine Zusicherung ueber das AUSBLEIBEN einer Absage bewacht keine Absenkung.*
    assert!(
        c.contains("return !(p->slots") || c.contains("!(t->slots"),
        "die Verneinung steht im erzeugten C:\n{c}"
    );
    let minus = absagen_von(
        "module t { impl fn f(x : i32) -> i32 effects { pure } costs <= 4 ops \
         { return -x; } }",
    );
    assert!(
        minus.iter().any(|s| s.contains("unary minus")),
        "das unaere Minus wird BEIM NAMEN abgelehnt -- in C bliebe `-x` auf einem \
         vorzeichenlosen Operanden vorzeichenlos: {minus:?}"
    );

    // **2c. `-> T or R`: der Rueckgabewert ist der ERFOLG, das Ergebnis geht durch `*_wert`.**
    //
    // Bis zum 2026-08-20 schrieb der Erzeuger `return <wert>;` in eine `bool`-Funktion. Das
    // Ergebnis war IMMER falsch, und zwar auf zwei Arten zugleich: `f(0)` meldete Misserfolg,
    // `f(7)` liess `*_wert` unberuehrt. *`gabbro pruefe`: 0 Fehler. `cc`: uebersetzt.*
    let (c, f) = c_von(
        "module t { reason R { A = 1 \"a\" exhaustive }\n \
         impl fn hol(x : u32) -> u32 or R effects { pure } costs <= 4 ops { return x; } }",
    );
    assert!(f.is_empty(), "{f:?}");
    assert!(c.contains("*_wert = x;"), "das Ergebnis geht durch `_wert`:\n{c}");
    assert!(c.contains("return true;"), "der Rueckgabewert ist der ERFOLG:\n{c}");
    assert!(
        !c.contains("__attribute__((const))") && !c.contains("__attribute__((pure))"),
        "eine Funktion, die durch `*_wert` schreibt, ist weder `const` noch `pure`:\n{c}"
    );

    // **3. `Some`/`None` sind Konstruktoren, keine Rufe** («B35»).
    let konstruktor = absagen_von(
        "module t { table T count 8 { slot { eltern : index into T, } }\n \
         impl fn f(t : ptr<normal, rw> T, i : index into T) \
         effects { writes t.slots } costs <= 4 ops { t.slots[i].eltern = None; } }",
    );
    assert!(
        konstruktor.iter().any(|s| s.contains("`option` constructor")),
        "`None` darf nicht als Ruf ausgegeben werden: {konstruktor:?}"
    );
}

/// **F8: die Sperre, der Sonderwert und der Austritt aus dem Block.**
///
/// Drei Absenkungen, die keine Uebersetzungen sind sondern Entscheidungen, und alle drei
/// stehen im Kopf von `emit.rs` mit ihrem Grund:
///
/// 1. **`option index into T` traegt den Sonderwert `N`.** Er ist gratis, weil `count N` den
///    Index auf `0 ..< N` bindet -- `N` ist der eine Wert, den M1 nie durchlaesst. *Und der
///    gemessene Bestand macht es von Hand: `while i != NIL`.*
/// 2. **Eine `lock`-Deklaration erzeugt zwei Prototypen und keine Zeile Rumpf.** Rang und
///    Haltezeit sind Uebersetzungszeit (`H006`, `K002`); das Primitiv ist Vertrauensbasis.
/// 3. **`locks X { … return … }` gibt die Sperre VOR jeder Rueckkehr frei.** Woertlich die
///    Klasse, die C8 bezahlt hat -- nur erbt der neue Abweispfad die Pflicht hier, weil nicht
///    der Schreiber sie ausgibt.
#[test]
fn der_erzeuger_gibt_die_sperre_auf_jedem_pfad() {
    let quelle = "module t {
const N : u32 = 1024;
type Id = u32 in 0 ..< N;
table L count N { slot { belegt : bool, } }
lock S protects { belegt } rank 2 held <= 300 ops shared held <= 32 ops;
extern fn aufloesen(l : ptr<normal, r> L, t : Id) -> option index into L
    requires Held(S, shared) effects { reads l.slots } costs <= 8 ops;
impl fn toeten(l : ptr<normal, rw> L, t : Id, k : index into L) -> bool
    effects { reads l.slots, writes l.slots, locks S } costs <= 340 ops
{
    locks S {
        match aufloesen(l, t) {
            Some(i) => { l.slots[i].belegt = false; return true; }
            None    => { return false; }
        }
    }
    return false;
}
}";
    let mut absagen = gabbro_syntax::Absagen::neu("f8.gab");
    let (baum, _) = gabbro_syntax::lies("f8.gab", quelle);
    let c = gabbro_check::emit::emittiere(&baum, &mut absagen);
    assert_eq!(absagen.fehler_zahl(), 0, "{}", absagen.zeige(quelle));

    // 1. Der Sonderwert ist die LAENGE, nicht null -- sonst kollidiert er mit Slot 0.
    assert!(c.contains("#define L_NONE (N)"), "der Sonderwert ist die Laenge:\n{c}");
    assert!(c.contains("!= L_NONE"), "der Vergleich benutzt ihn:\n{c}");

    // 2. Zwei Prototypen, und kein Rang und keine Haltezeit im C.
    assert!(c.contains("void S_nimm(void);"), "{c}");
    assert!(c.contains("void S_gib(void);"), "{c}");
    assert!(c.contains("void S_nimm_geteilt(void);"), "die geteilte Seite ist erklaert:\n{c}");
    assert!(!c.contains("300"), "die Haltezeit ist Uebersetzungszeit, nicht Laufzeit:\n{c}");
    assert!(!c.contains("rank"), "der Rang steht im C nirgends:\n{c}");

    // 3. **Die Freigabe steht vor JEDEM `return` im Block -- zweimal, einmal je Zweig.**
    let rumpf = &c[c.find("bool toeten").expect("toeten")..];
    assert_eq!(
        rumpf.matches("S_gib();").count(),
        3,
        "zwei Rueckkehrpfade im Block plus der normale Blockausgang:\n{rumpf}"
    );
    let vor_true = rumpf.find("return true;").expect("Some-Zweig");
    let gib_davor = rumpf[..vor_true].rfind("S_gib();").expect("keine Freigabe vor return true");
    assert!(
        rumpf[gib_davor..vor_true].trim().len() < 20,
        "die Freigabe muss DIREKT vor der Rueckkehr stehen:\n{rumpf}"
    );

    // Die Bindung des `Some`-Zweigs ist der Wert selbst.
    assert!(c.contains("uint32_t i = _o"), "der Binder bekommt den Index:\n{c}");

    // Und der tote Parameter: `k` wird nie gelesen. **`cc -Wextra` sagt das, kein Pass dieses
    // Uebersetzers sagt es** -- der Befund steht in TODO.md, die Stilllegung hier.
    assert!(c.contains("(void)k;"), "ein ungelesener Parameter wird stillgelegt:\n{c}");
    assert!(!c.contains("(void)l;"), "ein gelesener nicht:\n{c}");
}

/// **Zwei stille Ausfaelle und eine Laufzeitpruefung — 2026-08-17, beim Lesen gefunden.**
///
/// `x += 1` wurde `x = 1`. Der Operator stand im Baum und der Erzeuger sah ihn nicht an.
/// **Er ist in keiner der drei Waechtereinheiten vorgekommen — genau darum hat er
/// ueberlebt**, dieselbe Sorte wie die Null im Ausdruckszweig. *Ein offener Ausfall ist
/// unsichtbar, bis jemand hineinlaeuft.*
///
/// Und `narrow` ist die **einzige** Laufzeitpruefung, die dieser Erzeuger ausgibt — nicht weil
/// M1 versagt haette, sondern weil die Sprache sie als Pruefung definiert. *W6 gilt in beide
/// Richtungen: was M1 traegt, faellt weg; was `narrow` heisst, bleibt stehen.*
#[test]
fn zusammengesetzte_zuweisung_narrow_und_never() {
    let quelle = "module t {
const MAX : u32 = 64;
type Tiefe = u32 in 0 .. MAX;
table T count 8 { slot { z : u32 wrapping, } }
extern fn unlesbar() -> never effects { diverges } costs <= 0 ops;
impl fn zaehle(t : ptr<normal, rw> T, i : index into T, tiefe : Tiefe) -> u32
    effects { writes t.slots } costs <= 8 ops
{
    narrow tiefe to 0 ..< MAX else { return 0; }
    t.slots[i].z += 1;
    return 1;
}
}";
    let mut absagen = gabbro_syntax::Absagen::neu("p.gab");
    let (baum, _) = gabbro_syntax::lies("p.gab", quelle);
    let c = gabbro_check::emit::emittiere(&baum, &mut absagen);
    assert_eq!(absagen.fehler_zahl(), 0, "{}", absagen.zeige(quelle));

    // **Der Operator, und er ist der eigentliche Befund.**
    assert!(c.contains("z += 1;"), "`+=` ist nicht `=`:\n{c}");

    // `narrow … to 0 ..< MAX` -- die obere Schranke ist AUSGESCHLOSSEN. Ein `<=` statt `<`
    // liesse genau den einen Wert durch, gegen den die Schranke steht.
    //
    // **Und die untere Pruefung fehlt mit Absicht** (nachgezogen 2026-08-17): `tiefe` ist
    // `u32`, also ist `tiefe >= 0` immer wahr -- `-Wextra` sagt das zu Recht
    // (`-Wtype-limits`). Sie faellt aber **nur weg, wenn der Erzeuger die Vorzeichenlosigkeit
    // KENNT**; weiss er es nicht, gibt er sie aus und nimmt die Warnung in Kauf. *Dann wird
    // der Waechter rot, statt dass eine Pruefung still verschwindet.*
    assert!(c.contains("if (!(tiefe < MAX))"), "die Pruefung, exklusiv oben:\n{c}");
    assert!(!c.contains("tiefe >= 0"), "die vakuume untere Pruefung faellt weg:\n{c}");

    // `-> never` -- ohne das Wort sieht der C-Uebersetzer die Fehlerzweige als durchfallend
    // an. Genau daher kamen in F5 sechs `S002`, bevor `exit()` sein `-> never` bekam.
    assert!(c.contains("_Noreturn void unlesbar(void);"), "{c}");
}

/// **`retry` und `format` — die zwei Entscheidungen aus F10.**
///
/// `bounded N ops` ist ein **Operationsbudget**, kein Schleifenzaehler. `SPRACHE.md` ist
/// eindeutig -- die Einheit ist `ops`, Zeitmasse sind an D10 gestorben. Die Laufzeitschranke
/// ist also `floor(N / Kosten-je-Durchgang)`, **und die Kosten rechnet der Kostenpass**, nicht
/// ein zweiter Rechner im Erzeuger.
///
/// > **Der Vergleich mit `traverse` ist der Ertrag:** eine Traversierung braucht KEINEN
/// > Laufzeitzaehler, weil ihre Domaene durch Konstruktion endlich ist. Ein `retry` braucht
/// > einen, weil seine Bedingung von der Welt abhaengt -- und genau darum verlangt die
/// > Grammatik dort ein `on_exceeded` und hier keines.
///
/// Und ein `format` wird **kein C-Verbund**: Fuellung und Bitreihenfolge sind
/// implementierungsoffen, ein Format ist aber genau eine Zusage ueber Bytes.
#[test]
fn retry_teilt_das_budget_und_format_liest_bytes() {
    let quelle = "module t {
const MAGIE : u32 = 3735928559;
format Kopf @version 1 endian big {
    magie : u32 where magie == MAGIE,
    laenge : u32,
}
extern fn schritt(k : ptr<normal, r> Kopf) -> u32 effects { reads k } costs <= 4 ops;
extern fn leer() -> never effects { diverges } costs <= 0 ops;
impl fn zaehle(k : ptr<normal, r> Kopf) -> u32 effects { reads k } costs <= 4096 ops
{
    retry lesen until schritt(k) == 9
        bounded 400 ops progress verbraucht on_exceeded leer effects { reads k }
    { }
    return 0;
}
}";
    let mut absagen = gabbro_syntax::Absagen::neu("p.gab");
    let (baum, _) = gabbro_syntax::lies("p.gab", quelle);
    let c = gabbro_check::emit::emittiere(&baum, &mut absagen);
    assert_eq!(absagen.fehler_zahl(), 0, "{}", absagen.zeige(quelle));

    // **Das Format ist ein Bytezeiger, kein Verbund** -- und seit dem 2026-08-20 ein
    // SCHREIBBARER: `SPRACHE.md`:355 sagt Leser **und** Schreiber zu, und der Schreiber
    // fehlte. *Das `const` am Zeiger hatte ohnehin nie etwas gehalten -- es sagte nur, dass
    // `bytes` nicht umgehaengt wird, und `const N *` propagiert in C nicht nach innen.*
    assert!(c.contains("uint8_t *bytes"), "{c}");
    assert!(c.contains("static inline void Kopf_setz_magie(Kopf *v, uint32_t x)"), "der Schreiber fehlt:\n{c}");
    assert!(c.contains("gabbro_setz_be32(v->bytes + 0, x)"), "gross geschrieben:\n{c}");
    assert!(!c.contains("uint32_t magie;"), "kein Feld -- ein Zugriff:\n{c}");
    assert!(c.contains("gabbro_be32(v->bytes + 0)"), "Versatz 0, gross gelesen:\n{c}");
    assert!(c.contains("gabbro_be32(v->bytes + 4)"), "Versatz 4:\n{c}");
    assert!(!c.contains("gabbro_le32"), "nur der GEBRAUCHTE Leser wird erzeugt:\n{c}");

    // Die `where`-Klausel wird EINE Gueltigkeitsfunktion, mit der Laengenpruefung davor.
    assert!(c.contains("if (v->len < 8u) return false;"), "{c}");
    assert!(c.contains("if (!(Kopf_magie(v) == MAGIE)) return false;"), "{c}");

    // **Das Budget geteilt durch die Durchgangskosten.** Der Rumpf ist leer, die Bedingung
    // ruft `schritt` (4 ops) plus Vergleich -- der Kostenpass rechnet, der Erzeuger teilt.
    let z = c.find("_r1 >= ").expect("Durchgangsschranke fehlt");
    let zahl: u32 = c[z + 7..].split('u').next().unwrap().parse().expect("Zahl");
    assert!(zahl > 0 && zahl < 400, "geteilt, nicht uebernommen: {zahl} aus 400 ops");

    // Der Ueberlauf ist BENANNT -- D11 woertlich.
    assert!(c.contains("{ leer(); }"), "der benannte Ausgang wird gerufen:\n{c}");
    assert!(c.contains("_Noreturn void leer(void);"), "und er kehrt nicht zurueck:\n{c}");
}

/// **Zwei Regeln, die eine ueberlebende Mutation aufgedeckt hat (2026-08-17).**
///
/// `on-exceeded-darf-zurueckkehren` und `untere-schranke-faellt-immer-weg` gingen durch, ohne
/// dass etwas fiel. Beide Regeln waren gebaut und **keine von beiden war bewacht** -- genau
/// der Zustand, gegen den das Mutationsgeruest steht.
#[test]
fn on_exceeded_und_die_untere_schranke_sind_bewacht() {
    fn absagen_von(q: &str) -> Vec<String> {
        // **Die Absagen des PARSERS gehoeren dazu.** Ohne sie sieht ein Tippfehler in der
        // Probe aus wie ein Erzeuger, der nichts zu beanstanden hat -- und genau das ist
        // hier passiert: `r` als Schleifenmarke ist das Leserecht am Zeiger, die Probe
        // parste nicht, und die leere Absagenliste las sich wie ein Befund.
        let (baum, mut a) = gabbro_syntax::lies("p.gab", q);
        assert_eq!(a.fehler_zahl(), 0, "die Probe selbst parst nicht:\n{}", a.zeige(q));
        let _ = gabbro_check::emit::emittiere(&baum, &mut a);
        a.absagen.iter().map(|x| x.text.clone()).collect()
    }

    // **1. `on_exceeded` muss auf eine Funktion zeigen, die NICHT zurueckkehrt.** Kehrt sie
    // zurueck, dreht die Schleife nach dem Ueberlauf weiter -- die Schranke waere dann eine
    // Zusage ohne Wirkung, also genau das, wogegen D11 steht.
    let kehrt_zurueck = absagen_von(
        "module t {
extern fn schritt() -> u32 effects { pure } costs <= 4 ops;
extern fn merker() -> u32 effects { pure } costs <= 1 ops;
impl fn f() -> u32 effects { pure } costs <= 4096 ops
{ retry warten until schritt() == 9 bounded 400 ops progress p on_exceeded merker
    effects { pure } { } return 0; }
}",
    );
    assert!(
        kehrt_zurueck.iter().any(|s| s.contains("`never`")),
        "ein zurueckkehrendes `on_exceeded` muss abgelehnt werden: {kehrt_zurueck:?}"
    );

    // **2. Die untere `narrow`-Pruefung faellt NUR fuer nachweislich vorzeichenlose Werte
    // weg.** Bei einem vorzeichenbehafteten Wert ist `x >= 0` keine Redensart, sondern die
    // halbe Pruefung.
    let quelle = "module t {
type S = i32 in 0 .. 100;
impl fn f(x : S) -> u32 effects { pure } costs <= 8 ops
{ narrow x to 0 .. 50 else { return 0; } return 1; }
}";
    let mut a = gabbro_syntax::Absagen::neu("s.gab");
    let (baum, _) = gabbro_syntax::lies("s.gab", quelle);
    let c = gabbro_check::emit::emittiere(&baum, &mut a);
    assert_eq!(a.fehler_zahl(), 0, "{}", a.zeige(quelle));
    assert!(
        c.contains("x >= 0"),
        "bei einem vorzeichenbehafteten Wert bleibt die untere Pruefung stehen:\n{c}"
    );
}

/// **`traverse`, `forever` und der Austritt aus einem `if` — fuenf Regeln auf einmal.**
///
/// Alle fuenf ueberlebten ihre Mutation, weil sie **nur** vom Shell-Waechter beruehrt wurden
/// und `mutiere-pruefer.py` `cargo test` laeuft. *Eine Regel, die nur ein Werkzeug bewacht,
/// ist gegen jedes andere blind.*
#[test]
fn traversierung_forever_und_der_austritt_aus_einem_zweig() {
    fn c_von(q: &str) -> (String, Vec<String>) {
        let (baum, mut a) = gabbro_syntax::lies("p.gab", q);
        assert_eq!(a.fehler_zahl(), 0, "die Probe parst nicht:\n{}", a.zeige(q));
        let c = gabbro_check::emit::emittiere(&baum, &mut a);
        (c, a.absagen.iter().map(|x| x.text.clone()).collect())
    }

    // **1. Die Traversierung laeuft ueber die GANZE Domaene und greift durch den Zeiger.**
    let (c, f) = c_von(
        "module t { table W count 16 { slot { a : bool, } }
impl fn loesche(w : ptr<normal, rw> W) effects { writes w.slots } costs <= 64 ops
{ traverse i over slots of w by unvisited touches writes w.slots { w.slots[i].a = false; } } }",
    );
    assert!(f.is_empty(), "{f:?}");
    assert!(c.contains("i < (uint32_t)(sizeof("), "die Grenze ist `< n`, nicht `< n-1`:\n{c}");
    assert!(c.contains("sizeof(w->slots)"), "durch den Zeiger, nicht mit `.`:\n{c}");
    assert!(!c.contains("(void)w;"), "der traversierte Traeger ist nicht tot:\n{c}");

    // **2. Der Abstieg ist seit Stufe 3 entschieden, und zwar UNGLEICH** (2026-08-20).
    //
    // Bis dahin stand hier *„was es fuer den LAUF heisst, ist nicht entschieden"* -- fuer
    // BEIDE Ordnungen, und fuer `by decreasing` war das eine offene Frage ueber etwas ohne
    // Laufwirkung. Die Entscheidung trennt sie:
    //
    //   `by decreasing`  ein Terminierungszeuge, LAEUFT wie `by unvisited`
    //   `by consuming`   derselbe Lauf PLUS die Entnahme -- und die ist erzeugter Code
    let (_, f) = c_von(
        "module t { table W count 16 { slot { a : bool, } }
impl fn loesche(w : ptr<normal, rw> W) effects { writes w.slots } costs <= 64 ops
{ traverse i over slots of w by consuming touches writes w.slots { w.slots[i].a = false; } } }",
    );
    assert!(
        f.iter().any(|s| s.contains("the removal")),
        "`by consuming` braucht die Entnahme und darf nicht wie `by unvisited` laufen: {f:?}"
    );
    let (c, f) = c_von(
        "module t { table W count 16 { slot { a : bool, } }
impl fn loesche(w : ptr<normal, rw> W) effects { writes w.slots } costs <= 64 ops
{ traverse i over slots of w by decreasing (16 - i) touches writes w.slots { w.slots[i].a = false; } } }",
    );
    assert!(f.is_empty(), "`by decreasing` hat keine Laufwirkung und senkt ab: {f:?}");
    assert!(c.contains("i < (uint32_t)(sizeof("), "dieselbe Laufform wie `by unvisited`:\n{c}");

    // **2b. «B12» ist entschieden: `elems of` bindet einen INDEX.** Aus dem Index bekommt
    // man das Element, aus dem Element den Index nicht -- und `msg_kopiert` (*„beide Felder
    // stimmen an derselben Stelle ueberein"*) ist unter der Elementlesart nicht schreibbar.
    let (c, f) = c_von(
        "module t { type S = { worte : [u32; 8], };
impl fn loesche(s : ptr<normal, rw> S) effects { writes s } costs <= 64 ops
{ traverse i over elems of s.worte by unvisited touches writes s { s.worte[i] = 0; } } }",
    );
    assert!(f.is_empty(), "`elems of` senkt ab: {f:?}");
    assert!(
        c.contains("sizeof(s->worte)"),
        "die Schranke kommt aus dem Feld selbst, nicht aus einer Tabelle:\n{c}"
    );
    // **Und die Grenze ist `< n`, nicht `< n-1`.** Die erste Fassung dieses Tests pruefte nur
    // den `sizeof`-Traeger -- und die Mutation `elems-laesst-den-letzten-aus` UEBERLEBTE:
    // `{v} + 1 <` enthaelt denselben Traeger. *Eine Zusicherung, die den Traeger prueft und
    // nicht die Schranke, faengt genau den Fehler nicht, um den es geht.*
    assert!(
        c.contains("i < (uint32_t)(sizeof("),
        "die Domaene ist vollstaendig -- `< n`, nicht `< n-1`:\n{c}"
    );

    // **3. `forever` senkt ab, und die Klausel wird ein GEPRUEFTER BEZUG** (2026-08-20).
    //
    // Die Weigerung, die hier stand, nannte zwei Gruende, und der zweite war nicht mehr
    // wahr: *«B11»: there is no exit either.* `leave` steht laengst in der Grammatik. Der
    // erste gilt -- `per_pass … ops` ist Uebersetzungszeit, `on_exceeded` hat keinen
    // Ausloeser -- und wird eingeloest statt weggeraeumt: der C-Uebersetzer liest die
    // Klausel ein zweites Mal.
    let (c, f) = c_von(
        "module t {
extern fn wacht() -> never effects { diverges } costs <= 0 ops;
divergent fn dienst() -> never effects { diverges }
{ forever d per_pass bounded 64 ops on_exceeded wacht effects { pure } { } } }",
    );
    assert!(f.is_empty(), "{f:?}");
    assert!(c.contains("for (;;) {"), "{c}");
    assert!(
        c.contains("static void (*const d_wachhund)(void) __attribute__((unused)) = wacht;"),
        "der Wachhund muss im Erzeugnis stehen und benannt sein:\n{c}"
    );
    // **Eine Marke, die niemand anspringt, steht NICHT da** -- `-Wunused-label` faellt unter
    // `-Werror`, und ein Erzeugnis, das nicht uebersetzt, ist keines.
    assert!(!c.contains("d_ende:"), "eine Marke ohne Sprung:\n{c}");

    // **`leave` wird ein `goto`, kein `break`** -- die Marke nennt eine Schleife, und
    // `break` braeche in C immer die innerste. Und die Sperre, die INNERHALB genommen wurde,
    // wird davor freigegeben.
    let (c, f) = c_von(
        "module t { table W count 16 { slot { a : bool, } }
lock L protects { W } rank 0 held <= 400 ops;
extern fn wacht() -> never effects { diverges } costs <= 0 ops;
extern fn fertig() -> bool effects { pure } costs <= 1 ops;
impl fn dienst(w : ptr<normal, rw> W) effects { writes w.slots, locks L } costs <= 8 ops
{ forever d per_pass bounded 64 ops on_exceeded wacht effects { writes w.slots, locks L }
  { locks L { if fertig() { leave d; } } } } }",
    );
    assert!(f.is_empty(), "{f:?}");
    assert!(c.contains("d_ende: ;"), "die Marke steht hinter der Schleife:\n{c}");
    let sprung = c.find("goto d_ende;").expect("`leave` wird ein goto");
    let gib = c[..sprung].rfind("L_gib();").expect("die Sperre wird freigegeben");
    assert!(
        c[gib..sprung].lines().count() <= 2,
        "die Freigabe steht nicht unmittelbar vor dem Sprung:\n{c}"
    );

    // **4. Ein `return` aus einem `if` INNERHALB eines `locks` gibt die Sperre frei.**
    // Woertlich die Klasse, die C8 bezahlt hat -- und der Zweig ist der Weg, auf dem sie am
    // leichtesten verlorengeht.
    let (c, f) = c_von(
        "module t { table W count 16 { slot { a : bool, } }
lock S protects { a } rank 0 held <= 64 ops;
impl fn f(w : ptr<normal, rw> W, i : index into W) -> bool
    effects { reads w.slots, writes w.slots, locks S } costs <= 64 ops
{ locks S { if w.slots[i].a { return true; } } return false; } }",
    );
    assert!(f.is_empty(), "{f:?}");
    let vor_true = c.find("return true;").expect("der Zweig");
    assert!(
        c[..vor_true].rfind("S_gib();").is_some_and(|g| c[g..vor_true].trim().len() < 20),
        "die Freigabe muss direkt vor der Rueckkehr stehen:\n{c}"
    );
}

/// **Die Praemisse, die aus dem Beweis kam (2026-08-17).**
///
/// `beweise/Option_Sonderwert.thy` zeigt die Kodierung `None -> N`, `Some i -> i` als
/// injektiv — **unter `N < 2^w`**. Bei `N = 2^w` faellt der Sonderwert mit dem ersten Slot
/// zusammen (`sonderwert_kollidiert_bei_vollem_wort`), und `None` ist von `Some 0` nicht mehr
/// zu unterscheiden.
///
/// > **Die Praemisse stand in keiner der drei Fassungen des Satzes** — nicht im Register,
/// > nicht in `SPRACHE.md`, nicht im Erzeuger. In der Praxis war sie erfuellt (`count 80256`
/// > gegen `2^32`), *aber erfuellt und geprueft sind zwei Zustaende.*
#[test]
fn der_sonderwert_passt_ins_indexwort() {
    fn absagen_von(q: &str) -> Vec<String> {
        let (baum, mut a) = gabbro_syntax::lies("p.gab", q);
        assert_eq!(a.fehler_zahl(), 0, "die Probe parst nicht:\n{}", a.zeige(q));
        let _ = gabbro_check::emit::emittiere(&baum, &mut a);
        a.absagen.iter().map(|x| x.text.clone()).collect()
    }

    // Knapp darunter traegt es: 2^32 - 1 Slots, der Sonderwert ist 2^32 - 1... nein, er ist
    // die LAENGE, also passt er noch.
    let knapp = absagen_von(
        "module t { const N : u32 = 4294967295;
table T count N { slot { e : option index into T, } } }",
    );
    assert!(knapp.is_empty(), "unter der Wortgrenze traegt der Sonderwert: {knapp:?}");

    // **Genau darauf faellt es.**
    let voll = absagen_von(
        "module t { const N : u32 = 4294967296;
table T count N { slot { e : option index into T, } } }",
    );
    assert!(
        voll.iter().any(|s| s.contains("collides with slot 0")),
        "bei `N = 2^32` muss der Erzeuger anhalten: {voll:?}"
    );
}

/// **Das Geraet: ein Register ist KEIN Feld, und `at dma` wird abgelehnt.**
#[test]
fn ein_registerzugriff_ist_volatil_und_dma_wird_abgelehnt() {
    fn c_von(q: &str) -> (String, Vec<String>) {
        let (baum, mut a) = gabbro_syntax::lies("p.gab", q);
        assert_eq!(a.fehler_zahl(), 0, "die Probe parst nicht:\n{}", a.zeige(q));
        let c = gabbro_check::emit::emittiere(&baum, &mut a);
        (c, a.absagen.iter().map(|x| x.text.clone()).collect())
    }

    let (c, f) = c_von(
        "module t {
device R(basis : u64) at mmio {
    reg IDX : u16 wrapping @0x102 class rw
    reg LEN : u16          @0x104 class r
}
impl fn vor(r : ptr<mmio, rw> R) effects { writes r.IDX } costs <= 2 ops { r.IDX += 1; } }",
    );
    assert!(f.is_empty(), "{f:?}");

    // **Der Griff ist ein Zeiger, kein abgebildeter Registersatz.** Ein `struct` mit Feldern
    // haette eine Fuellung, ueber die der Uebersetzer entscheidet -- die Versaetze stehen aber
    // in der Deklaration.
    assert!(c.contains("volatile uint8_t *basis"), "{c}");
    assert!(!c.contains("uint16_t IDX;"), "kein Feld:\n{c}");

    // **`volatile` ist die eine Stelle, an der die Absenkung dem C-Uebersetzer etwas
    // VERBIETET** -- ein Registerzugriff darf nicht wegoptimiert werden.
    assert!(
        c.contains("(*(volatile uint16_t *)(r->basis + 258)) += 1;"),
        "Zugriff an basis + 0x102, volatil, und `+=` traegt sich von selbst:\n{c}"
    );

    // **`at dma` WITHOUT the named assumption is refused** -- and the refusal names it
    // (2026-08-26). Which barrier a DMA access needs is a statement about the memory model,
    // and the generator does not build it. *It carries it by NAME instead of inventing it --
    // or of leaving the obligation unpayable.*
    let (_, f) = c_von(
        "module t { device Q(basis : u64) at dma { reg I : u16 @0x0 class rw } }",
    );
    assert!(
        f.iter().any(|s| s.contains("MEMORY MODEL") && s.contains("dma_kohaerent")),
        "`at dma` ohne Annahme faellt, und die Absage nennt die fehlende Annahme: {f:?}"
    );

    // **And WITH it the access lowers, exactly as `at mmio` does.** That is the other
    // half: a refusal without a door is a ban; one with a door is a condition.
    let (c2, f2) = c_von(
        "module t { assume dma_kohaerent \"kohaerent und in Reihenfolge sichtbar.\" falsifier sonde_dma; \
         device Q(basis : u64) at dma { reg I : u16 @0x0 class rw } }",
    );
    assert!(f2.is_empty(), "mit `assume dma_kohaerent` senkt `at dma` ab: {f2:?}");
    assert!(
        c2.contains("dma_kohaerent"),
        "die Annahme reist in den Kopf des erzeugten C -- ihr Leser sieht, worauf es ruht:\n{c2}"
    );

    // **And `at normal` still falls, with a reason OF ITS OWN.** Until 2026-08-26 both
    // carried the same text -- a refusal whose stated ground was untrue for one of its two
    // halves: a `normal` access needs no barrier at all.
    let (_, f3) = c_von(
        "module t { device Q(basis : u64) at normal { reg I : u16 @0x0 class rw } }",
    );
    assert!(
        f3.iter().any(|s| s.contains("not a device access")),
        "`at normal` hat seinen eigenen Grund: {f3:?}"
    );
}

/// **Die Annahmenmenge faehrt jetzt mit dem Code mit — `SYNTAX.md` §12 verlangt es.**
///
/// *„Die Annahmenmenge wird ins Erzeugnis emittiert (‚bewiesen unter A1…An'), als Menge von
/// Namen mit Klasse, nicht als Zahl."* Bis zum 2026-08-17 hat das nichts getan: `gabbro
/// annahmen` druckte sie auf die Konsole, und das Erzeugnis wusste nichts davon.
///
/// > *Eine Zusage, die nur in einem Werkzeugaufruf steht, faehrt nicht mit dem Code mit.*
/// > Sie steht jetzt im Kopf der erzeugten Datei — dort, wo auch der Lizenzhinweis steht,
/// > und aus demselben Grund.
///
/// **Und ein Bitfeld wird gelesen, nicht geschrieben.** Ein Schreiben waere ein
/// Lese-Aendere-Schreib-Zug auf dem GANZEN Register — bei `class w` unmoeglich, und genau
/// dafuer gibt es `mirrors` (Falle 4).
#[test]
fn annahmen_und_bitfelder() {
    let (baum, mut a) = gabbro_syntax::lies(
        "p.gab",
        "module t {
axiom write_cr3(p : u64) effects { writes tlb } falsifier sonde_cr3;
assume tlb_leer \"Ein Schreiben auf CR3 verwirft die nicht-globalen Eintraege.\"
    unfalsifiable \"auf dieser Maschine nicht beobachtbar\";
device V(basis : u64) at mmio { reg GSTS : u32 @0x1c class r fields { TES @31, ND @[2:0], } }
impl fn bereit(v : ptr<mmio, r> V) -> u32 effects { reads v.GSTS } costs <= 2 ops
{ return v.GSTS.TES; } }",
    );
    let c = gabbro_check::emit::emittiere(&baum, &mut a);
    assert_eq!(a.fehler_zahl(), 0, "{}", a.zeige(""));

    // **Die Klasse steht dabei, nicht nur der Name** -- und der unfalsifizierbare Fall
    // traegt seinen Grund, sonst waere er eine Annahme ohne Rechenschaft.
    assert!(c.contains("Proved under the following assumptions"), "{c}");
    assert!(c.contains("write_cr3 (axiom): falsifier sonde_cr3"), "{c}");
    assert!(c.contains("UNFALSIFIABLE -- auf dieser Maschine nicht beobachtbar"), "{c}");

    // Ein Einzelbit und ein Bereich, beide aus demselben volatilen Wort.
    assert!(
        c.contains(">> 31) & 1u"),
        "das Einzelbit wird aus dem Wort geschoben und maskiert:\n{c}"
    );

    let (baum, mut a) = gabbro_syntax::lies(
        "p.gab",
        "module t { device V(basis : u64) at mmio { reg R : u8 @0x0 class r fields { X @9, } } }",
    );
    let _ = gabbro_check::emit::emittiere(&baum, &mut a);
    assert!(
        a.absagen.iter().any(|x| x.text.contains("outside the declared register width")),
        "eine Bitlage jenseits der erklaerten Breite ist ein Fehler, kein offener Punkt"
    );
}

/// **Falle 4, im erzeugten C statt in einem Kommentar.**
///
/// `GCMD` ist kein Lese-Aendere-Schreib-Register. Wer ein Bit setzt, schreibt das GANZE Wort —
/// und jedes Zustandsbit, das er nicht mitschreibt, ist danach geloescht. Die mitzuschreibenden
/// Bits stehen nicht in GCMD (`class w`, unlesbar), sondern im Statusregister daneben.
///
/// > `mirrors GCMD from GSTS;` ist **eine Zeile je Geraet** und ersetzt `GCMD_STATE_MASK`
/// > samt der Kommentarwand (`vtd.rs:42-52`). *Das Konstrukt war gegen die Falle gebaut —
/// > jetzt steht sie im C.*
#[test]
fn mirrors_schreibt_die_zustandsbits_mit() {
    let (baum, mut a) = gabbro_syntax::lies(
        "p.gab",
        "module t { device V(basis : u64) at mmio {
    mirrors GCMD from GSTS;
    reg GCMD : u32 @0x18 class w fields { SRTP @30, TE @31, }
    reg GSTS : u32 @0x1c class r fields { RTPS @30, TES @31, }
    transition setze_rtp { GCMD.SRTP: 0 -> 1 } requires GSTS.TES == 0 effects { writes GCMD }
} }",
    );
    let c = gabbro_check::emit::emittiere(&baum, &mut a);
    assert_eq!(a.fehler_zahl(), 0, "{}", a.zeige(""));

    // **Der Zustand kommt aus GSTS (Versatz 0x1c = 28), geschrieben wird GCMD (0x18 = 24).**
    assert!(c.contains("_s = (*(volatile uint32_t *)(d->basis + 28))"), "{c}");
    assert!(c.contains("(d->basis + 24)) = "), "{c}");

    // Die geaenderten Bits werden ausmaskiert, die uebrigen mitgeschrieben. Bit 30 = 2^30.
    // **Am oeffnenden Klammerpaar verankert.** Ohne es matchte auch `0*_s & …` -- und genau
    // das war die Mutation, die ueberlebt hat: eine Teilzeichenkette ist keine Verankerung.
    assert!(c.contains("((_s & (uint32_t)~(uint32_t)1073741824u)"), "die Maske:\n{c}");
    assert!(c.contains("| (uint32_t)1073741824u"), "und das neue Bit:\n{c}");

    // **Das `requires` wird KEINE Laufzeitpruefung** -- es ist dieselbe Art Klausel wie ein
    // `requires Held(...)` an einer Funktion, also eine Pflicht des Rufers. Hier zu pruefen
    // und dort nicht waere die stille Ausnahme.
    assert!(c.contains("a caller obligation, not a generated assertion"), "{c}");
    // Kein `assert(...)` im Rumpf -- der Kommentar oben enthaelt das Wort, der CODE nicht.
    let rumpf = &c[c.find("static inline void V_setze_rtp").expect("der Uebergang")..];
    assert!(!rumpf.contains("assert("), "keine erzeugte Zusicherung:\n{rumpf}");
}

/// **Drei Absenkungen aus einem Zug: `option` als Wert, `bank`, `transset`.**
#[test]
fn option_als_wert_bank_und_transset() {
    fn c_von(q: &str) -> (String, Vec<String>) {
        let (baum, mut a) = gabbro_syntax::lies("p.gab", q);
        assert_eq!(a.fehler_zahl(), 0, "die Probe parst nicht:\n{}", a.zeige(q));
        let c = gabbro_check::emit::emittiere(&baum, &mut a);
        (c, a.absagen.iter().map(|x| x.text.clone()).collect())
    }

    // **1. `x = None` braucht die ZIELTABELLE.** Der Sonderwert gehoert der Tabelle, auf die
    // das Feld zeigt -- nicht der, in der es steht. Bei zwei Tabellen faellt der Unterschied
    // auf, und genau darum weigerte sich der Erzeuger, solange er ihn nicht aufloesen konnte.
    let (c, f) = c_von(
        "module t {
table A count 8 { slot { a : bool, } }
table B count 16 { slot { zeigt : option index into A, } }
impl fn loesche(b : ptr<normal, rw> B, i : index into B)
    effects { writes b.slots } costs <= 4 ops { b.slots[i].zeigt = None; } }",
    );
    assert!(f.is_empty(), "{f:?}");
    assert!(c.contains("zeigt = A_NONE;"), "der Sonderwert der ZIELtabelle:\n{c}");
    assert!(!c.contains("B_NONE;"), "nicht der der eigenen:\n{c}");

    // **2. `bank` -- ein Registersatz an BERECHNETER Lage.** Die Lage kommt aus einem
    // gelesenen Feld; der Bestand rechnet dieselbe Adresse von Hand aus (`vtd.rs:442`).
    let (c, f) = c_von(
        "module t { device V(basis : u64) at mmio {
    reg CAP : u64 @0x08 class r fields { FRO @[33:24], }
    bank FRR at CAP.FRO * 16 stride 16 count 256 { reg LO : u64 @0x0 class r }
} }",
    );
    assert!(f.is_empty(), "{f:?}");
    assert!(c.contains("V_FRR_LO(const V *d, uint32_t i)"), "Zugriff mit Index:\n{c}");
    assert!(c.contains("i * 16u"), "der Schritt:\n{c}");
    assert!(
        c.contains(">> 24) & 1023u"),
        "die Lage kommt aus dem gelesenen Feld, nicht aus einer Konstanten:\n{c}"
    );

    // **3. `transset` -- mehrere Bits in EINEM Schreibzug.** Am Register geht das; an zwei
    // SLOTFELDERN nicht, und das ist «B17» eine Ebene tiefer.
    let (c, f) = c_von(
        "module t { device V(basis : u64) at mmio {
    reg R : u32 @0x0 class rw fields { A @0, B @1, }
    transition beide { R.A: 0 -> 1, R.B: 0 -> 1 } effects { writes R }
} }",
    );
    assert!(f.is_empty(), "{f:?}");
    assert!(c.contains("= (uint32_t)3u;"), "beide Bits in einem Zug:\n{c}");
}

/// **`atomic` ohne Nutzlast, `check` als Funktion — und `descendants of` als BEFUND.**
#[test]
fn atomic_check_und_die_unbenannte_kante() {
    fn c_von(q: &str) -> (String, Vec<String>) {
        let (baum, mut a) = gabbro_syntax::lies("p.gab", q);
        assert_eq!(a.fehler_zahl(), 0, "die Probe parst nicht:\n{}", a.zeige(q));
        let c = gabbro_check::emit::emittiere(&baum, &mut a);
        (c, a.absagen.iter().map(|x| x.text.clone()).collect())
    }

    // **1. `publishes nothing relaxed` ist die lastfreie Form** -- es gibt nichts zu paaren,
    // also nichts zu begruenden. `_Atomic` mit relaxed ist genau das, was dasteht.
    let (c, f) = c_von("module t { atomic n : u32 publishes nothing relaxed; }");
    assert!(f.is_empty(), "{f:?}");
    assert!(c.contains("_Atomic uint32_t n;"), "{c}");

    // **`release` wurde bis zum 2026-08-17 abgelehnt**, mit diesem Grund: *dass ein
    // release-Speichern die Sichtbarkeit HERSTELLT, die die Paarung behauptet, ist eine
    // Aussage ueber das Speichermodell.* **Der Grund stimmt weiter — er ist nur kein Grund
    // fuer eine Weigerung:** die Aussage steht seit K100.2 als **A10** in der Axiomschicht,
    // gebucht als *nicht falsifizierbar*.
    //
    // > Sich weiter zu weigern hiesse, dieselbe Aussage zweimal zu verlangen: einmal als
    // > Axiom und einmal als Beweis.
    //
    // **Was das C dafuer tragen MUSS**, ist die Ordnung, die die Quelle sagte — nicht das
    // Vorgabemodell von `_Atomic`.
    let (c, f) = c_von("module t { atomic n : u32 publishes { x } release; }");
    assert!(f.is_empty(), "unter A10 traegt die Absenkung: {f:?}");
    assert!(c.contains("#define n_ORDER memory_order_release"), "{c}");
    assert!(c.contains("A10"), "die Annahme steht im Erzeugnis, nicht nur im Ordner:\n{c}");

    // **Und ein LADEN mit `release` gibt es in C11 nicht.** Die Deklaration nennt die
    // Speicherseite; `awaits` laedt mit ACQUIRE. *Gefunden beim Lesen des erzeugten C —
    // `cc` haette es auch gesagt, aber sich darauf zu verlassen hiesse, die Absage zu
    // delegieren, wo die Antwort hier steht.*
    let (c, _) = c_von(
        "module t { static mut d : u32 = 0; atomic f : bool publishes { d } release;
impl fn lies() -> bool effects { reads f, reads d } costs <= 8 ops
{ let g = f awaits { d }; return g; } }",
    );
    assert!(
        c.contains("atomic_load_explicit(&f, memory_order_acquire)"),
        "ein Laden nimmt acquire, nicht release:\n{c}"
    );

    // **Und das SPEICHERN explizit, nicht ueber den Zuweisungsoperator.** `A = w` auf einem
    // `_Atomic` waere in C `seq_cst` -- eine andere und teurere Ordnung als die deklarierte.
    //
    // > *Diese Zeile fehlte bis zum 2026-08-17, und die Mutation
    // > `veroeffentlichung-nimmt-die-vorgabeordnung` UEBERLEBTE.* Ich hatte behauptet, die
    // > Ordnung werde von zwei Mutationen gehalten -- eine davon fing nichts. **Eine
    // > Beschaedigungsprobe, die niemand fangen kann, ist keine.**
    let (c, _) = c_von(
        "module t { static mut d : u32 = 0; atomic f : bool publishes { d } release;
impl fn melde(w : u32) effects { writes d, publishes f } costs <= 8 ops
{ d = w; f = true publishes { d }; } }",
    );
    assert!(
        c.contains("atomic_store_explicit(&f, true, memory_order_release)"),
        "ein Speichern nimmt die DEKLARIERTE Ordnung, kein `=`:\n{c}"
    );

    // **2. Ein `check` wird eine Funktion, und seine Behauptung faehrt mit.** Eine Probe
    // auszuliefern, deren Behauptung nirgends steht, waere eine Zahl ohne Gegenstand.
    let (c, f) = c_von(
        "module t {
extern fn hole() -> u32 effects { pure } costs <= 2 ops;
check eich {
    claim \"Das Messgeraet meldet an einem leeren Feld null.\"
    measures n
    gates all_done
    can_fail { if hole() != 0 { return false; } return true; }
    floor n >= 1
    counterprobe \"Fuellung ausgehaengt\" expects waechst
} }",
    );
    assert!(f.is_empty(), "{f:?}");
    assert!(c.contains("bool pruefe_eich(void) {"), "{c}");
    assert!(c.contains("claim: Das Messgeraet meldet"), "die Behauptung faehrt mit:\n{c}");
    // **Die Gegenprobe ist die Zeile, die die Probe erst zu einer macht.**
    assert!(c.contains("counterprobe: \"Fuellung ausgehaengt\""), "{c}");

    // **3. «B41b»: die Kante steht an der TABELLE, und dann laeuft der Durchlauf.**
    //
    // Der Befund kam aus dem Erzeuger -- *„the domain does not name the EDGE it walks"* --
    // und ist eingeloest: nicht so, wie `chain(a, b) in` es vormacht (am Durchlauf), sondern
    // an der `table`. Ein Baum wird an vielen Stellen durchlaufen, und zwei Stellen koennten
    // sonst verschiedene Felder nennen, ohne dass jemand die beiden vergleicht.
    let (c, f) = c_von(
        "module t { table T count 8 {
    tree { parent p, child k, sibling g }
    slot { p : option index into T, k : option index into T, g : option index into T, } }
impl fn f(t : ptr<normal, rw> T, s : index into T) effects { writes t.slots } costs <= 64 ops
{ traverse v over descendants of t.slots[s] by consuming touches writes t.slots { } } }",
    );
    assert!(f.is_empty(), "{f:?}");
    // Ohne Stapel: `k` hinunter, `g` zur Seite, `p` zurueck -- und der Sonderwert ist `count`.
    assert!(c.contains("t->slots[_k1].k != 8u"), "der Abstieg laeuft an `child`:\n{c}");
    assert!(c.contains("t->slots[_k1].g != 8u"), "zur Seite an `sibling`:\n{c}");
    assert!(c.contains("= t->slots[_k1].p;"), "zurueck an `parent`:\n{c}");
    // **Die Wurzel ist kein Nachfahre ihrer selbst.**
    assert!(c.contains("if (_k1 == _r1) break;"), "{c}");
    // **Jede Kante wird gelesen, BEVOR der Rumpf laeuft** -- `by consuming` zerstoert den
    // Knoten, den es bekommt.
    let vor = c.find("uint32_t _w1;").expect("der Nachfolger steht fest");
    let rumpf = c.find("const uint32_t v = _k1;").expect("der Rumpf steht da");
    assert!(vor < rumpf, "der Nachfolger wird NACH dem Rumpf gelesen:\n{c}");

    // **Und eine Tabelle OHNE `tree` faellt beim Namen** -- die Weigerung ist nicht weg,
    // sie hat nur ihren richtigen Grund bekommen.
    let (_, f) = c_von(
        "module t { table T count 8 { slot { p : option index into T, k : option index into T, } }
impl fn f(t : ptr<normal, rw> T, s : index into T) effects { writes t.slots } costs <= 64 ops
{ traverse v over descendants of t.slots[s] by consuming touches writes t.slots { } } }",
    );
    assert!(
        f.iter().any(|s| s.contains("with no `tree`")),
        "eine Tabelle ohne Kante muss beim Namen fallen: {f:?}"
    );

    // **Eine TEILMENGE ist eine Aussage.** Wer nur `parent` erklaert, kann aufwaerts laufen
    // und abwaerts nicht -- und hoert genau das, statt „noch nicht abgesenkt".
    let (_, f) = c_von(
        "module t { table T count 8 {
    tree { parent p }
    slot { p : option index into T, } }
impl fn f(t : ptr<normal, rw> T, s : index into T) effects { reads t.slots } costs <= 64 ops
{ traverse v over descendants of t.slots[s] by consuming touches reads t.slots { } } }",
    );
    assert!(
        f.iter().any(|s| s.contains("needs all three edges")),
        "der Abstieg braucht alle drei: {f:?}"
    );

    // **`D006`-`D008`: die Kante wird am SLOT geprueft, und zwar im Pruefer.** Die Lehre aus
    // «B24» -- eine Regel, die nur auf der Erzeugerflaeche steht, beruehren die meisten
    // Programme nie.
    for (quelle, code) in [
        ("tree { parent nichtsda }\n    slot { p : option index into T, }", "D006"),
        ("tree { parent p }\n    slot { p : u32, }", "D007"),
        ("tree { parent p }\n    slot { p : option index into U, }", "D008"),
    ] {
        let q = format!(
            "module t {{ table U count 4 {{ slot {{ x : bool, }} }}
table T count 8 {{ {quelle} }} }}"
        );
        let (baum, mut a) = gabbro_syntax::lies("p.gab", &q);
        gabbro_check::pruefe(&baum, &mut a);
        assert!(
            a.absagen.iter().any(|x| x.code == code),
            "{code} muss fallen: {:?}",
            a.absagen.iter().map(|x| format!("{} {}", x.code, x.text)).collect::<Vec<_>>()
        );
    }
}

/// **«B22» geschlossen: benachbarte Zeichenketten sind EINE.**
///
/// Der Befund lautete: *„Eine Behauptung, die in eine Zeile passen muss, wird kuerzer
/// geschrieben, nicht genauer."*
///
/// > **Die naheliegende Reparatur waere gewesen, `newline` in der Zeichenkette zu erlauben** —
/// > und sie haette die Pruefung mitgenommen, die dahintersteht: ein vergessenes
/// > Anfuehrungszeichen verschluckt sonst den Rest der Datei, und `L001` faende es nie.
/// > *W6 in die andere Richtung: eine Pruefung wegzunehmen braucht einen Grund, und hier gab
/// > es keinen.*
#[test]
fn benachbarte_zeichenketten_sind_eine_und_l001_bleibt() {
    let q = "module t {
extern fn e() -> u32 effects { pure } costs <= 2 ops;
check lang {
    claim    \"Erste Zeile,\"
             \"zweite Zeile,\"
             \"dritte.\"
    measures n
    gates    g
    can_fail { if e() != 0 { return false; } return true; }
    floor    n >= 1
} }";
    let (baum, mut a) = gabbro_syntax::lies("p.gab", q);
    assert_eq!(a.fehler_zahl(), 0, "{}", a.zeige(q));
    let c = gabbro_check::emit::emittiere(&baum, &mut a);
    assert!(
        c.contains("claim: Erste Zeile, zweite Zeile, dritte."),
        "die drei Stuecke werden EIN Satz, mit Leerzeichen verbunden:\n{c}"
    );

    // **Und die Sprechprobe: `L001` muss weiter greifen.** Eine Zeichenkette endet auf ihrer
    // Zeile -- daran hat sich nichts geaendert, und genau das faengt das vergessene
    // Anfuehrungszeichen.
    let (_, a2) = gabbro_syntax::lies("p.gab", "module t { assume x \"offen\n und weiter\" ; }");
    assert!(
        a2.absagen.iter().any(|x| x.code == "L001"),
        "eine Zeichenkette endet auf ihrer Zeile, und L001 sagt es: {:?}",
        a2.absagen.iter().map(|x| x.code).collect::<Vec<_>>()
    );
}

/// **«B14b» geschlossen: `let … else` packt auch einen `place` aus.**
///
/// Der Befund lautete: *„`let … else` verlangt RECHTS einen `call`. Ein `option`-wertiges
/// `place` laesst sich damit nicht auspacken — und ein Atomic IST ein `place`."* Genau daran
/// zerbrach die Messstelle in `FRAGMENTE.md` F6.
///
/// **Die Paesse, die nur Rufe interessieren, fragen ueber `als_ruf()`** — statt dass jeder von
/// ihnen die neue Form kennen muss. *Ein Ort ruft nichts: der Aufrufgraph sieht keine Kante,
/// M2 verbraucht nichts, und der Kostenpass zaehlt EINE Operation fuer die Ablesung.*
#[test]
fn let_else_packt_auch_einen_ort_aus() {
    let q = "module t {
atomic g : u32 publishes nothing relaxed;
impl fn f() -> bool effects { reads g } costs <= 4 ops
{ let x = g else (e) { return false; } return true; } }";
    let (baum, mut a) = gabbro_syntax::lies("p.gab", q);
    assert_eq!(a.fehler_zahl(), 0, "{}", a.zeige(q));
    let _ = gabbro_check::pruefe(&baum, &mut a);
    assert_eq!(a.fehler_zahl(), 0, "und die Paesse tragen es auch:\n{}", a.zeige(q));

    // **Ein Ort ruft nichts.** Der Aufrufgraph darf daraus keine Kante machen -- sonst
    // waere `g` ein unbekannter Gerufener und JEDE Huelle darueber eine untere Schranke.
    let h = gabbro_check::aufrufgraph::erhebe(&baum).huelle("t::f");
    assert!(
        h.unvollstaendig.is_none(),
        "ein ausgepackter Ort ist kein Ruf: {:?}",
        h.unvollstaendig
    );

    // Was NICHT geht, geht weiterhin nicht: ein zusammengesetzter Ausdruck.
    let (_, a2) = gabbro_syntax::lies("p.gab",
        "module t { impl fn f() -> bool effects { pure } costs <= 4 ops \
         { let x = 1 + 2 else (e) { return false; } return true; } }");
    assert!(
        a2.absagen.iter().any(|x| x.code == "P016"),
        "ein Rechenausdruck hat nichts auszupacken"
    );
}

/// **«B7» geschlossen: eine Funktion darf einen Verbund HERSTELLEN -- und wie, ist eine
/// Entscheidung ueber die Grammatik, nicht ueber eine fehlende Produktion.**
///
/// Der Befund lautete: *„`return Completion { id: …, len: … }` laesst sich nicht schreiben."*
/// Er las sich wie eine Luecke. **Er war eine Mehrdeutigkeit:** ein geschweiftes Literal waere
/// die ERSTE Ausdrucksform, die mit `{` weitergeht, und an **76** Korpusstellen folgt ein `{`
/// direkt auf einen Ausdruck. Rust loest das mit einem Kontextschalter; wer ihn falsch setzt,
/// verliest die 76 Stellen, **ohne dass ein Tor es meldet.**
///
/// Gewaehlt ist darum `P(a: 1, b: true)`: eine Klammer statt einer geschweiften, und die
/// Marke `ident ":"` kann kein Ausdruck sein.
#[test]
fn verbundwert_ist_ein_markierter_ruf() {
    let q = "module t {
type P = { a : u32, b : bool, };
impl fn f(x : u32) -> P requires x < 8 effects { pure } costs <= 4 ops
{ return P(a: x, b: true); } }";
    let (baum, mut a) = gabbro_syntax::lies("p.gab", q);
    assert_eq!(a.fehler_zahl(), 0, "{}", a.zeige(q));
    let _ = gabbro_check::pruefe(&baum, &mut a);
    assert_eq!(a.fehler_zahl(), 0, "und die Paesse tragen es auch:\n{}", a.zeige(q));

    // **Ein Konstruktor ruft nichts** -- dieselbe Aussage wie bei «B14b», und hier die
    // wichtigste: eine Kante auf `P` machte den Gerufenen unbekannt, und ueber einem
    // unbekannten Gerufenen ist jede Huelle nur noch eine untere Schranke.
    let h = gabbro_check::aufrufgraph::erhebe(&baum).huelle("t::f");
    assert!(
        h.unvollstaendig.is_none(),
        "ein Verbundkonstruktor ist kein Aufruf: {:?}",
        h.unvollstaendig
    );

    // Und im C steht ein zusammengesetztes Literal mit BENANNTEN Bestimmern -- die Marken
    // werden uebersetzt, nicht weggeworfen.
    let (baum, mut a) = gabbro_syntax::lies("p.gab", q);
    let c = gabbro_check::emit::emittiere(&baum, &mut a);
    assert!(
        c.contains("typedef struct {\n    uint32_t a;\n    bool b;\n} P;"),
        "ein `type` mit Feldern wird ein C-Verbund:\n{c}"
    );
    assert!(
        c.contains("return (P){ .a = x, .b = true };"),
        "die Marken werden benannte Bestimmer, nicht eine Reihung:\n{c}"
    );
}

/// **Die Gegenprobe zu «B7» -- und sie ist die Haelfte, an der die Entscheidung haengt.**
///
/// Eine Luecke schliesst sich immer, indem man die Form zulaesst. Was hier zaehlt, ist, dass
/// die verworfenen Formen **benannt** abgesagt werden statt still anders gelesen zu werden.
#[test]
fn die_verworfenen_verbundformen_werden_benannt_abgesagt() {
    let faellt = |q: &str, code: &str| {
        let (baum, mut a) = gabbro_syntax::lies("p.gab", q);
        let _ = gabbro_check::pruefe(&baum, &mut a);
        let c: Vec<&str> = a.absagen.iter().map(|x| x.code).collect();
        assert!(c.contains(&code), "erwartet {code}, gefallen {c:?}\n{q}");
    };

    // Das geschweifte Literal selbst -- mit seinem Grund, nicht als Folgefehler.
    faellt(
        "module t { type P = { a : u32, }; impl fn f() -> P effects { pure } costs <= 2 ops \
         { return P { a: 1 }; } }",
        "P037",
    );
    // **Der stille Fall, gegen den die Markenpflicht steht:** zwei gleichtypige Felder in
    // Reihung sind vertauschbar, ohne dass ein Typ dagegen spricht.
    faellt(
        "module t { type P = { a : u32, b : u32, }; impl fn f() -> P effects { pure } \
         costs <= 4 ops { return P(1, 2); } }",
        "M107",
    );
    // `deckt fs zs <-> map fst zs = fs`: die REIHENFOLGE, nicht bloss die Menge. Der Beweis
    // waehlt die strengere Fassung, und diese Zeile ist sie.
    faellt(
        "module t { type P = { a : u32, b : bool, }; impl fn f() -> P effects { pure } \
         costs <= 4 ops { return P(b: true, a: 1); } }",
        "M106",
    );
    // Ein ausgelassenes Feld -- die zweite Haelfte derselben Zusage.
    faellt(
        "module t { type P = { a : u32, b : bool, }; impl fn f() -> P effects { pure } \
         costs <= 4 ops { return P(a: 1); } }",
        "M106",
    );
    // Eine Marke an einer Funktion: die Reihenfolge ihrer Parameter steht in ihrer
    // Deklaration, und eine Marke am Aufruf waere eine zweite Wahrheit daneben.
    faellt(
        "module t { impl fn g(x : u32) -> u32 effects { pure } costs <= 2 ops { return x; } \
         impl fn f() -> u32 effects { pure } costs <= 4 ops { return g(x: 1); } }",
        "M107",
    );
    // Halb markiert ist weder das eine noch das andere.
    faellt(
        "module t { type P = { a : u32, b : u32, }; impl fn f() -> P effects { pure } \
         costs <= 4 ops { return P(a: 1, 2); } }",
        "P036",
    );

    // **Und die 76 Stellen lesen weiter wie vorher.** Das ist die Zusage, um derentwillen
    // die geschweifte Form ueberhaupt verworfen wurde -- sie gehoert angenagelt.
    let q = "module t { static s : u32 = 0;
impl fn f(x : u32) -> u32 requires x < 4 effects { reads s } costs <= 9 ops
{ if x < 2 { return 1; } return s; } }";
    let (_, a) = gabbro_syntax::lies("p.gab", q);
    assert_eq!(a.fehler_zahl(), 0, "ein `{{` nach einem Ausdruck gehoert dem Block:\n{}", a.zeige(q));
}

/// **«B37» geschlossen: eine ORDNUNG auf einer linearen Geistmarke.**
///
/// Der Befund stand im Bootfragment selbst: *„die Marke traegt die Reihenfolge, aber sie
/// traegt sie als LINEARITAET, nicht als ORDNUNG."* **Ein linearer Wert erzwingt eine KETTE,
/// aber nicht WELCHE** — bei sechs Bootschritten typprueften alle **720** Reihenfolgen, weil
/// M2 nur sieht, dass jede Marke genau einmal weiterwandert.
///
/// Das Fragment nannte beide Auswege und verwarf keinen: *je Schritt eine eigene Marke (dann
/// waechst der Wortschatz mit jedem Bootschritt) oder eine Ordnung auf Marken.* **Gewaehlt ist
/// die zweite:** die Stufen sind Bezeichner in EINER Deklaration, der Wortschatz waechst um
/// `order` und `advances` — einmal.
#[test]
fn eine_ordnung_auf_marken_schliesst_b37() {
    let kopf = "module t {
linear ghost type P order { roh, mmu, caps };
static mut w : u32 = 0;
extern fn a(p : P) -> P advances roh -> mmu effects { consumes p, writes w } costs <= 8 ops;
extern fn b(p : P) -> P advances mmu -> caps effects { consumes p, writes w } costs <= 8 ops;
";
    let sauber = format!(
        "{kopf}impl fn s(p : P) -> P advances roh -> caps effects {{ consumes p, writes w }} \
         costs <= 32 ops {{ let x = a(p); let y = b(x); return y; }} }}"
    );
    let (baum, mut ab) = gabbro_syntax::lies("p.gab", &sauber);
    assert_eq!(ab.fehler_zahl(), 0, "{}", ab.zeige(&sauber));
    let _ = gabbro_check::pruefe(&baum, &mut ab);
    assert_eq!(ab.fehler_zahl(), 0, "und die Paesse tragen es:\n{}", ab.zeige(&sauber));

    // **Die Zeile, die die 720 Reihenfolgen auf eine reduziert.** Vertauscht faellt `O003`.
    let vertauscht = format!(
        "{kopf}impl fn s(p : P) -> P advances roh -> caps effects {{ consumes p, writes w }} \
         costs <= 32 ops {{ let x = b(p); let y = a(x); return y; }} }}"
    );
    let (baum2, mut ab2) = gabbro_syntax::lies("p.gab", &vertauscht);
    let _ = gabbro_check::pruefe(&baum2, &mut ab2);
    let c: Vec<&str> = ab2.absagen.iter().map(|x| x.code).collect();
    assert!(c.contains(&"O003"), "zwei vertauschte Schritte muessen fallen: {c:?}");

    // **`O002` macht aus der Liste eine Ordnung.** Ohne sie waere `order` Zeremonie.
    let rueckwaerts = "module t { linear ghost type P order { roh, mmu }; static mut w : u32 = 0;
extern fn z(p : P) -> P advances mmu -> roh effects { consumes p, writes w } costs <= 8 ops; }";
    let (baum3, mut ab3) = gabbro_syntax::lies("p.gab", rueckwaerts);
    let _ = gabbro_check::pruefe(&baum3, &mut ab3);
    assert!(
        ab3.absagen.iter().any(|x| x.code == "O002"),
        "ein Schritt rueckwaerts ist keiner"
    );

    // **`O004`: eine Strecke, die unterwegs aufhoert, ist keine.**
    let kurz = format!(
        "{kopf}impl fn s(p : P) -> P advances roh -> caps effects {{ consumes p, writes w }} \
         costs <= 32 ops {{ let x = a(p); return x; }} }}"
    );
    let (baum4, mut ab4) = gabbro_syntax::lies("p.gab", &kurz);
    let _ = gabbro_check::pruefe(&baum4, &mut ab4);
    assert!(
        ab4.absagen.iter().any(|x| x.code == "O004"),
        "die Schritte muessen sich zur Zusage zusammensetzen"
    );
}

/// **K11.1 — der Zweig wird jetzt ENTSCHIEDEN, nicht nur gemeldet.**
///
/// Bis zum 2026-08-17 stand hier `O005`, ein Hinweis: *„dieser Pass entscheidet das nicht."*
/// Die Meldung war richtig und keine Loesung. Gewaehlt ist die strenge Fassung —
/// **alle Zweige erreichen dieselbe Stufe** —, weil man von ihr aus lockern kann und
/// umgekehrt nie.
///
/// > **Die erste Fassung fiel in der GEGENRICHTUNG auf**: die Giftprobe fiel wie gewollt, und
/// > die saubere fiel mit. Ein Zweig, der mit `return` ENDET, schliesst sich nicht an — er
/// > verlaesst die Funktion. *Ein Tor, das nur in eine Richtung geprueft wird, misst die
/// > Haelfte.*
#[test]
fn die_zweige_muessen_dieselbe_stufe_erreichen() {
    let kopf = "module t {
linear ghost type P order { roh, mmu };
static mut w : u32 = 0;
extern fn a(p : P) -> P advances roh -> mmu effects { consumes p, writes w } costs <= 8 ops;
extern fn ende(p : P) effects { consumes p, writes w } costs <= 8 ops;
";
    // **Sauber: beide Wege erreichen `mmu`** — der erste, indem er die Funktion verlaesst.
    let gleich = format!(
        "{kopf}impl fn s(p : P, k : bool) -> P advances roh -> mmu \
         effects {{ consumes p, writes w }} costs <= 32 ops \
         {{ if k {{ let x = a(p); return x; }} let y = a(p); return y; }} }}"
    );
    let (b1, mut a1) = gabbro_syntax::lies("p.gab", &gleich);
    let _ = gabbro_check::pruefe(&b1, &mut a1);
    assert_eq!(a1.fehler_zahl(), 0, "ein Zweig mit `return` endet:\n{}", a1.zeige(&gleich));

    // **Gift: ein Zweig schiebt, der andere nicht.**
    let ungleich = format!(
        "{kopf}impl fn s(p : P, k : bool) advances roh -> mmu \
         effects {{ consumes p, writes w }} costs <= 32 ops \
         {{ if k {{ let x = a(p); ende(x); }} else {{ ende(p); }} }} }}"
    );
    let (b2, mut a2) = gabbro_syntax::lies("p.gab", &ungleich);
    let _ = gabbro_check::pruefe(&b2, &mut a2);
    assert!(
        a2.absagen.iter().any(|x| x.code == "O006"),
        "auseinanderlaufende Zweige: {:?}",
        a2.absagen.iter().map(|x| x.code).collect::<Vec<_>>()
    );

    // **Ein Schritt in einer Schleife wird abgelehnt, nicht geeinigt.** Ein Schritt geschieht
    // einmal, eine Schleife oft.
    let schleife = format!(
        "{kopf}reason Ablauf {{ zu_lang = 1 \"zu lang\" }}
impl fn s(p : P) advances roh -> mmu effects {{ consumes p, writes w }} \
         costs <= 512 ops {{ retry warten until w == 1 bounded 64 ops \
         on_exceeded zu_lang effects {{ consumes p, writes w }} \
         {{ let x = a(p); ende(x); }} return; }} }}"
    );
    let (b3, mut a3) = gabbro_syntax::lies("p.gab", &schleife);
    let _ = gabbro_check::pruefe(&b3, &mut a3);
    assert!(
        a3.absagen.iter().any(|x| x.code == "O006"),
        "ein Schritt in einer Schleife: {:?}",
        a3.absagen.iter().map(|x| x.code).collect::<Vec<_>>()
    );
}

/// **K11.2.1 — `protects` beisst, und die Gegenrichtung fand den Befund zuerst.**
///
/// Bis zum 2026-08-17 ging das hier mit **0 Fehlern** durch: `lock KAPPEN protects { K }` stand
/// da, `K.slots[i].a = 1;` daneben, ohne `locks`. `H001`–`H006` pruefen die **Disziplin** einer
/// genommenen Sperre — geteilt gegen exklusiv, Rang, Haltezeit. **Sie pruefen nicht, dass sie
/// genommen wird.**
///
/// > *Die Klasse Rennen hing damit nicht am Speichermodell — sie hing an einer Regel, die
/// > niemand gebaut hatte.*
///
/// **`H008` ist ein HINWEIS, kein Fehler**, und darum steht die Probe hier statt in der
/// Giftmappe: in einem AUSSCHNITT kann die Nahme ausserhalb liegen. Im eigenen Korpus lag sie
/// nirgends — `beispiele/05` erklaerte `lock BERICHT protects { farbbericht }` und nahm sie
/// nie; der Platz war ueber `publishes`/`awaits` synchronisiert.
#[test]
fn protects_beisst_und_eine_nie_genommene_sperre_faellt_auf() {
    let kopf = "module t { table K count 8 { slot { a : u32, } }
lock KAPPEN protects { K } rank 3 held <= 40 ops;
";
    // **Drei Wege gelten als gehalten**, und das ist die Bauart der Sprache, keine Nachsicht.
    for (was, koerper) in [
        ("ein `locks`-Block", "effects { writes K, locks KAPPEN } costs <= 40 ops \
                               { locks KAPPEN { K.slots[i].a = 1; } return true; }"),
        ("ein `effects { locks … }`", "effects { writes K, locks KAPPEN } costs <= 40 ops \
                                       { K.slots[i].a = 1; return true; }"),
        ("ein `requires Held(…)`", "requires Held(KAPPEN) effects { writes K } \
                                    costs <= 4 ops { K.slots[i].a = 1; return true; }"),
    ] {
        let q = format!("{kopf}impl fn f(i : index into K) -> bool {koerper} }}");
        let (b, mut a) = gabbro_syntax::lies("p.gab", &q);
        let _ = gabbro_check::pruefe(&b, &mut a);
        assert!(
            !a.absagen.iter().any(|x| x.code == "H007"),
            "{was} zaehlt als gehalten:\n{}",
            a.zeige(&q)
        );
    }

    // **Und ohne alles faellt es.**
    let ohne = format!(
        "{kopf}impl fn f(i : index into K) -> bool effects {{ writes K }} costs <= 4 ops \
         {{ K.slots[i].a = 1; return true; }} }}"
    );
    let (b, mut a) = gabbro_syntax::lies("p.gab", &ohne);
    let _ = gabbro_check::pruefe(&b, &mut a);
    assert!(
        a.absagen.iter().any(|x| x.code == "H007"),
        "ein geschuetzter Platz ohne Sperre: {:?}",
        a.absagen.iter().map(|x| x.code).collect::<Vec<_>>()
    );

    // **Ein `spec fn` fasst zur Laufzeit nichts an** — die Vorabmessung meldete genau eine,
    // und sie war der einzige Treffer im Korpus.
    let spec = format!(
        "{kopf}spec fn p(i : index into K) -> bool effects {{ pure }} = K.slots[i].a == 1; }}"
    );
    let (b, mut a) = gabbro_syntax::lies("p.gab", &spec);
    let _ = gabbro_check::pruefe(&b, &mut a);
    assert!(
        !a.absagen.iter().any(|x| x.code == "H007"),
        "eine Spezifikationsfunktion braucht keine Sperre:\n{}",
        a.zeige(&spec)
    );

    // **`H008`: eine Klausel, die niemand einhaelt.** Hinweis, nicht Fehler — im Ausschnitt
    // kann die Nahme ausserhalb liegen.
    let nie = "module t { static mut b : u64 = 0;
lock B protects { b } rank 2 held <= 50 ops;
impl fn f(x : u32) -> u32 effects { pure } costs <= 4 ops { return x; } }";
    let (bb, mut aa) = gabbro_syntax::lies("p.gab", nie);
    let _ = gabbro_check::pruefe(&bb, &mut aa);
    assert!(
        aa.absagen.iter().any(|x| x.code == "H008"),
        "eine nie genommene Sperre: {:?}",
        aa.absagen.iter().map(|x| x.code).collect::<Vec<_>>()
    );
}

/// **`const fn` — comptime, das WERTE rechnet und keine Schablone kostet.**
///
/// Die Linie steht in `PLAN.md` („Wozu Gabbro taugen wird"):
///
/// ```text
/// comptime, das WERTE rechnet   ->  kostet keine Schablone
/// comptime, das CODE  erzeugt   ->  kostet eine, und die will bewiesen werden
/// ```
///
/// **Der Nachweis ist nicht, dass es parst, sondern dass die ZAHL ANKOMMT** — dass
/// `count zellen(NKERNE)` dieselbe Indexschranke erzeugt wie `count 256`.
#[test]
fn const_fn_rechnet_werte_und_die_schranke_kommt_an() {
    let mit = "module t {
const NKERNE : u32 = 64;
const fn zellen(kerne : u32 in 0 .. 256) -> u32 effects { pure } costs <= 4 ops
{ return kerne * 4; }
table W count zellen(NKERNE) { slot { a : u32, } }
impl fn f() -> u32 effects { reads W } costs <= 4 ops
{ let i : index into W = 300; return W.slots[i].a; } }";
    let (b, mut a) = gabbro_syntax::lies("p.gab", mit);
    assert_eq!(a.fehler_zahl(), 0, "es parst:\n{}", a.zeige(mit));
    let _ = gabbro_check::pruefe(&b, &mut a);
    let text: Vec<String> = a.absagen.iter().map(|x| x.text.clone()).collect();
    assert!(
        text.iter().any(|t| t.contains("0 .. 255")),
        "die gerechnete Zahl muss dieselbe Schranke erzeugen wie ein Literal: {text:?}"
    );

    // **Und ohne `const fn` dasselbe** — die beiden Wege müssen sich decken, sonst rechnet
    // der Zusatz etwas anderes als er verspricht.
    let ohne = mit.replace("count zellen(NKERNE)", "count 256");
    let (b2, mut a2) = gabbro_syntax::lies("p.gab", &ohne);
    let _ = gabbro_check::pruefe(&b2, &mut a2);
    let text2: Vec<String> = a2.absagen.iter().map(|x| x.text.clone()).collect();
    assert_eq!(text, text2, "gerechnet und hingeschrieben muessen dasselbe ergeben");
}

/// **M103 traf die Form nicht, für die es da ist — Kernzustand ohne Zeiger.**
///
/// `index_pruefen` schlug den globalen Träger **unqualifiziert** nach; in einem
/// `module`-Block traf `globale.get("W")` nie, und die Schranke sagte nichts.
///
/// > *Zwei Blicke auf dieselbe Karte gingen auseinander* — `typ_von_ort` benutzte `suche`,
/// > `index_pruefen` ein direktes `get`. **Und nur einer davon hatte einen Test.**
///
/// Gefunden, weil beim Bauen von `const fn` eine Giftprobe nicht fiel, die fallen musste (R11).
#[test]
fn die_indexschranke_greift_auch_an_einer_globalen_tabelle() {
    let q = "module t { table W count 8 { slot { a : u32, } }
impl fn f(i : u32 in 0 .. 300) -> u32 effects { reads W } costs <= 4 ops
{ return W.slots[i].a; } }";
    let (b, mut a) = gabbro_syntax::lies("p.gab", q);
    let _ = gabbro_check::pruefe(&b, &mut a);
    assert!(
        a.absagen.iter().any(|x| x.code == "M103"),
        "eine Tabelle ueber ihren globalen Namen hat dieselbe Schranke wie ueber einen Zeiger: {:?}",
        a.absagen.iter().map(|x| x.code).collect::<Vec<_>>()
    );

    // Und der saubere Fall geht durch -- sonst waere die Regel nur ein Verbot.
    let sauber = "module t { table W count 8 { slot { a : u32, } }
impl fn f(i : index into W) -> u32 effects { reads W } costs <= 4 ops
{ return W.slots[i].a; } }";
    let (b2, mut a2) = gabbro_syntax::lies("p.gab", sauber);
    let _ = gabbro_check::pruefe(&b2, &mut a2);
    assert_eq!(a2.fehler_zahl(), 0, "{}", a2.zeige(sauber));
}

/// **`accumulates` senkt ab — und der Beweis lag VOR dem Konstrukt.**
///
/// Zwei Entscheidungen, die die Sprache vorher nicht traf: **die Zellenzahl** (`per cpu N` —
/// `SPRACHE.md` §11.4 sagte *„one cell per core"* und nannte sie nirgends) und **der aktuelle
/// Kern**, der KEIN Ausdruck der Sprache ist, sondern ein fremder Rumpf.
///
/// > **Die Falle steckt in `min`:** C nullt statische Felder, und null ist nicht das Neutrale
/// > von `min`. Der erste Differenzlauf lieferte `0` statt `3`, weil 61 unberührte Zellen
/// > mitzählten. *Der Beweis hatte den Satz (`min_ist_monoid_mit_top`), die Absenkung nicht.*
///
/// Gelöst über die **Darstellung**: `min` und `and` speichern das Komplement und falten mit
/// `max` bzw. `or` — dann trifft Zero-Init genau das Neutrale.
#[test]
fn accumulates_senkt_ab_und_min_traegt_sein_neutrales() {
    let q = "module t {
const NK : u32 = 8;
accumulates hoch : u64 merge max per cpu NK;
accumulates tief : u64 merge min per cpu NK;
impl fn m(t : u64) effects { writes tief } costs <= 8 ops { tief = t; }
impl fn l() -> u64 effects { reads tief } costs <= 64 ops { return tief; } }";
    let (b, mut a) = gabbro_syntax::lies("p.gab", q);
    assert_eq!(a.fehler_zahl(), 0, "{}", a.zeige(q));
    let c = gabbro_check::emit::emittiere(&b, &mut a);
    assert_eq!(a.fehler_zahl(), 0, "die Absenkung traegt:\n{}", a.zeige(q));

    // **`max` faltet direkt, `min` ueber das Komplement** -- daran haengt das Neutrale.
    assert!(c.contains("static _Atomic uint64_t tief_zellen[NK];"), "{c}");
    assert!(c.contains("return (uint64_t)~z;"), "`min` nimmt die Umkehr zurueck:\n{c}");
    assert!(!c.contains("return (uint64_t)~z;\n}\n\nstatic uint64_t hoch"), "{c}");
    // Ein Schreiben MELDET, es setzt nicht -- der Kern faltet in seine eigene Zelle.
    assert!(c.contains("tief_melde("), "ein Schreiben meldet:\n{c}");
    assert!(c.contains("return tief_lies();"), "ein Lesen faltet:\n{c}");
    // Und der aktuelle Kern kommt von aussen.
    assert!(c.contains("gabbro_kern()"), "{c}");

    // **Ohne `per cpu` weigert er sich benannt** statt `NCORES` zu raten.
    let ohne = "module t { accumulates h : u64 merge max; }";
    let (b2, mut a2) = gabbro_syntax::lies("p.gab", ohne);
    let _ = gabbro_check::emit::emittiere(&b2, &mut a2);
    assert!(
        a2.absagen.iter().any(|x| x.code == "C001"),
        "eine Deklaration, die ihre eigene Groesse nicht nennt, ist keine"
    );
}

/// **Die parametrische Zusage wird GELESEN, nicht fallengelassen.**
///
/// Bis zum 2026-08-18 stand im Kostenpass ein `return`, wenn die Zusage nicht konstant
/// auswertbar war. Gemessen:
///
/// ```text
/// impl fn schleife(n : u32 in 0 .. 1000) -> u32 costs <= 0 * n ops { return n; }
/// -> 3 Items, 0 Fehler, 0 Hinweise        (der Rumpf kostet 1)
/// ```
///
/// > *Ein Vertrag, den niemand liest, ist keine Zusage, sondern eine Zeile.*
///
/// **Verglichen wird gegen die KLEINSTE Belegung** — alle Symbole null. Dort ist die Zusage
/// am kleinsten und muss genau dort halten. *`40 * n` ist bei `n = 0` gleich null.*
#[test]
fn eine_parametrische_kostenzusage_wird_entschieden() {
    let faellt = |q: &str, code: &str| {
        let (b, mut a) = gabbro_syntax::lies("p.gab", q);
        let _ = gabbro_check::pruefe(&b, &mut a);
        let c: Vec<&str> = a.absagen.iter().map(|x| x.code).collect();
        assert!(c.contains(&code), "erwartet {code}, gefallen {c:?}\n{q}");
    };
    let geht = |q: &str| {
        let (b, mut a) = gabbro_syntax::lies("p.gab", q);
        let _ = gabbro_check::pruefe(&b, &mut a);
        assert_eq!(a.fehler_zahl(), 0, "{}", a.zeige(q));
    };

    // **`0 * n` ist null, und ein Rumpf, der eine Operation kostet, verletzt das.**
    faellt(
        "module t { impl fn s(n : u32 in 0 .. 9) -> u32 effects { pure } costs <= 0 * n ops \
         { return n; } }",
        "K001",
    );
    // Dasselbe fuer `40 * n` -- bei `n = 0` ist auch das null.
    faellt(
        "module t { impl fn s(n : u32 in 0 .. 9) -> u32 effects { pure } costs <= 40 * n ops \
         { return n; } }",
        "K001",
    );
    // **Mit einem konstanten Glied haelt sie** -- und das ist die Form, die ein Programm
    // wirklich zusagen kann.
    geht(
        "module t { impl fn s(n : u32 in 0 .. 9) -> u32 effects { pure } \
         costs <= 1 + 40 * n ops { return n; } }",
    );
    // **Ein Produkt zweier Symbole ist nicht lesbar -- und das steht als ABSAGE da.**
    faellt(
        "module t { impl fn s(n : u32 in 0 .. 9, m : u32 in 0 .. 9) -> u32 effects { pure } \
         costs <= n * m ops { return n; } }",
        "K005",
    );
    // Und die Konstante bleibt, was sie war -- die haeufigste Form darf nicht teurer werden.
    geht("module t { impl fn s() -> u32 effects { pure } costs <= 2 ops { return 1; } }");
}

/// **`K010` — dieselbe Form, andere Klasse: unter einer Sperre ist sie ein FEHLER.**
///
/// Die Zeile darüber lässt `costs <= 40 * n` zu und hält sie gegen die kleinste Belegung.
/// **`held <= 40 * n` darf nicht zugelassen werden**, und der Grund steht nicht im Pass,
/// sondern im Wort: `held` ist eine **Latenzaussage** — wie lange ein *anderer* Kern wartet.
/// Die Latenz lebt an der GRÖSSTEN Belegung, und die hat ein Symbol nicht.
///
/// **Gemessen 2026-08-20, vor der Regel:**
///
/// ```text
/// lock KAPPEN … held <= 40 * eintraege ops;   locks KAPPEN { <5 Operationen> }
/// → 4 Items, 0 Fehler, 0 Hinweise
/// ```
///
/// `haltezeiten` nahm nur auf, was `konst_wert` hergab — der Rest fiel aus der Karte, **und
/// mit der Karte fiel `K002`.** *Eine Zusage, die den Wächter abschaltet, den sie füttern
/// sollte, ist teurer als gar keine.*
///
/// **Und `ast.rs` schrieb `held <= constexpr ops` in den Kommentar, seit es das Feld gibt.**
/// Der Parser nahm jeden Ausdruck. Eine Grammatikzusage im Kommentar ist keine.
#[test]
fn eine_haltezeit_muss_eine_zahl_sein() {
    let codes = |q: &str| -> Vec<String> {
        let (b, mut a) = gabbro_syntax::lies("p.gab", q);
        let _ = gabbro_check::pruefe(&b, &mut a);
        a.absagen.iter().map(|x| x.code.to_string()).collect()
    };
    // Der Rumpf ist in allen drei Fassungen derselbe: fuenf Zuweisungen unter der Sperre.
    let quelle = |haltezeit: &str| {
        format!(
            "module t {{ static mut e : u32 in 0 .. 1023 = 0; \
             lock K protects {{ e }} rank 0 {haltezeit}; \
             impl fn viel() effects {{ writes e, locks K }} costs <= 300 ops \
             {{ locks K {{ e = 1; e = 2; e = 3; e = 4; e = 5; }} }} }}"
        )
    };

    // **Die kaputte Richtung: ein Symbol in der Haltezeit.**
    let c = codes(&quelle("held <= 40 * e ops"));
    assert!(c.contains(&"K010".to_string()), "eine symbolische Haltezeit faellt nicht: {c:?}");

    // **Und die geteilte Seite hat denselben Riegel** — `shared held` ist ein eigenes Feld,
    // und ein Riegel, der nur den einen Zweig kennt, laesst den anderen offen.
    let c = codes(&quelle("held <= 40 ops shared held <= 40 * e ops"));
    assert!(c.contains(&"K010".to_string()), "eine symbolische GETEILTE Haltezeit faellt nicht: {c:?}");

    // **Die saubere Richtung: eine Zahl geht durch** -- und `K002` schweigt, weil fuenf
    // Operationen unter vierzig liegen.
    let c = codes(&quelle("held <= 40 ops"));
    assert!(c.is_empty(), "eine konstante Haltezeit faellt: {c:?}");

    // **Die dritte Richtung, und sie ist der eigentliche Ertrag:** mit der Zahl greift
    // `K002` wieder. *Ohne diese Zeile belegte der Test nur, dass nichts rot wird -- und
    // eine Zusicherung ueber das AUSBLEIBEN einer Absage bewacht keine Absenkung.*
    let c = codes(&quelle("held <= 2 ops"));
    assert!(c.contains(&"K002".to_string()), "die Sperre ist mit einer Zahl wieder bewacht: {c:?}");
}

/// **`opaque` beisst — und der Fund ist grösser als sein Anlass.**
///
/// ```gabbro
/// opaque type F32 = u32;
/// impl fn unsinn(a : F32, b : F32) -> F32 { return a & b; }
/// → 3 Items, 0 Fehler, 0 Hinweise          (bis 2026-08-18)
/// ```
///
/// Bitweises Und behält die Breite, also schwieg die Überlaufregel. **Dass `a + b` fiel, war
/// Zufall** — es fiel an `M104`, nicht an der Undurchsichtigkeit. *Wo die Breiten aufgingen,
/// ging der Unsinn durch.*
///
/// > Es trifft nicht nur `F32`, sondern **jeden Zeugen- und Neutyp der Sprache**: `Pa` gegen
/// > `Va`, zwei `index into` verschiedener Instanzen, einen Rang mit einer Zellenzahl.
///
/// **Die Probe trifft drei Operatoren, nicht einen** — eine Regel, die nur `&` fängt, ist eine
/// Regel über `&`.
#[test]
fn ein_undurchsichtiger_typ_hat_die_rechnung_seines_traegers_nicht() {
    let kopf = "module t { opaque type F32 = u32; type Zaehler = u32 in 0 .. 9;\n";
    for op in ["&", "|", "^"] {
        let q = format!(
            "{kopf}impl fn f(a : F32, b : F32) -> F32 effects {{ pure }} costs <= 4 ops \
             {{ return a {op} b; }} }}"
        );
        let (b, mut a) = gabbro_syntax::lies("p.gab", &q);
        let _ = gabbro_check::pruefe(&b, &mut a);
        assert!(
            a.absagen.iter().any(|x| x.code == "D003"),
            "`{op}` auf einem undurchsichtigen Typ: {:?}",
            a.absagen.iter().map(|x| x.code).collect::<Vec<_>>()
        );
    }

    // **Die Positivrichtung, und ohne sie wäre die Regel nur ein Verbot:** ein Neutyp, der
    // NICHT undurchsichtig ist, rechnet weiter.
    let klar = format!(
        "{kopf}impl fn s(a : Zaehler, b : Zaehler) -> u32 effects {{ pure }} costs <= 4 ops \
         {{ return a + b; }} }}"
    );
    let (b, mut a) = gabbro_syntax::lies("p.gab", &klar);
    let _ = gabbro_check::pruefe(&b, &mut a);
    assert_eq!(a.fehler_zahl(), 0, "{}", a.zeige(&klar));

    // **Und Vergleiche bleiben erlaubt.** Zwei Adressen zu vergleichen deutet den Träger
    // nicht um — es ordnet Werte desselben Typs. *Verboten ist das Rechnen.*
    let vgl = format!(
        "{kopf}impl fn g(x : F32, y : F32) -> bool effects {{ pure }} costs <= 4 ops \
         {{ return x == y; }} }}"
    );
    let (b, mut a) = gabbro_syntax::lies("p.gab", &vgl);
    let _ = gabbro_check::pruefe(&b, &mut a);
    assert_eq!(a.fehler_zahl(), 0, "ein Vergleich ordnet, er rechnet nicht:\n{}", a.zeige(&vgl));

    // **Und die Ablesung, um derentwillen der Fund entstand:** ein Gleitkommawort, das
    // Gabbro nur BEWEGT, braucht keine Arithmetik — und geht damit heute schon.
    let bewegt = "module t { opaque type F32 = u32;
table Ecken count 64 { slot { x : F32, } }
impl fn setze(i : index into Ecken, v : F32) effects { writes Ecken } costs <= 4 ops
{ Ecken.slots[i].x = v; } }";
    let (b, mut a) = gabbro_syntax::lies("p.gab", bewegt);
    let _ = gabbro_check::pruefe(&b, &mut a);
    assert_eq!(a.fehler_zahl(), 0, "ein Treiber bewegt, er rechnet nicht:\n{}", a.zeige(bewegt));
}

/// **«B24» entschieden: die Bitlage liegt im EIGENEN WORT des Feldes.**
///
/// Der Befund fragte zweierlei, und beides wird beantwortet statt umgangen:
///
/// | Frage | Antwort |
/// |---|---|
/// | worauf bezieht sich eine Position jenseits der Wortbreite? | **auf nichts** — eine Absage |
/// | wie wirkt sie mit `endian` zusammen? | das Wort wird zuerst gelesen, dann die Bits aus dem **Wert** gezogen |
///
/// **Die Kachelung ist nicht nur eine Prüfung, sondern die Wortgrenze selbst.** *Der erste
/// Anlauf las alle aufeinanderfolgenden Bitfelder gleicher Breite als EIN Wort und meldete an
/// `dscp @[7:2]` eine Überlappung mit `version @[7:4]` — zwei Bytes des IP-Kopfs, als eines
/// gelesen.*
#[test]
fn eine_bitlage_liegt_im_eigenen_wort() {
    let c_von = |q: &str| -> (String, Vec<String>) {
        let (baum, mut a) = gabbro_syntax::lies("p.gab", q);
        assert_eq!(a.fehler_zahl(), 0, "die Probe parst nicht:\n{}", a.zeige(q));
        let c = gabbro_check::emit::emittiere(&baum, &mut a);
        (c, a.absagen.iter().map(|x| x.text.clone()).collect())
    };

    // **Zwei Bytes, vier Felder** — und die Wortgrenze fällt aus der Kachelung.
    let (c, f) = c_von(
        "module t { format K endian big { a : u8 @[7:4], b : u8 @[3:0], \
         c : u8 @[7:2], d : u8 @[1:0], } }",
    );
    assert!(f.is_empty(), "{f:?}");
    assert!(c.contains("(v->bytes + 0) >> 4) & 15u"), "a liegt in Byte 0, oben:\n{c}");
    assert!(c.contains("(v->bytes + 1) >> 2) & 63u"), "c liegt in Byte 1:\n{c}");

    // Ein 16-Bit-Wort mit drei Flaggen und dreizehn Bits — der Fall des IP-Kopfs.
    let (c, f) = c_von(
        "module t { format K endian big { f : u16 @[15:13], g : u16 @[12:0], } }",
    );
    assert!(f.is_empty(), "{f:?}");
    assert!(c.contains("gabbro_be16(v->bytes + 0) >> 13) & 7u"), "{c}");

    // **Jenseits der Wortbreite ist nichts.**
    let (_, f) = c_von("module t { format K endian big { w : u8 @[9:8], r : u8 @[7:0], } }");
    assert!(
        f.iter().any(|s| s.contains("beyond the word width")),
        "eine Lage jenseits des Wortes ist eine Absage, keine Bedeutung: {f:?}"
    );

    // **Eine Lücke heisst `reserved`** — und ohne sie ist die Wortgrenze geraten.
    let (_, f) = c_von("module t { format K endian big { o : u8 @[7:4], u : u8 @[1:0], } }");
    assert!(f.iter().any(|s| s.contains("leave a gap")), "{f:?}");

    // Und `reserved` schliesst sie: das Feld existiert, sein Leser nicht.
    let (c, f) = c_von(
        "module t { format K endian big { o : u8 @[7:4], m : u8 @[3:2] reserved, \
         u : u8 @[1:0], } }",
    );
    assert!(f.is_empty(), "`reserved` fuellt die Luecke: {f:?}");
    assert!(!c.contains("K_m("), "ein reserviertes Feld bekommt keinen Leser:\n{c}");
}

/// **Ein Wirkungsattribut darf nicht an eine Funktion, die etwas RUFT** («OPT2», 2026-08-19).
///
/// `effects` ist geprüft — aber gegen die **deklarierten** Wirkungen der Gerufenen, und bei
/// einem `extern fn` ist diese Deklaration eine Annahme über fremden Code. Ein
/// `__attribute__((pure))` ist keine Buchung, sondern eine **Anweisung an den Übersetzer**.
///
/// Gemessen am selben Tag, in `pruefe-emission.sh`: Fragment 10 zählte 65 Rufe bei `-O0` und
/// **null** unter `-O1` — GCC strich sie, weil das Attribut sie für wirkungslos erklärte.
///
/// *Dieser Test steht hier und nicht nur im Emissionswächter, weil `mutiere-pruefer.py` nur
/// `cargo test` fährt: eine Regel, deren einzige Probe ein Shell-Wächter ist, kann keine
/// Mutation fangen.*
#[test]
fn ein_wirkungsattribut_geht_nur_an_wen_nichts_ruft() {
    let q = r#"
module m {
static mut z : u32 = 0;
extern fn fremd() -> u32 effects { reads z } costs <= 1 ops;
impl fn blatt(a : u32 in 0 .. 10) -> u32 effects { pure } costs <= 1 ops { return a; }
impl fn liest() -> u32 effects { reads z } costs <= 1 ops { return z; }
impl fn ruft() -> u32 effects { reads z } costs <= 4 ops { return fremd(); }
}
"#;
    let (baum, mut absagen) = gabbro_syntax::lies("attribut.gab", q);
    gabbro_check::pruefe(&baum, &mut absagen);
    let c = gabbro_check::emit::emittiere(&baum, &mut absagen);
    let zeile = |name: &str| -> String {
        c.lines()
            .find(|z| z.contains(&format!("{name}(")) && z.trim_end().ends_with(';'))
            .unwrap_or_else(|| panic!("kein Prototyp fuer `{name}` in:\n{c}"))
            .to_string()
    };
    assert!(
        zeile("blatt").contains("__attribute__((const))"),
        "ein `pure`-Blatt ohne Zeigerparameter bekommt `const`: {}",
        zeile("blatt")
    );
    assert!(
        zeile("liest").contains("__attribute__((pure))"),
        "ein reiner Leser bekommt `pure`: {}",
        zeile("liest")
    );
    // **Gefragt wird nach den WIRKUNGSATTRIBUTEN, nicht nach jedem `__attribute__`.**
    //
    // Seit dem 2026-08-25 traegt jede Funktion ohne `pub` im C ein `static` und dazu ein
    // `__attribute__((unused))` -- sonst faellt eine private Funktion, die in DIESER Einheit
    // niemand ruft, an `-Wunused-function`. *Das ist eine Aussage ueber die BINDUNG und
    // keine ueber die Wirkung*, und dieser Test fragt nach der Wirkung.
    //
    // > Die erste Fassung stand auf `!contains("__attribute__")` und hat damit zwei Fragen
    // > zu einer gemacht. Sie fiel an der richtigen Antwort.
    for verboten in ["__attribute__((const))", "__attribute__((pure))"] {
        assert!(
            !zeile("ruft").contains(verboten),
            "wer RUFT, bekommt KEINS -- unter dem Ruf kann ein fremder Rumpf liegen: {}",
            zeile("ruft")
        );
    }
}

/// **Ein `asm`-Block wird `__volatile__` abgesenkt** («OPT3», 2026-08-19).
///
/// Der Block hat **per Konstruktion** eine Wirkung, die Gabbro nicht liest — der Prüfer
/// kennt den Befehlstext nicht. Ohne `__volatile__` darf der C-Übersetzer ihn streichen,
/// wenn er kein Ergebnis benutzt sieht.
///
/// > *Wer den Text nicht liest, darf ihn auch nicht für entbehrlich halten.*
///
/// Der Test steht hier und nicht nur im Emissionswächter, weil `mutiere-pruefer.py` nur
/// `cargo test` fährt.
#[test]
fn ein_asm_block_ist_volatile_und_traegt_seine_operanden() {
    let q = r#"
module m {
static mut GERAET : u32 = 0;
impl fn ausgeben(tor : u16, wert : u8)
    effects { writes GERAET } costs <= 1 ops arch x86_64
    = asm { "outb %[wert], %[tor]" in { wert : "a", tor : "d" } clobbers { memory } };
}
"#;
    let (baum, mut absagen) = gabbro_syntax::lies("asm.gab", q);
    gabbro_check::pruefe(&baum, &mut absagen);
    assert_eq!(absagen.fehler_zahl(), 0, "der versiegelte Block ist sauber");
    let c = gabbro_check::emit::emittiere(&baum, &mut absagen);
    assert!(
        c.contains("__asm__ __volatile__("),
        "ohne `__volatile__` darf der C-Uebersetzer den Block streichen:\n{c}"
    );
    assert!(
        c.contains("[wert] \"a\" (wert)") && c.contains("[tor] \"d\" (tor)"),
        "die Operanden stehen mit ihrer Nebenbedingung da:\n{c}"
    );
    assert!(c.contains(": \"memory\");"), "`clobbers memory` steht im C:\n{c}");
}

/// **`restrict` nur bei genau EINEM Zeiger je Trägertyp** («OPT1», 2026-08-19).
///
/// Das ist Hypothese **H2a** aus `beweise/Restrict_Alleinzugriff.thy`. Fällt sie, fällt der
/// Satz — `ohne_trennung_kein_restrict` sagt es in der Gegenrichtung —, und was der Erzeuger
/// dann hinschreibt, ist **undefiniertes Verhalten**: Code, der bei `-O0` stimmt und bei
/// `-O2` nicht.
#[test]
fn restrict_nur_bei_einem_zeiger_je_traeger() {
    let q = r#"
module m {
const N : u32 = 4;
table T count N { slot { a : u32, } }
impl fn kopieren(d : ptr<normal, rw> T, s : ptr<normal, r> T, i : index into T)
    effects { reads s.slots, writes d.slots } costs <= 4 ops { d.slots[i].a = s.slots[i].a; }
impl fn setzen(d : ptr<normal, rw> T, i : index into T)
    effects { writes d.slots } costs <= 2 ops { d.slots[i].a = 1; }
}
"#;
    let (baum, mut absagen) = gabbro_syntax::lies("restrict.gab", q);
    gabbro_check::pruefe(&baum, &mut absagen);
    let c = gabbro_check::emit::emittiere(&baum, &mut absagen);
    assert!(
        c.contains("void kopieren(T *d, const T *s,"),
        "zwei Zeiger desselben Traegers koennen dasselbe sein -- KEIN restrict:\n{c}"
    );
    assert!(
        c.contains("void setzen(T *restrict d,"),
        "ein einziger Zeiger auf diesen Traeger -- restrict:\n{c}"
    );
}

/// **Ein `asm`-Rumpf liefert sein Ergebnis über `out { result : … }`** (2026-08-20).
///
/// Bis dahin weigerte sich der Erzeuger für jeden `asm`-Rumpf mit Rückgabewert, und damit war
/// ein Systemaufruf nur halb schreibbar: **absetzen ging, die Rückgabe lesen nicht.**
/// *`result` steht als Wort längst in der Grammatik (`primary`), also brauchte es kein neues.*
///
/// Der Test hält auch fest, was daran fast schiefgegangen wäre: `erwarte_text` fügt
/// benachbarte Zeichenketten mit einem **Leerzeichen** zusammen (richtig für Prosa in
/// `claim`), und damit wurde aus zwei Befehlszeilen `mov $1, %eax syscall` — kein Befehl mehr.
#[test]
fn ein_asm_rumpf_liefert_sein_ergebnis() {
    let q = r#"
module m {
static mut GERAET : u32 = 0;
impl fn schreiben(fd : u64, puffer : u64, laenge : u64) -> u64
    effects { writes GERAET } costs <= 1 ops arch x86_64
    = asm { "mov $1, %eax" "syscall"
            in  { fd : "D", puffer : "S", laenge : "d" }
            out { result : "=a" }
            clobbers { memory } };
}
"#;
    let (baum, mut absagen) = gabbro_syntax::lies("syscall.gab", q);
    gabbro_check::pruefe(&baum, &mut absagen);
    assert_eq!(absagen.fehler_zahl(), 0, "der versiegelte Aufruf ist sauber");
    let c = gabbro_check::emit::emittiere(&baum, &mut absagen);
    assert!(c.contains("uint64_t result;"), "das Ergebnis bekommt eine Stelle:\n{c}");
    assert!(c.contains("[result] \"=a\" (result)"), "und einen Ausgangsoperanden:\n{c}");
    assert!(c.contains("    return result;\n"), "und wird zurueckgegeben:\n{c}");
    // **Zwei Befehlszeilen bleiben ZWEI.**
    assert!(
        c.contains("\"mov $1, %%eax\\n\"") && c.contains("\"syscall\\n\""),
        "benachbarte Zeichenketten duerfen hier NICHT zusammenfallen:\n{c}"
    );
}

/// **«ABI0/ABI1» — die Brücke trägt, in BEIDE Richtungen** (2026-08-20).
///
/// Ohne sie fällt eine Zusage an der Dateigrenze laut, aber sie fällt: `E009`
/// (*„unknown to the graph"*) und `K003`. **Es fehlte kein Riegel, es fehlte eine Brücke.**
///
/// Mit ihr wird geprüft: ein falsches `pure` über die Grenze gibt `E008`, und eine richtige
/// Wirkungsliste geht durch. *Der Unterschied zwischen „schweigt" und „prüft" ist der ganze
/// Sinn der Sache.*
#[test]
fn eine_schnittstelle_traegt_die_zusage_ueber_die_dateigrenze() {
    let lib = r#"
module bib {
pub static mut z : u32 = 0;
pub impl fn tu() effects { writes z } costs <= 1 ops { z = 1; }
}
"#;
    let (lb, mut la) = gabbro_syntax::lies("bib.gab", lib);
    gabbro_check::pruefe(&lb, &mut la);
    assert_eq!(la.fehler_zahl(), 0, "die Bibliothek selbst ist sauber");
    let gabi = gabbro_check::abi::schreibe(&lb, lib);
    assert!(gabi.starts_with(gabbro_check::abi::MARKE), "die Marke steht oben:\n{gabi}");
    assert!(gabi.contains("pub extern fn tu()"), "die Signatur ohne Rumpf, mit `pub`:\n{gabi}");
    assert!(!gabi.contains("z = 1;"), "der RUMPF geht nicht mit:\n{gabi}");
    // **Und ausdruecklich nicht:** Hardwareannahmen und Sperrraenge. Absolute Raenge
    // komponieren nicht («ABI2»), und eine Annahme ueber die Grenze zu tragen, ohne die
    // Beweispflicht zu zaehlen, waere die stille Bewegung («ABI4»).
    assert!(!gabi.contains("assume"), "keine Annahmen in dieser Fassung:\n{gabi}");
    assert!(!gabi.contains("rank"), "keine Raenge in dieser Fassung:\n{gabi}");

    let falsch = format!("{gabi}\nmodule app {{\nuse bib::tu;\nimpl fn ruft() effects {{ pure }} costs <= 4 ops {{ tu(); }}\n}}\n");
    let (b1, mut a1) = gabbro_syntax::lies("app.gab", &falsch);
    gabbro_check::pruefe(&b1, &mut a1);
    assert!(
        a1.absagen.iter().any(|a| a.code == "E008"),
        "ein falsches `pure` ueber die Grenze muss FALLEN, nicht zu `E009` absinken"
    );

    let richtig = format!("{gabi}\nmodule app {{\nuse bib::tu;\nimpl fn ruft() effects {{ writes z }} costs <= 4 ops {{ tu(); }}\n}}\n");
    let (b2, mut a2) = gabbro_syntax::lies("app.gab", &richtig);
    gabbro_check::pruefe(&b2, &mut a2);
    assert_eq!(a2.fehler_zahl(), 0, "und die richtige Zusage geht durch:\n{}", a2.zeige(&richtig));
}

/// **«C1»: `option index into T` senkt zum SONDERWERT ab — und der Sonderwert ist `count`.**
///
/// Der Beweis lag seit dem 2026-08-17 in `beweise/Option_Sonderwert.thy`
/// (`sonderwert_ausserhalb`, `kodiere_injektiv`, `kodiere_wort_injektiv`) und **kein Erzeuger
/// benutzte ihn**: `None`, `Some(i)`, ein `static … = None` und ein `match` ueber einem Ort
/// waren zehn Weigerungen. *Ein Satz ohne Leser ist die Haelfte, die «NL» beklagt.*
///
/// Vier Stellen tragen die Absenkung, und jede ist hier gemessen:
///
/// * die Zieltabelle kommt aus dem TYP des Ortes, nicht aus seinem Namen (`ort_typ`),
/// * `None` wird `T_NONE` und **nur dort, wo die Zieltabelle feststeht**,
/// * `return None` haengt am Rueckgabetyp der Funktion, nicht am Ausdruck,
/// * ein `let` ohne erklaerten Typ liest ihn vom Slotfeld ab, statt ihn zu raten.
#[test]
fn option_senkt_zum_sonderwert_ab() {
    let q = "module t {
table H count 8 { slot { kopf : u64, naechst : option index into H, } }
static mut frei : option index into H = None;
impl fn belegen(h : ptr<normal, rw> H) -> option index into H
    effects { reads frei, writes frei, reads h.slots } costs <= 6 ops
{ match frei { None => { return None; } Some(i) => { frei = h.slots[i].naechst; return Some(i); } } }
impl fn freigeben(h : ptr<normal, rw> H, i : index into H)
    effects { reads frei, writes frei, writes h.slots } costs <= 5 ops
{ h.slots[i].naechst = frei; frei = Some(i); }
impl fn kopf(h : ptr<normal, r> H, i : index into H) -> u64
    effects { reads h.slots } costs <= 3 ops
{ let k = h.slots[i].kopf; return k; } }";
    let (b, mut a) = gabbro_syntax::lies("p.gab", q);
    assert_eq!(a.fehler_zahl(), 0, "{}", a.zeige(q));
    let c = gabbro_check::emit::emittiere(&b, &mut a);
    assert_eq!(a.fehler_zahl(), 0, "die Absenkung traegt:\n{}", a.zeige(q));

    // Der Sonderwert IST die Laenge -- der erste Index, den es nicht gibt.
    assert!(c.contains("#define H_NONE (8)"), "der Sonderwert ist `count`:\n{c}");
    // Ein `static` faengt bei ihm an, nicht bei null.
    assert!(c.contains("static uint32_t frei __attribute__((unused)) = H_NONE;"), "{c}");
    // Ein `match` ueber einem Ort wird der Vergleich gegen ihn.
    assert!(c.contains("!= H_NONE"), "das `match` vergleicht gegen den Sonderwert:\n{c}");
    // `return None` haengt am RUECKGABETYP -- ohne ihn stuende hier ein Bezeichner `None`.
    assert!(c.contains("return H_NONE;"), "`return None` kennt seine Tabelle:\n{c}");
    assert!(!c.contains(" None"), "kein blankes `None` im C:\n{c}");
    // `frei = Some(i)` ist der Wert selbst, kein Zusatzwort.
    assert!(c.contains("frei = i;"), "`Some(i)` ist der Index selbst:\n{c}");
    // Und ein `let` ohne erklaerten Typ liest ihn vom Slotfeld ab.
    assert!(c.contains("uint64_t k = h->slots[i].kopf;"), "der Typ wird abgelesen:\n{c}");

    // **Wo die Zieltabelle NICHT feststeht, weigert er sich** -- er raet keinen Sonderwert.
    let ohne = "module t { extern fn nimm(x : u32) costs <= 1 ops;
impl fn f() costs <= 2 ops { nimm(None); } }";
    let (b2, mut a2) = gabbro_syntax::lies("p.gab", ohne);
    let _ = gabbro_check::emit::emittiere(&b2, &mut a2);
    assert!(
        a2.absagen.iter().any(|x| x.code == "C001"),
        "ein `None` ohne Tabelle ist keine Absenkung, sondern ein Bezeichner"
    );
}

/// **Und die PRAEMISSE des Beweises wird geprueft, nicht angenommen.**
///
/// `sonderwert_kollidiert_bei_vollem_wort`: fuellt `count N` das Indexwort genau aus, faellt
/// der Sonderwert mit einem gueltigen Index zusammen. *Wer `count 2^32` schreibt, hat keinen
/// Platz mehr fuer „keine" — und das ist eine Absage, keine stille Verbreiterung.*
#[test]
fn der_sonderwert_prueft_seine_praemisse() {
    let q = "module t { const N : u64 = 4294967296;
table H count N { slot { naechst : option index into H, } } }";
    let (b, mut a) = gabbro_syntax::lies("p.gab", q);
    let _ = gabbro_check::emit::emittiere(&b, &mut a);
    assert!(
        a.absagen.iter().any(|x| x.code == "C001" && x.text.contains("fills the index word")),
        "die Praemisse des dritten Satzes wird GEPRUEFT: {:?}",
        a.absagen.iter().map(|x| x.text.clone()).collect::<Vec<_>>()
    );
}

/// **«C2»: ein `tagged type` senkt zu `struct { marke; union { … } }` ab.**
///
/// Fuenf Weigerungen im Korpus hingen daran, und keine war eine Sprachfrage. Die eine
/// Entscheidung ist der TYP der Marke: sie wird ein `enum`, damit `switch` ohne `default`
/// unter `-Wswitch` ein **zweiter Leser von `D005`** ist. *Zwei unabhaengige Leser derselben
/// Zusage -- dieselbe Bauart wie `-Wmissing-field-initializers` beim Verbundkonstruktor.*
#[test]
fn tagged_senkt_zu_marke_und_vereinigung_ab() {
    let q = "module t {
tagged type N = { Leer, Kurz(u32), Lang(u64) };
table A count 4 { slot { was : N, } }
impl fn gewicht(m : N) -> u64 effects { pure } costs <= 9 ops
{ match m { Leer => { return 0; } Kurz(k) => { return k; } Lang(p) => { return p; } } return 0; }
impl fn art(m : N) -> u32 effects { pure } costs <= 9 ops
{ match m { Leer => { return 0; } Kurz(k) => { return 1; } Lang(p) => { return 2; } } return 0; }
impl fn im_slot(a : ptr<normal, r> A, i : index into A) -> u64
    effects { reads a.slots } costs <= 12 ops
{ match a.slots[i].was { Leer => { return 0; } Kurz(k) => { return k; } Lang(p) => { return p; } }
  return 0; } }";
    let (b, mut a) = gabbro_syntax::lies("p.gab", q);
    assert_eq!(a.fehler_zahl(), 0, "{}", a.zeige(q));
    let c = gabbro_check::emit::emittiere(&b, &mut a);
    assert_eq!(a.fehler_zahl(), 0, "die Absenkung traegt:\n{}", a.zeige(q));

    // Die Marke ist ein `enum` -- ohne ihn haette `-Wswitch` nichts zu lesen.
    assert!(c.contains("typedef enum {"), "die Marke ist ein `enum`:\n{c}");
    assert!(c.contains("    N_Kurz,"), "je Variante ein Wert:\n{c}");
    // Eine Variante ohne Nutzlast steht in der Marke und in KEINEM Glied.
    assert!(!c.contains("Leer;"), "`Leer` hat kein Glied der Vereinigung:\n{c}");
    assert!(c.contains("    union {"), "{c}");
    assert!(c.contains("        uint64_t Lang;"), "je Nutzlast ein Glied:\n{c}");
    // Der `switch` liest die MARKE, nicht den Wert.
    assert!(c.contains("switch (m.marke) {"), "der `switch` liest die Marke:\n{c}");
    assert!(c.contains("switch (a->slots[i].was.marke) {"), "auch ueber einem Slotfeld:\n{c}");
    // **Kein Sammelzweig.** Er wuerde genau den Leser stilllegen, um dessentwillen die
    // Marke ein `enum` ist.
    assert!(!c.contains("default:"), "ein `switch` ohne `default`:\n{c}");
    // Jeder Zweig liest das Glied SEINER Variante -- und nur das.
    assert!(c.contains("uint32_t k = m.last.Kurz;"), "{c}");
    assert!(c.contains("uint64_t p = m.last.Lang;"), "{c}");
    // Und der Binder, den ein Zweig nicht liest, wird stillgelegt statt weggelassen.
    assert!(c.contains("(void)k;"), "ein ungelesener Binder wird stillgelegt:\n{c}");
    // *Aber nur der ungelesene:* `art` liest `k` nicht, `gewicht` sehr wohl.
    assert_eq!(c.matches("(void)k;").count(), 1, "nur der ungelesene:\n{c}");
}

/// **Und der Erzeuger prueft die Erschoepfung SELBST -- als zweiter Leser, nicht als erster.**
///
/// `D005` haelt sie eine Ebene hoeher. Steht hier trotzdem eine Pruefung, dann weil ein
/// `switch` mit einem fehlenden Fall **durchfaellt und NICHTS tut** — die eine Gestalt, in
/// der ein Erzeugnis stillschweigend etwas anderes rechnet als die Quelle sagt.
#[test]
fn markiertes_match_ohne_jede_variante_faellt() {
    let q = "module t {
tagged type N = { Leer, Kurz(u32), Lang(u64) };
impl fn g(m : N) -> u32 effects { pure } costs <= 9 ops
{ match m { Leer => { return 0; } Kurz(k) => { return k; } } return 0; } }";
    let (b, mut a) = gabbro_syntax::lies("p.gab", q);
    let _ = gabbro_check::emit::emittiere(&b, &mut a);
    assert!(
        a.absagen.iter().any(|x| x.code == "C001" && x.text.contains("every variant")),
        "ein `switch` mit fehlendem Fall faellt durch und tut nichts: {:?}",
        a.absagen.iter().map(|x| x.text.clone()).collect::<Vec<_>>()
    );
}

/// **«C3a/c»: `reason` senkt ab, `group` erzeugt NICHTS, und `let … else` bleibt `C001`.**
///
/// Die drei gehoeren zusammen, weil sie die Grenze dieses Plans zeigen: zwei Formen sind
/// Handwerk, die dritte waere eine **Sprachentscheidung** -- und die wird nicht getroffen,
/// sondern gebucht.
#[test]
fn reason_gruppe_und_die_gezogene_linie() {
    let q = "module t {
reason E { KeinSlot = 1 \"kein freier Slot mehr\" Ungueltig = 7 \"abgelaufen\" exhaustive }
table A count 4 { slot { a : u32, } }
table B count 4 { slot { b : u32, } }
group Zustellung over { A, B } { invariant beides cost O(n) runs offline :
    forall i in slots of A : A.slots[i].a >= B.slots[i].b; }
impl fn setze(i : index into A) effects { writes A.slots } costs <= 4 ops
{ A.slots[i].a = 3; } }";
    let (b, mut a) = gabbro_syntax::lies("p.gab", q);
    assert_eq!(a.fehler_zahl(), 0, "{}", a.zeige(q));
    let c = gabbro_check::emit::emittiere(&b, &mut a);
    assert_eq!(a.fehler_zahl(), 0, "die Absenkung traegt:\n{}", a.zeige(q));

    // **Die Zahlen STEHEN DA** -- der Erzeuger waehlt keine.
    assert!(c.contains("E_KeinSlot = 1,"), "der Wert kommt aus der Quelle:\n{c}");
    assert!(c.contains("E_Ungueltig = 7,"), "auch der zweite, und er ist nicht 2:\n{c}");
    // Und der Text faehrt mit: er ist die Erklaerung, die sonst nirgends steht.
    assert!(c.contains("kein freier Slot mehr"), "{c}");

    // **Eine `group` erzeugt nichts.** Kein Typ, kein Name, keine Zeile.
    assert!(!c.contains("Zustellung"), "eine Gruppe erzeugt NICHTS:\n{c}");
    assert!(!c.contains("beides"), "auch ihre Invariante nicht:\n{c}");

    // **Die Tabelle IST der Speicher, wo die Quelle sie beim Namen nennt** -- und nur dort.
    assert!(c.contains("static A A_speicher;"), "`A` wird beim Namen genannt:\n{c}");
    assert!(c.contains("A_speicher.slots[i].a = 3;"), "kein Pfeil auf einen Typnamen:\n{c}");
    assert!(!c.contains("B_speicher"), "`B` wird nur in der Invariante genannt:\n{c}");

    // **«C3a» ist entschieden: `-> T or R`** (2026-08-20). Die Absage, die hier stand,
    // nannte zwei Fragen -- was `e` traegt und wie ein Ruf sein Scheitern meldet -- und
    // beide sind jetzt an der DEKLARATION beantwortet, wo eine Antwort ueberprueft werden
    // kann. *Kein neues Wort: `or` steht schon im Wortschatz.*
    let l = "module t { reason G { Leer = 1 \"nichts da\" exhaustive }
extern fn hol() -> u32 or G effects { pure } costs <= 1 ops;
extern fn weg() -> never effects { diverges } costs <= 1 ops;
impl fn f() -> u32 effects { pure } costs <= 8 ops
{ let x = hol() else (e) { weg(); } return x; } }";
    let (b2, mut a2) = gabbro_syntax::lies("p.gab", l);
    let c2 = gabbro_check::emit::emittiere(&b2, &mut a2);
    assert_eq!(a2.fehler_zahl(), 0, "{}", a2.zeige(l));
    // Der Erfolg ist der Rueckgabewert, der Wert und der Grund gehen durch Ausgaenge.
    assert!(c2.contains("bool hol(uint32_t *_wert, G *_grund);"), "{c2}");
    // **`x` lebt AUSSERHALB des Blockes, `e` nicht.**
    let x = c2.find("uint32_t x;").expect("`x` steht vor dem Block");
    let e = c2.find("G e;").expect("`e` steht darin");
    assert!(x < e, "`x` muss den Block ueberleben:\n{c2}");
    assert!(c2.contains("if (!hol(&x, &e)) {"), "{c2}");

    // **Und die Gegenrichtung faellt im PRUEFER, nicht erst im Erzeuger** («B24»):
    // ein `let … else` ueber einer Funktion ohne `or`, und ein Ruf auf eine MIT `or`
    // ausserhalb eines `let … else`.
    for (quelle, code) in [
        ("extern fn hol() -> u32 effects { pure } costs <= 1 ops;
extern fn weg() -> never effects { diverges } costs <= 1 ops;
impl fn f() -> u32 effects { pure } costs <= 8 ops
{ let x = hol() else (e) { weg(); } return x; }", "N028"),
        ("reason G { Leer = 1 \"nichts\" exhaustive }
extern fn hol() -> u32 or G effects { pure } costs <= 1 ops;
impl fn f() -> u32 effects { pure } costs <= 8 ops
{ let x = hol(); return x; }", "N029"),
    ] {
        let q = format!("module t {{ {quelle} }}");
        let (baum, mut a) = gabbro_syntax::lies("p.gab", &q);
        gabbro_check::pruefe(&baum, &mut a);
        assert!(
            a.absagen.iter().any(|x| x.code == code),
            "{code} muss fallen: {:?}",
            a.absagen.iter().map(|x| format!("{} {}", x.code, x.text)).collect::<Vec<_>>()
        );
    }
}

/// **«C3b»: `rcu` und `observes` -- und der Unterschied zur Sperre ist das, was FEHLT.**
///
/// Ein `rcu` senkt ab wie ein `lock`: zwei Prototypen, keine Zeile Rumpf. Im Erzeugnis steht
/// dann kein `_nimm`, das jemanden aufhaelt -- der Lesebereich wird betreten und verlassen,
/// **ausgeschlossen wird niemand.** *Das ist die ganze Substanz des Konstrukts.*
#[test]
fn rcu_und_observes_senken_ab() {
    let q = "module t {
table K count 8 { slot { z : u32, } }
rcu D protects { K } reclaims frei;
static mut frei : option index into K = None;
lock S protects { K, frei } rank 3 held <= 100 ops;
impl fn lies(i : index into K) -> u32 effects { reads K.slots } costs <= 4 ops
{ observes D { return K.slots[i].z; } return 0; } }";
    let (b, mut a) = gabbro_syntax::lies("p.gab", q);
    assert_eq!(a.fehler_zahl(), 0, "{}", a.zeige(q));
    let c = gabbro_check::emit::emittiere(&b, &mut a);
    assert_eq!(a.fehler_zahl(), 0, "die Absenkung traegt:\n{}", a.zeige(q));

    // Zwei Prototypen, kein Rumpf -- der kommt von aussen.
    assert!(c.contains("void D_lese_start(void);"), "{c}");
    assert!(c.contains("void D_lese_ende(void);"), "{c}");
    // **Und KEIN `_nimm`.** Was RCU von einer Sperre unterscheidet, steht als das da, was fehlt.
    assert!(!c.contains("D_nimm"), "RCU schliesst niemanden aus:\n{c}");
    // `reclaims` erzeugt nichts -- wo zurueckgegeben werden darf, rechnet H011/H012 nach.
    assert!(c.contains("reclaims frei"), "der Ort steht als Kommentar daneben:\n{c}");

    // **Der Lesebereich wird auf JEDEM Pfad verlassen** -- auch dem mit `return` darin.
    let vor_return = c
        .find("D_lese_ende();\n        return")
        .or_else(|| c.find("D_lese_ende();\n            return"));
    assert!(vor_return.is_some(), "vor dem `return` wird der Bereich verlassen:\n{c}");
    assert_eq!(c.matches("D_lese_ende();").count(), 2, "einmal am `return`, einmal am Ende:\n{c}");

    // Und der Parameter, den nur der Lesebereich liest, gilt nicht als tot.
    assert!(!c.contains("(void)i;"), "`i` wird im `observes` gelesen:\n{c}");
}

/// **«C4»: der Tausch, und die ORDNUNG ist die Falle.**
///
/// Ein `=` auf einem `_Atomic` bedeutet in C `seq_cst` -- *eine andere und teurere Ordnung
/// als die, die dasteht.* Ein Differenztest kann das an einem Faden nicht zeigen; diese
/// Probe zeigt es am erzeugten Text, und eine Mutation daneben beschaedigt sie.
///
/// **Und `update` bleibt eine Absage mit zwei Gruenden:** der Platz im Korpus ist gar kein
/// `atomic`, und selbst an einem waere die Absenkung ohne `NCORES` eine unbeschraenkte
/// CAS-Schleife -- *die Sprache emittiert nichts, was sie verbietet.*
#[test]
fn compare_exchange_nimmt_die_deklarierte_ordnung() {
    let q = "module t {
const NIEMAND : u32 = 0;
atomic B : u32 release;
impl fn nimm(f : u32) -> bool requires f > 0
    effects { writes B, publishes B } costs <= 16 ops
{ let g = B exchange f when old(B) == NIEMAND returns erfolg publishes nothing; return g; } }";
    let (b, mut a) = gabbro_syntax::lies("p.gab", q);
    assert_eq!(a.fehler_zahl(), 0, "{}", a.zeige(q));
    let c = gabbro_check::emit::emittiere(&b, &mut a);
    assert_eq!(a.fehler_zahl(), 0, "die Absenkung traegt:\n{}", a.zeige(q));

    assert!(c.contains("atomic_compare_exchange_strong_explicit"), "{c}");
    // **Die DEKLARIERTE Ordnung, nicht die Vorgabe.**
    assert!(c.contains("memory_order_release, memory_order_acquire"), "{c}");
    assert!(!c.contains("memory_order_seq_cst"), "ein `=` waere seq_cst:\n{c}");
    // Der erwartete Wert steht in einer eigenen Zelle -- C schreibt bei Misserfolg hinein.
    assert!(c.contains("uint32_t _cx1 = (uint32_t)(NIEMAND);"), "{c}");
    // Und der Parameter, den nur der Tausch liest, gilt nicht als tot.
    assert!(!c.contains("(void)f;"), "`f` ist der neue Wert:\n{c}");

    // **`update` bleibt `C001`, und die Absage nennt ihren Grund.**
    let u = "module t {
atomic Z : u64 relaxed;
impl fn hoch() -> u64 effects { writes Z } costs <= 12 ops
{ let alt = Z exchange update(v) { return v + 1; } publishes nothing; return alt; } }";
    let (b2, mut a2) = gabbro_syntax::lies("p.gab", u);
    let _ = gabbro_check::emit::emittiere(&b2, &mut a2);
    assert!(
        a2.absagen.iter().any(|x| x.code == "C001" && x.text.contains("BOUNDED CAS loop")),
        "die Schranke braucht `NCORES`: {:?}",
        a2.absagen.iter().map(|x| x.text.clone()).collect::<Vec<_>>()
    );
}

/// **«C5»: der Kleinkram, und zwei Stuecke davon waren KEINE Bauarbeit, sondern ein zweites
/// Register.**
///
/// `u64::max` war in `umgebung.rs` seit jeher eine Zahl; der Erzeuger hatte daneben seinen
/// eigenen, schwaecheren Auswerter und weigerte sich. *Zwei Register ueber derselben Sache,
/// und das schwaechere hat entschieden* (W7). Dasselbe eine Zeile weiter: `s.len >= 0` stand
/// im C, weil der Erzeuger nur BASISNAMEN als vorzeichenlos kannte, nicht Felder.
#[test]
fn kleinkram_const_feld_und_geraetegriff() {
    let q = "module t {
const KAP : u32 = 64;
const OBEN : u64 = u64::max;
type Text = { bytes : [u8; KAP], len : u32 in 0 .. KAP, };
impl fn anhaengen(s : ptr<normal, rw> Text, w : u8) -> bool
    effects { reads s, writes s } costs <= 12 ops
{ narrow s.len to 0 ..< KAP else { return false; } s.bytes[s.len] = w; s.len += 1; return true; }
impl fn diff(a : u32 in 0 .. 100, b : u32 in 0 .. 100) -> u32
    requires a >= b
    effects { pure } costs <= 8 ops
{ let d = a - b; return d; } }";
    let (b, mut a) = gabbro_syntax::lies("p.gab", q);
    assert_eq!(a.fehler_zahl(), 0, "{}", a.zeige(q));
    let c = gabbro_check::emit::emittiere(&b, &mut a);
    assert_eq!(a.fehler_zahl(), 0, "die Absenkung traegt:\n{}", a.zeige(q));

    // `u64::max` ist eine Zahl -- und zwar die, die `umgebung.rs` schon kannte.
    assert!(c.contains("#define OBEN 18446744073709551615u"), "{c}");
    // Ein Feldtyp, der ein FELD ist: die Laenge steht in C hinter dem Namen.
    assert!(c.contains("uint8_t bytes[KAP];"), "{c}");
    // **Die untere Pruefung faellt weg, weil das FELD nachweislich vorzeichenlos ist.**
    assert!(c.contains("if (!(s->len < KAP))"), "{c}");
    assert!(!c.contains("s->len >= 0"), "`>= 0` auf `uint32_t` ist immer wahr:\n{c}");
    // Und ein `let` ohne erklaerten Typ liest ihn von den Parametern ab.
    assert!(c.contains("uint32_t d = a - b;"), "der Typ wird abgelesen:\n{c}");

    // **Ein Name, der zweimal verschieden erklaert ist, wird in SEINER Funktion gelesen**
    // (2026-08-20).
    //
    // Bis heute war die Karte global und konservativ: `b` als `u8` und als `u32` erklaert
    // liess sie beide fallen, und der Erzeuger weigerte sich. **Das war die harmlose Haelfte
    // desselben Fehlers.** Die scharfe Haelfte stand bei `werte`, wo Fehlen keine dritte
    // Antwort ist: draussen zu sein heisst *Zeiger*. `beispiele/08` nennt einen Parameter in
    // der einen Funktion `m : Nachricht` und in der anderen `m : ptr<normal, rw> Marken` --
    // beides voellig normal -- und bekam `m.slots[s].marke += 1;`, **einen Punkt, wo ein
    // Pfeil hingehoert.** *Kein Pass hat das gesehen; der C-Uebersetzer hat es gesehen.*
    let zwei = "module t {
impl fn eins(b : u8) -> u8 effects { pure } costs <= 4 ops { return b; }
impl fn zwei(a : u32, b : u32) -> u32 effects { pure } costs <= 8 ops
{ let d = a | b; return d; } }";
    let (b3, mut a3) = gabbro_syntax::lies("p.gab", zwei);
    let c3 = gabbro_check::emit::emittiere(&b3, &mut a3);
    assert_eq!(a3.fehler_zahl(), 0, "{}", a3.zeige(zwei));
    assert!(c3.contains("uint32_t d = a | b;"), "der Typ kommt aus DIESER Signatur:\n{c3}");

    // **Und dieselbe Probe an der Stelle, die den Fehler getragen hat:** ein Name, der
    // anderswo ein Wert ist, bleibt hier ein Zeiger.
    let beides = "module t { table M count 8 { slot { w : u32 wrapping, } }
tagged type N = { Leer, Kurz(u32) };
impl fn wert(m : N) -> u32 effects { pure } costs <= 8 ops
{ match m { Leer => { return 0; } Kurz(k) => { return k; } } }
impl fn dreh(m : ptr<normal, rw> M, s : index into M) effects { writes m.slots } costs <= 4 ops
{ m.slots[s].w += 1; } }";
    let (b4, mut a4) = gabbro_syntax::lies("p.gab", beides);
    let c4 = gabbro_check::emit::emittiere(&b4, &mut a4);
    assert_eq!(a4.fehler_zahl(), 0, "{}", a4.zeige(beides));
    assert!(c4.contains("m->slots[s].w += 1;"), "der Pfeil gehoert dahin:\n{c4}");
    assert!(!c4.contains("m.slots[s].w"), "ein Punkt auf einem Zeiger:\n{c4}");
}

/// **Und der Geraetegriff: die Parameterliste der Deklaration IST der Konstruktor.**
#[test]
fn geraetegriff_ist_ein_zusammengesetztes_literal() {
    let q = "module t {
opaque type Pa = u64;
device V(basis : Pa) at mmio { reg R : u32 @0x10 class rw }
impl fn setze(p : Pa) effects { writes v.R } costs <= 8 ops
{ let v = V(p); v.R = 1; } }";
    let (b, mut a) = gabbro_syntax::lies("p.gab", q);
    assert_eq!(a.fehler_zahl(), 0, "{}", a.zeige(q));
    let c = gabbro_check::emit::emittiere(&b, &mut a);
    assert_eq!(a.fehler_zahl(), 0, "die Absenkung traegt:\n{}", a.zeige(q));
    assert!(c.contains("V v = (V){ .basis = (volatile uint8_t *)(uintptr_t)p };"), "{c}");

    // **And every FURTHER declared parameter travels in the handle** (2026-08-26). Until
    // then the emitter read only the first entry of the parameter list, although
    // `beispiele/09` already said the sentence: *"the declaration's parameter list IS the
    // constructor."* `device Virtq(base : Iova, n : u16 …)` handed the emitter an `n` it
    // never saw.
    let q2 = "module t {
opaque type Pa = u64;
device V(basis : Pa, n : u16) at mmio { reg R : u32 @0x10 class rw }
impl fn setze(p : Pa) effects { writes v.R } costs <= 8 ops
{ let v = V(p, 8); v.R = v.n; } }";
    let (b2, mut a2) = gabbro_syntax::lies("p.gab", q2);
    assert_eq!(a2.fehler_zahl(), 0, "{}", a2.zeige(q2));
    let c2 = gabbro_check::emit::emittiere(&b2, &mut a2);
    assert_eq!(a2.fehler_zahl(), 0, "die Absenkung traegt:\n{}", a2.zeige(q2));
    assert!(c2.contains("volatile uint8_t *basis; uint16_t n;"), "der Griff traegt ihn:\n{c2}");
    assert!(c2.contains(".basis = (volatile uint8_t *)(uintptr_t)p, .n = 8"), "{c2}");
    // **A parameter is NOT a volatile access.** It has been fixed since the handle was
    // built; reading it volatile would claim the device could change it.
    assert!(c2.contains("= v.n;"), "gewoehnlicher Feldzugriff, nicht volatil:\n{c2}");
}

/// **Eine Schnittstelle nennt keinen Namen, den sie nicht erklärt — und sie ist seit dem
/// 2026-08-25 GESCHRIEBEN statt gerechnet** («ABI1», nachgezogen).
///
/// Bis dahin war sie ein **Fixpunkt**: `T` kam mit, weil ein `index into T` es nennt, dann
/// `N`, weil `count N` es nennt, und so weiter bis zum Stillstand. Der Grund war eine
/// fehlende Produktion — `table`, `lock`, `device` und `format` konnten gar kein `pub`
/// tragen, also *musste* jemand die Ausfuhrmenge ausrechnen.
///
/// > **Der Fixpunkt war die ehrliche Folge einer Lücke, nicht die Entscheidung, die er zu
/// > sein schien.** Er machte die Ausfuhrmenge implizit: sie stand nirgends geschrieben, sie
/// > ergab sich — und *„nichts ist implizit"* ist D2.
///
/// Jetzt trägt der Träger das Wort, und die Frage, die der Fixpunkt beantwortete, ist eine
/// **Absage**: `N038`. Beide Richtungen stehen hier, denn eine ohne die andere misst nichts
/// (R14/W17).
///
/// **Warum das hier steht und nicht nur in einer Wächterschleife:** `mutiere-pruefer.py`
/// fährt `cargo test`. Eine Regel, deren einzige Probe eine Shell-Schleife ist, kann keine
/// Mutation fangen — dieselbe Lehre wie beim Wirkungsattribut.
#[test]
fn eine_schnittstelle_erklaert_jeden_namen_den_sie_nennt() {
    let q = r#"
module bib {
pub const N : u32 = 8;
pub table T count N { slot { a : u32, } }
pub atomic zaehler : u32;
table Ungenannt count N { slot { b : u32, } }
pub impl fn tu(i : index into T) -> u32 effects { reads T, writes zaehler } costs <= 3 ops { return 1; }
}
"#;
    let (baum, mut absagen) = gabbro_syntax::lies("bib.gab", q);
    gabbro_check::pruefe(&baum, &mut absagen);
    assert_eq!(
        absagen.fehler_zahl(),
        0,
        "die geschlossene Hülle geht durch:\n{}",
        absagen.zeige(q)
    );
    let gabi = gabbro_check::abi::schreibe(&baum, q);

    assert!(gabi.contains("table T count N"), "der ausgeführte Traeger kommt mit:\n{gabi}");
    assert!(gabi.contains("atomic zaehler"), "das ausgeführte Atomic kommt mit:\n{gabi}");
    assert!(gabi.contains("const N"), "und die Konstante, die der Traeger braucht:\n{gabi}");
    assert!(
        !gabi.contains("Ungenannt"),
        "was kein `pub` traegt, bleibt daheim -- auch wenn es dieselbe Konstante nennt:\n{gabi}"
    );

    // **Und die Schnittstelle liest sich selbst.** Das ist die Aussage, auf der alles ruht:
    // ein `.gabi` ist gueltiger Gabbro-Quelltext, kein zweites Format.
    let (b2, mut a2) = gabbro_syntax::lies("bib.gabi", &gabi);
    gabbro_check::pruefe(&b2, &mut a2);
    assert_eq!(a2.fehler_zahl(), 0, "das eigene .gabi prueft sich:\n{}", a2.zeige(&gabi));

    // -- die Gegenrichtung: ohne `pub` am Traeger faellt die SIGNATUR, nicht die Ausfuhr ---
    //
    // *Das ist der ganze Unterschied zum Fixpunkt.* Er hat den Traeger stillschweigend
    // mitgenommen; hier steht eine Absage mit einer Zeilennummer darauf.
    let offen = q.replace("pub table T count N", "table T count N");
    let (b3, mut a3) = gabbro_syntax::lies("offen.gab", &offen);
    gabbro_check::pruefe(&b3, &mut a3);
    let codes: Vec<&str> = a3.absagen.iter().map(|x| x.code).collect();
    assert!(
        codes.contains(&"N038"),
        "eine `pub fn` ueber einer privaten Tabelle faellt benannt, gefallen ist {codes:?}"
    );
}

/// **Ein `extern fn` bekommt kein zweites `extern`, und ein `use` gehört in die Schnittstelle**
/// (gefunden 2026-08-20 an `beispiele/29-undurchsichtig.gab`, dem einzigen Beispiel mit *zwei*
/// Modulen).
///
/// Beides in einem Test, weil es derselbe Befund war: das doppelte `extern` gab `P001` und
/// **deckte damit zu**, dass der zweite Modulblock `Pa` nannte, ohne es zu importieren. *Ein
/// Parserfehler, der einen Namensfehler verbirgt* — die Reihenfolge der Pässe als Versteck.
#[test]
fn ein_extern_bleibt_einfach_und_ein_use_geht_mit() {
    let q = r#"
module a {
pub opaque type Pa = u64;
pub impl fn mach() -> Pa effects { pure } costs <= 2 ops { return Pa(1); }
}
module b {
use a::Pa;
extern fn mach() -> Pa effects { pure } costs <= 2 ops;
pub impl fn nutze() -> Pa effects { pure } costs <= 4 ops { return mach(); }
}
"#;
    let (baum, _) = gabbro_syntax::lies("zwei.gab", q);
    let gabi = gabbro_check::abi::schreibe(&baum, q);

    assert!(!gabi.contains("extern extern"), "kein zweites `extern`:\n{gabi}");
    assert!(gabi.contains("use a::Pa;"), "der Import gehoert in die Schnittstelle:\n{gabi}");

    let (b2, mut a2) = gabbro_syntax::lies("zwei.gabi", &gabi);
    gabbro_check::pruefe(&b2, &mut a2);
    assert_eq!(a2.fehler_zahl(), 0, "zwei Module, eine Schnittstelle:\n{}", a2.zeige(&gabi));
}

/// **Ein leerer Bereich sagt ab — und rechnet nicht** («M117», Rezension 2026-08-20).
///
/// ```gabbro
/// type Verdreht = u32 in 5 .. 0;
/// impl fn teile(a : u32, n : Verdreht) -> u32 { return a / n; }
/// ```
///
/// gab `panicked at typen.rs:558: attempt to divide by zero`. Der Wächter davor ist
/// `enthaelt_null()` = `min <= 0 && max >= 0`; bei `min = 5, max = 0` ist das **falsch**,
/// also lief `a.min / b.max` in die Null.
///
/// **Die Ursache war nicht die Division**, sondern die fehlende Zusicherung an der
/// Deklaration: allein ging sie mit null Fehlern durch, und mit `%` statt `/` ging auch die
/// Rechnung still durch. *Aus einem leeren Bereich folgt jede Aussage* — er hätte einen
/// Divisor als nicht-null und einen Index als in Schranken bewiesen.
///
/// Zwei Aussagen, darum zwei Hälften: `M117` an der Deklaration **und** der Riegel in
/// `typen.rs`, denn eine Absage hält den Rumpf nicht an.
#[test]
fn ein_leerer_bereich_sagt_ab_und_bringt_niemanden_um() {
    for op in ["/", "%"] {
        let q = format!(
            "module m {{\n\
             type Verdreht = u32 in 5 .. 0;\n\
             impl fn teile(a : u32, n : Verdreht) -> u32 effects {{ pure }} costs <= 4 ops \
             {{ return a {op} n; }}\n\
             }}\n"
        );
        let (baum, mut absagen) = gabbro_syntax::lies("leer.gab", &q);
        gabbro_check::pruefe(&baum, &mut absagen);
        let text = absagen.zeige(&q);
        assert!(text.contains("M117"), "`{op}`: die Deklaration muss absagen:\n{text}");
    }

    // Und der Riegel darunter, direkt: aus einem leeren Bereich kommt KEINE Rechnung.
    // `bereich: None` heisst „hierueber weiss M1 nichts" -- die einzige ehrliche Antwort.
    let leer = gabbro_check::typen::IntBereich::genau(32, false, 5, 0);
    let voll = gabbro_check::typen::IntBereich::genau(32, false, 1, 10);
    assert!(leer.ist_leer(), "5 .. 0 ist leer");
    assert!(!voll.ist_leer(), "1 .. 10 ist es nicht");
    assert!(gabbro_check::typen::teile(&voll, &leer).bereich.is_none());
    assert!(gabbro_check::typen::rest(&voll, &leer).bereich.is_none());
}

/// **Ein literales `%` im Assemblertext wird verdoppelt — sonst nimmt `cc` den Block nicht**
/// (Rezension 2026-08-20).
///
/// `beispiele/36-asm.gab` schreibt `"mov $1, %eax"`, und der Erzeuger reichte den Text
/// wörtlich in einen **erweiterten** `__asm__`-Block durch. Dort ist `%` das
/// Einleitungszeichen für einen Operanden; GCC sagte *„ungültiges »asm«: Operandennummer
/// fehlt hinter %-Buchstabe"*.
///
/// > **Warum das die teuerste Stelle ist:** bei `asm` sagt die Sprache ausdrücklich, dass sie
/// > den Inhalt nicht liest. Damit ist der C-Übersetzer die **einzige** Prüfung, die es
/// > überhaupt gibt — und `pruefe-emission.sh` deckte diese Datei nicht.
#[test]
fn ein_prozent_im_assembler_wird_verdoppelt_ausser_beim_operanden() {
    let q = r#"
module m {
static mut GERAET : u32 = 0;
impl fn schreiben(fd : u64) -> u64
    effects { writes GERAET }
    costs   <= 1 ops
    arch    x86_64
    = asm {
        "mov $1, %eax"
        "syscall"
        in  { fd : "D" }
        out { result : "=a" }
        clobbers { memory }
    };
}
"#;
    let (baum, mut absagen) = gabbro_syntax::lies("asm.gab", q);
    gabbro_check::pruefe(&baum, &mut absagen);
    let c = gabbro_check::emit::emittiere(&baum, &mut absagen);
    assert!(c.contains("mov $1, %%eax"), "das literale Prozent wird verdoppelt:\n{c}");
    assert!(!c.contains("%%["), "die Operandenform `%[…]` bleibt, wie sie ist:\n{c}");
}

/// **`wrapping` heisst DEFINIERT — und im C hiess es undefiniert** (Rezension 2026-08-20).
///
/// Gabbro sagt über `u16 wrapping`: der Überlauf ist deklariert und definiert. C sagt etwas
/// anderes: bei `a * a` hebt die ganzzahlige Aufwertung beide Operanden auf `int`, und ein
/// `int`-Überlauf ist **undefiniert**. Mit UBSan nachgewiesen:
///
/// ```text
/// runtime error: signed integer overflow: 50000 * 50000 cannot be represented in type 'int'
/// ```
///
/// Der Wert kam zufällig richtig heraus (63744) — *garantiert war er nicht.*
///
/// > **Das ist die Aussage, auf der das Projekt ruht.** Wo Gabbro `definiert` sagt und das
/// > Erzeugnis `undefiniert` meint, ist die Übersetzung nicht mehr das Geprüfte.
///
/// **Zwei Formen laufen um**, und die zweite fehlte in der ersten Fassung dieser Reparatur:
/// ein Slotfeld *und* ein Register (`reg X : u16 wrapping`, «B32»).
#[test]
fn eine_umlaufende_rechnung_wird_unsigned_gerechnet() {
    let q = r#"
module m {
table T count 4 { slot { a : u16 wrapping, b : u16, } }
device Ring(basis : u64) at mmio {
    reg IDX : u16 wrapping @0x102 class rw
}
impl fn quadriere(t : ptr<normal, rw> T, i : index into T)
    effects { reads t.slots, writes t.slots } costs <= 6 ops
{ t.slots[i].a = t.slots[i].a * t.slots[i].a; }
impl fn ring(r : ptr<mmio, rw> Ring)
    effects { reads r.IDX, writes r.IDX } costs <= 6 ops
{ r.IDX = r.IDX * r.IDX; }
}
"#;
    let (baum, mut absagen) = gabbro_syntax::lies("umlauf.gab", q);
    gabbro_check::pruefe(&baum, &mut absagen);
    assert_eq!(absagen.fehler_zahl(), 0, "{}", absagen.zeige(q));
    let c = gabbro_check::emit::emittiere(&baum, &mut absagen);

    // Gerechnet wird in `uint32_t` -- dort ist der Umlauf modulo 2^n ZUGESICHERT
    // (C11 6.2.5p9) -- und das Ergebnis faellt auf die erklaerte Breite zurueck.
    assert!(
        c.contains("(uint16_t)((uint32_t)(t->slots[i].a) * (uint32_t)(t->slots[i].a))"),
        "der umlaufende Slot rechnet unsigned:\n{c}"
    );
    assert!(
        c.contains("(uint16_t)((uint32_t)((*(volatile uint16_t *)(r->basis + 258)))"),
        "und das umlaufende REGISTER ebenso -- diese Form fehlte zuerst:\n{c}"
    );
}

/// **Auf ein `static` ohne `mut` zu schreiben sagt jetzt ab** («M118», Rezension 2026-08-20).
///
/// Das ging mit **null Fehlern** durch. Der Erzeuger ehrte die Deklaration die ganze Zeit
/// korrekt — `static const uint32_t zaehler` — und schrieb daneben `zaehler += 1;`. Erst
/// `gcc` sagte *„Zuweisung der schreibgeschützten Variable"*. Mit `static mut` fällt das
/// `const` weg: **die Unterscheidung existiert also und steuert die Absenkung, nur hielt sie
/// niemand.**
///
/// > Ein Deklarationszeichen, das der Erzeuger ehrt und das kein Pass hält — dieselbe
/// > Familie, in der `own` eine Woche vorher stand.
#[test]
fn ein_static_ohne_mut_wird_nicht_beschrieben() {
    let bau = |mut_wort: &str| {
        format!(
            "module m {{\n\
             type Z = u32 in 0 .. 1000;\n\
             static {mut_wort}zaehler : Z = 0;\n\
             impl fn tor() effects {{ reads zaehler, writes zaehler }} costs <= 3 ops \
             {{ if zaehler < 1000 {{ zaehler += 1; }} }}\n\
             }}\n"
        )
    };
    let ohne = bau("");
    let (b1, mut a1) = gabbro_syntax::lies("ohne.gab", &ohne);
    gabbro_check::pruefe(&b1, &mut a1);
    assert!(a1.zeige(&ohne).contains("M118"), "ohne `mut` faellt es:\n{}", a1.zeige(&ohne));

    // **Und die andere Richtung** -- sonst wäre die Regel ein Verbot von `static` überhaupt.
    let mit = bau("mut ");
    let (b2, mut a2) = gabbro_syntax::lies("mit.gab", &mit);
    gabbro_check::pruefe(&b2, &mut a2);
    assert_eq!(a2.fehler_zahl(), 0, "mit `mut` geht es durch:\n{}", a2.zeige(&mit));

    // Eine LOKALE Bindung darf einen `static` verdecken, und dann gilt sie -- nicht er.
    let schatten = "module m {\n\
        static zaehler : u32 in 0 .. 10 = 0;\n\
        impl fn tor() effects { pure } costs <= 4 ops \
        { let mut zaehler : u32 in 0 .. 10 = 0; zaehler += 1; }\n\
        }\n";
    let (b3, mut a3) = gabbro_syntax::lies("schatten.gab", schatten);
    gabbro_check::pruefe(&b3, &mut a3);
    assert!(
        !a3.zeige(schatten).contains("M118"),
        "die lokale Bindung verdeckt den `static`:\n{}",
        a3.zeige(schatten)
    );
}

/// **Ein `const` gehört an den ZEIGER, nicht an sein Ziel — und `M118` folgt derselben
/// Trennung** (nachgezogen 2026-08-20).
///
/// Zwei Defekte an einer Deklaration, und der zweite war der schärfere:
///
/// 1. `M118` hing an `suffixe.is_empty()`. `punkt.a = 5` auf einem unveränderlichen `static`
///    ging durch — *die Regel war eine Zeile kürzer als die Deklaration.*
/// 2. `static tz : ptr<normal, rw> T` ohne `mut` ergab `static const T * tz` — ein Zeiger auf
///    **konstantes** `T`. Gemeint ist ein **konstanter Zeiger** auf schreibbares `T`. `gcc`
///    wies damit ein Programm ab, das Gabbro richtig findet.
///
/// > Das fehlende `mut` sagt etwas über den Zeiger — dass er nicht umgehängt wird — und
/// > nichts über das, worauf er zeigt. Das steht in `ptr<…, rw>`, und es steht dort schon.
///
/// Fünf Fälle, weil eine Regel ohne ihre Ausnahme keine ist.
#[test]
fn ein_unveraenderlicher_static_und_die_ausnahme_des_zeigers() {
    let pruefe = |q: &str| -> String {
        let (b, mut a) = gabbro_syntax::lies("s.gab", q);
        gabbro_check::pruefe(&b, &mut a);
        a.zeige(q)
    };
    let verbund = |mut_wort: &str, rumpf: &str| {
        format!(
            "module m {{\n\
             type P = {{ a : u32 in 0 .. 100, b : u32 in 0 .. 100, }};\n\
             static {mut_wort}punkt : P = P(a: 0, b: 0);\n\
             impl fn setz() effects {{ writes punkt }} costs <= 3 ops {{ {rumpf} }}\n\
             }}\n"
        )
    };
    let zeiger = |mut_wort: &str, wirkung: &str, rumpf: &str| {
        format!(
            "module m {{\n\
             table T count 4 {{ slot {{ a : u32, }} }}\n\
             static {mut_wort}tz : ptr<normal, rw> T = 0;\n\
             impl fn f(i : index into T) effects {{ writes {wirkung} }} costs <= 3 ops \
             {{ {rumpf} }}\n\
             }}\n"
        )
    };

    // Ein FELD eines unveraenderlichen `static` -- das war das Loch.
    assert!(pruefe(&verbund("", "punkt.a = 5;")).contains("M118"));
    assert!(!pruefe(&verbund("mut ", "punkt.a = 5;")).contains("M118"));

    // **Die Ausnahme:** durch einen unveraenderlichen Zeiger zu schreiben ist ERLAUBT.
    let durch = zeiger("", "tz.slots", "tz.slots[i].a = 5;");
    assert!(!pruefe(&durch).contains("M118"), "durch den Zeiger geht es:\n{}", pruefe(&durch));

    // Ihn UMZUHAENGEN dagegen nicht -- das schreibt den `static` selbst.
    let umhaengen = zeiger("", "tz", "tz = 0;");
    assert!(pruefe(&umhaengen).contains("M118"), "umhaengen faellt:\n{}", pruefe(&umhaengen));

    // Und das `const` steht am Zeiger, nicht am Ziel -- sonst weist `cc` die Einheit ab.
    let (b, mut a) = gabbro_syntax::lies("z.gab", &durch);
    gabbro_check::pruefe(&b, &mut a);
    let c = gabbro_check::emit::emittiere(&b, &mut a);
    assert!(c.contains("static T * const tz"), "konstanter ZEIGER:\n{c}");
    assert!(!c.contains("static const T * tz"), "kein Zeiger auf konstantes T:\n{c}");
}

/// **Ein erschöpfender Ausdrucksläufer — eine Ursache, fünf Befunde** (Rezension 2026-08-20).
///
/// Auf **Anweisungsebene** war die Klasse vorbildlich gelöst: `unterbloecke`,
/// `eigene_ausdruecke` und `endet_immer` sind erschöpfende `match`es ohne `_`-Zweig, damit
/// eine neue `StmtArt` den Bau bricht. **Eine Ebene tiefer galt das nirgends** — sechzehn
/// handgerollte Ausdrucksläufer, und nur fünf stiegen in einen `OrtSuffix::Index` ab.
///
/// > Dieser Ordner hat die Klasse seiner Fehler richtig diagnostiziert — und dann eine
/// > Instanz behoben. Der Satz stammt von aussen und er sitzt.
#[test]
fn ein_ruf_ist_auch_in_indexposition_ein_ruf() {
    let bau = |rumpf: &str| {
        format!(
            "module m {{\n\
             static mut a : u32 = 0;\n\
             table T count 4 {{ slot {{ x : u32, }} }}\n\
             impl fn schreibt() -> u32 in 0 .. 3 effects {{ writes a }} costs <= 2 ops \
             {{ a = 1; return 1; }}\n\
             impl fn f(t : ptr<normal, r> T) -> u32 effects {{ pure }} costs <= 32 ops \
             {{ {rumpf} }}\n\
             }}\n"
        )
    };
    let fiel = |q: &str| {
        let (b, mut a) = gabbro_syntax::lies("x.gab", q);
        gabbro_check::pruefe(&b, &mut a);
        a.zeige(q).contains("E008")
    };
    // Der Ruf im INDEX -- die Form, die durchging.
    assert!(fiel(&bau("return t.slots[schreibt()].x;")), "Ruf in Indexposition");
    // Und in einem eingebauten Ausdruck, derselbe Grund.
    assert!(
        fiel(&bau("if aligned(schreibt(), 4) { return 0; } return 1;")),
        "Ruf in `aligned`"
    );

    // **Der Läufer selbst, direkt.** `alle_ausdruecke` liefert jeden Unterausdruck; ohne den
    // Abstieg in den Index fehlte hier einer.
    let q = bau("return t.slots[schreibt()].x;");
    let (baum, _) = gabbro_syntax::lies("x.gab", &q);
    let mut rufe = 0;
    let mut offen: Vec<&gabbro_syntax::ast::Item> = baum.items.iter().collect();
    while let Some(item) = offen.pop() {
        {
            if let gabbro_syntax::ast::ItemArt::Modul(md) = &item.art {
                offen.extend(md.items.iter());
                continue;
            }
            let gabbro_syntax::ast::ItemArt::Funktion(f) = &item.art else { continue };
            let gabbro_syntax::ast::FnRumpf::Block(b) = &f.rumpf else { continue };
            for s in &b.anweisungen {
                for e in gabbro_check::eigene_ausdruecke(s) {
                    for x in gabbro_check::alle_ausdruecke(e) {
                        if matches!(x.art, gabbro_syntax::ast::ExprArt::Ruf(_)) {
                            rufe += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(rufe, 1, "der Ruf im Index wird gefunden");
}

/// **Ein Name, den niemand deklariert, schaltete die Indexprüfung ab** («M119», 2026-08-20).
///
/// ```gabbro
/// return t.slots[j].x;      -- `j` gibt es nicht  ->  0 Fehler
/// return t.slots[i].x;      -- i : u32 in 0..127  ->  M103
/// ```
///
/// M1 überspringt still, was es nicht typisieren kann — **und druckte dazu „100 % coverage",
/// weil es den Ausdruck gar nicht erst gesehen hat.**
#[test]
fn ein_unbekannter_name_faellt_und_zaehlt_gegen_die_deckung() {
    let q = "module m {\n\
        table T count 64 { slot { x : u32, } }\n\
        impl fn f(t : ptr<normal, r> T, i : u32 in 0 .. 127) -> u32 effects { pure } \
        costs <= 4 ops { return t.slots[j].x; }\n\
        }\n";
    let (b, mut a) = gabbro_syntax::lies("j.gab", q);
    gabbro_check::pruefe(&b, &mut a);
    let text = a.zeige(q);
    assert!(text.contains("M119"), "der unbekannte Name faellt:\n{text}");
    assert_eq!(text.matches("M119").count(), 1, "und GENAU einmal:\n{text}");

    // **Die andere Richtung, und sie war ein Falschtreffer beim Bauen:** `u64::max` ist ein
    // Ort, dessen Basis das TYPWORT `u64` ist. Gefunden sofort an `11-grammatikbefunde.gab`.
    let k = "module m {\nconst A : u64 = u64::max;\n}\n";
    let (b2, mut a2) = gabbro_syntax::lies("k.gab", k);
    gabbro_check::pruefe(&b2, &mut a2);
    assert!(!a2.zeige(k).contains("M119"), "ein Typwort ist keine Variable:\n{}", a2.zeige(k));
}

/// **Zwei Wachen, die an drei von sechs Stellen verdrahtet waren** (Rezension 2026-08-20).
///
/// `TIEFE_MAX` sass an `expr`, `pred` und `block_innen`. Verschachtelte Klammern bei Tiefe 40
/// gaben ein sauberes `P038`; **300 verschachtelte `module` gaben
/// `fatal runtime error: stack overflow, aborting`.**
///
/// Und die Bereichsarithmetik rechnete in rohem `i128`:
///
/// ```gabbro
/// return a * b;      -- zwei blanke u64
/// ```
/// ```text
/// debug:   panicked at typen.rs:553: attempt to multiply with overflow
/// release: u64 in -36893488147419103231 .. 0      ← negative Untergrenze auf u64
/// ```
///
/// > **Ein Überlaufprüfer, dessen Arithmetik überläuft, beweist nichts.** Im Freigabebau fiel
/// > es nur zufällig noch an `M104`.
///
/// *Der Korpus hat 58 blanke `u64`-Parameter und multiplizierte nie zwei davon.*
#[test]
fn die_beiden_wachen_sitzen_an_allen_ihren_stellen() {
    let tief = |q: String| {
        let (_, a) = gabbro_syntax::lies("t.gab", &q);
        a.zeige(&q).contains("P038")
    };
    // Die drei Stellen, an denen der Wächter fehlte.
    assert!(
        tief(format!("module m {{\n{}const X : u32 = 1;\n{}}}\n", "module a {\n".repeat(80), "}\n".repeat(80))),
        "verschachtelte `module`"
    );
    assert!(
        tief(format!("module m {{\ntype T = {}u32{};\n}}\n", "{ a : ".repeat(60), ", }".repeat(60))),
        "verschachtelte Verbundtypen"
    );
    // Und die drei, an denen er schon sass -- damit die Reparatur keine davon verliert.
    assert!(
        tief(format!("module m {{\nconst A : u32 = {}1{};\n}}\n", "(".repeat(200), ")".repeat(200))),
        "verschachtelte Klammern"
    );

    // **Die Arithmetik.** `bereich: None` heisst „hierüber weiss M1 nichts" -- die einzige
    // ehrliche Antwort, wenn die eigene Rechnung nicht mehr trägt.
    let voll = gabbro_check::typen::IntBereich::voll(64, false);
    let r = gabbro_check::typen::multipliziere(&voll, &voll);
    assert!(r.bereich.is_none(), "kein erfundener Bereich");
    assert!(r.laeuft_ueber, "und der Ueberlauf wird GEMELDET, nicht verschwiegen");
    // Kein Bereich darf dabei eine negative Untergrenze auf einem vorzeichenlosen Typ tragen.
    if let Some(b) = gabbro_check::typen::multipliziere(
        &gabbro_check::typen::IntBereich::genau(64, false, 0, 3),
        &gabbro_check::typen::IntBereich::genau(64, false, 0, 3),
    )
    .bereich
    {
        assert!(b.min >= 0, "u64 hat keine negative Untergrenze: {b:?}");
    }
}

/// **Die vier M2-Löcher, alle vier** (Rezension 2026-08-20).
///
/// M2 ist der Pass, den der eigene Modulkopf *„das einzige Mittel in diesem Ordner, für das
/// es keinen Ersatz gibt"* nennt — und *genau einmal* stimmte auf vier Wegen nicht. **Es
/// trifft nicht nur `ghost`:** hier steht ein `linear type`, ein echtes
/// Laufzeit-Betriebsmittel.
///
/// 1. Ein **geschachtelter** Ruf: `aussen(wecken(p))` — der Läufer stieg nicht in Argumente
///    ab. Beide Rufe auf oberster Ebene gaben `L104`, einer geschachtelt: **stumm.** *Ein
///    Double-Free mit grünem Haken.*
/// 2. `ruf` band die Position `i` und benutzte sie nie — also galt an einer Rufstelle jedes
///    lineare Argument als verbraucht, sobald der Gerufene **irgendeinen** Parameter
///    verbraucht. In beide Richtungen falsch.
/// 3. Ein **Schleifenrumpf** lief einmal als geradliniger Code (`L108`).
/// 4. Ein im **Zweig** geborener Wert fiel an der Vereinigung heraus (`L109`).
#[test]
fn m2_zaehlt_genau_einmal_auf_allen_vier_wegen() {
    let kopf = "module m {\n\
        linear type Parked;\n\
        extern fn wecken(p : Parked) -> u32 in 0 .. 3 effects { consumes p } costs <= 2 ops;\n\
        extern fn parken() -> Parked effects { pure } costs <= 2 ops;\n\
        extern fn aussen(v : u32 in 0 .. 3) -> u32 in 0 .. 3 effects { pure } costs <= 1 ops;\n\
        extern fn beides(a : Parked, b : Parked) effects { consumes a } costs <= 2 ops;\n";
    let melden = |rumpf: &str| -> String {
        let q = format!("{kopf}{rumpf}}}\n");
        let (b, mut a) = gabbro_syntax::lies("m2.gab", &q);
        gabbro_check::pruefe(&b, &mut a);
        a.zeige(&q)
    };

    // 1. Der geschachtelte Verbrauch.
    let t1 = melden(
        "impl fn f(p : Parked) -> u32 in 0 .. 3 effects { consumes p } costs <= 16 ops \
         { let a = aussen(wecken(p)); let b = wecken(p); return b; }\n",
    );
    assert!(t1.contains("L104"), "geschachtelt ist auch zweimal:\n{t1}");

    // 2. **Die POSITION -- und dafuer braucht es ZWEI lineare Argumente.**
    //
    // Die erste Fassung dieser Probe hatte eines (`nimmt(k, p)` mit `k : u32`), und die
    // kaputte Regel UEBERLEBTE sie: ein nichtlinearer Name steht gar nicht erst in `zust`.
    // *Der Mutationslauf hat das gesagt, nicht ich* -- `m2-nimmt-jede-position` kam als
    // UEBERLEBT zurueck, und die Suche nach dem Grund fand die zu schwache Probe.
    //
    // `beides` verbraucht NUR `a`. Mit der kaputten Regel gilt `q` an dieser Rufstelle
    // trotzdem als verbraucht, und `wecken(q)` gibt ein falsches `L104`.
    let t2 = melden(
        "impl fn f(p : Parked, q : Parked) effects { consumes p, consumes q } \
         costs <= 16 ops { beides(p, q); wecken(q); }\n",
    );
    assert!(!t2.contains("L104"), "`q` wird von `beides` nur GELIEHEN:\n{t2}");

    // 3. Der Schleifenrumpf laeuft OFT.
    let t3 = melden(
        "impl fn f(p : Parked) effects { consumes p } costs <= 64 ops \
         { retry warten until false bounded 32 ops progress ir on_exceeded auf \
           effects { consumes p } { wecken(p); } }\n",
    );
    assert!(t3.contains("L108"), "einmal gezaehlt, oft gelaufen:\n{t3}");

    // ... und ein Wert, der IM Rumpf entsteht, ist dort in Ordnung.
    let t3b = melden(
        "impl fn f() effects { pure } costs <= 64 ops \
         { retry warten until false bounded 32 ops progress ir on_exceeded auf \
           effects { pure } { let p = parken(); let x = wecken(p); } }\n",
    );
    assert!(!t3b.contains("L108"), "je Durchlauf geboren und gestorben:\n{t3b}");

    // 4. Im Zweig geboren, im Zweig gestorben -- oder eben nicht.
    let t4 = melden(
        "impl fn f(k : u32 in 0 .. 3) effects { pure } costs <= 32 ops \
         { if k == 1 { let p = parken(); } }\n",
    );
    assert!(t4.contains("L109"), "der Zweig ist das ganze Leben des Wertes:\n{t4}");
    let t4b = melden(
        "impl fn f(k : u32 in 0 .. 3) effects { pure } costs <= 32 ops \
         { if k == 1 { let p = parken(); let x = wecken(p); } }\n",
    );
    assert!(!t4b.contains("L109"), "im Zweig verbraucht ist in Ordnung:\n{t4b}");
}

/// **The fifth way: a branch that `return`s HAS consumed** (2026-08-25).
///
/// ```gabbro
/// impl fn f(p : Parked, b : bool) -> u32 effects { consumes p } {
///     if b { wecken(p); return 1; } else { wecken(p); return 2; }
/// }
/// ```
///
/// gave **`L101` -- „`p` is listed under `consumes` but is consumed on no path"**. Consumed
/// on *both* ways, and the checker said: on none. **A false rejection of a correct
/// program** -- the same class as «U005»: the programmer can repair nothing, because
/// nothing is broken.
///
/// Two errors sat on top of each other, and the second became visible only once the first
/// was gone:
///
/// 1. `abgleich` exited early at *„every branch ends"* and left `zust` at the state from
///    before -- the consumption was gone.
/// 2. `endet()` asked only for the **kind of the last statement**. A block whose last
///    statement is a branch in which every path returns counted as running on -- and
///    entered the reconciliation with a consumed value against the implicit else path.
///    *As long as (1) threw the consumption away, the paths agreed by accident.*
///
/// **And the counter-direction stands below it:** a branch that returns without consuming
/// is still a leak. The repair adopts only what **all** ending paths agree on -- otherwise
/// the false rejection would have become a false pass.
#[test]
fn ein_zweig_der_zurueckkehrt_hat_trotzdem_verbraucht() {
    let kopf = "module m {\n\
        linear type Parked;\n\
        extern fn wecken(p : Parked) -> u32 in 0 .. 3 effects { consumes p } costs <= 2 ops;\n";
    let melden = |rumpf: &str| -> String {
        let q = format!("{kopf}{rumpf}}}\n");
        let (b, mut a) = gabbro_syntax::lies("m2-pfad.gab", &q);
        gabbro_check::pruefe(&b, &mut a);
        a.zeige(&q)
    };

    // 1. Both branches return, both consume. **Must pass.**
    let t1 = melden(
        "impl fn f(p : Parked, b : bool) -> u32 in 0 .. 3 effects { consumes p } \
         costs <= 16 ops { if b { return wecken(p); } else { return wecken(p); } }\n",
    );
    assert!(
        !t1.contains("L101") && !t1.contains("L103") && !t1.contains("L104"),
        "exactly once on both ways:\n{t1}"
    );

    // 2. **Nested** -- the outer branch ends on every INNER way. Must pass.
    let t2 = melden(
        "impl fn f(p : Parked, b : bool, c : bool) -> u32 in 0 .. 3 effects { consumes p } \
         costs <= 24 ops { if b { if c { return wecken(p); } else { return wecken(p); } } \
         return wecken(p); }\n",
    );
    assert!(
        !t2.contains("L101") && !t2.contains("L103") && !t2.contains("L104"),
        "the outer branch leaves the function on every way:\n{t2}"
    );

    // 3. **The counter-direction: an ending branch WITHOUT a consumption is still a leak.**
    let t3 = melden(
        "impl fn f(p : Parked, b : bool) -> u32 in 0 .. 3 effects { consumes p } \
         costs <= 16 ops { if b { return wecken(p); } else { return 2; } }\n",
    );
    assert!(
        t3.contains("L101"),
        "the else path leaves the function with `p` still alive:\n{t3}"
    );

    // 4. And a DOUBLE consumption in a branch still falls at `L104` -- and only there.
    let t4 = melden(
        "impl fn f(p : Parked, b : bool) -> u32 in 0 .. 3 effects { consumes p } \
         costs <= 24 ops { if b { return wecken(p); } \
         else { let x = wecken(p); return wecken(p); } }\n",
    );
    assert!(t4.contains("L104"), "twice in the same branch:\n{t4}");
    assert!(!t4.contains("L101"), "the false `L101` beside it is gone:\n{t4}");
}

/// **The `can_fail` body was a body without a reader** (2026-08-25).
///
/// The effect pass walked `ItemArt::Funktion` and nothing else. The same call therefore
/// gave two different answers -- «E008» and «K001» in an `impl fn`, and **zero errors** in
/// the probe body. And because `consumes` is an effect, a *double free* stood there with a
/// green tick: `nimm(m); nimm(m);` -- M2 does not see this block either.
///
/// «N027» already forbade the statement forms (assignment, `locks`, `publishes`,
/// `exchange`) and stated the principle this continues: *„a body without a contract may not
/// do what needs one."* **A CALL was not covered by it.**
///
/// > No new code -- the same sentence as in an `impl fn`, only with a contract that is not
/// > written down but holds: **a probe is `pure` by construction.**
#[test]
fn ein_can_fail_rumpf_ist_pure_von_bauart_wegen() {
    let melden = |rumpf: &str, zusatz: &str| -> String {
        let q = format!(
            "module m {{\n\
             static mut zaehler : u32 in 0 .. 100 = 0;\n\
             linear type Marke;\n\
             extern fn teuer() -> u32 in 0 .. 100 effects {{ writes zaehler }} \
             costs <= 5000 ops;\n\
             extern fn liest() -> u32 in 0 .. 100 effects {{ reads zaehler }} costs <= 2 ops;\n\
             extern fn hol() -> Marke effects {{ pure }} costs <= 2 ops;\n\
             extern fn nimm(m : Marke) effects {{ consumes m }} costs <= 2 ops;\n\
             impl fn tor()  effects {{ pure }} costs <= 4 ops {{ return; }}\n\
             impl fn frei() effects {{ pure }} costs <= 4 ops {{ return; }}\n\
             {zusatz}\
             check probe {{\n\
               claim \"eine Behauptung\"\n\
               measures zaehler\n\
               gates tor, frei\n\
               can_fail {{ {rumpf} }}\n\
               floor zaehler >= 0\n\
               counterprobe \"eine Gegenprobe\" expects sonde\n\
             }}\n}}\n"
        );
        let (b, mut a) = gabbro_syntax::lies("check.gab", &q);
        gabbro_check::pruefe(&b, &mut a);
        a.zeige(&q)
    };

    // 1. A call that WRITES -- in an `impl fn` it falls; here it did not.
    let t1 = melden("let g = teuer(); if g > 3 { return false; } return true;", "");
    assert!(t1.contains("E008"), "a call with `writes` in a probe body:\n{t1}");

    // 2. **And with that the double free has become unwritable.** `consumes` is an
    //    effect; the call falls before M2 would have had to see it.
    let t2 = melden("let m = hol(); nimm(m); nimm(m); return true;", "");
    assert!(t2.contains("E008"), "`consumes` in a probe body:\n{t2}");

    // 3. **The counter-direction, and it is the more important one:** read, compute,
    //    compare, return -- exactly what the corpus does -- stays allowed.
    let t3 = melden("if liest() > 3 { return false; } return true;", "");
    assert!(
        !t3.contains("E008"),
        "a probe MAY read, otherwise it would check nothing:\n{t3}"
    );
}

/// **A call killed every fact -- even a `pure` one** (2026-08-25).
///
/// `aufruf_toetet_fakten` deleted every fact about a non-local place at EVERY call. Over a
/// table with `backed` that means:
///
/// ```gabbro
/// narrow i to 0 ..< hinterlegt else { return 0; }
/// rein();                        -- effects { pure }
/// return h.slots[i].kopf;        -- M108: „nothing shows it is BACKED"
/// ```
///
/// **Three of four cases were false rejections** -- `pure`, a foreign `writes`, and only
/// the fourth, which really writes `hinterlegt`, fired rightly. *Whoever has to narrow again
/// after every call writes the narrowing until it is ceremony.*
///
/// The upper bound already stood there: the callee's `effects`, which «E008» reconciles
/// against its hull. **Two resolution traps lay on the way**, and both looked like „no
/// finding": `funktionen` and `globale` are keyed **qualified**, so a `get(name)` with the
/// bare name never hits inside a `module` block and falls back silently to the coarse rule.
/// *The refinement would have been there and done nothing.*
///
/// > Refined **only** when every written place is a known world name and not a parameter
/// > name of the callee; otherwise the coarse rule applies. Incompleteness costs precision
/// > here, not soundness.
#[test]
fn ein_reiner_ruf_toetet_keine_tatsache() {
    let melden = |rumpf: &str| -> String {
        let q = format!(
            "module m {{\n\
             const N : u32 = 256;\n\
             static mut hinterlegt : u32 in 0 .. N = 0;\n\
             static mut fremd : u32 in 0 .. 100 = 0;\n\
             table H count N backed hinterlegt {{ slot {{ kopf : u64, }} }}\n\
             extern fn rein() effects {{ pure }} costs <= 2 ops;\n\
             extern fn schreibt_fremd() effects {{ writes fremd }} costs <= 2 ops;\n\
             extern fn schrumpft() effects {{ writes hinterlegt }} costs <= 2 ops;\n\
             {rumpf}}}\n"
        );
        let (b, mut a) = gabbro_syntax::lies("narrow.gab", &q);
        gabbro_check::pruefe(&b, &mut a);
        a.zeige(&q)
    };
    let fn_mit = |wirkung: &str, zwischen: &str| -> String {
        format!(
            "impl fn f(h : ptr<normal, r> H, i : index into H) -> u64\n\
             effects {{ reads h.slots, reads hinterlegt{wirkung} }} costs <= 8 ops\n\
             {{ narrow i to 0 ..< hinterlegt else {{ return 0; }} {zwischen} \
             return h.slots[i].kopf; }}\n"
        )
    };

    // 1. Without a call -- the baseline, it always passed.
    let t1 = melden(&fn_mit("", ""));
    assert!(!t1.contains("M108"), "the narrowing carries:\n{t1}");

    // 2. **A `pure` call in between.** It can touch nothing, so nothing falls.
    let t2 = melden(&fn_mit("", "rein();"));
    assert!(!t2.contains("M108"), "`pure` kills no fact:\n{t2}");

    // 3. A call that writes something ELSE.
    let t3 = melden(&fn_mit(", writes fremd", "schreibt_fremd();"));
    assert!(!t3.contains("M108"), "`writes fremd` does not touch `hinterlegt`:\n{t3}");

    // 4. **The counter-direction, and it is the one that matters:** a call that writes
    //    the backing kills the fact -- otherwise a false rejection would have turned into
    //    a faulty access.
    let t4 = melden(&fn_mit(", writes hinterlegt", "schrumpft();"));
    assert!(
        t4.contains("M108"),
        "whoever writes the backing takes the narrowing with it:\n{t4}"
    );
}

/// **`decreases` war eine Namensprobe** («K009» geschärft, Rezension 2026-08-20).
///
/// Die alte Bedingung fragte nur, ob sich an einer Massstelle *irgendetwas* ändert. **Eine
/// Vertauschung ist eine Änderung:** `g(m, n)` ging durch, wurde emittiert, übersetzt, und
/// `g(1,1)` endete mit `SIGSEGV`. Ein *steigendes* Mass fiel nur zufällig an der
/// Bereichsgrenze.
///
/// > Von den zwei möglichen Antworten — Regel schärfen oder Zusage zurücknehmen — ist dies
/// > die erste. *Aus der strengen Lesart kann man lockern, nie umgekehrt.*
#[test]
fn ein_rekursionsmass_muss_sichtbar_fallen() {
    let mit = |ruf: &str| -> String {
        let q = format!(
            "module m {{\n\
             impl fn g(n : u32 in 0 .. 8, m : u32 in 0 .. 8) -> u32 in 0 .. 8\n\
             effects {{ pure }} costs <= 64 ops decreases n\n\
             {{ if n == 0 {{ return 0; }} return {ruf}; }}\n\
             }}\n"
        );
        let (b, mut a) = gabbro_syntax::lies("d.gab", &q);
        gabbro_check::pruefe(&b, &mut a);
        a.zeige(&q)
    };
    assert!(mit("g(m, n)").contains("K009"), "eine Vertauschung faellt nicht");
    assert!(mit("g(n + 1, m)").contains("K009"), "ein steigendes Mass steigt");
    assert!(mit("g(n, m)").contains("K009"), "unveraendert ist unveraendert");
    // Die zwei angenommenen Formen -- sonst waere die Regel ein Verbot von `decreases`.
    assert!(!mit("g(n - 1, m)").contains("K009"), "`n - 1` faellt");
    assert!(!mit("g(n / 2, m)").contains("K009"), "`n / 2` faellt");
}

/// **Eine benannte Konstante behält ihren Wert** (Rezension 2026-08-20).
///
/// `return x + 8;` ging durch, `const RESERVE : u32 = 8; return x + RESERVE;` fiel an
/// `M104`: der Ort löste auf den *deklarierten* Typ auf, nicht auf die Zahl. Der Auswerter
/// stand die ganze Zeit daneben und wird für Typschranken schon benutzt.
///
/// > Eine Konstante zu benennen ist die Gegenbewegung zur magischen Zahl. **Ein Prüfer, der
/// > sie dafür bestraft, erzieht zur magischen Zahl.**
#[test]
fn eine_benannte_konstante_behaelt_ihren_wert() {
    let q = "module m {\n\
        const RESERVE : u32 = 8;\n\
        impl fn a(x : u32 in 0 .. 100) -> u32 in 0 .. 200 effects { pure } costs <= 2 ops \
        { return x + 8; }\n\
        impl fn b(x : u32 in 0 .. 100) -> u32 in 0 .. 200 effects { pure } costs <= 2 ops \
        { return x + RESERVE; }\n\
        }\n";
    let (b, mut a) = gabbro_syntax::lies("k.gab", q);
    gabbro_check::pruefe(&b, &mut a);
    assert_eq!(a.fehler_zahl(), 0, "die Zahl und ihr Name sind dasselbe:\n{}", a.zeige(q));
}


/// **Die sieben Entscheidungen vom 2026-08-20, jede an ihrer Stelle** -- und die fuenf
/// Erzeugerfehler, die dabei herausgefallen sind.
///
/// *Ohne diese Zusicherungen waere die neue Flaeche unbeschaedigbar:* `mutiere-pruefer.py`
/// entscheidet allein an `cargo test`, und ein Fehler im ERZEUGTEN TEXT faellt dort nur auf,
/// wenn jemand den Text liest.
#[test]
fn die_emission_traegt_ihre_sieben_entscheidungen() {
    fn c_von(q: &str) -> String {
        let (baum, mut a) = gabbro_syntax::lies("p.gab", q);
        assert_eq!(a.fehler_zahl(), 0, "die Probe parst nicht:\n{}", a.zeige(q));
        let c = gabbro_check::emit::emittiere(&baum, &mut a);
        assert_eq!(a.fehler_zahl(), 0, "die Absenkung traegt:\n{}", a.zeige(q));
        c
    }

    // **1. Eine MARKE traegt ein Byte, ein Geist gar nichts** -- und der Unterschied ist die
    // ganze Bedeutung der zwei Woerter.
    let c = c_von(
        "module t {
linear type Angemeldet;
linear ghost type Beleg;
extern fn dienst(a : Angemeldet, b : Beleg) effects { pure } costs <= 1 ops; }",
    );
    assert!(c.contains("typedef struct { uint8_t nichts; } Angemeldet;"), "{c}");
    assert!(c.contains("void dienst(Angemeldet a);"), "der Geist ist geloescht:\n{c}");

    // **2. Die Marke steht VOR ihrem ersten Gebrauch**, auch wenn die Quelle sie zuletzt
    // erklaert. Dieselbe Regel wie „alle Prototypen vor allen Ruempfen".
    let c = c_von(
        "module t {
extern fn dienst(a : Angemeldet) effects { pure } costs <= 1 ops;
linear type Angemeldet; }",
    );
    let typ = c.find("typedef struct { uint8_t nichts; } Angemeldet;").expect("die Marke");
    let benutzt = c.find("void dienst(Angemeldet a);").expect("der Prototyp");
    assert!(typ < benutzt, "der Typ steht hinter seinem Gebrauch:\n{c}");

    // **3. Und dasselbe fuer einen VERBUND** -- `beispiele/05` erklaert seinen als letztes
    // Item. Dazu: die `#define`s stehen vor den Typen, sonst ist `[u8; KAP]` eine unbekannte
    // Laenge.
    let c = c_von(
        "module t {
extern fn nimm(z : ptr<normal, rw> Zelle) effects { writes z } costs <= 1 ops;
const KAP : u32 = 8;
type Zelle = { bytes : [u8; KAP], }; }",
    );
    let d = c.find("#define KAP 8u").expect("das define");
    let t = c.find("} Zelle;").expect("der typedef");
    let g = c.find("void nimm(Zelle *").expect("der Prototyp");
    assert!(d < t && t < g, "Reihenfolge define -> typedef -> Gebrauch:\n{c}");

    // **4. `static` ueber einem Feld: die Laenge steht HINTER dem Namen**, und `= 0` ist
    // `{0}`, weil beide Lesarten sich genau bei der Null treffen.
    let c = c_von("module t { type Z = u32 in 0 .. 9; static mut last : [Z; 64] = 0; }");
    assert!(c.contains("uint32_t last[64]"), "{c}");
    assert!(c.contains("= {0};"), "die Null belegt das ganze Feld:\n{c}");

    // **5. Ein `format`: `bool @N` ist ein Bitfeld, `embeds` eine LAGE, und die Wortbreite
    // kommt aus den GANZZAHLFELDERN der Gruppe.** Ein `bool` sagt, welches Bit, nie welches
    // Wort -- die erste Fassung las die Breite aus dem ersten Feld und haette hier ein Byte
    // gesehen, wo ein Achtbytewort steht.
    let c = c_von(
        "module t { format P endian little {
    da    : bool @0,
    frei  : u64 @[62:1] reserved,
    nx    : bool @63,
} }",
    );
    assert!(c.contains("static inline bool P_da(const P *v)"), "ein `bool` liest sich als bool:\n{c}");
    assert!(c.contains("gabbro_le64(v->bytes + 0)"), "acht Byte, nicht eines:\n{c}");
    // **Und der Achtbyteleser bringt seinen Vierbyteleser mit** -- er ist aus ihm gebaut.
    assert!(c.contains("static inline uint32_t gabbro_le32"), "die Abhaengigkeit fehlt:\n{c}");
    assert!(!c.contains("P_frei"), "ein `reserved` bekommt keinen Leser:\n{c}");

    // **6. `embeds [hi:lo] scale K` -- der Faktor gehoert IN den Leser.** Ein ungeskalierter
    // Rohwert waere eine Zahl, die aussieht wie die richtige.
    let c = c_von(
        "module t { format Pte endian little {
    da     : bool @0,
    lo     : u64 @[11:1] reserved,
    rahmen : u64 embeds [51:12] scale 4096,
    hi     : u64 @[63:52] reserved,
} }",
    );
    assert!(c.contains(">> 12"), "{c}");
    assert!(c.contains("* 4096u"), "der Faktor fehlt:\n{c}");

    // **7. Ein `format`-Feld ist ein RUF, kein Feldzugriff** -- ein Format ist kein
    // C-Verbund, sondern eine Zusage ueber BYTES.
    let c = c_von(
        "module t { format K endian little { w : u32, }
impl fn lies(p : ptr<normal, r> K) -> u32 effects { reads p } costs <= 4 ops
{ return p.w; } }",
    );
    assert!(c.contains("return K_w(p);"), "{c}");
    assert!(!c.contains("p->w"), "ein Pfeil auf einen Byteleser:\n{c}");

    // **8. `accumulates` ruft `gabbro_kern()`, und ein fremder Rumpf braucht seinen
    // Prototypen.** C11 machte daraus sonst eine implizite Deklaration.
    let c = c_von("module t { const N : u32 = 4; accumulates h : u64 merge max per cpu N; }");
    let proto = c.find("uint32_t gabbro_kern(void);").expect("der Prototyp");
    let ruf = c.find("k = gabbro_kern();").expect("der Ruf");
    assert!(proto < ruf, "der Prototyp steht hinter seinem Ruf:\n{c}");

    // **9. «C4b»: die CAS-Schleife ist BESCHRAENKT, und beschraenkt ist der Punkt.**
    let c = c_von(
        "module t {
const NK : u32 = 8;
atomic Z : u64 relaxed;
extern fn streit() -> never effects { diverges } costs <= 1 ops;
impl fn hoch() -> u64 effects { reads Z, writes Z } costs <= 2048 ops
{ let alt = Z exchange update(v) bounded NK * 4 ops on_exceeded streit
  { return v; } publishes nothing;
  return alt; } }",
    );
    assert!(c.contains("atomic_compare_exchange_weak_explicit("), "{c}");
    // **Die Zusicherung nennt die GANZE Bedingung, nicht ihr Ende** (2026-08-20).
    //
    // Sie stand hier als `>= (uint32_t)(NK * 4)) { streit(); }` -- und `cas-schleife-ohne-
    // schranke` hat trotzdem UEBERLEBT: die Mutation setzt ein `0 &&` DAVOR, und der Text
    // enthaelt das Ende danach unveraendert. *Eine Probe, die nur das Ende einer Bedingung
    // liest, kann eine ausgeschaltete Bedingung nicht von einer geltenden trennen.*
    let bedingung = format!("if (_ci{} >= (uint32_t)(NK * 4)) {{ streit(); }}", 1);
    assert!(c.contains(&bedingung), "die Schranke ist nicht wirksam:\n{c}");

    // **10. `ancestors of` faengt beim ELTER an** -- ein Knoten ist kein Vorfahr seiner
    // selbst.
    let c = c_von(
        "module t { table T count 8 { tree { parent p } slot { p : option index into T, } }
impl fn hoch(i : index into T) -> bool effects { reads T.slots } costs <= 64 ops
{ traverse v of i over ancestors of i by unvisited { if v == 0 { return true; } } return false; } }",
    );
    assert!(
        c.contains("for (uint32_t v = T_speicher.slots[i].p; v != 8u; v = T_speicher.slots[v].p)"),
        "die Kette faengt beim Elter an und endet am Sonderwert:\n{c}"
    );
}

/// **`breaking` ist kein Schreibrecht — und die Buchung sagte das Gegenteil.**
///
/// `TODO.md` (Stufe 5) führte als offenen Durchstich: *„`kbedingung.rs` hält die
/// `breaking`-Stellen je Träger, und `ist_geschlossen` verlangt, dass es keine gibt — ein
/// `breaking` **öffnet den Träger damit wieder**, statt ein Übersetzungsfehler zu sein."*
///
/// **Zwei Dinge daran waren falsch, und beide sind messbar.**
///
/// * `ist_geschlossen` gibt es nicht. Die Funktion heisst `Traeger::k_haelt`.
/// * Ein `breaking` öffnet gar nichts: `sammle` steigt über `crate::unterbloecke` in den
///   Rumpf ab wie in jeden anderen Unterblock, und die Handmutation fällt an `D001` — am
///   `by ops`-Feld zusätzlich an `D002`.
///
/// **Was `breaking` wirklich tut, ist eine Aussage über die MESSUNG**: der Träger fällt aus
/// der Zählung *„K hält"*, weil das Messprotokoll verlangt, dass ALLE Mutationen erzeugt
/// sind — und ein Bereich, in dem ein Satz ruht, ist genau der, den *„der Erzeuger zeigt es
/// einmal"* nicht deckt. *Zwei Fragen, die der Ordner zusammengezogen hatte.*
///
/// > Und die dritte Bewegung: **`breaking` hatte bis zum 2026-08-20 null Korpusstellen.**
/// > Ein Satz über ein Konstrukt, an dem nie etwas gefallen ist, ist eine Vermutung (W11).
#[test]
fn ein_breaking_oeffnet_den_traeger_nicht() {
    let codes = |q: &str| -> Vec<String> {
        let (b, mut a) = gabbro_syntax::lies("p.gab", q);
        let _ = gabbro_check::pruefe(&b, &mut a);
        a.absagen.iter().map(|x| x.code.to_string()).collect()
    };
    // Ein Rumpf, EINE Handmutation -- einmal mit `ops` an der Tabelle und `by ops` am Feld,
    // einmal ohne beides. Der `breaking`-Block steht in beiden Fassungen.
    let quelle = |ops: &str, feld: &str| {
        format!(
            "module t {{ const N : u32 = 8; \
             table O count N {{ slot {{ benutzt : bool, z : u32 in 0 .. 65535{feld}, }} \
             invariant zb cost O(n) runs offline : \
             forall s in slots of Self : Self.slots[s].z >= 0; {ops} }} \
             impl fn h(o : ptr<normal, rw> O, i : index into O) \
             effects {{ writes o.slots }} costs <= 8 ops \
             {{ breaking zb {{ o.slots[i].z = 0; }} }} }}"
        )
    };

    // **Die kaputte Richtung:** `by ops` am Feld, `ops` an der Tabelle, Handmutation im
    // `breaking`. Beide Riegel greifen -- der `breaking`-Block ist keine Hintertuer.
    // *Nachgezogen beim Zusammenfuehren (2026-08-21): `P039` haelt die Wortmenge von `ops`
    // seit demselben Tag geschlossen, und diese Probe entstand parallel mit erfundenen
    // Woertern -- derselbe Grund, aus dem die Luecke so lange nicht auffiel.*
    let c = codes(&quelle("ops insert, remove;", " by ops"));
    assert!(c.contains(&"D002".to_string()), "`by ops` haelt im `breaking` nicht: {c:?}");
    assert!(c.contains(&"D001".to_string()), "`ops` haelt im `breaking` nicht: {c:?}");

    // **Die saubere Richtung:** ohne `ops` und ohne `by ops` ist dieselbe Handmutation im
    // selben `breaking`-Block erlaubt -- eine Tabelle ohne erzeugte Operationen ist reine
    // Beschreibung, und `breaking` bleibt, was es ist: eine sichtbare Ruhezone.
    //
    // *Ohne diese Haelfte belegte die obere nur, dass etwas rot wird -- und nicht, dass es
    // das `ops` ist, das es rot macht.*
    let c = codes(&quelle("", ""));
    assert!(c.is_empty(), "ein `breaking` ohne `ops` faellt: {c:?}");
}

/// **`V` — die Vorbedingung am Rufort, und sie stand in keinem Register.**
///
/// `M115` weist ab, wo der Bereich des Arguments die Vorbedingung **ausschliesst**, und
/// schweigt sonst — *eine untere Schranke, und sie steht als solche da.* Was nirgends stand,
/// war die **Gegenseite dieser Schranke**: wie viele Rufstellen eine Bedingung tragen, die
/// niemand nachhält. `TODO.md` (Stufe 5) verlangte diese Zahl ausdrücklich, bevor die starke
/// Fassung von `M115` gebaut wird.
///
/// **Gemessen 2026-08-20 über `beispiele/*.gab`: 12.** *Ein Preis, den kein Werkzeug nennt,
/// sieht aus wie null.*
#[test]
fn eine_vorbedingung_am_rufort_wird_gezaehlt() {
    let v = |q: &str| -> usize {
        let (b, _a) = gabbro_syntax::lies("p.gab", q);
        gabbro_check::pflichten::sammle(&b)
            .iter()
            .filter(|x| x.art == gabbro_check::pflichten::Art::Vorbedingung)
            .count()
    };

    // **Die zaehlende Richtung:** ein Ruf auf eine Funktion mit ZWEI `requires` zaehlt zwei.
    assert_eq!(
        v("module t { extern fn nimm(x : u32 in 0 .. 9) requires x < 9, x > 0 \
           effects { pure } costs <= 1 ops; \
           impl fn ruft(y : u32 in 0 .. 9) effects { pure } costs <= 8 ops \
           { nimm(y); } }"),
        2,
        "zwei Vorbedingungen an einer Rufstelle sind zwei Pflichten"
    );

    // **Die schweigende Richtung:** dieselbe Funktion ohne `requires` zaehlt nichts. *Ohne
    // diese Haelfte belegte die obere nur, dass irgendetwas gezaehlt wird.*
    assert_eq!(
        v("module t { extern fn nimm(x : u32 in 0 .. 9) effects { pure } costs <= 1 ops; \
           impl fn ruft(y : u32 in 0 .. 9) effects { pure } costs <= 8 ops \
           { nimm(y); } }"),
        0,
        "ohne `requires` gibt es am Rufort nichts zu schulden"
    );

    // **Und der Abstieg ist die eigentliche Falle:** ein Ruf unter einer Sperre ist derselbe
    // Ruf. *Dieselbe Lehre wie `pruefe-abstieg.py`, nur an einer Zaehlung statt an einem Pass.*
    assert_eq!(
        v("module t { static mut z : u32 = 0; lock L protects { z } rank 0 held <= 40 ops; \
           extern fn nimm(x : u32 in 0 .. 9) requires x < 9 effects { pure } costs <= 1 ops; \
           impl fn ruft(y : u32 in 0 .. 9) effects { locks L } costs <= 8 ops \
           { locks L { nimm(y); } } }"),
        1,
        "ein Ruf unter einer Sperre faellt aus der Zaehlung"
    );
}

// --- Stufe 6, Teil E ---

/// **«B38» — `H101`, die Nebenbedingung am benannten Traeger, in BEIDE Richtungen.**
///
/// `FRAGMENTE.md` F8 misst fuenf Werte, die im Planer eine Sperrgrenze ueberqueren; zwei
/// ruhen nicht auf Neuvalidierung, sondern auf der Interruptmaskierung. Die ehrliche Form
/// ist *„prueft neu ODER nennt, was sie stattdessen traegt"* — **und ein Traeger
/// `masks IRQ` zaehlt nur, wenn der Eintrittskontext `nested masked` traegt.**
///
/// **Was vorher war, gemessen 2026-08-21:** dieselbe Datei ergab **0 Fehler**, und das
/// `masks IRQ` kaufte sogar die Ausnahme von `H013`. *Ein Wort in der Wirkungsliste, und der
/// Pruefer schwieg ueber einem ungeschuetzten Weltzustand* — die Zusicherung aus R15.
#[test]
fn ein_traeger_masks_irq_verlangt_nested_masked() {
    fn codes(q: &str) -> Vec<&'static str> {
        let (baum, mut a) = gabbro_syntax::lies("p.gab", q);
        assert_eq!(a.fehler_zahl(), 0, "die Probe selbst parst nicht:\n{}", a.zeige(q));
        gabbro_check::pruefe(&baum, &mut a);
        a.absagen.iter().map(|x| x.code).collect()
    }

    // Ein Eintritt, dessen Weg `masks IRQ` nennt -- einmal mit `nested never`, einmal mit
    // `nested masked`. Sonst Zeichen fuer Zeichen dieselbe Datei.
    let quelle = |nested: &str| {
        format!(
            "module t {{
assume ein_kern \"one core\" falsifier sonde;
static mut z : u32 = 0;
impl fn a() effects {{ writes z, masks IRQ }} costs <= 4 ops {{ z = 1; }}
entry sc vector 0x80 via idt arch x86_64 {{
    regs in  {{ }}
    regs out {{ }}
    preserves {{ rbx }}
    clobbers  {{ rcx }}
    stack ks per cpu nested {nested}
    dispatch t::a;
}}
}}"
        )
    };

    // **1. Die fallende Richtung.** `nested never` ist eine Aussage ueber den WIEDEREINTRITT,
    // nicht ueber den Zustand -- der Traeger ist damit nicht gedeckt.
    assert!(
        codes(&quelle("never")).contains(&"H101"),
        "`nested never` deckt keinen Traeger `masks IRQ`: {:?}",
        codes(&quelle("never"))
    );

    // **2. Die schweigende Richtung, und sie ist die eigentliche Probe.** Eine Regel, deren
    // Abhilfe eine ANDERE Regel ausloest, ist keine Abhilfe: die Datei mit `nested masked`
    // muss GANZ sauber sein, nicht nur frei von `H101`. *Vor der Zeile in `ein_kern_deckt`
    // fiel hier `H013`* -- `Verschachtelt::Maskiert` hat ausser dem Erzeuger niemand gelesen.
    assert_eq!(
        codes(&quelle("masked")),
        Vec::<&str>::new(),
        "`nested masked` traegt den Traeger -- und darf keine zweite Absage ausloesen"
    );

    // **3. Und ohne Traeger faellt `H101` nicht**, sonst waere es eine Regel ueber `entry`
    // statt ueber den Traeger. *Der Weltzustand bleibt ungeschuetzt, also faellt `H013` --
    // genau das trennt die beiden Regeln.*
    let ohne = codes(
        "module t {
assume ein_kern \"one core\" falsifier sonde;
static mut z : u32 = 0;
impl fn a() effects { writes z } costs <= 4 ops { z = 1; }
entry sc vector 0x80 via idt arch x86_64 {
    regs in  { }
    regs out { }
    preserves { rbx }
    clobbers  { rcx }
    stack ks per cpu nested never
    dispatch t::a;
}
}",
    );
    assert!(!ohne.contains(&"H101"), "ohne Traeger gibt es nichts zu decken: {ohne:?}");
    assert!(ohne.contains(&"H013"), "der ungeschuetzte Platz faellt weiterhin: {ohne:?}");
}

/// **Die Zahl neben dem Urteil: ein erklaerter Traeger, den KEIN Kontext erreicht.**
///
/// `messung/fragmente/F08.gab` ist genau dieser Fall — ein `masks IRQ` und kein `entry`.
/// **Er ist nicht freigesprochen, sondern ungesehen** (W10), und `gabbro kontexte` muss das
/// hinschreiben statt zu schweigen. *Ein stiller Lauf liest sich sonst wie ein bestandener.*
#[test]
fn ein_unerreichter_traeger_wird_gezaehlt_statt_verschwiegen() {
    let mit_kontext = "module t {
static mut z : u32 = 0;
impl fn a() effects { writes z, masks IRQ } costs <= 4 ops { z = 1; }
entry sc vector 0x80 via idt arch x86_64 {
    regs in  { }
    regs out { }
    preserves { rbx }
    clobbers  { rcx }
    stack ks per cpu nested masked
    dispatch t::a;
}
}";
    // Dieselbe Einheit OHNE den Eintritt -- eine Bibliothek, wie F08 eine ist.
    let ohne_kontext = "module t {
static mut z : u32 = 0;
impl fn a() effects { writes z, masks IRQ } costs <= 4 ops { z = 1; }
}";

    let l = |q: &str| gabbro_check::kontexte::lage(&baum(q));

    let a = l(mit_kontext);
    assert_eq!(a.traeger_erklaert, 1, "ein `masks IRQ` ist ein erklaerter Traeger");
    assert_eq!(a.traeger_unerreicht, 0, "der Eintritt erreicht ihn");
    assert_eq!(a.gedeckt, 1, "und `nested masked` deckt ihn");

    let b = l(ohne_kontext);
    assert_eq!(b.traeger_erklaert, 1, "der Traeger steht auch ohne Eintritt da");
    assert_eq!(b.traeger_unerreicht, 1, "und ihn erreicht niemand -- das ist die Zahl");
    assert_eq!(b.ungedeckt, 0, "abgesagt wird hier NICHT: `H101` sieht keinen Kontext");
}

// --- emit ---

/// **Die aufgeloesten Auffangzweige der Emission -- je Zweig die Entscheidung, die vorher
/// still fiel.**
///
/// `mutiere-pruefer.py` sagt es selbst: *„Eine Flaeche mit 0 Mutationen ist nicht gedeckt,
/// sondern unbeschaedigbar."* Dieselbe Ueberlegung gilt eine Ebene tiefer -- **ein `_`-Zweig
/// ueber einem Summentyp ist eine Entscheidung ohne Probe**: er hat eine Antwort, aber die
/// Antwort steht nirgends, also kann auch nichts an ihr fallen.
///
/// Jede Behauptung hier gehoert zu genau einer Mutation in `mutiere-pruefer.py`.
#[test]
fn die_aufgeloesten_emissionszweige_tragen_ihre_entscheidung() {
    fn absagen_von(q: &str) -> Vec<String> {
        let (baum, mut a) = gabbro_syntax::lies("p.gab", q);
        assert_eq!(a.fehler_zahl(), 0, "die Probe parst nicht:\n{}", a.zeige(q));
        let _ = gabbro_check::emit::emittiere(&baum, &mut a);
        a.absagen.iter().map(|x| x.text.clone()).collect()
    }
    fn c_ohne_absage(q: &str) -> String {
        let (baum, mut a) = gabbro_syntax::lies("p.gab", q);
        assert_eq!(a.fehler_zahl(), 0, "die Probe parst nicht:\n{}", a.zeige(q));
        let c = gabbro_check::emit::emittiere(&baum, &mut a);
        assert_eq!(a.fehler_zahl(), 0, "die Absenkung traegt:\n{}", a.zeige(q));
        c
    }

    // **1. `sammle_retry` erreicht ein `retry` in einem `if`.**
    //
    // Der Sammelzweig stand hinter vier Armen -- `locks`, `match`, `narrow` und dem Rumpf
    // des `retry` selbst. Ein `retry` unter einem `if` bekam damit **keinen Eintrag in der
    // Schrankenkarte**, und die Absenkung antwortete darauf mit `C001`: *„`bounded … ops`
    // -- the per-pass cost is not fixed"*. **Die Kosten standen fest; der Sammler kam nicht
    // hin.** Eine Absage mit dem falschen Grund ist einen Schritt von einer stillen entfernt.
    let im_zweig = absagen_von(
        "module t {
extern fn weg() -> never effects { diverges } costs <= 0 ops;
impl fn f(c : bool) effects { pure } costs <= 4096 ops {
    if c {
        retry warten until c bounded 1024 ops on_exceeded weg effects { pure } { }
    }
}
}",
    );
    assert!(
        !im_zweig.iter().any(|s| s.contains("per-pass cost is not fixed")),
        "ein `retry` in einem `if` hat eine Schranke, und der Sammler muss sie finden: {im_zweig:?}"
    );

    // **2. `breaking` wird beim NAMEN abgelehnt.**
    //
    // Hinter *„no lowering: statement kind"* stand nicht eine offene Liste, sondern genau
    // EINE Anweisungsart. Sechzehn von siebzehn senken ab -- die Absage nannte trotzdem
    // keine von ihnen.
    let brechend = absagen_von(
        "module t {
table O count 8 {
    slot { zaehler : u32 in 0 .. 9, }
    invariant zaehler_klein cost O(n) runs offline :
        forall s in slots of Self : Self.slots[s].zaehler >= 0;
}
impl fn f(o : ptr<normal, rw> O, i : index into O) effects { writes o.slots }
    costs <= 8 ops { breaking zaehler_klein { o.slots[i].zaehler = 0; } }
}",
    );
    assert!(
        brechend.iter().any(|s| s.contains("`breaking")),
        "die Absage muss `breaking` beim Namen nennen: {brechend:?}"
    );

    // **3. Die drei Ausdrucksformen ohne Absenkung tragen DREI Gruende, nicht einen.**
    //
    // `sizeof`/`lenof`/`aligned`, `old(place)` und `result` fielen unter *„expression
    // form"* zusammen. Ein Zeugnis, das das sagt, nennt die Form nicht.
    let ergebnis = absagen_von(
        "module t {
impl fn f(x : u32 in 0 .. 9) -> u32 in 0 .. 9 ensures result == x effects { pure } \
costs <= 2 ops { return x; }
impl fn g(x : u32 in 0 .. 9) -> u32 in 0 .. 9 effects { pure } costs <= 2 ops \
{ return sizeof(u32); }
}",
    );
    assert!(
        ergebnis.iter().any(|s| s.contains("`sizeof`")),
        "ein `sizeof` im Rumpf wird beim Namen abgelehnt: {ergebnis:?}"
    );

    // **4. Ein Gleitkommafeld in einem TRAEGER laesst die Einheit es ansagen.**
    //
    // `rechnet_mit_gleitkomma` fragte fuenf Itemarten und liess neunzehn in den
    // Sammelzweig fallen -- darunter `table` und `format`. Eine Einheit mit `f64` im Slot
    // rechnete damit mit Gleitkomma **ohne die Ansage**, und die Ansage ist keine
    // Verzierung: sie sagt `-ffast-math ist verboten` und benennt die SSE2-Annahme.
    let mit_f64 = c_ohne_absage(
        "module t { table T count 4 { slot { g : f64, } } }",
    );
    assert!(
        mit_f64.contains("Gleitkomma"),
        "ein `f64` im Slot ist Gleitkomma, und die Einheit sagt es an:\n{mit_f64}"
    );
    // Die schweigende Richtung -- *ohne sie belegte die obere nur, dass irgendetwas steht.*
    let ohne_f64 = c_ohne_absage("module t { table T count 4 { slot { g : u64, } } }");
    assert!(
        !ohne_f64.contains("Diese Einheit rechnet mit Gleitkomma"),
        "eine Ganzzahltabelle sagt nichts ueber Gleitkomma an:\n{ohne_f64}"
    );

    // **5. Ein `transition` ueber einem INDEX sagt, warum ein Index dort nicht geht.**
    //
    // Der Sammelzweig stand fuer ZWEI Suffixformen (`[…]` und `->`) und nannte nur eine.
    // Die zweite ist ausgeschrieben und **durch die Grammatik unerreichbar** -- `parse::
    // transition` schaltet `->` links vom `:` als Suffix ab (G3), ein `R->A:` faellt schon
    // an `P001`. *Darum hat dieser Zweig keine Probe und darf keine haben;* geprueft wird
    // der, den ein Programm erreichen kann.
    let index = absagen_von(
        "module t { type Pa = u64; device D(basis : Pa) at mmio {
    reg R : u32 @0x0 class rw fields { A @0, }
    transition an { R[0]: 0 -> 1 } effects { writes R }
} }",
    );
    assert!(
        index.iter().any(|s| s.contains("which register an index picks is a run time")),
        "die Absage nennt den Grund und nicht nur die Form: {index:?}"
    );
}

// --- p6 ---
//
// **P6 -- the GENERATED refinement obligation** (2026-08-21). `gabbro pflichten --isabelle`
// writes the very register `gabbro pflichten` counts, as an Isabelle theory.
//
// The condition this emitter was built under stands in `README.md` and in
// `mutiere-pruefer.py` under the surface `annotation`:
//
// > *A generator that quietly emits weakened contracts delivers a green proof of a WEAKER
// > statement, and no probe catches it.*
//
// **A duty that vanishes is noticed; one that gets weaker is not.** Every probe below aims
// at a weakening rather than at a disappearance -- and beside each of them stands the
// mutation in `mutiere-pruefer.py` that makes it fall.

/// The theory of a source, exactly as `gabbro pflichten --isabelle` prints it.
fn p6_theory(q: &str) -> String {
    let (b, _a) = gabbro_syntax::lies("p6.gab", q);
    gabbro_check::refinement::theory(&b, "p6.gab")
}

/// `total`, `goals`, `refused` off the header line -- the balance the emitter keeps about
/// itself.
fn p6_balance(t: &str) -> (usize, usize, usize) {
    let line = t
        .lines()
        .find(|z| z.contains("@duty 1"))
        .expect("the emitter keeps a header line about itself");
    let number = |word: &str| -> usize {
        let mut s = line.split_whitespace();
        while let Some(w) = s.next() {
            if w == word {
                return s.next().and_then(|x| x.parse().ok()).unwrap_or(usize::MAX);
            }
        }
        usize::MAX
    };
    (number("total"), number("goals"), number("refused"))
}

/// A caller that WRITES its own parameter, beside one that leaves it alone.
const P6_WRITTEN: &str = "module t {
type Klein = u32 in 0 .. 9;
impl fn nimm(x : Klein) requires x < 9 effects { pure } costs <= 1 ops { }
impl fn f(a : Klein, b : Klein)
    requires a < 9, b < 9
    effects  { writes a }
    costs    <= 20 ops
{
    a = 5;
    nimm(b);
}
}";

/// **A generated goal carries EVERY conjunct of the precondition it discharges.**
///
/// `requires k < 64 && n < 4096` is one clause and two statements. An emitter that drops the
/// second writes down a goal a prover closes without complaint -- *and the duty it has then
/// proved is not the one in the contract.*
///
/// The mutation is `p6-and-becomes-or`; it turns the `\<and>` into a `\<or>`: one line,
/// the same two conjuncts, **and the weaker statement.**
#[test]
fn a_generated_goal_carries_every_conjunct() {
    let t = p6_theory(
        "module t {
impl fn zwei(k : u32, n : u32) requires k < 64 && n < 4096 effects { pure } costs <= 1 ops { }
impl fn g(k : u32) requires k < 64 effects { pure } costs <= 20 ops { zwei(k, 7); }
}",
    );
    let shows = t
        .lines()
        .find(|z| z.trim_start().starts_with("shows "))
        .unwrap_or("<no shows>");
    assert_eq!(
        shows.trim(),
        "shows \"((g_k) < ((64 :: int))) \\<and> (((7 :: int)) < ((4096 :: int)))\"",
        "both conjuncts, joined by `\\<and>` -- the claim, word for word"
    );
    assert_eq!(p6_balance(&t), (1, 1, 0), "one duty, one goal, no refusal");
}

/// **A precondition the caller brings along holds AT ENTRY -- not later.**
///
/// `requires a < 9` is a sentence about `a` on entry. Once the body writes `a`, it says
/// nothing at the call site. An emitter that writes it down as an assumption anyway proves
/// under a hypothesis nobody granted -- **exactly the quiet weakening this surface exists
/// for.**
///
/// Measured on the same source: `b` is never touched, so `r_2` stands; `a` is written, so
/// neither `r_1` nor the type bound of `a` may appear.
#[test]
fn a_precondition_about_a_written_parameter_is_no_assumption() {
    let t = p6_theory(P6_WRITTEN);
    assert!(
        t.contains("assumes r_2:"),
        "`b` is untouched -- `requires b < 9` holds at the call site and stands there:\n{t}"
    );
    assert!(
        !t.contains("assumes r_1:"),
        "`a` is written -- `requires a < 9` must NOT stand at the call site:\n{t}"
    );
    assert!(
        !t.contains("assumes t_a:"),
        "and neither may the type bound of `a` -- it is the same sentence about entry:\n{t}"
    );
}

/// **An argument the body has touched carries no goal at all.**
///
/// The counterpart to the previous probe: there the ARGUMENT was stable and an assumption
/// inadmissible; here the argument is the written parameter itself. Without this gate a goal
/// would arise about `g_a`, whose value in the program is long since another one.
#[test]
fn a_written_parameter_as_argument_yields_no_goal() {
    let t = p6_theory(
        "module t {
type Klein = u32 in 0 .. 9;
impl fn nimm(x : Klein) requires x < 9 effects { pure } costs <= 1 ops { }
impl fn f(a : Klein)
    requires a < 9
    effects  { writes a }
    costs    <= 20 ops
{
    a = 5;
    nimm(a);
}
}",
    );
    assert_eq!(p6_balance(&t), (1, 0, 1), "one duty, NO goal, one refusal");
    assert!(
        t.contains("argument-not-stable (1)"),
        "and the refusal names its reason:\n{t}"
    );
}

/// **The bound of the declared type is the bound of the declared type.**
///
/// A bound that is too TIGHT is the quietest weakening of all: `9 \<le> g_b \<and> g_b \<le>
/// 9` pins the value down, and after that every goal goes through. Nothing in the output
/// looks smaller than before -- *there is even more standing there.*
#[test]
fn the_type_bound_is_the_declared_one() {
    let t = p6_theory(P6_WRITTEN);
    assert!(
        t.contains("assumes t_b: \"0 \\<le> g_b \\<and> g_b \\<le> 9\""),
        "`type Klein = u32 in 0 .. 9` gives exactly 0 .. 9 -- a range with a name is no wall:\n{t}"
    );
}

/// **`Held(…)` is no prover obligation, and does not become one.**
///
/// The lock passes carry it (`H005`/`H006`/`H012`/`H016` in `geteilt.rs`). An emitter that
/// turns it into `True` has not merely written a wrong line -- it has turned a CARRIED duty
/// into a trivial goal, and the balance afterwards reports more coverage than before.
#[test]
fn a_lock_witness_does_not_become_a_goal() {
    let t = p6_theory(
        "module t {
static mut w : u32 = 0;
lock L protects { w } rank 0 held <= 10 ops;
impl fn unter_sperre(z : u32) requires Held(L) effects { locks L } costs <= 4 ops { }
impl fn h() effects { locks L } costs <= 20 ops { locks L { unter_sperre(1); } }
}",
    );
    assert_eq!(p6_balance(&t), (1, 0, 1), "one duty, NO goal");
    assert!(
        t.contains("lock-witness (1)"),
        "and it stands under the reason that says WHO carries it:\n{t}"
    );
}

/// **An `ensures` at a foreign body stays an ASSUMPTION and is not filed as a goal.**
///
/// The most expensive mistake here would be an axiom: an assumption about foreign code
/// standing as an Isabelle axiom proves everything that comes after it. Hence its own
/// refusal reason, and not the one a body of our own gets.
#[test]
fn a_foreign_ensures_stays_an_assumption() {
    let t = p6_theory(
        "module t {
extern fn fremd() -> u32 ensures result <= 100 effects { pure } costs <= 1 ops;
}",
    );
    assert_eq!(p6_balance(&t), (1, 0, 1));
    assert!(
        t.contains("foreign-body (1)"),
        "the reason names the foreign body, not the missing body semantics:\n{t}"
    );
}

/// **The balance adds up, and it adds up over THE SAME register `gabbro pflichten` counts.**
///
/// *An output that forgets one kind looks complete* (`messung/ABI.md`, the `lock` line that
/// was missing for a day). Against exactly that: `goals + refused == total`, and `total` is
/// the length of the register -- not a second number from a second walk.
#[test]
fn the_balance_of_the_emitter_adds_up() {
    let q = "module t {
type Klein = u32 in 0 .. 9;
static mut w : u32 = 0;
lock L protects { w } rank 0 held <= 10 ops;
extern fn fremd() -> u32 ensures result <= 100 effects { pure } costs <= 1 ops;
spec fn ruhig() -> bool effects { pure } = w == 0;
impl fn nimm(x : Klein) requires x < 9 effects { pure } costs <= 1 ops { }
impl fn unter_sperre(z : u32) requires Held(L) effects { locks L } costs <= 4 ops { }
impl fn f(b : Klein) requires b < 9 effects { pure } costs <= 20 ops { nimm(b); }
impl fn h() maintains ruhig effects { locks L, reads w } costs <= 40 ops
{ locks L { unter_sperre(1); } }
}";
    let (b, _a) = gabbro_syntax::lies("p6.gab", q);
    let register = gabbro_check::pflichten::sammle(&b).len();
    let judged = gabbro_check::refinement::verdicts(&b).len();
    assert_eq!(
        register, judged,
        "the emitter judges every duty of the register and no second one"
    );
    let (total, goals, refused) = p6_balance(&p6_theory(q));
    assert_eq!(total, register, "the header names the length of the register");
    assert_eq!(
        goals + refused,
        total,
        "goals + refused == total -- otherwise a duty got lost on the way"
    );
    assert!(goals >= 1, "and at least one of them stands closed:\n{q}");
}

// ===========================================================================================
// THE BODY CHANNEL -- `gabbro pflichten --lean`
//
// `refinement.rs` refuses every obligation about a body with one word: `body-effect`. The
// Lean channel is the other half -- `passlogik/Passlogik/Rumpf.lean` says what a body MEANS,
// and `lean.rs` writes a body as a datum of it.
//
// **Each probe below stands against one WEAKENING**, and each weakening has a mutation. *A
// duty that disappears is noticed; one that gets weaker is not* -- so these probes read the
// TEXT and not only the balance line: five of the weakenings leave the balance untouched.
// ===========================================================================================

fn lean_modul(q: &str) -> String {
    let (b, _a) = gabbro_syntax::lies("lean.gab", q);
    gabbro_check::lean::module(&b, "lean.gab")
}

/// A unit in the shape the channel was built for: a `refines` at a straight-line body.
const LEAN_VERFEINERUNG: &str = "module t {
const N : u32 = 8;
type Zahl = u32 in 0 .. 99;
lock L protects { B } rank 0 held <= 10 ops;
table B count N { slot { belegt : bool, wert : Zahl, } }
spec fn frei(p : index into B) -> bool effects { pure } = !B.slots[p].belegt;
impl fn gib_frei(p : index into B)
    refines  frei
    requires Held(L), B.slots[p].belegt
    effects  { reads B.slots, writes B.slots, locks L }
    costs    <= 8 ops
{
    B.slots[p].belegt = false;
    B.slots[p].wert   = 0;
}
}
";

/// A body that CALLS. The call is outside the sequential core, and the whole obligation has
/// to be refused -- **not the call silently dropped.**
const LEAN_MIT_RUF: &str = "module t {
const N : u32 = 8;
lock L protects { B } rank 0 held <= 10 ops;
table B count N { slot { belegt : bool, } }
impl fn helfer(p : index into B)
    requires Held(L)
    effects  { writes B.slots, locks L }
    costs    <= 4 ops
{ B.slots[p].belegt = false; }
impl fn ruft(p : index into B)
    requires Held(L)
    ensures  B.slots[p].belegt == false
    effects  { writes B.slots, locks L }
    costs    <= 9 ops
{ helfer(p); }
}
";

/// **The balance the emitter keeps about itself, and it must add up.** Same reading as the
/// Isabelle channel keeps, so the two can be held against each other.
#[test]
fn lean_bilanz_geht_auf() {
    for q in [LEAN_VERFEINERUNG, LEAN_MIT_RUF] {
        let t = lean_modul(q);
        let (total, goals, refused) = p6_balance(&t);
        assert_eq!(
            goals + refused,
            total,
            "goals + refused == total -- otherwise a duty got lost on the way:\n{t}"
        );
    }
}

/// **The head form goes through the channel and comes out as a THEOREM.** Both halves have
/// to be there: the body as a datum, and the postcondition the `spec fn` gives.
#[test]
fn lean_verfeinerung_wird_ein_ziel() {
    let t = lean_modul(LEAN_VERFEINERUNG);
    let (_, goals, _) = p6_balance(&t);
    assert_eq!(goals, 1, "the `refines` is the one goal of this unit:\n{t}");
    assert!(t.contains("def body_duty_1"), "the body stands as a datum:\n{t}");
    assert!(
        t.contains("def post_duty_1"),
        "and the specification as the postcondition:\n{t}"
    );
    // The `spec fn` names `p`; the implementation names `p` too, and the emitter substitutes
    // positionally rather than by luck.
    assert!(
        t.contains(r#".place "B" (.name "p") "belegt""#),
        "the place carries carrier, index and field:\n{t}"
    );
}

/// **The goal is the STRONG form.** `\forall l', end = some l' -> P l'` is vacuously true
/// for a body that gets stuck, and a vacuous theorem reads exactly like a proved one.
#[test]
fn lean_ziel_ist_die_starke_form() {
    let t = lean_modul(LEAN_VERFEINERUNG);
    assert!(
        t.contains("∃ s', finalState"),
        "the body must be shown to REACH an end state:\n{t}"
    );
    assert!(
        !t.contains("∀ s', finalState"),
        "and not merely to satisfy the postcondition IF it reaches one:\n{t}"
    );
}

/// **`autoImplicit` off, and it is a guard.** With it on, a predicate name Lean does not know
/// becomes an implicitly bound variable -- measured on the first run of this emitter, where
/// a hypothesis whose predicate was out of scope elaborated to a BINDER instead of failing.
#[test]
fn lean_autoimplicit_bleibt_aus() {
    let t = lean_modul(LEAN_VERFEINERUNG);
    assert!(
        t.contains("set_option autoImplicit false"),
        "a misspelt hypothesis must FAIL, not turn into a free variable:\n{t}"
    );
}

/// **The field shape is read from the DECLARATION.** `belegt : bool` gives `istWahrheit`;
/// guessing it from the use would make the goal easier, not harder.
#[test]
fn lean_feldform_kommt_aus_der_deklaration() {
    let t = lean_modul(LEAN_VERFEINERUNG);
    assert!(
        t.contains(r#"isBool (s.world (.slot "B" k "belegt"))"#),
        "a `bool` field carries the truth shape:\n{t}"
    );
    assert!(
        t.contains(r#"isInt (s.world (.slot "B" k "wert"))"#),
        "and an integer field the number shape:\n{t}"
    );
}

/// **A statement outside the core is REFUSED, not dropped.** A call that vanished from the
/// datum would leave a body that does less than the real one -- and the goal would then be
/// about a program nobody wrote.
#[test]
fn lean_ruf_wird_abgesagt_nicht_verschluckt() {
    let t = lean_modul(LEAN_MIT_RUF);
    let (_, goals, refused) = p6_balance(&t);
    assert_eq!(goals, 0, "a body with a call carries no goal here:\n{t}");
    assert!(refused >= 1, "and the obligation is refused:\n{t}");
    // **The reason names the CALL, not "a statement kind".** Eight reasons stand where one
    // stood: the coarse one hid that a call, a loop and a `publishes` cost three different
    // things, and a work order over a single bucket is not one.
    assert!(
        t.contains("call-not-compositional"),
        "BY NAME, and the name is the call:\n{t}"
    );
}

/// **A conjunction stays a conjunction.** `ensures a, b` and `p && q` are the strongest form
/// the postcondition has; an OR leaves both operands standing and halves the duty -- the
/// weakening that a balance line cannot see.
#[test]
fn lean_und_bleibt_und() {
    let q = "module t {
const N : u32 = 8;
lock L protects { B } rank 0 held <= 10 ops;
table B count N { slot { belegt : bool, frisch : bool, } }
impl fn raeume(p : index into B)
    requires Held(L)
    ensures  B.slots[p].belegt == false && B.slots[p].frisch == true
    effects  { writes B.slots, locks L }
    costs    <= 9 ops
{
    B.slots[p].belegt = false;
    B.slots[p].frisch = true;
}
}
";
    let t = lean_modul(q);
    assert!(
        t.contains(".bin .and"),
        "the conjunction of the postcondition survives translation:\n{t}"
    );
    assert!(
        !t.contains(".bin .or"),
        "and does not quietly become a disjunction:\n{t}"
    );
}

/// **A compound assignment takes its operator from the field's declared SHAPE.**
///
/// `x += e` is `x = x + e` -- `M104` says the result fits, and both forms have the same
/// result. But `&=` on an INTEGER field is a bit operation, and those are refused for the
/// same reason division is: the model would compute something Gabbro does not.
#[test]
fn lean_mischzuweisung_folgt_der_form() {
    let mit = |op: &str, feld: &str| {
        format!(
            "module t {{
const N : u32 = 8;
type Kleines = u32 in 0 .. 99;
table B count N {{ slot {{ zahl : Kleines, ja : bool, }} }}
impl fn f(p : index into B)
    effects  {{ reads B.slots, writes B.slots }}
    costs    <= 8 ops
{{ B.slots[p].{feld} {op} {}; }}
}}
",
            if feld == "ja" { "true" } else { "1" }
        )
    };
    let plus = lean_programm(&mit("+=", "zahl"));
    assert!(
        plus.contains("(.bin .add (.place \"B\" (.name \"p\") \"zahl\")"),
        "`+=` on an integer field unfolds to `x + e`:\n{plus}"
    );
    let bitund = lean_programm(&mit("&=", "zahl"));
    assert!(
        bitund.contains("(compound-assignment)"),
        "`&=` on an INTEGER field is a bit operation and is refused:\n{bitund}"
    );
    assert!(
        !bitund.contains(".bin .and"),
        "and it is not taken as a truth value:\n{bitund}"
    );
}

/// **A record or `format` field is a place too -- and it carries NO index.**
///
/// A record is one object, a table is a row of them. Giving a record field a dummy index
/// would make two different things one `Place`, and a slot could then alias a record field.
#[test]
fn lean_verbundfeld_traegt_keinen_index() {
    let q = "module t {
const KAP : u32 = 8;
type Text = { laenge : u32 in 0 .. KAP, offen : bool, };
impl fn schliessen(s : ptr<normal, rw> Text)
    effects  { writes s }
    costs    <= 4 ops
{ s.offen = false; }
impl fn ist_offen(s : ptr<normal, r> Text) -> bool
    effects  { reads s }
    costs    <= 4 ops
{ return s.offen; }
}
";
    let t = lean_programm(q);
    assert!(
        t.contains(r#"(.assignField "s" "offen""#),
        "the write goes to a FIELD, not to a slot:\n{t}"
    );
    // **The READ path is a separate arm and needs its own probe.** A mutation that turned a
    // record read into a slot at index zero slipped past a test that only ever wrote.
    assert!(
        t.contains(r#"(.fieldOf "s" "offen")"#),
        "and so does the read:\n{t}"
    );
    assert!(
        !t.contains(r#"(.slot "s" 0"#),
        "neither of them becomes a slot at a made-up index:\n{t}"
    );
    assert!(
        t.contains(r#"("Text", "offen", "isBool")"#),
        "and the field stands in the dictionary with its declared shape:\n{t}"
    );
    assert!(
        t.contains(r#"(isBool (s.world (.field "Text" "offen")))"#),
        "and in `wellFormed`, without an index:\n{t}"
    );
}

/// **A `reserved` field of a `format` carries NO shape.** It is not readable -- the wire
/// never promised anything about it -- so a hypothesis about its value would be one about
/// something nobody said.
#[test]
fn lean_reserviertes_feld_bekommt_keine_form() {
    let q = "module t {
format Kopf endian little {
    marke  : u32,
    luecke : u32 reserved,
}
impl fn lies(k : ptr<normal, r> Kopf) -> u32
    effects  { reads k }
    costs    <= 4 ops
{ return k.marke; }
}
";
    let t = lean_programm(q);
    assert!(
        t.contains(r#"("Kopf", "marke", "isInt")"#),
        "the readable field stands in the dictionary:\n{t}"
    );
    assert!(
        !t.contains(r#""luecke""#),
        "the `reserved` one does not, in any table:\n{t}"
    );
}

/// **`let n = f(a);` and `return f(a);` are CALLS, and they stay statements.**
///
/// A callee may write, so an expression carrying a call would no longer be pure -- `eval`
/// would have to take the environment, and the whole model would move one level up. Keeping
/// them as statements is what lets `eval` stay a function of the state alone.
#[test]
fn lean_ruf_im_let_und_im_return_bleibt_anweisung() {
    let q = "module t {
const N : u32 = 8;
table B count N { slot { belegt : bool, } }
impl fn frag(p : index into B) -> bool
    effects  { reads B.slots }
    costs    <= 4 ops
{ return B.slots[p].belegt; }
impl fn merkt(p : index into B) -> bool
    effects  { reads B.slots }
    costs    <= 12 ops
{
    let w = frag(p);
    return w;
}
impl fn reicht_durch(p : index into B) -> bool
    effects  { reads B.slots }
    costs    <= 12 ops
{ return frag(p); }
}
";
    let t = lean_programm(q);
    assert!(
        t.contains(r#"(.bindCall "w" "frag" ["p"] [(.name "p")])"#),
        "`let w = frag(p);` binds the RESULT of a call:\n{t}"
    );
    assert!(
        t.contains(r#"(.retCall "frag" ["p"] [(.name "p")])"#),
        "`return frag(p);` returns it straight on:\n{t}"
    );
    // **Neither becomes a plain binding.** A call folded into `bindName` would lose the
    // callee entirely, and the body would then say `let w = <nothing>`.
    assert!(
        !t.contains(r#"(.bindName "w""#),
        "and neither is taken as an ordinary expression:\n{t}"
    );
}

/// **A loop is an anonymous routine, and its `invariant` is DATA.**
///
/// The measure was carried by the language from the start; the statement had no word until
/// 2026-08-28 (`messung/SCHLEIFENINVARIANTE.md`). A loop WITHOUT one is still refused --
/// that is the point of the word, not a gap in it.
#[test]
fn lean_schleife_traegt_ihre_invariante() {
    let mit = |inv: &str| {
        format!(
            "module t {{
const N : u32 = 8;
table B count N {{ slot {{ belegt : bool, }} tree {{ parent elter }} }}
impl fn leeren(h : ptr<normal, rw> B, s : index into B)
    effects {{ writes h.slots }}
    costs   <= 200 ops
{{
    traverse k over descendants of h.slots[s] by consuming
        touches consumes h.slots{inv}
    {{ h.slots[k].belegt = false; }}
    traverse m over descendants of h.slots[s] by consuming
        touches consumes h.slots{inv}
    {{ h.slots[m].belegt = true; }}
}}
}}
"
        )
    };
    let ohne = lean_programm(&mit(""));
    assert!(
        ohne.contains("(loop)"),
        "a loop with no `invariant` is refused BY NAME:\n{ohne}"
    );
    let t = lean_programm(&mit("\n        invariant h.slots[s].belegt"));
    assert!(
        t.contains(r#"(.loop "leeren#1""#),
        "one with an invariant becomes a datum, under an id of its own:\n{t}"
    );
    assert!(
        t.contains(r#"(.place "h" (.name "s") "belegt")"#),
        "and the invariant travels with it -- it is what the loop rule quantifies over:\n{t}"
    );
    // **The loop VARIABLE is a local.** Read as a world name it would make the datum say the
    // body touches a global nobody declared.
    assert!(
        t.contains(r#"(.name "k")"#),
        "the bound variable is a local, not a global:\n{t}"
    );
    assert!(
        !t.contains(r#"(.global "k")"#),
        "and never a global:\n{t}"
    );
    // **Two loops in one routine need two ids.** Sharing one environment entry would let a
    // hypothesis about the first silently cover the second -- and the second is a different
    // loop with a different body.
    assert!(
        t.contains(r#"(.loop "leeren#2""#),
        "the second loop gets an id of its own:\n{t}"
    );
}

/// **A critical section keeps its NAME in the datum.**
///
/// `locks S { … }` means what its body means -- the whole model is sequential, and what makes
/// that sound is exactly that the lock is held (`H005`/`H006`/`H012`/`H016`). *But inlining
/// the body would erase the critical section from the record*, and a reader could no longer
/// see where one was.
#[test]
fn lean_kritischer_abschnitt_behaelt_seinen_namen() {
    let q = "module t {
const N : u32 = 8;
lock L protects { B } rank 0 held <= 10 ops;
table B count N { slot { belegt : bool, } }
impl fn leeren(p : index into B)
    effects  { writes B.slots, locks L }
    costs    <= 20 ops
{
    locks L { B.slots[p].belegt = false; }
}
}
";
    let t = lean_programm(q);
    assert!(
        t.contains(r#"(.locked "L" ["#),
        "the lock names itself in the datum:\n{t}"
    );
    assert!(
        t.contains(r#"(.assign "B" (.name "p") "belegt""#),
        "and the body is inside it:\n{t}"
    );
    let (_, bodies, refused, _) = lean_programm_kopf(&t);
    assert_eq!(bodies, 1, "the routine carries a body:\n{t}");
    assert_eq!(refused, 0, "and nothing is refused:\n{t}");
}

/// **The pairing carries, and the PAYLOAD stays in the datum.**
///
/// `release_stellt_sichtbarkeit_her` is an assumption of the axiom layer -- `unfalsifiable`,
/// with its reason written out, rebooked there by `K100.2`. So a release store is a store and
/// an acquire load is a load. *The payload is the surface that rests on the assumption rather
/// than on the transition*, and a record that dropped it would hide which places those are.
#[test]
fn lean_paarung_traegt_die_nutzlast() {
    let q = "module t {
atomic FERTIG : bool release;
atomic ZAHL   : u64 relaxed;
static mut bericht : u64 = 0;
impl fn meldet()
    effects { writes bericht, publishes FERTIG }
    costs   <= 8 ops
{
    bericht = 1;
    FERTIG = true publishes { bericht };
}
impl fn zaehlt(w : u64)
    effects { writes ZAHL }
    costs   <= 8 ops
{ ZAHL = w publishes nothing; }
impl fn liest() -> u64
    effects { reads FERTIG, reads bericht }
    costs   <= 8 ops
{
    let fertig = FERTIG awaits { bericht };
    return bericht;
}
}
";
    let t = lean_programm(q);
    assert!(
        t.contains(r#"(.publish "FERTIG" (.lit (.bool true)) ["bericht"])"#),
        "the release store names its payload:\n{t}"
    );
    // **`publishes nothing` is a WORD, not an empty hole**, and the datum keeps the
    // distinction: an empty payload is a promise about nothing, and it says so.
    assert!(
        t.contains(r#"(.publish "ZAHL" (.name "w") [])"#),
        "`publishes nothing` is the empty payload, not a missing one:\n{t}"
    );
    assert!(
        t.contains(r#"(.awaitLoad "fertig" "FERTIG" ["bericht"])"#),
        "and the acquire load names the same payload:\n{t}"
    );
    let (_, bodies, refused, _) = lean_programm_kopf(&t);
    assert_eq!(bodies, 3, "all three routines carry a body:\n{t}");
    assert_eq!(refused, 0, "and none is refused:\n{t}");
}

/// **Every refusal reason has a tag and a sentence, and `ALL` names all of them.** A reason
/// missing from `ALL` would be counted by nobody -- the register would look smaller than it
/// is, and smaller is the direction that flatters.
#[test]
fn lean_absagegruende_sind_vollzaehlig() {
    use gabbro_check::lean::LeanReason;
    let mut tags: Vec<&str> = LeanReason::ALL.iter().map(|r| r.tag()).collect();
    let n = tags.len();
    tags.sort_unstable();
    tags.dedup();
    assert_eq!(n, tags.len(), "two reasons share a tag: {tags:?}");
    for r in LeanReason::ALL {
        assert!(!r.tag().is_empty() && !r.sentence().is_empty(), "{r:?} is mute");
    }
}

// ===========================================================================================
// THE PROGRAM EXPORT -- `gabbro lean`
//
// A different artefact from the obligation channel above, and the difference is the
// direction: this one carries NO specification. It carries the program, so that a
// hand-written Lean specification can be held against it.
// ===========================================================================================

fn lean_programm(q: &str) -> String {
    let (b, _a) = gabbro_syntax::lies("prog.gab", q);
    gabbro_check::lean::program(&b, &["prog.gab".to_string()])
}

/// `routines`, `bodies`, `refused`, `places` off the export's header line.
fn lean_programm_kopf(t: &str) -> (usize, usize, usize, usize) {
    let line = t
        .lines()
        .find(|z| z.contains("@program 1"))
        .expect("the export keeps a header line about itself");
    let n = |w: &str| -> usize {
        let mut s = line.split_whitespace();
        while let Some(x) = s.next() {
            if x == w {
                return s.next().and_then(|y| y.parse().ok()).unwrap_or(usize::MAX);
            }
        }
        usize::MAX
    };
    (n("routines"), n("bodies"), n("refused"), n("places"))
}

/// A program with one body inside the fragment and one outside it.
const PROG: &str = "module t {
const N : u32 = 8;
type Kleines = u32 in 0 .. 99;
lock L protects { B } rank 0 held <= 10 ops;
table B count N { slot { belegt : bool, wert : Kleines, } }
impl fn leeren(p : index into B)
    requires Held(L), B.slots[p].belegt
    effects  { reads B.slots, writes B.slots, locks L }
    costs    <= 8 ops
{
    B.slots[p].belegt = false;
    B.slots[p].wert   = 0;
}
impl fn ruft(p : index into B)
    requires Held(L)
    effects  { reads B.slots, writes B.slots, locks L }
    costs    <= 20 ops
{ leeren(p); }
impl fn schleift(p : index into B)
    effects  { reads B.slots, writes B.slots }
    costs    <= 300 ops
{
    traverse k over descendants of B.slots[p] by consuming
        touches consumes B.slots
    { B.slots[k].belegt = false; }
}
}
";

/// **The balance the export keeps about itself, and it must add up.** A routine that vanishes
/// looks exactly like one that was refused, and only the second has measured anything.
#[test]
fn lean_programm_bilanz_geht_auf() {
    let t = lean_programm(PROG);
    let (routines, bodies, refused, places) = lean_programm_kopf(&t);
    assert_eq!(
        bodies + refused,
        routines,
        "bodies + refused == routines -- otherwise a routine got lost:\n{t}"
    );
    // **The routine that stands OUTSIDE is a loop WITHOUT an `invariant`**, and it is chosen
    // for durability: three earlier versions of this probe named a `locks` block and then a
    // `publishes`, and both were carried within the day. *A probe whose negative example
    // keeps being overtaken measures the calendar, not the fragment.* A loop without an
    // invariant is refused BY DESIGN -- that is what the word is for.
    assert_eq!(bodies, 2, "the leaf and the CALLER are both data:\n{t}");
    assert_eq!(refused, 1, "the loop without a statement about it is outside:\n{t}");
    assert_eq!(places, 2, "the table declares two fields with a shape:\n{t}");
}

/// **A routine outside the fragment is REFUSED BY NAME, not dropped.** A body that vanished
/// from the export would leave a specification standing over a program that is not there.
#[test]
fn lean_programm_sagt_ab_statt_zu_verschlucken() {
    let t = lean_programm(PROG);
    assert!(
        t.contains("-- REFUSED  schleift  (loop)"),
        "the routine outside the fragment stands with its reason:\n{t}"
    );
    assert!(!t.contains("def schleift_body"), "and carries no body:\n{t}");
    assert!(t.contains("def leeren_body"), "the leaf does:\n{t}");
    // **A call is a DATUM, never an inlining.** The callee is named and its parameters are
    // bound; what it does is looked up in an environment the reader's theorem quantifies
    // over. *An inlined body would make the goal a statement about a program nobody wrote.*
    assert!(
        t.contains(r#"(.call "leeren" ["p"] [(.name "p")])"#),
        "the call names the callee and binds its parameters:\n{t}"
    );
    assert!(
        t.contains("def leeren_post"),
        "and the contract a caller takes it over stands in the export:\n{t}"
    );
}

/// **The place dictionary and `wellFormed` come from ONE source and must agree.** The
/// dictionary is what a specification is held against; a field in one and not the other
/// would let a typo through in exactly the direction that flatters.
#[test]
fn lean_programm_woerterbuch_deckt_wohlgeformtheit() {
    let t = lean_programm(PROG);
    for feld in ["belegt", "wert"] {
        assert!(
            t.contains(&format!("\"B\", \"{feld}\"")),
            "`{feld}` stands in the dictionary:\n{t}"
        );
        assert!(
            t.contains(&format!("(.slot \"B\" k \"{feld}\")")),
            "and in `wellFormed`:\n{t}"
        );
    }
}

/// **A precondition this channel cannot say is DROPPED and LISTED.** Dropping is the safe
/// direction -- a hypothesis fewer makes the goal harder, never the proof wrong. *Dropping
/// it in SILENCE is not*: the trust surface would leave the file without a word.
#[test]
fn lean_programm_nennt_die_fallengelassene_vorbedingung() {
    let t = lean_programm(PROG);
    assert!(
        t.contains("DROPPED from the precondition"),
        "a `Held(L)` this channel has no term for is named:\n{t}"
    );
    // **And the reason is `lock-witness`, not "no term".** `Held(L)` is not a missing
    // translation -- the lock passes discharge it (H005/H006/H012/H016). Reporting it as a
    // gap counted a carried obligation as an open one, which is the direction that flatters.
    assert!(
        t.contains("lock-witness"),
        "and the reason names what it really is:\n{t}"
    );
}

/// **`autoImplicit` off in the export too.** The same guard as in the obligation channel: a
/// name Lean does not know must FAIL, not become a free variable.
#[test]
fn lean_programm_autoimplicit_bleibt_aus() {
    let t = lean_programm(PROG);
    assert!(
        t.contains("set_option autoImplicit false"),
        "a misspelt name must fail, not turn into a binder:\n{t}"
    );
    // And it carries no specification of its own -- that is the whole point of the artefact.
    // **The check looks at line STARTS**, not at the word: the closing comment shows a
    // specification as an example, and a `contains` found that and called it a theorem.
    assert!(
        !t.lines().any(|z| z.starts_with("theorem ")),
        "the export states nothing; a specification is written elsewhere:\n{t}"
    );
}
