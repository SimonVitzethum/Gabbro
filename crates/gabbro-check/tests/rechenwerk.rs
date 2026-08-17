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
    assert!(c.contains("const Objekte *o"), "{c}");
    assert!(c.contains("uint32_t stand("), "{c}");

    // `r` ohne `w` wird `const`; `rw` nicht. Die Rechte am Zeiger stehen im C.
    assert!(c.contains("void belegen(Objekte *o"), "{c}");

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
