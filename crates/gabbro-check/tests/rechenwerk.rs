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
    let unaer = absagen_von(
        "module t { table T count 8 { slot { benutzt : bool, } }\n\
         impl fn f(t : ptr<normal, r> T, i : index into T) -> bool \
         effects { reads t.slots } costs <= 4 ops { return !t.slots[i].benutzt; } }",
    );
    assert!(
        unaer.iter().any(|s| s.contains("expression form")),
        "eine unbekannte Ausdrucksform muss beim Namen abgelehnt werden: {unaer:?}"
    );

    // **3. `Some`/`None` sind Konstruktoren, keine Rufe** («B35»).
    let konstruktor = absagen_von(
        "module t { table T count 8 { slot { eltern : index into T, } }\n\
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

    // **Das Format ist ein Bytezeiger, kein Verbund.**
    assert!(c.contains("const uint8_t *bytes"), "{c}");
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

    // **2. Eine andere Zeugenordnung ist eine andere Laufform.** `by consuming` sagt etwas
    // ueber die Erhaltung einer Ordnung -- was es fuer den LAUF heisst, ist nicht entschieden.
    let (_, f) = c_von(
        "module t { table W count 16 { slot { a : bool, } }
impl fn loesche(w : ptr<normal, rw> W) effects { writes w.slots } costs <= 64 ops
{ traverse i over slots of w by consuming touches writes w.slots { w.slots[i].a = false; } } }",
    );
    assert!(
        f.iter().any(|s| s.contains("witness ordering")),
        "`by consuming` darf nicht wie `by unvisited` laufen: {f:?}"
    );

    // **3. `forever` wird abgelehnt, und der Grund ist ein Befund des Ordners.** `per_pass`
    // ist eine Aussage ueber die UEBERSETZUNGSZEIT, also hat `on_exceeded` keinen Ausloeser --
    // die Klausel liesse sich nur still fallenlassen.
    let (_, f) = c_von(
        "module t {
extern fn wacht() -> never effects { diverges } costs <= 0 ops;
divergent fn dienst() -> never effects { diverges }
{ forever d per_pass bounded 64 ops on_exceeded wacht effects { pure } { } } }",
    );
    assert!(
        f.iter().any(|s| s.contains("COMPILE-TIME claim")),
        "`forever` darf nicht still uebergangen werden: {f:?}"
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

    // **`at dma` wird abgelehnt, und der Grund ist der Pruefer selbst:** welche Barriere ein
    // `dma`-Zugriff braucht, ist eine Aussage ueber das Speichermodell, und M3 baut sie
    // ausdruecklich nicht. *Der Erzeuger darf nicht entscheiden, was der Pruefer offenlaesst.*
    let (_, f) = c_von(
        "module t { device Q(basis : u64) at dma { reg I : u16 @0x0 class rw } }",
    );
    assert!(
        f.iter().any(|s| s.contains("memory model")),
        "`at dma` darf nicht abgesenkt werden: {f:?}"
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

    // **3. `descendants of` ist ein BEFUND, kein Bauposten.** Die Domaene sagt nicht, an
    // welcher Kante sie laeuft -- und `chain(a, b) in` zeigt, dass die Grammatik es kann.
    let (_, f) = c_von(
        "module t { table T count 8 { slot { p : option index into T, k : option index into T, } }
impl fn f(t : ptr<normal, rw> T, s : index into T) effects { writes t.slots } costs <= 64 ops
{ traverse v over descendants of t.slots[s] by consuming touches writes t.slots { } } }",
    );
    assert!(
        f.iter().any(|s| s.contains("does not name the EDGE")),
        "die unbenannte Kante muss beim Namen stehen: {f:?}"
    );
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
    let h = gabbro_check::aufrufgraph::erhebe(&baum).huelle("f");
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
    let h = gabbro_check::aufrufgraph::erhebe(&baum).huelle("f");
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
