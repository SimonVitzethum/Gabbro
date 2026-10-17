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
             impl fn tor() effects {{ reads zaehler, writes zaehler }} costs <= 5 ops \
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

    // **And the trap sprang a second time, at `let … else`** (2026-09-03). `rufe_im_block`
    // walked bodies through `eigene_ausdruecke`, which answers `Vec::new()` for a `LetSonst`
    // and says why in its own comment: *"`let x = f() else …` carries its call in the source,
    // not in an `Expr`."* So this count entered the body and missed one of its arms -- and
    // the loss was SILENT, not small: no `V` line at all for the callee's `requires`.
    //
    // Measured over the corpus that day: **101 -> 107 obligation lines**, four of them at
    // `messung/fragmente/F01.gab`:426, where `revoke` calls `delete_leaf` this way. Two of
    // those four close `PFLICHTEN.txt` F1 rows `236` and `337`, and `337` is the one that file
    // calls *"the load-bearing statement of `revoke`"*.
    assert_eq!(
        v("module t { extern fn nimm(x : u32 in 0 .. 9) -> u32 or Fehler requires x < 9, x > 0 \
           effects { pure } costs <= 1 ops; \
           type Fehler = enum { Weg, }; \
           impl fn ruft(y : u32 in 0 .. 9) -> u32 or Fehler effects { pure } costs <= 8 ops \
           { let r = nimm(y) else (e) { return e; } return r; } }"),
        2,
        "ein Ruf in einem `let … else` ist derselbe Ruf -- und war bis 2026-09-03 unsichtbar"
    );

    // **The silent half of the same arm:** `let x = <place> else …` unpacks an atomic and
    // calls NOTHING («B14b»). `als_ruf()` answers `None` there, so this must stay at zero --
    // otherwise the fix above would have bought its lines by inventing a call.
    assert_eq!(
        v("module t { atomic g : u32 publishes nothing relaxed; \
           impl fn f() -> bool effects { reads g } costs <= 4 ops \
           { let x = g else (e) { return false; } return true; } }"),
        0,
        "ein ausgepackter Ort ruft nichts, also schuldet er am Rufort auch nichts"
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

/// **A device promise is not a foreign `ensures`, and until 2026-09-02 this channel said it
/// was.**
///
/// `reg … requires` and `transition … requires` carry `Material::Foreign` -- Gabbro never
/// sees the device -- and `verdict` dispatched on the material alone. The sentence a reader
/// got was therefore *"an `ensures` at a body Gabbro never sees"*, over a clause that is a
/// `requires` and has no body at all. **The Lean channel had carried its own
/// `device-promise` since it was built**, so one register was described two ways by two
/// tools, and only one of them was about the thing in front of it.
#[test]
fn a_device_promise_gets_its_own_reason_in_both_channels() {
    let q = "module t {
device Vtd(basis : u64) at mmio {
reg GCMD : u32 @0x18 class w fields { TE @31, }
reg GSTS : u32 @0x1c class r fields { RTPS @30, }
transition an { GCMD.TE: 0 -> 1 } requires GSTS.RTPS == 1 effects { writes GCMD }
}
}";
    // **TWO duties since 2026-09-04, and both are this device's.** The `requires` is the
    // GUARD and the `transset` is the MOVE; until that day only the guard reached the
    // register, so a `transition` without a `requires` reached it not at all. Both are
    // refused for the same named reason -- Gabbro never sees the device -- and the pair is
    // what makes the reason visible as a property of the CONSTRUCT and not of the clause.
    let (b, _a) = gabbro_syntax::lies("p6.gab", q);
    let isa = gabbro_check::refinement::theory(&b, "p6.gab");
    assert_eq!(p6_balance(&isa), (2, 0, 2), "two duties, both refused:\n{isa}");
    assert!(
        isa.contains("device-promise (2)"),
        "the Isabelle channel names the DEVICE, not a foreign body:\n{isa}"
    );
    assert!(
        !isa.contains("foreign-body"),
        "and it no longer says `ensures` about a `requires`:\n{isa}"
    );
    // **The two channels agree, and that is the point of the repair.**
    let lean = gabbro_check::lean::module(&b, "p6.gab");
    assert!(
        lean.contains("device-promise (2)"),
        "the Lean channel said this all along:\n{lean}"
    );
}

/// **The balance adds up, and it adds up over THE SAME register `gabbro pflichten` counts.**
///
/// *An output that forgets one kind looks complete* (`dokumente/SPRACHE.md`, the `lock` line that
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
    // **Since 2026-09-07 the goal is the ROUTINE's theorem**, and the `refines` is one clause
    // of its promise -- so the body and the post stand under the routine's name.
    assert!(t.contains("_body : List Stmt"), "the body stands as a datum:\n{t}");
    assert!(
        t.contains("_post (s s' : State) (r : Option Value) : Prop"),
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
    // **Since 2026-09-07 the shapes stand in ONE typing for the unit** (`shapeOf`), and
    // `wellFormed` is `WF shapeOf` -- one form, read from the declarations.
    assert!(
        t.contains(r#"| .slot "B" _ "belegt" => some .bool"#),
        "a `bool` field carries the truth shape:\n{t}"
    );
    // **and since 2026-09-08 a ranged integer field carries its RANGE** (`Shape.intIn`):
    // `Zahl = u32 in 0 .. 99` is not a number, it is a number in `0 .. 99`, and the
    // well-typed world says so -- a read comes with its bounds, a store owes them
    assert!(
        t.contains(r#"| .slot "B" _ "wert" => some (.intIn 0 99)"#),
        "and an integer field the number shape WITH its declared range:\n{t}"
    );
}

/// **A call is taken over the callee's CONTRACT, never over its body** (2026-09-07). Until
/// that day a body with a call carried no goal at all -- refused as `call-not-compositional`,
/// *"and that gate is not built"*. The gate is built: the caller's theorem carries
/// `Contract` and `Frame` of the callee as hypotheses, and the callee's `requires` is the
/// stuck-condition of the call.
#[test]
fn lean_ruf_wird_abgesagt_nicht_verschluckt() {
    let t = lean_modul(LEAN_MIT_RUF);
    let (_, goals, _) = p6_balance(&t);
    assert!(goals >= 1, "a body with a call carries a goal:\n{t}");
    assert!(
        !t.contains("call-not-compositional"),
        "and nothing is refused for being a call:\n{t}"
    );
    assert!(
        t.contains("Contract ρ "),
        "the callee's contract is a HYPOTHESIS of the caller's theorem:\n{t}"
    );
    assert!(
        t.contains("Frame ρ "),
        "and so is its frame:\n{t}"
    );
    // **The callee is named in the datum, never inlined.** An inlined body would make the
    // goal a statement about a program nobody wrote.
    assert!(
        t.contains("(.call \"") || t.contains("(.bindCall \"") || t.contains("(.retCall \""),
        "the call stands as a datum with the callee's name:\n{t}"
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
        bitund.contains("(.bin .band (.place \"B\" (.name \"p\") \"zahl\")"),
        "`&=` on an INTEGER field is the bit MASK:\n{bitund}"
    );
    assert!(
        !bitund.contains(".bin .and"),
        "and it is not taken as a truth value:\n{bitund}"
    );
    let jaund = lean_programm(&mit("&=", "ja"));
    assert!(
        jaund.contains("(.bin .and (.place \"B\" (.name \"p\") \"ja\")"),
        "and on a BOOL field the same token is the truth value:\n{jaund}"
    );
}

/// **The seven operators the model gained, and each one by NAME.**
///
/// A single probe over "some bit operation goes through" would pass with all seven mapped to
/// the same constructor -- and `a % b` written as `a / b` is a body that computes something
/// else while the balance line still adds up. *That is the class this whole file reads text
/// for.*
#[test]
fn lean_division_und_bits_werden_beim_namen_genannt() {
    let mit = |ausdruck: &str| {
        format!(
            "module t {{
const N : u32 = 8;
type Zahl = u32 in 0 .. 99;
table B count N {{ slot {{ zahl : Zahl, }} }}
impl fn f(p : index into B, a : Zahl, b : u32 in 1 .. 99)
    effects  {{ reads B.slots, writes B.slots }}
    costs    <= 16 ops
{{ B.slots[p].zahl = {ausdruck}; }}
}}
"
        )
    };
    for (ausdruck, konstruktor) in [
        ("a / b", ".bin .div"),
        ("a % b", ".bin .rem"),
        ("a & b", ".bin .band"),
        ("a | b", ".bin .bor"),
        ("a ^ b", ".bin .bxor"),
        ("a >> 1", ".bin .shr"),
    ] {
        let t = lean_programm(&mit(ausdruck));
        assert!(
            t.contains(konstruktor),
            "`{ausdruck}` becomes `{konstruktor}`:\n{t}"
        );
        assert!(
            !t.contains("REFUSED"),
            "and the body is carried, not refused:\n{t}"
        );
    }
    // `<<` on its own, because a shift LEFT out of `0 .. 99` is an `M104` overflow and the
    // unit would carry no register at all -- the bound is what makes the model's booking
    // true, so the probe has to respect it.
    let t = lean_programm(
        "module t {
const N : u32 = 8;
table B count N { slot { zahl : u32, } }
impl fn f(p : index into B, a : u32 in 0 .. 255)
    effects  { reads B.slots, writes B.slots }
    costs    <= 16 ops
{ B.slots[p].zahl = a << 4; }
}
",
    );
    assert!(t.contains(".bin .shl"), "`a << 4` becomes `.bin .shl`:\n{t}");
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
    // **The carrier is the RECORD'S name, not the parameter's** (2026-09-07) -- as a
    // table's is -- so that a callee's promise about `s.offen` reads at a caller's
    // `t.offen`, and `shapeOf` types the place by the declaration.
    assert!(
        t.contains(r#"(.assignField "Text" "offen""#),
        "the write goes to a FIELD, not to a slot:\n{t}"
    );
    // **The READ path is a separate arm and needs its own probe.** A mutation that turned a
    // record read into a slot at index zero slipped past a test that only ever wrote.
    assert!(
        t.contains(r#"(.fieldOf "Text" "offen")"#),
        "and so does the read:\n{t}"
    );
    assert!(
        !t.contains(r#"(.slot "s" 0"#) && !t.contains(r#"(.slot "Text" 0"#),
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
    // Since 2026-09-07 every call carries the callee's PRECONDITION as its last operand --
    // the stuck-condition of the call.
    assert!(
        t.contains(r#"(.bindCall "w" "frag" ["p"] [(.name "p")] "#),
        "`let w = frag(p);` binds the RESULT of a call:\n{t}"
    );
    assert!(
        t.contains(r#"(.retCall "frag" ["p"] [(.name "p")] "#),
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
/// 2026-08-28 (`dokumente/PRUEFER.md`). A loop WITHOUT one is still refused --
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
    // **A loop without an `invariant` is carried with the invariant `true`** (2026-09-07):
    // nothing is known after it but the shapes of the locals, and that is the sound reading
    // of a loop nobody wrote a statement for.
    let ohne = lean_programm(&mit(""));
    assert!(
        !ohne.contains("(loop)") && ohne.contains(r#"(.loop "leeren#1""#),
        "a loop with no `invariant` is a datum with the invariant `true`:\n{ohne}"
    );
    let t = lean_programm(&mit("\n        invariant h.slots[s].belegt"));
    assert!(
        t.contains(r#"(.loop "leeren#1""#),
        "one with an invariant becomes a datum, under an id of its own:\n{t}"
    );
    // The place is written under the TABLE's name -- `h` points at `B`, and a contract
    // about `B.slots[…]` has to be readable by every routine that names the table.
    assert!(
        t.contains(r#"(.place "B" (.name "s") "belegt")"#),
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

    // **And `ALL` is held against the ENUM, not against itself.** The old form of this test
    // asserted that what stands in `ALL` has a tag and a sentence -- true of a list that is
    // missing a variant, which is exactly what happened on 2026-09-08: `PassCounter` was
    // declared, tagged, refused by the emitter, and named by nothing, because it was not in
    // `ALL`. *A test over a register cannot take that register as its population.*
    //
    // Rust has no way to walk the variants of an enum, so the population comes from the
    // SOURCE -- the same move `wortschatz.rs` makes with `SPRACHE.md`.
    let quelle = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/src/lean.rs"))
        .expect("`src/lean.rs` stands beside this test");
    let rumpf = quelle
        .split_once("pub enum LeanReason {")
        .expect("the enum is declared")
        .1;
    let rumpf = rumpf.split_once("\n}").expect("and it ends").0;
    let varianten: Vec<&str> = rumpf
        .lines()
        .map(str::trim)
        .filter(|z| z.ends_with(','))
        .map(|z| z.trim_end_matches(','))
        .filter(|z| {
            let mut c = z.chars();
            c.next().is_some_and(|a| a.is_ascii_uppercase()) && c.all(|a| a.is_ascii_alphanumeric())
        })
        .collect();
    assert!(varianten.len() >= 40, "the enum was not read: {varianten:?}");
    let liste = quelle
        .split_once("pub const ALL: [LeanReason;")
        .expect("`ALL` stands there")
        .1;
    let liste = liste.split_once("];").expect("and it ends").0;
    for v in &varianten {
        assert!(
            liste.contains(&format!("LeanReason::{v},")),
            "`LeanReason::{v}` is declared and NOT in `ALL` -- it would be refused by the \
             emitter and named by no report; the balance line would count it among refusals \
             it cannot name"
        );
    }
    assert_eq!(
        varianten.len(),
        LeanReason::ALL.len(),
        "the enum has {} variants and `ALL` names {}",
        varianten.len(),
        LeanReason::ALL.len()
    );
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
    // **Since 2026-09-07 the loop without an `invariant` is a datum too** -- with the
    // invariant `true`. What is outside the fragment today: nothing in this probe.
    assert_eq!(bodies, 3, "the leaf, the CALLER and the loop are all data:\n{t}");
    assert_eq!(refused, 0, "nothing in this probe is outside the fragment:\n{t}");
    assert_eq!(places, 2, "the table declares two fields with a shape:\n{t}");
}

/// **A routine outside the fragment is REFUSED BY NAME, not dropped.** A body that vanished
/// from the export would leave a specification standing over a program that is not there.
#[test]
fn lean_programm_sagt_ab_statt_zu_verschlucken() {
    let t = lean_programm(PROG);
    // **Since 2026-09-07 the loop without a statement is carried with `true`**, so the
    // probe's negative example is gone; what this test still holds is the POSITIVE half.
    assert!(t.contains("def schleift_body"), "the loop is a datum:\n{t}");
    assert!(t.contains("def leeren_body"), "and so is the leaf:\n{t}");
    // **A call is a DATUM, never an inlining.** The callee is named and its parameters are
    // bound; what it does is looked up in an environment the reader's theorem quantifies
    // over. *An inlined body would make the goal a statement about a program nobody wrote.*
    assert!(
        t.contains(r#"(.call "leeren" ["p"] [(.name "p")] "#),
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
    // **Since 2026-09-07 `Held(L)` in a contract is `true`** -- the lock passes discharge
    // it (H005/H006/H012/H016), and a precondition this channel could not write would refuse
    // the whole callee. So nothing is dropped here any more, and the word stays out.
    let t = lean_programm(PROG);
    assert!(
        !t.contains("DROPPED from the precondition"),
        "a `Held(L)` costs no clause:\n{t}"
    );
    assert!(
        !t.contains("lock-witness"),
        "and is not reported as a gap:\n{t}"
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

// ===========================================================================================
// THE COLLECTING BUCKET -- what `call-not-compositional` really held (2026-08-28, `B1`)
//
// Seventeen refusals of the program channel stood under one word, and **not one of them was
// a call over a contract**: six generated operations, six constructors, four `transition`s,
// and one `return Some(i);` the model could carry all along. `dokumente/SPRACHE.md` measures
// it and decides the split; the probes below are what keeps the four apart.
//
// *A refusal filed under the wrong reason names a missing gate where a missing value form
// stands* -- the same lesson the `Carrier` / `FieldShape` split books in `lean.rs`.
// ===========================================================================================

/// A table with `ops`, a device with a `transition`, a record, and an option-valued return.
const LEAN_VIER_DINGE: &str = "module t {
const N : u32 = 8;
table V count N {
    slot { benutzt : bool, naechst : option index into V, }
    ops insert, remove;
    occupied benutzt;
}
type Paar = { a : u32, b : u32, };
device Dv(basis : u64) at mmio {
    reg ST : u32 @0x00 class rw fields { AN @0, }
    transition anschalten { ST.AN: 0 -> 1 } effects { writes ST }
}
impl fn nimm(v : ptr<normal, rw> V, i : index into V)
    requires !v.slots[i].benutzt
    effects  { writes v.slots }
    costs    <= 4 ops
{
    V::insert(v, i);
}
impl fn schalte(d : ptr<mmio, rw> Dv)
    effects { writes d.ST }
    costs   <= 4 ops
{
    anschalten(d);
}
impl fn paare(x : u32, y : u32) -> Paar
    effects { pure }
    costs   <= 4 ops
{
    return Paar(a: x, b: y);
}
impl fn griff() -> Dv
    effects { pure }
    costs   <= 4 ops
{
    let g : Dv = Dv(4096);
    return g;
}
impl fn hol(v : ptr<normal, rw> V, i : index into V) -> option index into V
    effects { reads v.slots }
    costs   <= 4 ops
{
    return Some(i);
}
}";

/// **Four things parse as a call, and only one of them is one.** Each stands under its own
/// name now, because each waits on something different: a schema, a piece of hardware, a
/// value form the model does not have.
#[test]
fn lean_ruf_sammeltopf_ist_aufgeteilt() {
    let t = lean_programm(LEAN_VIER_DINGE);
    // **Since 2026-09-07 a generated operation and a transition are CALLEES** -- their
    // premises are the stuck-condition, their frame the table or the device -- so only the
    // two constructed values are still refused, and each under its own name.
    for (routine, grund) in [
        ("paare", "constructed-value"),
        ("griff", "constructed-value"),
    ] {
        let z = t
            .lines()
            .find(|z| z.contains("REFUSED") && z.contains(routine))
            .unwrap_or_else(|| panic!("`{routine}` stands in the report:\n{t}"));
        assert!(
            z.contains(grund),
            "`{routine}` is refused as `{grund}` and not as a call:\n{z}"
        );
    }
    // **And the word `call-not-compositional` is spent on none of them.** It is reserved for
    // a call over a CONTRACT, and a bucket that also held hardware said the register was
    // waiting on a gate that would have taken nothing.
    assert!(
        !t.contains("(call-not-compositional)"),
        "not one of these four is a call over a contract:\n{t}"
    );
}

/// **`return Some(i);` is a VALUE, and the model has carried `.someOf` since its first day.**
///
/// The `let` and `return` arms sent every `ExprArt::Ruf` to `call_parts` before `expr_term`
/// could see it, so a body whose only sin was an option value was refused whole. *Measured
/// at `beispiele/27-freiliste.gab :: belegen`, which gains a body by this line alone.*
#[test]
fn lean_optionswert_ist_kein_ruf() {
    let t = lean_programm(LEAN_VIER_DINGE);
    assert!(
        t.contains("(.ret (some (.someOf (.name \"i\"))))"),
        "`return Some(i);` descends to `.someOf`, not to a call:\n{t}"
    );
    assert!(
        !t.lines().any(|z| z.contains("REFUSED") && z.contains("hol")),
        "and the routine that writes it carries a body:\n{t}"
    );
}

/// **The SAME rule stands at two arms, and only one of them had a probe** (2026-08-30).
///
/// The full mutation run over the merged state -- the first one that exercised these rules
/// rather than only counting their anchors -- let the option-value mutation of the `Let` arm
/// SURVIVE. The reason is exact: the probe above reads `return Some(i);`, which is the
/// `Return` arm, while the mutation damages the `Let` arm. *Two arms, one rule, one probe --
/// and a rule that can fall at one arm while every test stays green.* The mutation carries
/// its name in `dokumente/PRUEFER.md`, where the German side of this run is booked.
#[test]
fn lean_optionswert_im_let_ist_kein_ruf() {
    let t = lean_programm(
        "module t {
const N : u32 = 8;
table V count N {
    slot { benutzt : bool, naechst : option index into V, }
    occupied benutzt;
}
impl fn merke(v : ptr<normal, rw> V, i : index into V)
    effects  { writes v.slots }
    costs    <= 8 ops
{
    let n = Some(i);
    v.slots[i].naechst = n;
}
}",
    );
    assert!(
        t.contains("(.bindName \"n\" (.someOf (.name \"i\")))"),
        "`let n = Some(i);` binds a VALUE, it does not call `Some`:\n{t}"
    );
    let (_, bodies, refused, _) = lean_programm_kopf(&t);
    assert_eq!(bodies, 1, "the routine carries a body:\n{t}");
    assert_eq!(refused, 0, "and nothing is refused:\n{t}");
}

/// **The obligation channel keeps its own refusal, and it is the honest one.**
///
/// A call over a contract is still not carried there -- `allow_calls` is `false` in `judge`
/// on purpose, because a goal under an unconstrained environment states something no proof
/// closes. *The split changes what the word MEANS, not what the gate does.*
#[test]
fn lean_vertragstor_bleibt_zu() {
    let t = lean_modul(
        "module t {
const N : u32 = 8;
type Zahl = u32 in 0 .. 99;
table B count N { slot { belegt : bool, wert : Zahl, } }
impl fn setz(p : index into B, w : Zahl)
    effects { writes B.slots }
    costs   <= 4 ops
{
    B.slots[p].wert = w;
}
impl fn ruf(p : index into B, w : Zahl)
    ensures  B.slots[p].wert == w
    effects  { writes B.slots }
    costs    <= 9 ops
{
    setz(p, w);
}
}",
    );
    // **The gate is built** (2026-09-07): the caller's theorem carries the callee's
    // contract, and the register counts the postcondition as a goal.
    let (_, goals, _) = p6_balance(&t);
    assert!(goals >= 1, "a call at a DECLARED routine goes through the gate:\n{t}");
    assert!(
        t.contains(r#"Contract ρ "setz" setz_requires setz_post"#),
        "over the callee's CONTRACT, never its body:\n{t}"
    );
    assert!(
        !t.contains("call-not-compositional"),
        "and nothing is refused for being a call:\n{t}"
    );
}

// ===========================================================================================
// A SUSPENSION IS NOT AN EXIT (2026-08-28, `B2`)
//
// `breaking I { … }` stood in one arm with `leave` and `next` under the sentence *"a
// non-local exit out of a named loop"*. It is neither non-local nor an exit: what it changes
// is which DUTY holds inside the block, not which statements run. **All four obligations
// behind `non-local-exit` were `breaking`** -- `dokumente/PRUEFER.md` measures
// it, and the four go through Lean since the split.
// ===========================================================================================

const LEAN_AUSSETZUNG: &str = "module t {
const N : u32 = 8;
table B count N {
    slot { a : option index into B, b : option index into B, }
    invariant paarig cost O(n) runs offline :
        forall s in slots of Self : (Self.slots[s].a == None) == (Self.slots[s].b == None);
}
impl fn setze(p : index into B, x : index into B)
    ensures   B.slots[p].a == Some(x)
    maintains paarig
    effects   { writes B.slots }
    costs     <= 8 ops
{
    breaking paarig {
        B.slots[p].a = Some(x);
        B.slots[p].b = Some(x);
    }
}
}";

/// **The suspension travels into the datum, and its NAME with it.**
///
/// The name is the load-bearing half: this reading is sound exactly as far as the channel
/// cannot state a table invariant, and a record that inlined the body would have erased
/// where the suspension lay.
#[test]
fn lean_aussetzung_traegt_ihren_namen() {
    let t = lean_programm(LEAN_AUSSETZUNG);
    assert!(
        t.contains("(.breaking [\"paarig\"] ["),
        "`breaking paarig` descends to `.breaking`, with the name kept:\n{t}"
    );
    assert!(
        !t.contains("non-local-exit"),
        "and it is not filed as an exit -- it is neither non-local nor one:\n{t}"
    );
    let (_, bodies, refused, _) = lean_programm_kopf(&t);
    assert_eq!(bodies, 1, "the routine carries a body:\n{t}");
    assert_eq!(refused, 0, "and nothing is refused:\n{t}");
}

/// **The obligation channel writes the GOAL, and the `maintains` duty stays beside it.**
///
/// That is what makes the reading sound rather than convenient: the `ensures` becomes a
/// theorem, the table invariant is refused by name, and the two never merge.
#[test]
fn lean_aussetzung_gibt_ein_ziel_und_behaelt_die_invariante() {
    let t = lean_modul(LEAN_AUSSETZUNG);
    assert!(
        t.contains("_meets : ") && t.contains("_meets_statement"),
        "the `ensures` over a suspended block becomes a goal:\n{t}"
    );
    // **Since 2026-09-07 the `maintains` duty is CARRIED too** -- the invariant is a bounded
    // quantifier over the declared `count`, it stands in the routine's precondition and in
    // its promise, and the suspension inside changes nothing about the two ends.
    assert!(
        !t.contains("table-invariant"),
        "and the `maintains` duty is carried, not refused:\n{t}"
    );
    assert!(
        t.contains("_inv_paarig : Expr"),
        "the invariant stands as an expression under the routine's name:\n{t}"
    );
}

/// **A `leave` of the innermost loop is CARRIED** (2026-09-07): `Stmt.leave`, `Outcome.left`
/// -- the pass ends, the invariant has to hold, and `iterate` stops. What is still refused
/// under `non-local-exit` is a mark that names an OUTER loop: it would have to travel
/// through a `.loop` step that does not run the body.
#[test]
fn lean_echter_ausgang_bleibt_abgesagt() {
    let mit = |innen: &str| {
        format!(
            "module t {{
const N : u32 = 8;
table B count N {{ slot {{ aktiv : bool, fertig : bool, }} }}
extern fn watchdog() -> never effects {{ diverges }} costs <= 1 ops;
assume tick \"Der Zeitgeber tickt.\" falsifier sonde_tick;
impl fn dienst(b : ptr<normal, rw> B, i : index into B)
    ensures !b.slots[i].aktiv
    effects {{ diverges, writes b.slots, reads b.slots }}
{{
    forever runde
        per_pass bounded 64 ops
        on_exceeded watchdog
        effects  {{ writes b.slots, reads b.slots }}
        progress tick
        invariant !b.slots[i].aktiv
    {{
        b.slots[i].aktiv = false;
        {innen}
    }}
}}
}}"
        )
    };
    let t = lean_programm(&mit("if b.slots[i].fertig { leave runde; }"));
    assert!(
        t.contains(".leave"),
        "a `leave` of the innermost loop is a datum:\n{t}"
    );
    assert!(
        !t.contains("non-local-exit"),
        "and is not refused:\n{t}"
    );
    let aussen = lean_programm(&mit(
        "forever innen per_pass bounded 8 ops on_exceeded watchdog effects { reads b.slots } progress tick { if b.slots[i].fertig { leave runde; } }",
    ));
    let z = aussen
        .lines()
        .find(|z| z.contains("REFUSED") && z.contains("dienst"))
        .unwrap_or_else(|| panic!("the routine stands in the report:\n{aussen}"));
    assert!(
        z.contains("non-local-exit"),
        "a `leave` aimed at an OUTER loop is refused by name:\n{z}"
    );
}

// ===========================================================================================
// `result` IS A NAME (2026-08-28, `B3` / «B6»)
//
// `result` stood in `primary` and in eight corpus sites; what was missing was never the
// spelling but the BINDING -- a postcondition is evaluated over a `State`, and a result is
// not part of one. The goal binds it, and no arm of the model changed for it: `finalValue`
// has carried it since day one (`dokumente/PRUEFER.md`).
// ===========================================================================================

const LEAN_ERGEBNIS: &str = "module t {
type Klein = u32 in 0 .. 100;
format Kopf { eintritt : u64, laenge : u32, }
impl fn lies(k : ptr<normal, r> Kopf) -> u64
    ensures  result == k.eintritt
    effects  { reads k }
    costs    <= 8 ops
{
    return k.eintritt;
}
}";

/// **The export datum carries an `ensures result`, stated over entry, exit and
/// result (lane 141, F4 of lane 126).**
///
/// Until lane 141 this was the other half of the split of 2026-08-30: a promise
/// the datum declined to repeat -- sayable, deliberately unsaid. The reference
/// program showed the price: anyone reading only the program view saw a
/// contract-free program. The datum now states the clause the way the duty
/// channel does, with `result` bound and `old` beside it; what stays refused
/// is named under its own clause, never silently.
#[test]
fn lean_export_sagt_die_zusage_unter_dem_klauselnamen_ab() {
    let t = lean_programm(LEAN_ERGEBNIS);
    assert!(
        t.contains("def lies_post (s s' : State) (r : Option Value) : Prop"),
        "the promise is stated over entry, exit and result:\n{t}"
    );
    assert!(
        t.contains("\"result\"") && t.contains(".bin .eq"),
        "and it carries result == slot:\n{t}"
    );
    assert!(
        !t.contains("result-in-ensures"),
        "and nothing drops under the clause name any more:\n{t}"
    );
    assert!(
        !t.contains("result-in-body"),
        "and not the body case -- this body never writes `result`:\n{t}"
    );
}

/// **The goal over an `ensures result` demands three things, and the middle one is the point.**
///
/// A body that runs off the end has no result -- `finalValue` is `none` there -- so a goal
/// without that conjunct would prove the promise of a routine that never makes one. *The
/// form is strictly stronger than the two-part one, which is the direction a goal may move.*
#[test]
fn lean_ergebnis_verlangt_dass_ein_wert_entstand() {
    let t = lean_modul(LEAN_ERGEBNIS);
    assert!(
        t.contains("theorem lies_meets"),
        "an `ensures result` becomes a goal:\n{t}"
    );
    // **The promise takes the result as `r`, and a clause that names it demands one.** The
    // goal hands `finalValue` in; the clause says `∃ v, r = some v`.
    assert!(
        t.contains("lies_post s s' (finalValue (exec ρ lies_body s))"),
        "the goal hands the body's result to the promise:\n{t}"
    );
    assert!(
        t.contains("∃ v, r = some v ∧"),
        "and the clause demands that the body PRODUCED a value:\n{t}"
    );
    assert!(
        t.contains("bindLocal s.local' \"result\" v"),
        "`result` is bound as a name, exactly as a parameter is read:\n{t}"
    );
    assert!(
        !t.contains("result-in-ensures"),
        "and it is not refused any more:\n{t}"
    );
}

/// **`result` stays refused inside a BODY**, where it names nothing.
///
/// The flag goes up after `block_term` has run and before the conclusion is translated, so
/// the two cannot be confused -- that ordering is the guarantee, not a comment.
///
/// **This probe carried its name and not its object until 2026-08-30**: it read a program
/// whose body never wrote `result` at all, so the rule it is named after could be deleted
/// while it stayed green. The body-side `result` mutation SURVIVED the first full mutation
/// run over the merged state, and that is what it survived on. *A probe named after a rule
/// it does not touch reads as coverage* -- the same class as the `bank` stride assertion of
/// 2026-08-28, which stood over the whole output rather than over one block.
///
/// The first half below is the one that was missing; the second is the original, kept
/// because it does say something -- a postcondition that never names `result` may not
/// silently acquire the stronger goal shape.
#[test]
fn lean_ergebnis_bleibt_im_rumpf_abgesagt() {
    // A body that names `result` where it names nothing is refused by name, and no goal
    // comes out of it.
    //
    // **The site moved on 2026-09-05 and the case did not.** Here stood `let x = result;`,
    // and since the word is a word only inside a contract that line binds an ordinary local
    // now -- `M119` catches it three passes earlier, at the checker, which is where an
    // undeclared name belongs. What is left of the case is the place where `result` is still
    // the CONTRACT word and still names nothing: a **loop invariant**, which is a promise
    // inside a body, with no return value in scope. *The refusal was right about the word
    // and wrong about only the address.*
    let im_rumpf = lean_modul(
        "module t {
type Kopf = { eintritt : u64, };
impl fn lies(k : ptr<normal, r> Kopf) -> u64
    ensures  result == k.eintritt
    effects  { reads k }
    costs    <= 8 ops
{
    retry warten until k->eintritt == 1
        bounded 4 ops
        on_exceeded zeitablauf
        effects { reads k }
        invariant result == 0
    { }
    return k.eintritt;
}
}",
    );
    assert!(
        im_rumpf.contains("result-in-body"),
        "`result` inside a body is refused by name:\n{im_rumpf}"
    );
    // **And by the name of its OWN case.** Until 2026-08-30 this refusal was booked as
    // `result-in-ensures` with the sentence *"one gate away, not far"* -- both true of the
    // other case and neither true of this one. A reader looked for a missing gate and found a
    // program error wearing its label.
    assert!(
        !im_rumpf.contains("result-in-ensures"),
        "and not under the name of the clause case:\n{im_rumpf}"
    );
    assert!(
        im_rumpf.contains("a program error, not a gap"),
        "the sentence says which of the two it is:\n{im_rumpf}"
    );
    assert!(
        !im_rumpf.contains("theorem lies_meets"),
        "and no goal is written over it:\n{im_rumpf}"
    );
    // *Two refusals, not one, since the site moved into a loop: the loop's own invariant is
    // the second, refused for the same reason -- the routine's body has no datum. The half
    // this probe is about is `refused` and not `goals` -- nothing is proved over either.*
    assert!(
        im_rumpf.contains("goals 0  refused 2"),
        "the balance line says the same thing:\n{im_rumpf}"
    );

    // A postcondition without `result` keeps the two-part goal -- the shape may not change
    // for bodies that never mention it.
    let t = lean_modul(
        "module t {
const N : u32 = 8;
type Zahl = u32 in 0 .. 99;
table B count N { slot { belegt : bool, wert : Zahl, } }
impl fn setz(p : index into B, w : Zahl)
    ensures  B.slots[p].wert == w
    effects  { writes B.slots }
    costs    <= 4 ops
{
    B.slots[p].wert = w;
}
}",
    );
    assert!(
        t.contains("theorem setz_meets"),
        "the plain postcondition still becomes a goal:\n{t}"
    );
    assert!(
        !t.contains("∃ v, r = some v"),
        "and its promise does not demand a value nobody promised:\n{t}"
    );
}

/// **«B14» -- an `option index into T` at a parameter, a `let` and a return.**
///
/// The entry said `option` stands only in `slottype`. It stands in `typeexpr`, the checker
/// takes all three positions, and the body channel carries every one of the bodies.
#[test]
fn lean_option_steht_auch_ausserhalb_des_slottyps() {
    let t = lean_programm(
        "module t {
const N : u32 = 8;
table B count N { slot { elter : option index into B, } }
impl fn setze(b : ptr<normal, rw> B, i : index into B, p : option index into B)
    effects { writes b.slots }
    costs   <= 4 ops
{
    b.slots[i].elter = p;
}
impl fn lies(b : ptr<normal, rw> B, i : index into B) -> option index into B
    effects { reads b.slots }
    costs   <= 4 ops
{
    let e : option index into B = b.slots[i].elter;
    return e;
}
}",
    );
    let (_, bodies, refused, _) = lean_programm_kopf(&t);
    assert_eq!(bodies, 2, "both bodies are carried:\n{t}");
    assert_eq!(refused, 0, "and neither is refused:\n{t}");
}

// ===========================================================================================
// A LOCAL IS NOT A GLOBAL, ON THE WRITE SIDE TOO (2026-08-28, `B5`)
//
// `place_term` has always distinguished a local from a world name when READING one. The
// assignment arm did not: every suffix-less target became `.assignGlobal`. **That is not a
// refusal but a wrong program** -- the datum bound the local, stored into a world place
// nothing declares, and read the local back.
//
// Measured at `messung/abi-proben/zaehlwerk.gab :: hole_stand`, whose datum said the routine
// always returns zero while it returns the slot's value. The export is what a hand-written
// Lean specification is held against, so a person could have proved a true theorem about a
// program nobody wrote.
// ===========================================================================================

const LEAN_LOKALE: &str = "module t {
const N : u32 = 8;
static G : u32 = 0;
table B count N { slot { belegt : bool, wert : u32, } }
impl fn zwei(b : ptr<normal, r> B, i : index into B) -> u32
    effects { reads b.slots }
    costs   <= 8 ops
{
    let mut n : u32 in 0 .. 4 = 0;
    if b.slots[i].belegt {
        n = 2;
    }
    return n;
}
impl fn setz_global(w : u32)
    effects { writes G }
    costs   <= 4 ops
{
    G = w;
}
}";

/// **A write to a `let mut` rebinds the NAME; it does not store into the world.**
#[test]
fn lean_lokale_zuweisung_bindet_neu() {
    let t = lean_programm(LEAN_LOKALE);
    assert!(
        t.contains("(.bindName \"n\" (.lit (.int 2)))"),
        "`n = 2;` at a local rebinds it:\n{t}"
    );
    assert!(
        !t.contains("(.assignGlobal \"n\""),
        "and it never becomes a store to a world place nothing declares:\n{t}"
    );
    // **The other direction, and it is what keeps this from being a blanket rule**: a real
    // `static` still goes to the world. Without this half the fix would have moved every
    // global write into the local environment, which is the same fault mirrored.
    assert!(
        t.contains("(.assignGlobal \"G\""),
        "a `static` is still a world place:\n{t}"
    );
}

/// **`+=` at a local is an addition, and the model is safe where a shape would be guessed.**
///
/// The ambiguity the compound arm refuses lives in `&=`/`|=` -- conjunction on a truth value,
/// a bit mask on an integer. `+=` has no second reading, and `binop .add` is `none` on
/// anything but two integers, so a body that added to a non-number gets STUCK.
#[test]
fn lean_lokales_plusgleich_ist_eine_addition() {
    let t = lean_programm(
        "module t {
const N : u32 = 8;
table B count N { slot { aktiv : bool, } }
impl fn zaehle(b : ptr<normal, r> B) -> u32
    effects { reads b.slots }
    costs   <= 64 ops
{
    let mut n : u32 in 0 .. N = 0;
    traverse i over slots of b by unvisited
        touches reads b.slots
        invariant n <= N
    {
        if b.slots[i].aktiv { n += 1; }
    }
    return n;
}
}",
    );
    assert!(
        t.contains("(.bindName \"n\" (.bin .add (.name \"n\") (.lit (.int 1))))"),
        "`n += 1;` at a local is `n = n + 1` over the local:\n{t}"
    );
    let (_, bodies, refused, _) = lean_programm_kopf(&t);
    assert_eq!(bodies, 1, "and the counting loop carries a body:\n{t}");
    assert_eq!(refused, 0, "with nothing refused:\n{t}");
}

// -- A ghost bound by `let` ------------------------------------------------------------
