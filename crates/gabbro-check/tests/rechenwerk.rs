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

/// The lines of one emitted function body, from its opening line to the closing brace at
/// column zero. **A probe that reads the whole product reads the writer as well** -- and a
/// generator satisfies a claim over its own entire output without ever emitting the block in
/// question (W16, 2026-08-28).
fn bloeck<'a>(c: &'a str, kopf: &str) -> String {
    let von = c.find(kopf).unwrap_or_else(|| panic!("kein Rumpf `{kopf}` im Erzeugnis:\n{c}"));
    let rest = &c[von..];
    let bis = rest.find("\n}").map(|i| i + 2).unwrap_or(rest.len());
    rest[..bis].to_string()
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

/// The body of one C function, brace-matched -- **assertions belong to a BLOCK**.
///
/// A `contains` over the whole emission passes as soon as ANY line satisfies it, and the
/// prototype line alone already carries the name. That shape hid a producer fault on
/// 2026-08-28 (class `W16`), so the probe below reads one body at a time.
fn c_rumpf(c: &str, signatur: &str) -> String {
    let auf = c
        .find(&format!("{signatur} {{"))
        .unwrap_or_else(|| panic!("`{signatur}` steht nicht im Erzeugnis:\n{c}"));
    let rest = &c[auf..];
    let start = rest.find('{').expect("brace");
    let mut tiefe = 0usize;
    for (i, z) in rest[start..].char_indices() {
        match z {
            '{' => tiefe += 1,
            '}' => {
                tiefe -= 1;
                if tiefe == 0 {
                    return rest[start..start + i + 1].to_string();
                }
            }
            _ => {}
        }
    }
    panic!("`{signatur}` bleibt offen:\n{c}");
}

// -- `let … else` over a place -----------------------------------------------------------

/// **The source of a `let … else` must not decide whether M1 can see the type** (2026-08-30).
///
/// «B14b» (2026-08-17) let the statement unpack a `place` as well as a call. The type
/// binding stayed behind: the call half asked the callee's signature, the place half wrote
/// `Typ::Unbekannt` and gave up, though the type stood in the register declaration the whole
/// time.
///
/// **Both functions below carry the same body**, one line apart in what they read from.
/// Measured on the unchanged checker: 3 expressions and 0 untyped with the call alone, 5
/// expressions and **1 untyped** once the place twin joins -- and that one untyped name is
/// what silences `M104` over any arithmetic that follows it.
///
/// *The probe reads M1's own instrument.* The pass counts every expression it fails to type,
/// so an uncovered name shows up as a number and as nothing else -- no refusal ever names it,
/// which is exactly how the gap survived thirteen days.
#[test]
fn ein_let_else_ueber_einem_place_bindet_den_erklaerten_typ() {
    let quelle = "
module probe::letsonst {

reason Geraetelug { ZuTief = 1 \"zu tief\" exhaustive }

device Tiefengeraet(basis : u64) at mmio {
    reg TIEFE : u32 @0x08 class r requires TIEFE <= 8 else Geraetelug::ZuTief
}

extern fn hol_tiefe() -> u32 or Geraetelug effects { pure } costs <= 1 ops;

impl fn via_ruf() -> u32 or Geraetelug effects { pure } costs <= 8 ops {
    let t = hol_tiefe() else (e) { return Geraetelug::ZuTief; }
    return t;
}

impl fn via_ort(d : ptr<mmio, r> Tiefengeraet) -> u32 or Geraetelug
    effects { reads d } costs <= 8 ops
{
    let t = d.TIEFE else (e) { return Geraetelug::ZuTief; }
    return t;
}

}
";
    let mut absagen = gabbro_syntax::Absagen::neu("probe.gab");
    let bericht = gabbro_check::pruefe(&baum(quelle), &mut absagen);

    assert_eq!(absagen.fehler_zahl(), 0, "{}", absagen.zeige(quelle));
    assert_eq!(
        bericht.m1.unbekannt, 0,
        "beide Quellen tragen einen erklaerten Typ; ungetypt bleibt keiner"
    );
}

/// **The domain bound of `mappings of` is `node length ^ levels` -- pinned by the TEXT.**
///
/// `saetze.rs::kosten.domaenenschranke` said the gap out loud, and it was true until here:
///
/// > *"No probe and no mutation measures the bound against the domain. `K003` has 2 probes,
/// > but they measure that a MISSING bound is refused -- not that a PRESENT one is right.
/// > That is the difference the 2 048/512^4 error lived in."*
///
/// **The error this closes is measured, not imagined.** Until 2026-08-20 `umgebung.rs`
/// computed `levels x node length` -- 2 048 where the leaf set holds 512^4 = 68 719 476 736.
/// Seven orders of magnitude, carried for three days, and found because the EMITTER walked
/// into it. *No test fell. No mutation bit.*
///
/// The probe moves ONE dial at a time and reads the number out of the `K001` message per
/// site, never out of a tally:
///
/// ```text
///   levels 1..4 at node length 2   ->   4    8    16   32       (2 x l^e:  2  4   8  16)
///                                       and NOT 4 8 12 16       (2 x e*l:  2  4   6   8)
///   levels 4 at node length 512    ->   137 438 953 472         (= 2 x 512^4 -- F09)
///   body 0 / 2 / 4 ops at l=8, e=2 ->   --   128  256           (the body is a FACTOR)
/// ```
///
/// **`e = 3, l = 2` is the smallest place where the two readings part** -- 16 against 12. A
/// probe that only sampled `e = 1`, or only `e = l`, would have stayed green through all
/// three days. *That is why the exponent is walked and not sampled.*
///
/// See `dokumente/PRUEFER.md` for the whole chain, and for why `F09` keeps its
/// wrong promise on purpose.
#[test]
fn die_schranke_von_mappings_of_ist_knotenlaenge_hoch_ebenen() {
    // One `walk`, one `traverse`, three dials: levels, node length, body cost.
    fn quelle(ebenen: u32, laenge: u32, rumpfzweige: u32) -> String {
        let mut rumpf = String::new();
        for i in 0..rumpfzweige {
            rumpf.push_str(&format!(
                "        if a.level == {i} {{\n            return true;\n        }}\n"
            ));
        }
        format!(
            "module p {{
const EBENEN   : u32 = {ebenen};
const EINTRAEGE: u32 = {laenge};
format Pte @version 1 endian little {{
    unten : u64 @[11:0] reserved,
    roh : u64 embeds [51:12] scale 4096,
    oben  : u64 @[63:52] reserved,
}}
device T(basis : u64) at normal {{
    reg EINTRAG : u64 @0x0 class rw fields {{ P @0, PS @7, NX @63, }}
}}
walk W levels EBENEN {{
    node : [Pte; EINTRAEGE],
    down : roh when EINTRAG.PS == 0,
    leaf : EINTRAG.PS == 1,
}}
impl fn f(w : ptr<normal, r> W) -> bool
    effects {{ reads w }}
    costs   <= 1 ops
{{
    traverse a over mappings of w by unvisited
        touches reads w
    {{
{rumpf}    }}
    return false;
}}
}}
"
        )
    }

    // The number `K001` PRINTS at this site -- the text, not a tally.
    fn gedruckte_kosten(q: &str) -> Option<i128> {
        let (b, mut a) = gabbro_syntax::lies("p.gab", q);
        let _ = gabbro_check::pruefe(&b, &mut a);
        let k = a.absagen.iter().find(|x| x.code == "K001")?;
        // `f promises <= 1 ops, the body costs N`
        let n = k.text.rsplit_once("the body costs ")?.1.trim().to_string();
        Some(n.parse().unwrap_or_else(|e| panic!("{n:?}: {e} -- in {:?}", k.text)))
    }

    let mut gesehen = Vec::new();
    for ebenen in 1..=4u32 {
        for laenge in [2u32, 8, 512] {
            let erwartet = 2 * (laenge as i128).pow(ebenen);
            let gemessen = gedruckte_kosten(&quelle(ebenen, laenge, 1))
                .unwrap_or_else(|| panic!("no K001 at levels {ebenen}, node {laenge}"));
            assert_eq!(
                gemessen, erwartet,
                "levels {ebenen}, node {laenge}: the bound is `l^e`, not `e*l` -- the old \
                 reading would have printed {}",
                2 * (ebenen as i128) * (laenge as i128)
            );
            gesehen.push(gemessen);
        }
    }

    // **`F09` in one line** -- the value the whole question turned on.
    assert!(
        gesehen.contains(&137_438_953_472),
        "levels 4 x node 512 must be 2 x 512^4, seen: {gesehen:?}"
    );

    // **The body is a FACTOR, not a summand.** Two arms cost twice as much, and an empty
    // body costs nothing -- then `K001` does not fall at all, because 0 <= 1.
    assert_eq!(gedruckte_kosten(&quelle(2, 8, 1)), Some(128), "2 ops x 8^2");
    assert_eq!(gedruckte_kosten(&quelle(2, 8, 2)), Some(256), "4 ops x 8^2");
    assert_eq!(gedruckte_kosten(&quelle(2, 8, 0)), None, "0 ops x 8^2 = 0, and 0 <= 1");
}

/// **An overflowing bound promises NOTHING -- and that is the one direction that counts.**
///
/// `K001` is an UPPER bound: an over-count is coarse, a wrapped under-count is a lie. Both
/// multiplications on the way refuse instead of wrapping -- `checked_pow` in `umgebung.rs`
/// for `l^e`, `checked_mul` in `kosten.rs::mal` for `body x bound`. This probe reads that at
/// the boundary: `512^14 = 2^126` still fits, and `2 x 2^126 = 2^127` no longer fits `i128`.
#[test]
fn eine_ueberlaufende_domaenenschranke_verspricht_nichts() {
    let quelle = |ebenen: u32| {
        format!(
            "module p {{
const EBENEN   : u32 = {ebenen};
const EINTRAEGE: u32 = 512;
format Pte @version 1 endian little {{
    unten : u64 @[11:0] reserved,
    roh : u64 embeds [51:12] scale 4096,
    oben  : u64 @[63:52] reserved,
}}
device T(basis : u64) at normal {{
    reg EINTRAG : u64 @0x0 class rw fields {{ P @0, PS @7, NX @63, }}
}}
walk W levels EBENEN {{
    node : [Pte; EINTRAEGE],
    down : roh when EINTRAG.PS == 0,
    leaf : EINTRAG.PS == 1,
}}
impl fn f(w : ptr<normal, r> W) -> bool
    effects {{ reads w }}
    costs   <= 1 ops
{{
    traverse a over mappings of w by unvisited
        touches reads w
    {{
        if a.level == 0 {{
            return true;
        }}
    }}
    return false;
}}
}}
"
        )
    };
    let codes = |q: &str| -> Vec<&'static str> {
        let (b, mut a) = gabbro_syntax::lies("p.gab", q);
        let _ = gabbro_check::pruefe(&b, &mut a);
        a.absagen.iter().map(|x| x.code).collect()
    };

    let k14 = codes(&quelle(14));
    assert!(k14.contains(&"K003"), "levels 14 must say `K003`, fallen: {k14:?}");
    assert!(!k14.contains(&"K001"), "an overflowing computation is no promise: {k14:?}");
}

/// **A `walk` is a TYPE because it was declared, not because its leaf count fits.**
///
/// Found on 2026-08-31 in the `W24` run-up to `K001`: the name resolver asked
/// `walkschranken` -- the COST map -- whether a `walk` type exists. Three ordinary
/// declarations have no entry there:
///
/// ```text
///   walk W levels 0   { node : [Pte; 512], … }     0^… -- guarded away
///   walk W levels 4   { node : [Pte; 0],   … }     same guard
///   walk W levels 15  { node : [Pte; 512], … }     512^15 = 2^135, past `u128`
/// ```
///
/// All three answered **`N040`: `W` names no type** at a declaration standing three lines
/// above, and then sent the reader after *"is the table missing its `count`?"* -- a table
/// that does not exist in the file. **Two of the three are ordinary typos**, not corners.
///
/// *Two questions, one map* (`W7`), and the wrong answer named the wrong thing (`W16`). The
/// name lives in `walknamen`, the number in `walkschranken`, and this probe reads the two
/// apart: **no `N040` at any of the three, and `K003` at all three** -- the bound really is
/// missing, and that is what the refusal should say.
#[test]
fn ein_walk_ohne_brauchbare_blattzahl_bleibt_ein_typ() {
    fn quelle(ebenen: &str, laenge: &str) -> String {
        format!(
            "module p {{
format Pte @version 1 endian little {{
    unten : u64 @[11:0] reserved,
    roh : u64 embeds [51:12] scale 4096,
    oben  : u64 @[63:52] reserved,
}}
device T(basis : u64) at normal {{
    reg EINTRAG : u64 @0x0 class rw fields {{ P @0, PS @7, NX @63, }}
}}
walk W levels {ebenen} {{
    node : [Pte; {laenge}],
    down : roh when EINTRAG.PS == 0,
    leaf : EINTRAG.PS == 1,
}}
impl fn f(w : ptr<normal, r> W) -> bool
    effects {{ reads w }}
    costs   <= 1 ops
{{
    traverse a over mappings of w by unvisited
        touches reads w
    {{
        if a.level == 0 {{
            return true;
        }}
    }}
    return false;
}}
}}
"
        )
    }
    let urteil = |q: &str| -> (Vec<&'static str>, String) {
        let (b, mut a) = gabbro_syntax::lies("p.gab", q);
        let _ = gabbro_check::pruefe(&b, &mut a);
        let codes = a.absagen.iter().map(|x| x.code).collect();
        let texte = a.absagen.iter().map(|x| x.text.clone()).collect::<Vec<_>>().join(" | ");
        (codes, texte)
    };

    for (was, ebenen, laenge) in [
        ("levels 0", "0", "512"),
        ("node length 0", "4", "0"),
        ("512^15 past u128", "15", "512"),
    ] {
        let (codes, texte) = urteil(&quelle(ebenen, laenge));
        assert!(
            !codes.contains(&"N040"),
            "{was}: the `walk` is DECLARED, so its name is a type -- got {codes:?} ({texte})"
        );
        assert!(
            codes.contains(&"K003"),
            "{was}: the bound really is missing, and `K003` is the refusal for that -- \
             got {codes:?} ({texte})"
        );
        // **The text must name the declaration it wants.** Until 2026-08-31 it asked after a
        // table's `count` for every domain, including this one.
        assert!(
            texte.contains("`walk` from `levels`"),
            "{was}: the refusal has to name the `walk` declaration, not a table -- {texte}"
        );
    }

    // And the ordinary case is untouched: a bound that exists is still a bound.
    let (codes, _) = urteil(&quelle("4", "512"));
    assert!(codes.contains(&"K001"), "levels 4 x node 512 still computes: {codes:?}");
    assert!(!codes.contains(&"K003"), "a bound that exists is not a missing one: {codes:?}");
}

/// **The four domain bounds nobody had ever measured -- `count`, `queue`, `elems of`,
/// `index into T`.**
///
/// On 2026-08-31 lane P measured the fifth (`mappings of`) and deliberately left the state of
/// `saetze.rs::kosten.domaenenschranke` at `CONJECTURED`, with the reason written out:
///
/// > *"For `count`, `queue`, `elems of` and `index into T` the statement is still untested in
/// > exactly the way it was: `K003` has 2 probes, and they measure that a MISSING bound is
/// > refused -- not that a PRESENT one is right. That is the difference the 2 048/512^4 error
/// > lived in."*
///
/// **The difference matters because the historic error was a PRESENT bound, not a missing
/// one.** `mappings of` handed out `levels x node length` = 2 048 where the leaf set holds
/// `512^4` = 68 719 476 736 -- seven orders of magnitude, three days, no falling test. A
/// probe that only checks "no declaration -> `K003`" is green through all of that.
///
/// So this probe turns the dial that IS the declaration and reads the number out of the
/// `K001` text per site, never out of a tally:
///
/// ```text
///   table T count n        slots of w              n in {3, 7, 13}   ->  2 x n
///   type S = [u32; n]      elems of s.worte        n in {2, 9, 31}   ->  2 x n
///   type Q = [u32; n]      queue q by consuming    n in {3, 5, 16}   ->  2 x n
///   table T count n        descendants of g        n in {4, 6, 11}   ->  2 x n
///                          with g : index into T
/// ```
///
/// **2 x n since 2026-09-13 (lane 139, F1)** -- every arm below stores through an index,
/// and the store counts its target index. (The `queue` arm always cost 2 per pass; the
/// other three moved from 1.)
///
/// **The four are FOUR read paths and not one**, and that is why each gets its own dial:
/// `slots of` resolves through `Typ::Tabelle`, `index into T` through the name prefix of
/// `tabellenname`, `queue` through `arraylaenge_im_verbund`, and `elems of` returns before
/// the table branch is ever reached. *A single probe over one of them says nothing about the
/// other three -- which is exactly the state this replaces.*
///
/// Each path carries its own mutation in `mutiere-pruefer.py`
/// (`count-schranke-um-eins-daneben`, `elems-schranke-um-eins-daneben`,
/// `queue-schranke-um-eins-daneben`, `index-into-tabelle-verloren`), and each is an
/// off-by-one rather than a removal: **a bound that is GONE is already refused by `K003`, a
/// bound that is WRONG is the gap.**
#[test]
fn die_vier_uebrigen_domaenenschranken_kommen_aus_ihrer_deklaration() {
    // The number `K001` PRINTS at this site -- the text, not a tally.
    fn gedruckt(q: &str) -> Option<i128> {
        let (b, mut a) = gabbro_syntax::lies("p.gab", q);
        let _ = gabbro_check::pruefe(&b, &mut a);
        let k = a.absagen.iter().find(|x| x.code == "K001")?;
        let n = k.text.rsplit_once("the body costs ")?.1.trim().to_string();
        Some(n.parse().unwrap_or_else(|e| panic!("{n:?}: {e} -- in {:?}", k.text)))
    }

    // 1. `slots of` -- the bound is the `count` of the table.
    for n in [3i128, 7, 13] {
        let q = format!(
            "module p {{
const N : u32 = {n};
table T count N {{
    slot {{
        a : bool,
    }}
}}
impl fn f(w : ptr<normal, rw> T)
    effects {{ writes w.slots }}
    costs   <= 1 ops
{{
    traverse i over slots of w by unvisited
        touches writes w.slots
    {{
        w.slots[i].a = false;
    }}
}}
}}
"
        );
        assert_eq!(
            gedruckt(&q),
            Some(2 * n),
            "`slots of` at `count {n}`: the bound is the table's `count`, 2 ops per pass \
             since lane 139 (the store counts its target index)"
        );
    }

    // 2. `elems of` -- the bound is the length in the FIELD TYPE, and the table branch is
    // never reached. Found 2026-08-19 building «H2.1»: `tabellenname` looks for a table and
    // `s.worte` is a field, so the bound fell out silently.
    for n in [2i128, 9, 31] {
        let q = format!(
            "module p {{
type S = {{ worte : [u32; {n}], }};
impl fn f(s : ptr<normal, rw> S)
    effects {{ writes s }}
    costs   <= 1 ops
{{
    traverse i over elems of s.worte by unvisited
        touches writes s
    {{
        s.worte[i] = 0;
    }}
}}
}}
"
        );
        assert_eq!(
            gedruckt(&q),
            Some(2 * n),
            "`elems of` at `[u32; {n}]`: the bound is the array length, 2 ops per pass \
             since lane 139 (the store counts its target index)"
        );
    }

    // 3. `queue` -- the bound is the length of the record's SINGLE field array. Two arrays
    // and it is not decidable, so the pass says `K003` instead of guessing; that half has a
    // probe already. This half measures that the one it does read is the right one.
    for n in [3i128, 5, 16] {
        let q = format!(
            "module p {{
type Q = {{ buf : [u32; {n}], kopf : u32, }};
impl fn f(q : ptr<normal, rw> Q)
    effects {{ writes q, consumes q }}
    costs   <= 1 ops
{{
    traverse c over queue q by consuming
        touches consumes q
    {{
        q.kopf = c;
    }}
}}
}}
"
        );
        assert_eq!(
            gedruckt(&q),
            Some(2 * n),
            "`queue` at `[u32; {n}]`: the bound is the single field array, 2 ops per pass"
        );
    }

    // 4. `index into T` -- the bound comes from the table the TYPE NAME points at, not from
    // the place. Found 2026-08-17 building `ancestors of`: no example had ever triggered the
    // site, because the corpus carries `descendants of` only inside predicates, where no cost
    // pass runs. *A bound never triggered is not covered, it is unbreakable.*
    for n in [4i128, 6, 11] {
        let q = format!(
            "module p {{
const N : u32 = {n};
table T count N {{
    slot {{
        a      : bool,
        eltern : option index into T,
        kind   : option index into T,
        gesch  : option index into T,
    }}
    tree {{
        parent  eltern,
        child   kind,
        sibling gesch,
    }}
}}
impl fn f(w : ptr<normal, rw> T, g : index into T)
    effects {{ writes w.slots }}
    costs   <= 1 ops
{{
    traverse v over descendants of g by unvisited
        touches writes w.slots
    {{
        w.slots[v].a = false;
    }}
}}
}}
"
        );
        assert_eq!(
            gedruckt(&q),
            Some(2 * n),
            "`descendants of g` with `g : index into T` at `count {n}`: the bound is the \
             table named by the TYPE (2 ops per pass since lane 139)"
        );
    }

    // **And what this does NOT say.** It measures that the pass READS the declared number,
    // not that the number IS the cardinality of the domain. For `slots of` and `elems of`
    // the two coincide by construction. For `queue` and `descendants of` the declared number
    // is an UPPER bound and coarse on purpose: a queue holds at most its array, a descendant
    // chain visits at most every slot once. *Coarse upwards is a cost promise that holds;
    // the 2 048 was coarse DOWNWARDS, and that is the direction that lies.*
}

/// **`D014`-`D016`: the chain names its edge AT THE WALK, and nobody read it.**
///
/// `dokumente/PRUEFER.md`, 2026-08-31: five falsifications of the edge in
/// `beispiele/55-kindkette.gab`, in `ensures`, in an `invariant` and in the body of a `spec
/// fn` -- **0 errors and 0 `C001` every time**, while `tree { child gibtsnicht }` at the very
/// same table falls at `D006`.
///
/// The test has **three halves**, and the third is the one that makes a rule honest:
///
/// 1. one poison probe per class,
/// 2. **the counter-direction** -- what was green stays green, and that expressly includes
///    the two falsifications this rule does NOT catch (the exchanged pair and
///    `chain(parent, parent)`): both are well-formed chains, and refusing them would need a
///    statement about what was meant,
/// 3. **all four positions** -- `ensures`, `requires`, `invariant`, `traverse`. The rule does
///    not hang on the one clause that `M109` reads.
///
/// The tail of the test held the S2 gap open -- *what happens when the place is no table at
/// all* -- and since `D018` (2026-08-31) it holds the DIVISION instead: the place rule
/// speaks, the three edge rules stay silent.
#[test]
fn die_kettenkante_wird_gegen_ihre_tabelle_gehalten() {
    const TABELLE: &str = "table N count 4 { slot { w : u32, } }
table T count 8 {
    tree { parent elter, child kind, sibling gesch }
    slot {
        belegt  : bool,
        elter   : option index into T,
        kind    : option index into T,
        gesch   : option index into T,
        fremd   : option index into N,
        blank   : index into T,
    } }";

    fn absagen(quelle: &str) -> Vec<String> {
        let (baum, mut a) = gabbro_syntax::lies("p.gab", quelle);
        gabbro_check::pruefe(&baum, &mut a);
        a.absagen.iter().map(|x| x.code.to_string()).collect()
    }
    fn mit_ensures(kette: &str) -> String {
        format!(
            "module t {{ {TABELLE}
impl fn f(t : ptr<normal, rw> T, p : index into T)
    ensures forall x in {kette} in t.slots[p] : t.slots[x].belegt
    effects {{ reads t.slots, writes t.slots }} costs <= 4 ops {{ }} }}"
        )
    }

    // 1 -- one probe per class.
    for (kette, code) in [
        ("chain(gibtsnicht, auchnicht)", "D014"),
        ("chain(belegt, belegt)", "D015"),
        ("chain(blank, blank)", "D015"),
        ("chain(fremd, fremd)", "D016"),
    ] {
        let g = absagen(&mit_ensures(kette));
        assert!(
            g.iter().any(|c| c == code),
            "{kette} muss an {code} fallen, gefallen ist: {g:?}"
        );
    }

    // 2 -- the counter-direction. **A refusal without a clean control is half a measurement.**
    for kette in [
        "chain(kind, gesch)",  // the declared chain
        "chain(gesch, kind)",  // exchanged -- structurally still a chain
        "chain(elter, elter)", // the ancestor chain
        "chain(kind, kind)",   // the leftmost spine of the tree
    ] {
        let g = absagen(&mit_ensures(kette));
        assert!(
            !g.iter().any(|c| c.starts_with("D01")),
            "{kette} ist wohlgeformt und darf nicht fallen: {g:?}"
        );
    }

    // 3 -- all four positions. `M109` reads only `ensures`; this rule reads all of them.
    let stellungen = [
        (
            "requires",
            format!(
                "module t {{ {TABELLE}
impl fn f(t : ptr<normal, rw> T, p : index into T)
    requires forall x in chain(gibtsnicht, auchnicht) in t.slots[p] : t.slots[x].belegt
    effects {{ reads t.slots }} costs <= 4 ops {{ }} }}"
            ),
        ),
        (
            "invariant",
            format!(
                "module t {{ table N count 4 {{ slot {{ w : u32, }} }}
table T count 8 {{
    tree {{ parent elter, child kind, sibling gesch }}
    slot {{ belegt : bool, elter : option index into T,
            kind : option index into T, gesch : option index into T, }}
    invariant i cost O(n) runs offline :
        forall s in slots of Self :
            forall x in chain(gibtsnicht, auchnicht) in Self.slots[s] :
                Self.slots[x].belegt;
}} }}"
            ),
        ),
        (
            "spec fn",
            format!(
                "module t {{ {TABELLE}
spec fn f(t : ptr<normal, r> T, p : index into T) -> bool
    effects {{ pure }}
    = forall x in chain(gibtsnicht, auchnicht) in t.slots[p] : t.slots[x].belegt; }}"
            ),
        ),
        (
            "traverse",
            format!(
                "module t {{ {TABELLE}
impl fn f(t : ptr<normal, rw> T, p : index into T)
    effects {{ reads t.slots, writes t.slots }} costs <= 64 ops
{{ traverse x over chain(gibtsnicht, auchnicht) in t.slots[p] by unvisited
       touches reads t.slots, writes t.slots {{ t.slots[x].belegt = true; }} }} }}"
            ),
        ),
    ];
    for (stellung, quelle) in stellungen {
        let g = absagen(&quelle);
        assert!(
            g.iter().any(|c| c == "D014"),
            "in `{stellung}` muss D014 fallen, gefallen ist: {g:?}"
        );
    }

    // And the carrier that is NOT a table. **Until 2026-08-31 this was held here as an open
    // gap -- the S2 cell of `dokumente/PRUEFER.md` -- and `D018` closed it the same
    // day.** The division of labour is the point of the assertion: the three CHAIN rules
    // stay silent, because without a table there is no slot to hold the two field names
    // against; the refusal comes from the rule about the PLACE, and it names the place.
    let g = absagen(
        "module t { type R = { a : [u32; 4], k : u32, };
impl fn f(r : ptr<normal, rw> R)
    ensures forall x in chain(gibtsnicht, auchnicht) in r : r.k == 0
    effects { reads r, writes r } costs <= 4 ops { } }",
    );
    assert!(
        g.iter().any(|c| c == "D018"),
        "ueber einem Verbund faellt die Regel ueber den ORT: {g:?}"
    );
    assert!(
        !g.iter().any(|c| c == "D014" || c == "D015" || c == "D016"),
        "und die drei Kantenregeln schweigen, denn es gibt keinen Slot: {g:?}"
    );
}

/// **`D017`/`D018`: the PLACE of a quantifier domain -- its name and its kind.**
///
/// `dokumente/PRUEFER.md`, 2026-08-31. The corpus carries 72 quantifier sites;
/// **19 stand in an `ensures` and 53 do not.** Each of the 53 was falsified ONE BY ONE
/// against the unchanged checker -- the base name replaced by `zzznix`, the file's own base
/// load subtracted -- and **51 stayed silent**; the two that spoke said `D012`, about a
/// premise at a call and not about the name. Thirty-eight TYPE falsifications across five
/// positions got zero.
///
/// The test has the same three halves as the chain-edge test above, and the third is again
/// the one that makes the rule honest:
///
/// 1. one probe per class, in every position the rule claims,
/// 2. **the counter-direction** -- each domain over the carrier it actually wants, and the
///    two positions where `D017` deliberately says nothing (`ensures`, where `M109` reads
///    every name of the clause, and a `traverse`, where a `let` binding would be refused by
///    a pass that carries no block scope),
/// 3. **what resolves must not fall** -- a parameter, a bare table name, `Self` at a table
///    and at a `walk`, and a variable an enclosing quantifier just bound.
#[test]
fn der_ort_einer_domaene_wird_gehalten() {
    fn absagen(quelle: &str) -> Vec<String> {
        let (baum, mut a) = gabbro_syntax::lies("p.gab", quelle);
        gabbro_check::pruefe(&baum, &mut a);
        a.absagen.iter().map(|x| x.code.to_string()).collect()
    }
    // A table, a record, an array field, a `format` and a `walk` -- one of each, so that
    // every domain has both a right carrier and a wrong one in the same unit.
    const WELT: &str = "const N : u32 = 8;
table T count N {
    tree { parent elter, child kind, sibling gesch }
    slot { belegt : bool,
           elter : option index into T,
           kind  : option index into T,
           gesch : option index into T, } }
type R = { plaetze : [u32; 8], kopf : u32, };
format Wort endian little {
    gueltig : bool @0,
    schreib : bool @1,
    frei    : u64 @[11:2] reserved,
    rahmen  : u64 embeds [51:12] scale 4096,
    hoch    : u64 @[63:52] reserved, }
walk Baum levels 2 {
    node : [Wort; 512],
    down : rahmen when it.gueltig && !it.schreib,
    leaf : it.gueltig && it.schreib, }";

    fn mit(klausel: &str) -> String {
        format!(
            "module t {{ {WELT}
impl fn f(t : ptr<normal, rw> T, r : ptr<normal, rw> R, w : ptr<normal, rw> Baum,
          p : index into T, z : u32)
    {klausel}
    effects {{ reads t.slots, writes t.slots }}
    costs   <= 4 ops {{ }} }}"
        )
    }

    // 1a -- `D017`, in every position the rule claims. 41 of the 53 corpus sites are a
    // `table` invariant, 7 a `requires`, 5 the body of a `spec fn`, 4 a `walk` invariant.
    let stellungen = [
        (
            "requires",
            mit("requires forall s in slots of zzznix : t.slots[p].belegt"),
        ),
        (
            "table invariant",
            format!(
                "module t {{ table T count 8 {{ slot {{ belegt : bool, }}
    invariant i cost O(n) runs offline :
        forall s in slots of zzznix : Self.slots[0].belegt; }} }}"
            ),
        ),
        (
            "walk invariant",
            format!(
                "module t {{ {WELT}
walk Zweiter levels 1 {{
    node : [Wort; 512],
    down : rahmen when it.gueltig,
    leaf : it.schreib,
    invariant i cost O(n) runs offline :
        forall m in mappings of zzznix : m.gueltig; }} }}"
            ),
        ),
        (
            "spec fn",
            format!(
                "module t {{ {WELT}
spec fn g(t : ptr<normal, r> T) -> bool
    effects {{ pure }}
    = forall s in slots of zzznix : t.slots[s].belegt; }}"
            ),
        ),
    ];
    for (stellung, quelle) in &stellungen {
        let g = absagen(quelle);
        assert!(
            g.iter().any(|c| c == "D017"),
            "in `{stellung}` muss D017 fallen, gefallen ist: {g:?}"
        );
    }

    // 1b -- `D018`, one falsification per domain. The name resolves every time; only the
    // KIND is wrong, and until 2026-08-31 not one of these fell.
    for (was, klausel) in [
        ("slots of ueber einem Verbund", "requires forall s in slots of r : r.kopf == 0"),
        ("slots of ueber einem Skalar", "requires forall s in slots of z : z == 0"),
        ("queue ueber einer Tabelle", "requires forall i in queue t : t.slots[p].belegt"),
        ("queue ueber einem Skalar", "requires forall i in queue z : z == 0"),
        ("elems of ueber einer Tabelle", "requires forall i in elems of t : t.slots[p].belegt"),
        ("elems of ueber einem Skalarfeld", "requires forall i in elems of r.kopf : r.kopf == 0"),
        ("mappings of ueber einer Tabelle", "requires !exists m in mappings of t : m.gueltig"),
        ("descendants of ueber einem Verbund", "requires !exists x in descendants of r : r.kopf == 0"),
        ("ancestors of ueber einem Verbund", "requires forall x in ancestors of r : r.kopf == 0"),
        ("chain in ueber einem Verbund", "requires forall x in chain(kind, gesch) in r : r.kopf == 0"),
    ] {
        let g = absagen(&mit(klausel));
        assert!(
            g.iter().any(|c| c == "D018"),
            "{was} muss an D018 fallen, gefallen ist: {g:?}"
        );
    }

    // 2 -- the counter-direction. **A refusal without a clean control is half a measurement.**
    // Each domain over the carrier it actually wants, plus the two shapes the corpus writes
    // that no type alone can settle: a BARE declaration name and `<x>.slots[i]`.
    for klausel in [
        "requires forall s in slots of t : t.slots[s].belegt",
        "requires forall s in slots of T : t.slots[p].belegt",
        "requires forall j in queue r : r.plaetze[j] == 0",
        "requires forall j in elems of r.plaetze : r.plaetze[j] == 0",
        "requires !exists m in mappings of w : m.gueltig",
        "requires !exists x in descendants of t.slots[p] : t.slots[x].belegt",
        "requires forall x in ancestors of t.slots[p] : t.slots[x].belegt",
        "requires forall x in chain(kind, gesch) in t.slots[p] : t.slots[x].belegt",
        "requires forall x in ancestors of p : t.slots[x].belegt",
        "requires forall f in fields of Wort : t.slots[p].belegt",
        "requires forall th in threads : t.slots[p].belegt",
    ] {
        let g = absagen(&mit(klausel));
        assert!(
            !g.iter().any(|c| c == "D017" || c == "D018"),
            "`{klausel}` ist wohlgeformt und darf nicht fallen: {g:?}"
        );
    }

    // 3 -- `Self` is the CARRIER question and belongs to `M120`; a bound variable is
    // declared by the quantifier above it. **26 of the 53 corpus places are `Self`** --
    // without these two lines the rule would have refused them all.
    for quelle in [
        format!(
            "module t {{ table T count 8 {{ slot {{ belegt : bool, }}
    invariant i cost O(n) runs offline :
        forall s in slots of Self : Self.slots[s].belegt; }} }}"
        ),
        format!(
            "module t {{ {WELT}
walk Zweiter levels 1 {{
    node : [Wort; 512],
    down : rahmen when it.gueltig,
    leaf : it.schreib,
    invariant i cost O(n) runs offline :
        forall m in mappings of Self : m.gueltig; }} }}"
        ),
    ] {
        let g = absagen(&quelle);
        assert!(
            !g.iter().any(|c| c == "D017" || c == "D018"),
            "`Self` ist der Traeger und darf nicht fallen: {g:?}"
        );
    }

    // 4 -- the two positions `D017` deliberately leaves alone, and both are measured.
    //
    // In an `ensures` `M109` resolves EVERY name of the clause, so a second refusal would
    // be a second refusal for one fault; at a `traverse` a domain may run over a `let`
    // binding, and this pass carries no block scope.
    let e = absagen(&mit("ensures forall s in slots of zzznix : t.slots[p].belegt"));
    assert!(
        e.iter().any(|c| c == "M109") && !e.iter().any(|c| c == "D017"),
        "in `ensures` spricht `M109` und `D017` schweigt: {e:?}"
    );
    let d = absagen(
        "module t { table T count 8 { slot { belegt : bool, } }
impl fn f(t : ptr<normal, rw> T)
    effects { reads t.slots, writes t.slots } costs <= 64 ops
{ let q = t; traverse i over slots of q by unvisited
      touches reads t.slots, writes t.slots { t.slots[i].belegt = true; } } }",
    );
    assert!(
        !d.iter().any(|c| c == "D017"),
        "an einem `traverse` darf eine lokale Bindung nicht als unbekannt gelten: {d:?}"
    );

    // 5 -- **`None` means stay silent.** A place whose type the checker cannot resolve is
    // not a place of the wrong kind, and a refusal about the checker's own ignorance is the
    // false alarm this bench spent a whole build undoing.
    let u = absagen(
        "module t { extern fn fremd() -> u32 effects { pure } costs <= 1 ops;
table T count 8 { slot { belegt : bool, } }
impl fn f(t : ptr<normal, rw> T, x : fnptr())
    requires forall s in slots of x : t.slots[0].belegt
    effects { reads t.slots, writes t.slots } costs <= 4 ops { } }",
    );
    assert!(
        !u.iter().any(|c| c == "D018"),
        "ueber einem Ort, dessen Typ nicht aufloest, schweigt `D018`: {u:?}"
    );
}

/// **The two binders a `let` does not write down -- the traversal variable and a `match`
/// arm.**
///
/// `domaene.rs::aus_block` got its block scope on 2026-08-31, and it carried `let`,
/// `let ... else`, `await load` and `exchange`. Two statements that DECLARE a name were not
/// among them, and both produce the same false refusal: a domain deeper inside names
/// something the enclosing line just introduced, and `D017` says it *"is not declared
/// here"*.
///
/// Measured against the unchanged checker, one program per gap:
///
/// ```text
/// error: [D017] g3.gab:24:50: `a` in an `invariant` is not declared here
/// error: [D017] g2.gab:28:54: `k` in an `invariant` is not declared here
/// ```
///
/// The control in the same run is the whole argument: **the same `invariant` moved up to
/// the line that binds the name gives `0 errors`.** The traversal variable was pushed
/// around the loop's OWN invariant and popped again before the body was walked; the arm
/// binder was never pushed at all.
///
/// ## Half two, and it is the one that kills the too-wide version
///
/// A rule that simply stopped refusing here would pass half one exactly like this one. So
/// every gap has its mirror: **the same name one statement LATER**, where nothing binds it
/// any more, still has to fall -- and the binder of one `match` arm must not reach the
/// other. *A scope that never ends is not a scope.*
#[test]
fn die_laufvariable_und_der_matchbinder_gelten_im_rumpf() {
    fn absagen(quelle: &str) -> Vec<String> {
        let (baum, mut a) = gabbro_syntax::lies("p.gab", quelle);
        gabbro_check::pruefe(&baum, &mut a);
        a.absagen.iter().map(|x| x.code.to_string()).collect()
    }
    const WELT: &str = "const N : u32 = 8;
table T count N {
    tree { parent elter, child kind, sibling gesch }
    slot { wert  : u32,
           elter : option index into T,
           kind  : option index into T,
           gesch : option index into T, } }
tagged type Fund = { Nichts, Knoten(index into T) };";

    fn mit(rumpf: &str) -> String {
        format!(
            "module t {{ {WELT}
impl fn f(x : Fund, g : index into T) -> u32
    effects {{ reads T.slots }}
{{ {rumpf} return 0; }} }}"
        )
    }

    // 1 -- the traversal variable holds in the BODY, not only in its own `invariant`.
    let a = absagen(&mit(
        "traverse a of g over ancestors of g by unvisited decreases a
             touches reads T.slots
         {
             traverse b of g over ancestors of g by unvisited decreases b
                 touches reads T.slots
                 invariant forall k in descendants of a : T.slots[k].wert == 0
             { }
         }",
    ));
    assert!(
        !a.iter().any(|c| c == "D017"),
        "`a` ist von der umschliessenden Traversierung gebunden: {a:?}"
    );

    // 2 -- the binder of a `match` arm holds in that arm.
    let b = absagen(&mit(
        "match x {
             Nichts => { }
             Knoten(k) => {
                 traverse a of g over ancestors of g by unvisited decreases a
                     touches reads T.slots
                     invariant forall z in descendants of k : T.slots[z].wert == 0
                 { }
             }
         }",
    ));
    assert!(
        !b.iter().any(|c| c == "D017"),
        "`k` ist vom Zweig `Knoten(k)` gebunden: {b:?}"
    );

    // 3 -- **the scope ENDS.** Without these three the rule could bind every name forever
    // and both halves above would still be green.
    for (was, rumpf) in [
        (
            "nach der Traversierung",
            "traverse a of g over ancestors of g by unvisited decreases a
                 touches reads T.slots
             { }
             traverse b of g over ancestors of g by unvisited decreases b
                 touches reads T.slots
                 invariant forall k in descendants of a : T.slots[k].wert == 0
             { }",
        ),
        (
            "nach dem `match`",
            "match x { Nichts => { } Knoten(k) => { } }
             traverse a of g over ancestors of g by unvisited decreases a
                 touches reads T.slots
                 invariant forall z in descendants of k : T.slots[z].wert == 0
             { }",
        ),
        (
            "im anderen Zweig",
            "match x {
                 Knoten(k) => { }
                 Nichts => {
                     traverse a of g over ancestors of g by unvisited decreases a
                         touches reads T.slots
                         invariant forall z in descendants of k : T.slots[z].wert == 0
                     { }
                 }
             }",
        ),
    ] {
        let g = absagen(&mit(rumpf));
        assert!(
            g.iter().any(|c| c == "D017"),
            "{was} bindet den Namen nicht mehr -- `D017` muss fallen: {g:?}"
        );
    }

    // 4 -- and the loop does not bind its own domain: the place of `traverse i over
    // slots of i` is read in the OUTER scope, where `i` stands nowhere.
    let d = absagen(
        "module t { table T count 8 { slot { wert : u32, } }
impl fn f(t : ptr<normal, r> T) -> u32
    effects { reads t.slots }
{ traverse i over slots of t by unvisited touches reads t.slots
      { traverse j over slots of t by unvisited touches reads t.slots
            invariant forall k in slots of i : t.slots[k].wert == 0 { } }
  return 0; } }",
    );
    assert!(
        !d.iter().any(|c| c == "D017"),
        "auch hier ist `i` gebunden -- `D018` mag schweigen, `D017` darf nicht sprechen: {d:?}"
    );
}

/// **`D019`: the FIELD names in the suffix of a domain's place.**
///
/// The third question at the same place -- `D017` reads its base name, `D018` its kind,
/// `D019` the field names of its suffix. `dokumente/PRUEFER.md` §7 carried the
/// cell as unchecked with a reason read off the source; the measurement of 2026-08-31
/// (`messung/proben/probe-elems-feldname.gab`) found it too kind to the checker:
///
/// ```text
/// …: 8 items, 0 errors, 0 hints
/// ```
///
/// `elems of r.gibtsnichtfeld` in `ensures`, in `requires` and in the body of a `spec fn`
/// -- **not one of them**, and `ensures` among them, so `M109` did not read it either. The
/// control in the same run: the same place with a falsified BASE name does fall, at
/// `M109`. *The base is read and the field is not.*
#[test]
fn der_feldname_am_ort_einer_domaene() {
    fn absagen(quelle: &str) -> Vec<String> {
        let (baum, mut a) = gabbro_syntax::lies("p.gab", quelle);
        gabbro_check::pruefe(&baum, &mut a);
        a.absagen.iter().map(|x| x.code.to_string()).collect()
    }
    fn mit(klausel: &str) -> String {
        format!(
            "module t {{
const NRING : u32 = 32;
type RingNr = u32 in 0 ..< 32;
const LEER : RingNr = 0;
type Ring = {{ plaetze : [RingNr; NRING], }};
impl fn f(r : ptr<normal, rw> Ring)
    {klausel}
    effects {{ reads r, writes r }}
    costs   <= 4 ops
{{ }} }}"
        )
    }

    // 1 -- every position, and `ensures` among them: the rule speaks where `M109` does
    // not, and `M109` does not read a field name anywhere.
    for klausel in [
        "ensures forall j in elems of r.gibtsnichtfeld : r.plaetze[j] != LEER",
        "requires forall j in elems of r.gibtsnichtfeld : r.plaetze[j] != LEER",
    ] {
        let a = absagen(&mit(klausel));
        assert!(
            a.iter().any(|c| c == "D019"),
            "`{klausel}` quantifiziert ueber ein Feld, das nirgends steht: {a:?}"
        );
    }

    // 2 -- the counter-direction: the same place with the field it actually has.
    for klausel in [
        "ensures forall j in elems of r.plaetze : r.plaetze[j] != LEER",
        "requires forall j in elems of r.plaetze : r.plaetze[j] != LEER",
    ] {
        let g = absagen(&mit(klausel));
        assert!(
            !g.iter().any(|c| c == "D019"),
            "`{klausel}` nennt ein Feld, das es gibt, und darf nicht fallen: {g:?}"
        );
    }

    // 3 -- **silence where the prefix is not known, and that is the whole discipline.** At
    // a `traverse` over a `let` binding the base does not resolve in this pass, so nothing
    // is claimed about the field either. *The missing block scope -- the reason `D017` has
    // to skip a `traverse` at all -- cannot produce a false refusal here.*
    let ueber_ein_let = absagen(
        "module t {
const NRING : u32 = 32;
type RingNr = u32 in 0 ..< 32;
type Ring = { plaetze : [RingNr; NRING], };
impl fn f(r : ptr<normal, rw> Ring)
    effects { reads r } costs <= 64 ops
{ let q = r; traverse j over elems of q.plaetze by unvisited
      touches reads r { } } }",
    );
    assert!(
        !ueber_ein_let.iter().any(|c| c == "D019"),
        "ueber einem Traeger, den dieser Pass nicht aufloest, wird nichts behauptet: \
         {ueber_ein_let:?}"
    );

    // 4 -- and the OTHER answer `Feldurteil` carries: a carrier that has no fields at all.
    // A number is not a record with the wrong names -- the refusal has to say which.
    let ohne_felder = absagen(
        "module t {
static mut k : u32 = 0;
impl fn f() -> bool
    requires forall j in elems of k.plaetze : j != 0
    effects { reads k } costs <= 4 ops { return true; } }",
    );
    assert!(
        ohne_felder.iter().any(|c| c == "D019"),
        "ein Feldzugriff auf eine Zahl faellt ebenfalls, mit dem anderen Satz: \
         {ohne_felder:?}"
    );
}

/// **`D020`: the FIELD names of a bound MAPPING.**
///
/// The fourth question at a quantifier and the first about the VARIABLE. `D017`/`D018`/`D019`
/// all stop at the PLACE, and `ortsfelder_pruefen` says why in its own second line: *"a
/// quantifier variable carries no type in this pass"*. **For `mappings of` it does** -- the
/// type stands in the `walk` declaration, and `mappings of` is the one domain that binds a
/// record rather than an index (`SPRACHE.md` §6).
///
/// Measured 2026-09-01 against the unchanged checker: `forall m in mappings of Self :
/// !m.gibtsnicht` gave `3 items, 0 errors, 0 hints`. The control in the same run -- the same
/// line with a falsified BASE name -- fell at `D017`.
///
/// The two counter-probes below are the reason the rule is not tidiness: an ENTRY field
/// travels with a grafted subtree, and `va` does not, because it is synthesised from the
/// position. `dokumente/PLAN-HARDWARE.md` §5 Layer 2 turns on that split.
#[test]
fn der_feldname_einer_gebundenen_abbildung() {
    fn absagen(quelle: &str) -> Vec<String> {
        let (baum, mut a) = gabbro_syntax::lies("p.gab", quelle);
        gabbro_check::pruefe(&baum, &mut a);
        a.absagen.iter().map(|x| x.code.to_string()).collect()
    }
    fn mit(pred: &str) -> String {
        format!(
            "module t {{
format Pte endian little {{
    praesent   : bool @0,
    schreibbar : bool @1,
    frei       : u64 @[11:2] reserved,
    rahmen     : u64 embeds [51:12] scale 4096,
    hoch       : u64 @[62:52] reserved,
    nx         : bool @63,
}}
walk Tabelle levels 4 {{
    node : [Pte; 512],
    down : rahmen when it.praesent,
    leaf : !it.praesent,
    invariant i cost O(n) runs online : {pred};
}} }}"
        )
    }

    // 1 -- the poison: a name that is neither an entry field nor a position field.
    let erfunden = absagen(&mit("forall m in mappings of Self : !m.gibtsnicht"));
    assert!(
        erfunden.iter().any(|c| c == "D020"),
        "an invented field on a bound mapping has to fall: {erfunden:?}"
    );

    // 2 -- counter-probe: fields of the node `format`. They travel with the entry.
    let eintragsbits = absagen(&mit(
        "forall m in mappings of Self : !(m.schreibbar && !m.nx)",
    ));
    assert!(
        !eintragsbits.iter().any(|c| c == "D020"),
        "the node format's own fields carry: {eintragsbits:?}"
    );

    // 3 -- counter-probe: `va` stands in NO `format` and is carried by the domain
    // (`SPRACHE.md`:930, "including virtual address and level"). It is the field that makes
    // an invariant path-DEPENDENT, and refusing it would refuse the sharper half.
    let stellung = absagen(&mit(
        "forall m in mappings of Self : m.va < 0xFFFF_8000_0000_0000 || !m.praesent",
    ));
    assert!(
        !stellung.iter().any(|c| c == "D020"),
        "`va`, `level` and `index` come from the POSITION and stand in no `format`: \
         {stellung:?}"
    );

    // 4 -- a domain that is not `mappings of` binds an INDEX, and an index has no fields.
    // The rule must not spread to it: `D019` and `M134` own that question.
    let andere_domaene = absagen(
        "module t {
table K count 8 { slots { marke : u32, } }
impl fn f(k : ptr<normal, r> K) -> bool
    requires forall s in slots of k : k.slots[s].marke == 0
    effects { reads k.slots } costs <= 4 ops { return true; } }",
    );
    assert!(
        !andere_domaene.iter().any(|c| c == "D020"),
        "`slots of` binds an index, not a mapping: {andere_domaene:?}"
    );

    // 5 -- **an inner quantifier that REBINDS the name, and this one was measured wrong
    // first.** The rule as committed in `ca1831b` walked the whole body for `m.field` and
    // read the INNER `m` -- a mapping of `Zwei` -- against the OUTER walk's node `format`:
    //
    //     error: [D020] `m.belegt` is not a field of a mapping
    //       = `mappings of` binds a leaf entry of `Eins` …
    //
    // **A false refusal**, and `belegt` is a perfectly good field of `Bz`. It is reachable
    // only through `mappings of`, because that is the one domain that binds a record; the
    // other seven bind an index and would have hidden the fault. *A rule that is right only
    // because the neighbouring domains cannot express the shape is right by accident.*
    let geschachtelt = absagen(
        "module t {
format Pte endian little {
    praesent : bool @0,
    frei     : u64 @[11:1] reserved,
    rahmen   : u64 embeds [51:12] scale 4096,
    hoch     : u64 @[63:52] reserved,
}
format Bz endian little {
    belegt  : bool @0,
    bz_frei : u64 @[11:1] reserved,
    block   : u64 embeds [51:12] scale 4096,
    bz_hoch : u64 @[63:52] reserved,
}
walk Eins levels 4 { node : [Pte; 512], down : rahmen when it.praesent, leaf : !it.praesent, }
walk Zwei levels 3 { node : [Bz; 256], down : block when it.belegt, leaf : !it.belegt, }
spec fn zwei(a : ptr<normal, r> Eins, b : ptr<normal, r> Zwei) -> bool
    effects { pure }
    = forall m in mappings of a : forall m in mappings of b : m.belegt; }",
    );
    assert!(
        !geschachtelt.iter().any(|c| c == "D020"),
        "a rebinding inner quantifier must not be read against the outer walk: \
         {geschachtelt:?}"
    );
}

/// **`N044`/`N045`: a probe yields a VERDICT, and on every path.**
///
/// `can_fail` is a probe -- it falls or it holds (`SYNTAX.md` §13). Measured 2026-08-31
/// against the unchanged checker: **six of the twelve files in `messung/tor-proben/` emit C
/// that `cc` refuses.**
///
/// ```c
/// bool pruefe_c(void) { if (k >= 3) { return; } }
/// ```
///
/// `gabbro pruefe` reported 0 errors, `gabbro emit` no `C001`; only `cc` said *"return with
/// no value in function returning non-void"*. **Three stages passed it, and the fourth is
/// not part of the language.**
///
/// > And `beispiele/06-annahmen.gab` has carried the finding as a COMMENT since 2026-08-20
/// > -- it says in so many words that the body returned no value -- with no rule behind it.
/// > Six files walked back into it. *A comment that names a defect is read as evidence.*
///
/// Three halves, as everywhere here: a probe per class, the counter-direction, and the
/// division of labour between the two codes.
#[test]
fn eine_probe_gibt_ein_urteil_zurueck() {
    fn absagen(quelle: &str) -> Vec<String> {
        let (baum, mut a) = gabbro_syntax::lies("p.gab", quelle);
        gabbro_check::pruefe(&baum, &mut a);
        a.absagen.iter().map(|x| x.code.to_string()).collect()
    }
    fn mit(rumpf: &str) -> String {
        format!(
            "module t {{
static mut k : u32 = 0;
impl fn tor() effects {{ reads k }} costs <= 1 ops {{ return; }}
check c {{
    claim    \"unter drei\"
    measures k
    gates    tor
    can_fail {{ {rumpf} }}
    floor    k >= 1
}} }}"
        )
    }

    // 1 -- one probe per class, and each falls ALONE: the two faults are separable.
    let a = absagen(&mit("if k >= 3 { return; } return true;"));
    assert!(
        a.iter().any(|c| c == "N044") && !a.iter().any(|c| c == "N045"),
        "ein wertloses `return` faellt an N044, und der Block endet trotzdem: {a:?}"
    );
    let b = absagen(&mit("if k >= 3 { return false; }"));
    assert!(
        b.iter().any(|c| c == "N045") && !b.iter().any(|c| c == "N044"),
        "ein Weg ohne `return` faellt an N045, und die `return`s sind in Ordnung: {b:?}"
    );

    // 2 -- the counter-direction. **The corpus shape of `beispiele/06-annahmen.gab`**, and
    // the three ways a block can end on every path.
    for rumpf in [
        "if k >= 3 { return false; } return true;",
        "return true;",
        "if k >= 3 { return false; } else { return true; }",
    ] {
        let g = absagen(&mit(rumpf));
        assert!(
            !g.iter().any(|c| c == "N044" || c == "N045"),
            "`{rumpf}` gibt auf jedem Weg ein Urteil und darf nicht fallen: {g:?}"
        );
    }

    // 3 -- a value-less `return` is refused WHEREVER it stands, not only at the top level:
    // the emitted C does not care how deeply the statement is nested.
    let tief = absagen(&mit(
        "if k >= 3 { if k >= 9 { return; } return false; } return true;",
    ));
    assert!(
        tief.iter().any(|c| c == "N044"),
        "auch zwei Ebenen tief faellt das wertlose `return`: {tief:?}"
    );

    // 4 -- **a divergent call ends the block.** Without the `divergent` list `endet_immer`
    // would call this path open and refuse a probe for a way that does not exist.
    let nie = absagen(
        "module t {
static mut k : u32 = 0;
divergent fn halt() -> never effects { diverges } costs <= 0 ops { halt(); }
impl fn tor() effects { reads k } costs <= 1 ops { return; }
check c {
    claim    \"unter drei\"
    measures k
    gates    tor
    can_fail { if k >= 3 { return false; } halt(); }
    floor    k >= 1
} }",
    );
    assert!(
        !nie.iter().any(|c| c == "N045"),
        "ein Ruf, der nicht zurueckkehrt, beendet den Block: {nie:?}"
    );

    // 5 -- **and a `forever` without an exit ends it too** (measured 2026-08-31,
    // `messung/proben/probe-probenurteil-schleife.gab`). Until that day `N045` refused this
    // shape: `endet_immer` answered `false` for every loop, `m2::endet` had learned the
    // difference a day earlier and this copy had not. The emitted C is `for (;;) { … }`,
    // and `cc -O0 -Wall -Wextra -Werror` accepts it -- *a `for (;;)` has no end for a
    // function to fall out of, so the "path that reaches its closing brace" is a path that
    // does not exist.*
    let schleife = |rumpf: &str| {
        absagen(&format!(
            "module t {{
static mut k : u32 = 0;
extern fn wachhund() -> never effects {{ diverges }};
extern fn sonde_tickt() -> bool effects {{ pure }} costs <= 1 ops;
impl fn tor() effects {{ reads k }} costs <= 1 ops {{ return; }}
check c {{
    claim    \"unter drei\"
    measures k
    gates    tor
    can_fail {{
        forever runde
            per_pass bounded 4 ops
            on_exceeded wachhund
            effects  {{ reads k }}
            progress tickt
        {{ {rumpf} }}
    }}
    floor    k >= 1
}}
assume tickt \"der Zeitgeber unterbricht\" falsifier sonde_tickt; }}"
        ))
    };
    let ohne_ausgang = schleife("if k >= 3 { return false; } return true;");
    assert!(
        !ohne_ausgang.iter().any(|c| c == "N045"),
        "ein `forever` ohne `leave` faellt nicht durch -- `N045` hat dort nichts zu sagen: \
         {ohne_ausgang:?}"
    );

    // 6 -- **the counter-direction, and it is what keeps 5 from being a blanket amnesty.**
    // The same loop WITH a `leave runde` does fall through, and then the closing brace is
    // reachable again. `beispiele/gift/407` carries the same pair for `L103`.
    let mit_ausgang = schleife("if k >= 3 { return false; } leave runde;");
    assert!(
        mit_ausgang.iter().any(|c| c == "N045"),
        "mit `leave runde` faellt die Schleife durch, und der Weg an die Klammer ist \
         wieder da: {mit_ausgang:?}"
    );
}

/// **`M135`: `bool` is not a number** -- and the other half of `N044`'s sentence.
///
/// `N044` sees THAT a verdict is missing; nobody saw whether the one that is there is a
/// verdict at all. Measured 2026-08-31 (`messung/proben/probe-rueckgabetyp.gab`): four
/// falsified returns in one file and exactly ONE falls -- the one where both sides carry a
/// range. `m1.rs::passt` ends in a comparison of ranges and `Typ::Wahrheit` has none, so
/// the whole boundary fell through a silent `else`.
///
/// **And no stage after it says a word either**: the emitter writes `return 7;` into a
/// `bool` function and `cc -O0 -Wall -Wextra -Werror` accepts it, because C converts. *A
/// probe that returns `7` HOLDS on that path, always -- a counterprobe that cannot fall.*
#[test]
fn wahrheit_ist_keine_zahl() {
    fn absagen(quelle: &str) -> Vec<String> {
        let (baum, mut a) = gabbro_syntax::lies("p.gab", quelle);
        gabbro_check::pruefe(&baum, &mut a);
        a.absagen.iter().map(|x| x.code.to_string()).collect()
    }
    fn mit(kopf: &str, rumpf: &str) -> String {
        format!(
            "module t {{
static mut k : u32 = 0;
static mut w : bool = false;
impl fn f() -> {kopf} effects {{ reads k, reads w }} costs <= 1 ops {{ {rumpf} }} }}"
        )
    }

    // 1 -- both directions across the boundary.
    for (kopf, rumpf) in [("bool", "return 7;"), ("u32", "return w;"), ("bool", "return k;")] {
        let a = absagen(&mit(kopf, rumpf));
        assert!(
            a.iter().any(|c| c == "M135"),
            "`-> {kopf} {{ {rumpf} }}` kreuzt die Grenze und muss fallen: {a:?}"
        );
    }

    // 2 -- the counter-direction. **A range still belongs to `M101`** -- one rule per
    // question, and widening this one would take a refusal away from the other.
    let bereich = absagen(&mit("u8", "return 300;"));
    assert!(
        bereich.iter().any(|c| c == "M101") && !bereich.iter().any(|c| c == "M135"),
        "ein Bereichsfehler bleibt `M101`s Sache: {bereich:?}"
    );
    for (kopf, rumpf) in [("bool", "return true;"), ("u32", "return k;"), ("bool", "return w;")] {
        let g = absagen(&mit(kopf, rumpf));
        assert!(
            !g.iter().any(|c| c == "M135"),
            "`-> {kopf} {{ {rumpf} }}` kreuzt nichts und darf nicht fallen: {g:?}"
        );
    }

    // 3 -- **the one-bit exception, and `beispiele/gift/416` wrote it.** A device field of
    // one bit has type `u8 in 0 .. 1`: it admits both truth values and nothing else, so it
    // carries the same question as `bool`. *The line is the RANGE and not the width* -- a
    // literal `1` has `u8 in 1 .. 1`, admits one value, and falls.
    let bit = absagen(
        "module t {
device Uart at mmio {
    reg LSR : u8 @0x3FD class r fields { THRE @5, }
}
impl fn lies(d : ptr<mmio, r> Uart) -> bool effects { reads d.LSR } costs <= 2 ops
{ return d.LSR.THRE; } }",
    );
    assert!(
        !bit.iter().any(|c| c == "M135"),
        "ein Ein-Bit-Feld in ein `bool` ist kein Uebergang: {bit:?}"
    );
    let eins = absagen(&mit("bool", "return 1;"));
    assert!(
        eins.iter().any(|c| c == "M135"),
        "`return 1` laesst genau einen Wert zu und ist kein Wahrheitswert: {eins:?}"
    );

    // 4 -- **the two defects `M135` found in this checker on its first corpus run**, and
    // they are the reason it is worth its own rule. Both bound a name to the wrong type,
    // and both had been silent because nothing ever compared the two sides.
    //
    // (a) `when … returns e` hands back WHETHER the swap happened -- the emitter writes
    // `bool genommen; genommen = atomic_compare_exchange_strong_explicit(…)`
    // (`beispiele/35-tausch.gab`), and this pass called it `u32`.
    let cas = absagen(
        "module t {
const NIEMAND : u32 = 0;
atomic BESITZER : u32 release;
impl fn nimm(f : u32) -> bool
    requires f > 0
    effects { writes BESITZER, publishes BESITZER }
    costs   <= 16 ops
{
    let genommen = BESITZER exchange f when old(BESITZER) == NIEMAND returns erfolg
        publishes nothing;
    return genommen;
} }",
    );
    assert!(
        !cas.iter().any(|c| c == "M135" || c == "M101"),
        "ein compare-exchange liefert ein `bool`, kein `u32`: {cas:?}"
    );

    // (b) a `return` in an `update` body yields the NEW value of the PLACE, not the
    // enclosing function's result. In the corpus the two coincided by accident
    // (`beispiele/05-nebenlaeufigkeit.gab`); inside a `check` they do not.
    let update = absagen(
        "module t {
const GRENZE : u32 = 65535;
const NKERNE : u32 = 4;
atomic ZAEHLER : u32 relaxed;
extern fn streit() -> never effects { diverges } costs <= 1 ops;
impl fn tor() effects { reads ZAEHLER } costs <= 1 ops { return; }
check c {
    claim    \"der Zaehler bleibt unter seiner Grenze\"
    measures ZAEHLER
    gates    tor
    can_fail {
        let alt = ZAEHLER exchange update(v)
            bounded NKERNE * 4 ops
            on_exceeded streit
        {
            if v < GRENZE { return v + 1; }
            return v;
        } publishes nothing;
        return alt < GRENZE;
    }
    floor    ZAEHLER >= 0
} }",
    );
    assert!(
        !update.iter().any(|c| c == "M135"),
        "der Rumpf eines `update` liefert den neuen Wert des ORTS, nicht das Ergebnis der \
         umgebenden Funktion: {update:?}"
    );
}

/// **`M148`: a `return` with a value in a function that declares none.**
///
/// The fourth door in the `M140` wall, and this one was never a range question either:
/// the EXISTENCE of the slot. `m1.rs` compared the return value solely against the
/// declared result (`if let Some(z) = ergebnis`), so a value in a result-less body fell
/// through the `if` silently -- and the emitter writes it straight into a `void`
/// function, where both C families refuse it (`-Werror=return-type`).
///
/// Measured 2026-09-12 on `beispiele/gift/776`: the checker said 0 errors, the emitter
/// wrote `return m;` into `static void kreis`, and `cc` and `clang` refused it line for
/// line. *Three stages passed it, and the fourth is not part of the language* -- the same
/// shape as `N044`'s, one construct further out. The poison probe is
/// `beispiele/gift/788`; the twin `gib` beside it declares `-> u32` and keeps the same
/// lines silent, and the bare `return;` of `leer` is the third arm.
#[test]
fn rueckgabe_traegt_einen_wert_ohne_ergebnis() {
    fn absagen(quelle: &str) -> Vec<String> {
        let (baum, mut a) = gabbro_syntax::lies("p.gab", quelle);
        gabbro_check::pruefe(&baum, &mut a);
        a.absagen.iter().map(|x| x.code.to_string()).collect()
    }
    fn mit(kopf: &str, rumpf: &str) -> String {
        format!(
            "module t {{
static mut m : u32 = 0;
impl fn f(){kopf} effects {{ reads m }} costs <= 1 ops {{ {rumpf} }} }}"
        )
    }

    // 1 -- a valued `return` in a result-less body falls, and falls ALONE: the bare
    // `return;` beside it is the form SYNTAX.md reads as the end of such a body.
    let a = absagen(&mit("", "if m > 0 { return m; } return 0;"));
    assert_eq!(
        a.iter().filter(|c| *c == "M148").count(),
        2,
        "beide wertvollen `return` fallen an M148, und sonst nichts: {a:?}"
    );

    // 2 -- the counter-direction. The same lines under a declared `-> u32` are the
    // program the rule must never touch; the bare `return;` under no result is the
    // sugar SYNTAX.md promises such a body.
    for (kopf, rumpf) in [
        (" -> u32", "if m > 0 { return m; } return 0;"),
        ("", "return;"),
        ("", "if m > 0 { return; }"),
    ] {
        let g = absagen(&mit(kopf, rumpf));
        assert!(
            !g.iter().any(|c| c == "M148"),
            "`f(){kopf} {{ {rumpf} }}` ist richtig und darf nicht fallen: {g:?}"
        );
    }

    // 3 -- a valued `return` is refused WHEREVER it stands, not only at the top level:
    // the emitted C does not care how deeply the statement is nested.
    let tief = absagen(&mit("", "if m > 0 { if m > 9 { return m; } return 0; } return 0;"));
    assert_eq!(
        tief.iter().filter(|c| *c == "M148").count(),
        3,
        "auch zwei Ebenen tief faellt jedes wertvolle `return`: {tief:?}"
    );
}

/// **The block boundary of `N001` -- and the mutation that showed it had no anchor.**
///
/// `namen.rs::rumpf_geltung` refuses two declarations of one name in ONE scope, because the
/// emitter writes them out unchanged and `cc` then answers *redeclared as different kind of
/// symbol*. It deliberately stops at the block boundary: **C accepts a nested covering**, and
/// `beispiele/gift/19-let-verdeckt.gab` has held that form as a legal program since
/// 2026-08-14 -- `let x : u8 = 0;` inside an `if`, covering the parameter `x`, expected to
/// fall at `M102` because the narrowing fact belongs to the covered binding.
///
/// The mutation `rumpf_geltung(k, &mut scope.clone(), …)` -- let the sub-block inherit the
/// enclosing scope -- **survived the whole suite on 2026-08-31.** `19-let-verdeckt.gab` still
/// falls, only now with an added `N001`, and `jedes_gift_faellt_mit_seinem_code` asks whether
/// the expected code is AMONG the fallen, not whether it is alone. *A rule that is too broad
/// looks exactly like a rule that is right, from a probe that only asks whether something
/// fell.*
///
/// This is the anchor for the other direction, and it is the one the corpus could not give:
/// the nested form must produce **no `N001` at all**.
#[test]
fn eine_verdeckung_im_unterblock_ist_kein_n001() {
    fn absagen(quelle: &str) -> Vec<String> {
        let (baum, mut a) = gabbro_syntax::lies("p.gab", quelle);
        gabbro_check::pruefe(&baum, &mut a);
        a.absagen.iter().map(|x| x.code.to_string()).collect()
    }

    // The covering sits in the `if` body -- a scope of its own, and legal C.
    let verschachtelt = absagen(
        "module t {
impl fn f(x : u8) -> u8 effects { pure } costs <= 8 ops {
    if x >= 1 {
        let x : u8 = 7;
        return x;
    }
    return 0;
} }",
    );
    assert!(
        !verschachtelt.iter().any(|c| c == "N001"),
        "eine Verdeckung im Unterblock ist erlaubt -- C nimmt sie an, und `19-let-verdeckt` \
         fuehrt sie seit dem 2026-08-14 als gueltiges Programm: {verschachtelt:?}"
    );

    // Two sibling arms binding the same name never see each other either.
    let geschwister = absagen(
        "module t {
impl fn f(b : bool) -> u8 effects { pure } costs <= 8 ops {
    if b {
        let n : u8 = 1;
        return n;
    }
    let n : u8 = 2;
    return n;
} }",
    );
    assert!(
        !geschwister.iter().any(|c| c == "N001"),
        "zwei Geschwisterbloecke teilen keinen Geltungsbereich: {geschwister:?}"
    );

    // And the form that HAS no reading still falls: same scope as the parameter.
    let selber = absagen(
        "module t {
impl fn f(x : u8) -> u8 effects { pure } costs <= 8 ops {
    let x : u8 = 7;
    return x;
} }",
    );
    assert!(
        selber.iter().any(|c| c == "N001"),
        "im Geltungsbereich des Rumpfblocks liegt der Parameter -- `cc` weist die zweite \
         Deklaration ab, also weist der Pruefer sie ab: {selber:?}"
    );
}

// ==========================================================================================
// **The block scope of the cost pass** (2026-08-31). Until this day `kosten.rs` knew the
// PARAMETERS of a function and nothing else -- a `let` in an inner block was invisible to
// it, and `typ_von_ort` therefore answered with the parameter a `let` had shadowed one line
// above. The bound then belonged to the wrong table, in both directions.
// ==========================================================================================

/// **A shadowing `let` decides the bound, and the number says which binding was read.**
///
/// The measurement that forced this: the same body, once over the shadowing name and once
/// over the real one, and the promise `costs <= 17 ops` went through with **0 errors** --
/// while the emitted C ran 64 passes (`sizeof(t->slots)` reads the INNER `t`; compiled and
/// run, it printed `64`). *A cost promise the delivered program violates, and no pass said
/// a word.*
///
/// **The exact number is the point, and it is what kills a too-wide fix.** A version that
/// binds every `let` to `Unbekannt` also stops printing 17 -- it prints `OFFEN` and refuses
/// at `K003`, which looks like a repair and is a second defect. Only the honest reading of
/// the shadowing binding lands on 325 (197 before lane 139 counted `+=` as a bare store).
#[test]
fn ein_let_im_inneren_block_verdeckt_den_parameter_und_die_schranke_folgt_ihm() {
    let q = "module p {
const KLEIN : u32 = 4;
const GROSS : u32 = 64;
table Winzig count KLEIN { slot { wert : u32, } }
table Riesig count GROSS { slot { wert : u32, } }
impl fn schatten(t : ptr<normal, r> Winzig, g : ptr<normal, r> Riesig, f : bool) -> u32
    effects { reads t.slots, reads g.slots }
    costs   <= 17 ops
{
    let mut summe : u32 in 0 .. 65535 = 0;
    if f {
        let t = g;
        traverse i over slots of t by unvisited
            touches reads t.slots
        {
            if summe < 60000 {
                summe += 1;
            }
        }
    }
    return summe;
}
}
";
    // **325 since lane 139 (197 before)** -- 64 passes over the bound of `Riesig`, not
    // the 17 of `Winzig` (4); each pass costs (3 + 2) ops since `+=` loads and computes.
    assert_eq!(
        gerechnet(q, "schatten"),
        325,
        "the traversal runs over the INNER `t`, which is `g` -- 64 slots, not 4"
    );
    let (b, mut a) = gabbro_syntax::lies("p.gab", q);
    let _ = gabbro_check::pruefe(&b, &mut a);
    let codes: Vec<&str> = a.absagen.iter().map(|x| x.code).collect();
    assert!(
        codes.contains(&"K001"),
        "a promise of 17 over a body of 197 must fall, fallen: {codes:?}"
    );
    // **And the refusal has to be `K001`, not `K003`.** A pass that answers *"no bound"*
    // here has thrown away a bound that stands in the declaration -- the very defect this
    // scope was built against, only in the other direction.
    assert!(
        !codes.contains(&"K003"),
        "the bound STANDS -- `Riesig count 64`; `K003` here would be a second defect: {codes:?}"
    );
}

/// **The other direction: a `let` that shadows NOTHING must still carry its bound.**
///
/// `let tafel = w; traverse i over slots of tafel` was a `K003` until today -- a correct
/// program refused over a bound that stands in the declaration
/// (`messung/proben/probe-traverse-grundname.gab`, case (a)). *This is the test that kills
/// the cheap fix:* binding every `let` to `Unbekannt` closes the shadowing hole and reopens
/// this one, and a poison sample asking only whether the expected code is AMONG the fallen
/// would not notice.
#[test]
fn ein_let_ohne_verdeckung_erbt_den_typ_seines_wertes() {
    let q = "module p {
const NSLOTS : u32 = 8;
table Werte count NSLOTS { slot { wert : u32, } }
impl fn ueber_ein_let(w : ptr<normal, r> Werte) -> u32
    effects { reads w.slots }
    costs   <= 64 ops
{
    let mut summe : u32 in 0 .. 65535 = 0;
    let tafel = w;
    traverse i over slots of tafel by unvisited
        touches reads tafel.slots
    {
        if summe < 60000 {
            summe += 1;
        }
    }
    return summe;
}
}
";
    assert_eq!(
        gerechnet(q, "ueber_ein_let"),
        44,
        "`tafel` IS `w` -- 8 slots, and the number stands in the declaration \
         (28 before lane 139 counted `+=` as a bare store)"
    );
    let (b, mut a) = gabbro_syntax::lies("p.gab", q);
    let _ = gabbro_check::pruefe(&b, &mut a);
    let codes: Vec<&str> = a.absagen.iter().map(|x| x.code).collect();
    assert!(
        codes.is_empty(),
        "a correct program, and it was refused until 2026-08-31: {codes:?}"
    );
}

/// **The traversal variable is a place index, not a table** -- and it is bound in the body.
///
/// Without this line a `traverse t over …` inside a function with a parameter `t` would
/// hand the parameter's bound to `slots of t` in the body. The honest answer is *no bound*,
/// and `K003` says so instead of naming a number that belongs to another table.
#[test]
fn die_laufvariable_verdeckt_den_parameter_und_traegt_keine_schranke() {
    let q = "module p {
const NSLOTS : u32 = 8;
table Werte count NSLOTS { slot { wert : u32, } }
impl fn f(t : ptr<normal, r> Werte) -> u32
    effects { reads t.slots }
    costs   <= 999 ops
{
    let mut summe : u32 in 0 .. 65535 = 0;
    traverse t over slots of t by unvisited
        touches reads t.slots
    {
        traverse j over slots of t by unvisited {
            summe += 1;
        }
    }
    return summe;
}
}
";
    let (b, mut a) = gabbro_syntax::lies("p.gab", q);
    let _ = gabbro_check::pruefe(&b, &mut a);
    let codes: Vec<&str> = a.absagen.iter().map(|x| x.code).collect();
    assert!(
        codes.contains(&"K003"),
        "`slots of t` over the LOOP variable has no bound -- it is an index: {codes:?}"
    );
}

// ===========================================================================================
// THE LEAN CHANNEL -- THE REFUSED FORMS, AND THE ONE WIRING THAT WAS MISSING (2026-09-08)
//
// `programmlogik/PLAN.md` §5.2 items 2 and 3. Each test below is the container half of a
// measurement whose other half runs `lean` over the corpus on the model machine: the
// emitter's TEXT is what a `cargo test` can hold, and it is held here so that a form that
// silently stops being carried falls at build time and not eight minutes later.
// ===========================================================================================

/// **`forall f in fields of <format>` is a FINITE conjunction, and the emitter knows the
/// list.** Until 2026-09-08 it stood under `quantified` with `threads` and `mappings of` --
/// three domains, one tag, and only one of the three reasons true for all of them. A body
/// that does not read the binder is every use of the domain in the corpus, and there the
/// quantifier collapses to its body.
#[test]
fn lean_felder_von_wird_zur_konjunktion() {
    let q = "module t {
        table K count 4 { slot { marke : u32, } }
        format W endian little { g : bool @0, s : bool @1, }
        impl fn d6(k : ptr<normal, rw> K)
            ensures forall f in fields of W : k.slots[0].marke == 0
            effects { reads k.slots, writes k.slots }
            costs   <= 4 ops
        { }
    }";
    let t = lean_modul(q);
    assert!(
        t.contains("carried by `d6_meets`"),
        "a `fields of` whose body does not read the binder is carried:\n{t}"
    );
    assert!(
        !t.contains("quantified"),
        "and nothing about it is refused any more:\n{t}"
    );
    // the collapsed conjunct IS the body, and the binder appears nowhere
    assert!(
        t.contains("(.place \"K\" (.lit (.int 0)) \"marke\")") && !t.contains("(.name \"f\")"),
        "the quantifier collapses to its body, and the field NAME is not a value:\n{t}"
    );
}

/// **A `fields of` whose body READS the binder is still refused** -- a field name is not a
/// value of this model, and n copies of a term mentioning `f` would be n copies of a name
/// nothing binds. *The soundness half of the test above.*
#[test]
fn lean_felder_von_mit_gelesenem_binder_bleibt_abgesagt() {
    let q = "module t {
        table K count 4 { slot { marke : u32, } }
        format W endian little { g : bool @0, s : bool @1, }
        impl fn d6(k : ptr<normal, rw> K)
            ensures forall f in fields of W : k.slots[f].marke == 0
            effects { reads k.slots, writes k.slots }
            costs   <= 4 ops
        { }
    }";
    let t = lean_modul(q);
    assert!(
        t.contains("refused (quantified)"),
        "a binder the body reads has no term here, and the refusal says so:\n{t}"
    );
}

/// **`threads` and `mappings of` are two refusals and not one.** Their grounds differ --
/// `threads` has no declaration anywhere in the language, `mappings of` speaks about
/// hardware -- and so do their ways out. One tag over both told a reader neither.
#[test]
fn lean_threads_und_abbildungen_haben_je_eine_marke() {
    let q = "module t {
        table K count 4 { slot { belegt : bool, } }
        format W endian little { g : bool @0, r : u64 embeds [51:12] scale 4096, }
        walk B levels 2 { node : [W; 512], down : r when it.g, leaf : it.g,
        }
        impl fn d8(k : ptr<normal, rw> K)
            ensures forall x in threads : k.slots[0].belegt
            effects { reads k.slots, writes k.slots }
            costs   <= 4 ops
        { }
        impl fn d9(w : ptr<normal, rw> B)
            ensures !exists m in mappings of w : m.g
            effects { writes w }
            costs   <= 4 ops
        { }
    }";
    let t = lean_modul(q);
    assert!(
        t.contains("refused (quantified-threads)") && t.contains("refused (quantified-mappings)"),
        "each domain carries its own tag:\n{t}"
    );
    assert!(
        t.contains("threads over T") && t.contains("ASSUMED by name"),
        "and each names its own way out:\n{t}"
    );
}

/// **A refusal that is INHERITED says so.** `ensures result == puffer.e_eintritt` has a
/// term; what has none is the `requires lenof(puffer) >= sizeof(…)` of the same routine --
/// and the register used to print the built-in's tag beside the `ensures` with nothing to
/// say that the `ensures` was not the problem. *A reader went looking for a built-in in a
/// clause that has none.*
#[test]
fn lean_geerbte_absage_nennt_ihren_ursprung() {
    let q = "module t {
        format K endian little { e : u64 @[63:0], }
        impl fn kopf(p : ptr<normal, r> K) -> u64
            requires lenof(p) >= sizeof(K)
            ensures  result == p.e
            effects  { reads p }
            costs    <= 16 ops
        { return p.e; }
    }";
    let t = lean_modul(q);
    assert!(
        t.contains("layout-buffer-length"),
        "`lenof` over a buffer nothing measures has its OWN tag now:\n{t}"
    );
    assert!(
        t.contains("inherited: this clause HAS a term"),
        "and the line says that the refusal is not this clause's:\n{t}"
    );
}

/// **A recursive call inside a loop is WIRED** (`contract_of_duty_rec_loop_in`,
/// `Gabbro/Body.lean` §8). Three things have to be in the text, and each was missing before:
/// the pass gets the bounded self-contract at the ROUTINE's entry state, it carries the
/// measure across, and `unit_closed` composes the two inductions in one step.
///
/// *The corpus had no unit of this shape; `messung/proben/probe-rekursion-in-schleife.gab`
/// is the one that measures it, and this test is its container half.*
#[test]
fn lean_rekursion_in_der_schleife_wird_verdrahtet() {
    let q = "module t {
        const T : u32 = 8;
        table Z count 4 { slot { marke : u32 in 0 .. T, } }
        impl fn f(z : ptr<normal, rw> Z, n : u32 in 0 .. T)
            ensures forall s in slots of z : z.slots[s].marke <= T
            effects { reads z.slots, writes z.slots }
            costs   <= 65536 ops
            decreases n
        {
            traverse i over slots of z by unvisited
                touches reads z.slots, writes z.slots
                invariant n <= T
            {
                z.slots[i].marke = n;
                if n > 0 { f(z, n - 1); }
            }
        }
    }";
    let t = lean_modul(q);
    assert!(
        !t.contains("NOT WIRED"),
        "the one shape `unit_closed` could not close is closed:\n{t}"
    );
    assert!(
        t.contains("contract_of_duty_rec_loop_in ρ \"f\""),
        "and it is closed by the model's theorem, not by a hole:\n{t}"
    );
    assert!(
        t.contains("(c_f : ContractBelow ρ \"f\" f_decreases s0 f_requires f_post)"),
        "the pass assumes the self-contract below the ROUTINE's entry state:\n{t}"
    );
    assert!(
        t.contains("eval t' f_decreases = eval s0 f_decreases"),
        "and owes that the measure has not moved -- without this the bound is vacuous:\n{t}"
    );
    assert!(
        t.contains("contractBelow_of_contract"),
        "and the loop's own rule follows from the finished contract:\n{t}"
    );
}

/// **A routine with TWO loops, the call in one of them, is wired** (agent b, 2026-09-08).
///
/// The earlier refusal (*"one of SEVERAL loops"*) was an OVER-refusal: the second loop has
/// nothing to do with the recursion. What it DID hide is a real obligation, and the probe
/// `messung/proben/probe-rekursion-zwei-schleifen.gab` found it: a `LoopRule` says nothing
/// about the locals, so a loop in front of the recursive one could, as far as the model
/// knows, have moved the measure. **Every loop of the routine carries the measure now**, and
/// each proves it of its own body.
#[test]
fn lean_rekursion_in_einer_von_zwei_schleifen_wird_verdrahtet() {
    let q = "module t {
        const T : u32 = 8;
        table Z count 4 { slot { marke : u32 in 0 .. T, } }
        impl fn f(z : ptr<normal, rw> Z, n : u32 in 0 .. T)
            effects { reads z.slots, writes z.slots }
            costs   <= 131072 ops
            decreases n
        {
            traverse j over slots of z by unvisited
                touches writes z.slots
                invariant n <= T
            {
                z.slots[j].marke = 0;
            }
            traverse i over slots of z by unvisited
                touches reads z.slots, writes z.slots
                invariant n <= T
            {
                z.slots[i].marke = n;
                if n > 0 { f(z, n - 1); }
            }
        }
    }";
    let t = lean_modul(q);
    assert!(
        !t.contains("NOT WIRED"),
        "a second loop beside the recursion is no reason to refuse:\n{t}"
    );
    assert!(
        t.contains("contract_of_duty_rec_loop_in ρ \"f\""),
        "the composition is the model's, as with one loop:\n{t}"
    );
    assert!(
        t.contains("have lp_f_loop_1"),
        "the innocent loop's rule is built beside it, quantified over the entry state:\n{t}"
    );
    assert!(
        t.matches("eval t' f_decreases = eval s0 f_decreases").count() >= 2,
        "and EVERY loop of the routine owes that the measure has not moved:\n{t}"
    );
}

/// **A `retry` loop takes the same composition, without a range** (agent b, 2026-09-08).
///
/// The refusal read *"no index range to induct over"* and the ground was wrong: the
/// induction is over the `decreases`, never over the index. `looprule_of_body` builds the
/// rule of a rangeless loop, and `contract_of_duty_rec_loop` composes it.
#[test]
fn lean_rekursion_in_retry_schleife_wird_verdrahtet() {
    let q = "module t {
        const T : u32 = 8;
        static mut stand : u32 in 0 .. 255 = 0;
        extern fn ende() -> never effects { diverges } costs <= 1 ops;
        assume jemand_zaehlt \"Somebody raises it.\" falsifier sonde_jemand_zaehlt;
        impl fn f(n : u32 in 0 .. T)
            effects { reads stand, writes stand }
            costs   <= 65536 ops
            decreases n
        {
            retry runde until stand >= 1
                bounded 1024 ops
                progress jemand_zaehlt
                on_exceeded ende
                effects { reads stand, writes stand }
                invariant n <= T
            {
                stand = 1;
                if n > 0 { f(n - 1); }
            }
        }
    }";
    let t = lean_modul(q);
    assert!(
        !t.contains("NOT WIRED"),
        "a loop without an index range is no reason to refuse:\n{t}"
    );
    assert!(
        t.contains("contract_of_duty_rec_loop ρ \"f\""),
        "the rangeless composition is the one used:\n{t}"
    );
    assert!(
        t.contains("looprule_of_body ρ \"f#1\""),
        "and the rangeless loop-rule builder with it:\n{t}"
    );
}

/// **A STACK of loops keeps its refusal, and names which shape.** Every loop on the way to
/// the recursive call would have to carry the measure, and the composition composes one
/// rule, not a stack of them.
#[test]
fn lean_rekursion_in_geschachtelter_schleife_bleibt_unverdrahtet_mit_grund() {
    let q = "module t {
        const T : u32 = 8;
        table Z count 4 { slot { marke : u32 in 0 .. T, } }
        impl fn f(z : ptr<normal, rw> Z, n : u32 in 0 .. T)
            effects { reads z.slots, writes z.slots }
            costs   <= 131072 ops
            decreases n
        {
            traverse i over slots of z by unvisited
                touches reads z.slots, writes z.slots
                invariant n <= T
            {
                traverse j over slots of z by unvisited
                    touches reads z.slots, writes z.slots
                    invariant n <= T
                {
                    z.slots[j].marke = n;
                    if n > 0 { f(z, n - 1); }
                }
            }
        }
    }";
    let t = lean_modul(q);
    assert!(
        t.contains("NOT WIRED") && t.contains("holds another loop") && t.contains("stack of rules"),
        "an unwired shape names the construct and why -- and NOT `SEVERAL loops`, which a \
         nested call makes true and which would send a reader to the wrong place:\n{t}"
    );
}
// ===========================================================================================
// **The pass counter of a `traverse`** (agent b, 2026-09-08) -- `PLAN.md` §5.2 item 1.
//
// `passes` is the number of passes already done. It is readable in the `invariant` of a
// `traverse` and nowhere else, it is a GHOST (nothing of it reaches the generated C), and a
// declared name of the same spelling shadows it. What it buys is the one sentence a counter
// in a loop needs and could not be written: `n <= passes` survives a pass, while `n <= N`
// -- true of every run -- does not survive the rule, because the rule quantifies over every
// state the invariant admits, including `n == N`.
// ===========================================================================================

const LEAN_ZAEHLER: &str = "module p {
const NSLOTS : u32 = 16;
table Werte count NSLOTS { slot { aktiv : bool, } }
impl fn zaehle(w : ptr<normal, r> Werte) -> u32
    effects { reads w.slots }
    costs   <= 999 ops
{
    let mut n : u32 in 0 .. NSLOTS = 0;
    traverse i over slots of w by unvisited
        touches reads w.slots
        invariant n <= passes
    {
        if w.slots[i].aktiv { n += 1; }
    }
    return n;
}
}
";

/// **The emitted form**: the counter is bound to zero before the loop, the pass increases it
/// as its FIRST statement (so a `next` or a `leave` cannot skip it), the loop's rule is
/// `LoopRuleP`, and the environment promise carries the bound on the NUMBER of passes.
#[test]
fn der_passzaehler_wird_gebunden_erhoeht_und_beschraenkt() {
    let lean = lean_modul(LEAN_ZAEHLER);
    assert!(
        lean.contains("(.bindName \"#pass\" (.lit (.int 0))), (.loop \"zaehle#1\""),
        "the counter stands at zero one statement before the loop:\n{lean}"
    );
    assert!(
        lean.contains(
            "def zaehle_loop_1_body : List Stmt :=\n  [(.bindName \"#pass\" (.bin .add (.name \"#pass\") (.lit (.int 1))))"
        ),
        "and every pass increases it, first thing:\n{lean}"
    );
    assert!(
        lean.contains("(.bin .le (.name \"n\") (.name \"#pass\"))"),
        "`passes` in the invariant IS the counter, not a global of that name:\n{lean}"
    );
    assert!(
        !lean.contains("(.global \"passes\")"),
        "and it is never read out of the world:\n{lean}"
    );
    // the bound on the number of passes -- the table's `count`, not the index range
    assert!(
        lean.contains("RunsLoopN ρ \"zaehle#1\" zaehle_loop_1_body \"i\" 0 16 16"),
        "the environment promise bounds how OFTEN the body runs:\n{lean}"
    );
    assert!(
        lean.contains("LoopRuleP ρ \"zaehle#1\" wellFormed zaehle_loop_1_inv \"#pass\"")
            && lean.contains("looprule_of_body_p ρ \"zaehle#1\""),
        "and the rule is the one that carries the counter:\n{lean}"
    );
    // what the pass may assume, and what it owes back
    for z in [
        "(hplo : 0 ≤ i)",
        "(hphi : i < 16)",
        "(hpass : t.local' \"#pass\" = .int i)",
        "∧ t'.local' \"#pass\" = .int (i + 1)",
    ] {
        assert!(z_in(&lean, z), "the pass's own hypothesis `{z}` is missing:\n{lean}");
    }
}

fn z_in(h: &str, n: &str) -> bool {
    h.contains(n)
}

/// **A loop whose invariant does not name `passes` does not move a single line.** A
/// convenience nobody asked for must not change the proof obligation of every other loop.
#[test]
fn ohne_passes_bleibt_die_schleife_wie_sie_war() {
    let ohne = LEAN_ZAEHLER.replace("invariant n <= passes", "invariant n <= NSLOTS");
    let lean = lean_modul(&ohne);
    assert!(!lean.contains("#pass"), "no counter where none was named:\n{lean}");
    assert!(
        lean.contains("RunsLoopIn ρ \"zaehle#1\"") && lean.contains("looprule_of_body_in"),
        "the rule stays `LoopRule`:\n{lean}"
    );
}

/// **A declared name shadows the ghost.** `passes` is a word a program may already use, and
/// where it does, the invariant means the program's name -- in the checker (`D021` stays
/// silent because the local is declared) and in the emitter alike.
#[test]
fn ein_deklariertes_passes_verdeckt_den_zaehler() {
    let q = "module p {
const NSLOTS : u32 = 16;
table Werte count NSLOTS { slot { aktiv : bool, } }
impl fn zaehle(w : ptr<normal, r> Werte, passes : u32) -> u32
    effects { reads w.slots }
    costs   <= 999 ops
{
    let mut n : u32 in 0 .. NSLOTS = 0;
    traverse i over slots of w by unvisited
        touches reads w.slots
        invariant n <= passes
    {
        if w.slots[i].aktiv { n += 1; }
    }
    return n;
}
}
";
    let lean = lean_modul(q);
    assert!(
        !lean.contains("#pass"),
        "the parameter is the parameter, and no counter is emitted:\n{lean}"
    );
}

/// **`passes` outside a loop invariant is still nothing** -- `D021` says so, as it did
/// before. The ghost is declared by the `traverse` and by nothing else.
#[test]
fn passes_ausserhalb_der_invariante_bleibt_unbekannt() {
    let q = "module p {
impl fn f(n : u32) -> u32
    requires n <= passes
    effects { pure }
    costs   <= 9 ops
{
    return n;
}
}
";
    let (b, mut a) = gabbro_syntax::lies("p.gab", q);
    let _ = gabbro_check::pruefe(&b, &mut a);
    let codes: Vec<&str> = a.absagen.iter().map(|x| x.code).collect();
    assert!(
        codes.contains(&"D021"),
        "`passes` in a `requires` names nothing: {codes:?}"
    );
}

/// **A loop that is not a bounded `traverse` cannot count its passes.** The checker refuses
/// the name there (`D021` -- it is declared by a `traverse` and by nothing else); the
/// emitter, which reads the tree either way, refuses it with a tag of its own instead of
/// writing `passes` out as a place of the world -- the wrong proof object `D021` names.
#[test]
fn passes_ohne_schranke_wird_abgesagt() {
    let q = "module p {
static mut a : u32 in 0 .. 16 = 0;
extern fn zeitablauf() -> never effects { diverges };
assume geraet_antwortet \"the device answers.\" falsifier sonde;
impl fn f() -> u32
    effects { writes a }
    costs   <= 999 ops
{
    retry warten until a == 16
        bounded 2 ops
        progress geraet_antwortet
        on_exceeded zeitablauf
        effects { writes a }
        invariant a <= passes
    {
        a = 1;
    }
    return a;
}
}
";
    let (b, mut a) = gabbro_syntax::lies("p.gab", q);
    let _ = gabbro_check::pruefe(&b, &mut a);
    let codes: Vec<&str> = a.absagen.iter().map(|x| x.code).collect();
    assert!(
        codes.contains(&"D021"),
        "`passes` is declared by a `traverse` and by nothing else: {codes:?}"
    );
    let lean = gabbro_check::lean::module(&b, "p.gab");
    assert!(
        lean.contains("pass-counter"),
        "and the emitter refuses it with its own tag:\n{lean}"
    );
    assert!(
        !lean.contains("(.global \"passes\")"),
        "the name never becomes a place of the world:\n{lean}"
    );
}

// ---------------------------------------------------------------------------------------
// **Bit intrinsics (PLAN-BITS §3, surface half): one probe per intrinsic, then the run.**
//
// The seven calls are ordinary single-segment calls the checker claims by name
// (`m1.rs::intrinsik_ruf`, `M157`-`M160`): no new word, no grammar change. What
// stands here pins all four halves -- the typing (clean here, refusal below),
// the lowering text, the compilation under two compilers with `-Werror`, and
// the computed VALUES at run time (a text probe alone cannot tell
// `__builtin_clz` from `__builtin_ctz`: both compile, only one counts right).
// ---------------------------------------------------------------------------------------

/// The unit every probe below checks: one function per intrinsic and width.
const BITS_QUELLE: &str = "module t {
impl fn clz32(v : u32 in 1 .. 4294967295) -> u32 effects { pure } costs <= 9 ops { return clz(v); }
impl fn ctz32(v : u32 in 1 .. 4294967295) -> u32 effects { pure } costs <= 9 ops { return ctz(v); }
impl fn log32(v : u32 in 1 .. 4294967295) -> u32 effects { pure } costs <= 9 ops { return log2_floor(v); }
impl fn pop32(v : u32) -> u32 effects { pure } costs <= 9 ops { return popcount(v); }
impl fn rot32(x : u32, s : u32 in 0 .. 31) -> u32 effects { pure } costs <= 9 ops { return rotl(x, s); }
impl fn ror32(x : u32, s : u32 in 0 .. 31) -> u32 effects { pure } costs <= 9 ops { return rotr(x, s); }
impl fn swp32(v : u32) -> u32 effects { pure } costs <= 9 ops { return bswap(v); }
impl fn clz16(v : u16 in 1 .. 65535) -> u16 effects { pure } costs <= 9 ops { return clz(v); }
impl fn rot16(x : u16, s : u16 in 0 .. 15) -> u16 effects { pure } costs <= 9 ops { return rotl(x, s); }
impl fn swp16(v : u16) -> u16 effects { pure } costs <= 9 ops { return bswap(v); }
impl fn clz8(v : u8 in 1 .. 255) -> u8 effects { pure } costs <= 9 ops { return clz(v); }
impl fn pop64(v : u64) -> u64 effects { pure } costs <= 9 ops { return popcount(v); }
impl fn rot64(x : u64, s : u64 in 0 .. 63) -> u64 effects { pure } costs <= 9 ops { return rotl(x, s); }
impl fn swp64(v : u64) -> u64 effects { pure } costs <= 9 ops { return bswap(v); }
impl fn mix64(v : u64 in 1 .. 1000000) -> u64 effects { pure } costs <= 9 ops { return clz(v) + ctz(v) + log2_floor(v); }
}";

/// Checker verdicts over a source: `(error codes, all diagnostic texts)`.
fn bits_absagen(q: &str) -> (Vec<String>, Vec<String>) {
    let (baum, mut a) = gabbro_syntax::lies("bits.gab", q);
    assert_eq!(a.fehler_zahl(), 0, "the probe itself does not parse:\n{}", a.zeige(q));
    let _ = gabbro_check::pruefe(&baum, &mut a);
    let codes: Vec<String> = a
        .absagen
        .iter()
        .filter(|x| x.stufe == gabbro_syntax::diag::Stufe::Fehler)
        .map(|x| x.code.to_string())
        .collect();
    // The message AND its notes: the remedy (`narrow`) stands in a note, and
    // a probe that only reads the first line cannot tell whether it is named.
    let mut texte: Vec<String> = Vec::new();
    for x in &a.absagen {
        texte.push(x.text.clone());
        texte.extend(x.notizen.iter().cloned());
    }
    (codes, texte)
}

const BITS_TREIBER: &str = r#"
#include <stdio.h>

int main(void) {
    int bad = 0;
#define C(name, expr, want) \
    do { unsigned long long g = (unsigned long long)(expr); \
         unsigned long long w = (unsigned long long)(want); \
         if (g != w) { bad++; \
             printf("MISS %s: got=%llu want=%llu\n", name, g, w); } \
    } while (0)
    C("clz32", clz32(1u), 31u);
    C("ctz32", ctz32(12u), 2u);
    C("log32", log32(1000u), 9u);
    C("pop32", pop32(0xFFFFFFFFu), 32u);
    C("rot32", rot32(0x80000001u, 1u), 3u);
    C("rot32-null", rot32(0x80000001u, 0u), 0x80000001u);
    C("ror32", ror32(0x80000001u, 1u), 0xC0000000u);
    C("ror32-null", ror32(0x80000001u, 0u), 0x80000001u);
    C("swp32", swp32(0x12345678u), 0x78563412u);
    C("clz16", clz16(0x0100u), 7u);
    C("rot16", rot16(0x8001u, 1u), 3u);
    C("swp16", swp16(0x1234u), 0x3412u);
    C("clz8", clz8(1u), 7u);
    C("pop64", pop64(0xFFFFFFFFFFFFFFFFull), 64u);
    C("rot64", rot64(0x8000000000000001ull, 1ull), 3ull);
    C("swp64", swp64(0x0102030405060708ull), 0x0807060504030201ull);
    C("mix64", mix64(1ull), 63u);
    printf("checked=17 bad=%d\n", bad);
    return 0;
}
"#;

/// Compile one C text with one compiler and run it, demanding the exact line.
fn bits_baue_und_laufe(c: &str, cc: &str, stufen: &[&str], name: &str) {
    let d = std::env::temp_dir().join("gabbro-bits-87");
    std::fs::create_dir_all(&d).expect("the work directory is writable");
    let quelle = d.join(format!("lauf-{name}.c"));
    let ziel = d.join(format!("lauf-{name}"));
    std::fs::write(&quelle, c).expect("the emitted C is writable");
    let mut args: Vec<std::ffi::OsString> =
        vec!["-std=c11".into(), "-Wall".into(), "-Wextra".into(), "-Werror".into()];
    for s in stufen {
        args.push((*s).into());
    }
    args.push("-o".into());
    args.push(ziel.clone().into_os_string());
    args.push(quelle.clone().into_os_string());
    let bau = std::process::Command::new(cc).args(&args).output();
    let bau = match bau {
        Ok(r) => r,
        // **A missing compiler is a missing measurement, never a green one** (W1).
        Err(e) => panic!("`{cc}` cannot be started ({e}) -- NOTHING measured"),
    };
    assert!(
        bau.status.success(),
        "the emitted C does not compile under `{cc} -Werror`:\n{}\n{}",
        String::from_utf8_lossy(&bau.stderr),
        quelle.display()
    );
    let lauf = std::process::Command::new(&ziel)
        .output()
        .unwrap_or_else(|e| panic!("the compiled program does not run ({e}) -- NOTHING measured"));
    assert!(lauf.status.success(), "the compiled program aborts under {cc}/{name}");
    let aus = String::from_utf8_lossy(&lauf.stdout);
    assert!(
        aus.contains("checked=17 bad=0"),
        "the shipped C computes something other than what was checked ({cc}/{name}):\n{aus}"
    );
    let _ = std::fs::remove_file(&quelle);
    let _ = std::fs::remove_file(&ziel);
}

/// **Rotation needs a whole word.** Over `u32 in 0 .. 5` the wrap point is
/// ambiguous (mod 6 costs a division per operation), so it is not derivable
/// there -- `M159` alone.
#[test]
fn bit_intrinsic_rotl_refuses_a_narrowed_range() {
    let (codes, _) = bits_absagen(
        "module t {
impl fn p(x : u32 in 0 .. 5, s : u32 in 0 .. 31) -> u32 effects { pure } costs <= 9 ops { return rotl(x, s); }
}",
    );
    assert_eq!(codes, vec!["M159"], "rotl over `u32 in 0 .. 5` must fall with `M159` alone: {codes:?}");
    // The amount is typed too: 32 is not a shift in a 32-bit word.
    let (codes, _) = bits_absagen(
        "module t {
impl fn p(x : u32, s : u32 in 0 .. 32) -> u32 effects { pure } costs <= 9 ops { return rotl(x, s); }
}",
    );
    assert_eq!(codes, vec!["M159"], "rotl with an amount reaching 32 must fall with `M159` alone: {codes:?}");
    // A sub-width sugar range is EXACT (`u13 in 0 .. 8191`) and still falls:
    // the checker reads the storage width (`u16`), and a 13-bit rotation in a
    // 16-bit word is a different function from a 16-bit one. The type system
    // erases `u13` from `u16 in 0 .. 8191`, so no rule could tell which width
    // to rotate in -- refusing is the only direction that does not guess it.
    let (codes, _) = bits_absagen(
        "module t {
impl fn p(x : u13, s : u8 in 0 .. 7) -> u16 effects { pure } costs <= 9 ops { return rotl(x, s); }
}",
    );
    assert_eq!(codes, vec!["M159"], "rotl over exact `u13` must fall with `M159` alone: {codes:?}");
}

/// **A one-byte value has no byte order.** `bswap` over `u8` falls with `M160`
/// alone; the signed twin (`i32`) falls at the same code, for the unsigned
/// half of the rule.
#[test]
fn bit_intrinsic_bswap_refuses_u8() {
    let (codes, _) = bits_absagen(
        "module t {
impl fn p(x : u8) -> u8 effects { pure } costs <= 9 ops { return bswap(x); }
}",
    );
    assert_eq!(codes, vec!["M160"], "bswap over `u8` must fall with `M160` alone: {codes:?}");
    let (codes, _) = bits_absagen(
        "module t {
impl fn p(x : i32) -> i32 effects { pure } costs <= 9 ops { return bswap(x); }
}",
    );
    assert_eq!(codes, vec!["M160"], "bswap over `i32` must fall with `M160` alone: {codes:?}");
}

/// **A declaration carrying an intrinsic name stands uncalled.** The call form
/// never reaches it, so the declaration is refused (`N058`) -- the
/// prohibition-without-replacement shape, caught at the declaration instead of
/// at every call that routes around it.
#[test]
fn bit_intrinsic_name_cannot_be_declared() {
    let (codes, _) = bits_absagen(
        "module t {
impl fn clz(x : u32) -> u32 effects { pure } costs <= 9 ops { return x; }
}",
    );
    assert_eq!(codes, vec!["N058"], "a `fn clz` must fall with `N058` alone: {codes:?}");
}

/// **Wall 5: the annotation on `let … else` is honoured.** `ast::LetSonst` used to carry no `typ`: the parser read
/// `let m : T = f() else (e) { … }` and threw the `T` away, so a callee that answers a `u64` bound to a `bool` said nothing.
/// Now the callee's answer is held against the annotation like a plain `let`'s -- `M135` across kinds, `M101` for a range the
/// `ensures` does not prove -- and the name is bound at the annotated type (its range).
#[test]
fn die_anmerkung_am_let_else_wird_gehalten() {
    fn codes(q: &str) -> Vec<String> {
        let (b, mut a) = gabbro_syntax::lies("p.gab", q);
        gabbro_check::pruefe(&b, &mut a);
        a.absagen
            .iter()
            .filter(|x| x.stufe == gabbro_syntax::diag::Stufe::Fehler)
            .map(|x| x.code.to_string())
            .collect()
    }
    let kopf = "module t {
reason F { Weg = 1 \"weg\" exhaustive }
impl fn kanal(w : u64 in 0 .. 100) -> u64 or F ensures result <= 2048 effects { pure } costs <= 8 ops
{ if w == 0 { return F::Weg; } return 9; }
";
    // A `bool` over a number: another kind.
    let q1 = format!("{kopf}impl fn f() -> u64 effects {{ pure }} costs <= 60 ops
{{ let m : bool = kanal(1) else (e) {{ return 0; }} return 1; }} }}");
    assert_eq!(codes(&q1), vec!["M135"], "a bool is not a number");
    // A range the `ensures` does not prove.
    let q2 = format!("{kopf}impl fn f() -> u64 effects {{ pure }} costs <= 60 ops
{{ let m : u64 in 0 .. 100 = kanal(1) else (e) {{ return 0; }} return m; }} }}");
    assert_eq!(codes(&q2), vec!["M101"], "0 .. 2048 does not fit 0 .. 100");
    // A range it DOES prove, and the name has it: `m + 1` fits a `u64` and `m` fits a `u32 in 0 .. 2048`.
    let q3 = format!("{kopf}impl fn f() -> u32 effects {{ pure }} costs <= 60 ops
{{ let m : u64 in 0 .. 2048 = kanal(1) else (e) {{ return 0; }} let n : u32 in 0 .. 2048 = m; return n; }} }}");
    assert_eq!(codes(&q3), Vec::<String>::new(), "the annotation is a range the name has from here on");
    // No annotation: as before.
    let q4 = format!("{kopf}impl fn f() -> u64 effects {{ pure }} costs <= 60 ops
{{ let m = kanal(1) else (e) {{ return 0; }} return m; }} }}");
    assert_eq!(codes(&q4), Vec::<String>::new(), "an unannotated let … else binds the callee's answer, as before");
}

/// **The `else` of a `narrow` may end in a `-> never` function inside a `module`** (C-free lane).
///
/// `endet_immer` looked the callee up by its bare name, and the keys are qualified, so inside a
/// `module` block the exit routine of a program was never found and the branch was refused
/// (`M105`) as one that returns. The twin below, whose `else` returns nothing and calls a
/// function that does come back, still falls.
#[test]
fn der_else_eines_narrow_endet_in_einer_nie_funktion_im_modul() {
    fn codes(quelle: &str) -> Vec<String> {
        let (baum, mut a) = gabbro_syntax::lies("p.gab", quelle);
        gabbro_check::pruefe(&baum, &mut a);
        a.absagen.iter().map(|x| x.code.to_string()).collect()
    }
    let kopf = "module t {\n\
        fn ende() -> never effects { diverges } costs <= 10 ops { ende(); }\n\
        fn weiter() -> u64 effects { pure } costs <= 2 ops { return 0; }\n";
    let gut = codes(&format!(
        "{kopf}fn f(x : u64) -> u64 effects {{ pure }} costs <= 20 ops {{ narrow x to 0 .. 9 else {{ ende(); }} return x; }} }}"
    ));
    assert!(!gut.iter().any(|c| c == "M105"), "a `-> never` call ends the branch: {gut:?}");
    let schlecht = codes(&format!(
        "{kopf}fn f(x : u64) -> u64 effects {{ pure }} costs <= 20 ops {{ narrow x to 0 .. 9 else {{ weiter(); }} return x; }} }}"
    ));
    assert!(schlecht.iter().any(|c| c == "M105"), "a returning call does not: {schlecht:?}");
}
