//! **Pass — `locks shared`, die geteilte Sperrnahme.**
//!
//! Das Konstrukt kam nicht aus einem Entwurf, sondern aus einer **Messung**
//! ([`MESSUNGEN.md`](MESSUNGEN.md), Papiertest CapSpace/CDT vom 2026-08-14). Dort starb der
//! Kandidat `locks ordered` an null Prüffällen — und derselbe Test fand die Lücke, die auf
//! keiner Liste stand:
//!
//! > *Die heisseste Sperre des Baums ist ein **Reader-Writer**-Lock
//! > (`static CAPS: RwSpinLock<Caps>`), und der heisse Pfad ist die **geteilte** Seite:
//! > **33 `read()`-Stellen gegen 44 `write()`**. `lock`/`locks` und der `Held`-Zeuge waren
//! > exklusiv gedacht — der meistgelaufene Pfad des Kernels war nicht schreibbar.*
//!
//! ## Warum das ein Konstrukt sein darf und nicht bloss ein Kommentar
//!
//! Weil die Zusage **mechanisch prüfbar** ist, und zwar gegen etwas, das ohnehin dasteht:
//!
//! > **Geteilt halten heisst: die geschützten Plätze lesen, sie nicht schreiben.**
//!
//! `protects { … }` nennt die Plätze; der Rumpf nennt seine Schreibziele. Der Abgleich ist
//! derselbe Handgriff wie in `E006` — kein neuer Beweisbegriff, kein Vertrauen, keine
//! Annahme. **Das ist das Kriterium, an dem `abi { … }` und `locks ordered` gescheitert
//! sind, und dieses Konstrukt besteht es.**
//!
//! ## Die fuenf Absagen
//!
//! **Kennbuchstabe `H` (Halten), nicht `S`.** Beim Bau am 2026-08-14 habe ich `S001`–`S005`
//! vergeben, ohne den Kennungsraum zu pruefen — `schleifen.rs` fuehrt `S001`/`S002` seit
//! Pass 6 fuer die Schleifenmarke und den durchfallenden `else`-Zweig. Zusammen mit der
//! `K003`-Doppelbelegung war das **dreimal dieselbe Klasse an einem Tag**: eine Kennung
//! vergeben, ohne nachzusehen, wer sie schon hat. **Die Giftproben pruefen auf Kennungen** —
//! jede Doppelbelegung macht sie mehrdeutig.
//!
//! * **`H001`** — Schreiben auf einen geschützten Platz unter geteilter Nahme. *Die
//!   tragende Regel.*
//! * **`H002`** — geteilt genommen, aber die Sperre erklärt kein `shared held <= … ops`.
//!   Ohne die Zahl hat die Latenzaussage aus §9.3 für diese Sperre keinen Zweig
//!   (Nebenbefund **N3**: `held` war für **exklusive** Halter gedacht; auf der geteilten
//!   Seite ist die Rechengrösse die **Schreiberwartezeit unter Leserdruck**).
//! * **`H003`** — Hochstufung: exklusive Nahme derselben Sperre **innerhalb** einer
//!   geteilten. Auf einer Drehsperre ist das kein Stilfehler, sondern ein Deadlock.
//! * **`H004`** — `shared held` erklärt, aber die Sperre wird nirgends geteilt genommen.
//!   *Eine Zahl ohne Messstelle ist eine Behauptung; dieselbe Regel wie beim toten
//!   Kandidaten — kein Konstrukt ohne gemessenen Bedarf.*
//! * **`H005`** — **die Zwischenregel an der Aufrufgrenze.** Siehe unten.
//!
//! ## `H005` — **die Zwischenregel ist ERSETZT (2026-08-15), nicht gelockert**
//!
//! Die tragende Regel `H001` sieht nur, was der Block **selbst** schreibt. Ein Aufruf trägt
//! sie nicht mit: ruft ein geteilter Block eine Funktion mit `requires Held(N)`, so schreibt
//! **der Gerufene** exklusiv-berechtigt, während **der Rufer** nur geteilt hält. **Das ist
//! `H001` durch die Hintertür**, und bis Pass 8 steht, ist dieses Loch nicht bloss offen,
//! sondern **durchlässig**: der Zeuge existiert, seine Stärke wird nicht geprüft.
//!
//! Die grobe Fassung lautete: *„Ein geteilter Block ruft **keine** Funktion mit
//! `requires Held(…)`. Punkt."* — zu streng, denn sie verbot auch den harmlosen Aufruf über
//! eine **andere** Sperre. Der Preis stand in der Absage, und die ersetzende Prüfung war
//! dort **angekündigt**. *W5: eine Zwischenregel trägt die Ablösung in ihrer eigenen
//! Absage.* **Hier ist sie.**
//!
//! Die echte Regel, seit `aufrufgraph.rs` steht:
//!
//! > **Ein geteilter Block darf `requires Held(L, shared)` rufen. Eine exklusive
//! > Forderung — `requires Held(L)` — bleibt gesperrt, und zwar nur für die Sperre, die
//! > hier geteilt gehalten wird.**
//!
//! Die Asymmetrie steht damit eine Ebene höher noch einmal so, wie `E007` sie unten
//! schneidet: **wer mehr fordert, als der Rufer hält, fällt; wer weniger fordert, nicht.**
//!
//! *Was die Ablösung gekostet hat:* eine eigene Grammatikregel für den Zeugen
//! (`heldpred = "Held" "(" ident [ "," "shared" ] ")"`), weil `shared` ein Wort des
//! Wortschatzes ist und bleiben soll — **keine Aufweichung des Ausdrucks**.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::BTreeMap;

/// Nennt die `requires`-Klausel einen `Held(…)`-Zeugen? — der Prädikatbaum, flach gelesen.
/// Was über eine Sperre im Baum steht.
struct Sperre {
    schuetzt: Vec<String>,
    hat_geteilte_zeit: bool,
    /// Der `rank`. **`None`, wenn er nicht konstant auswertbar ist** -- dann sagt `H006`
    /// nichts, statt eine Ordnung zu erfinden (W9: die Grobheit hat eine Richtung, und die
    /// sichere ist hier Schweigen ueber eine unbekannte Zahl, nicht eine angenommene).
    rang: Option<i128>,
    span: Span,
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let mut sperren: BTreeMap<String, Sperre> = BTreeMap::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Lock(l) = &item.art {
            sperren.insert(
                l.name.text.clone(),
                Sperre {
                    schuetzt: l.schuetzt.iter().map(|o| o.text()).collect(),
                    hat_geteilte_zeit: l.geteilte_haltezeit.is_some(),
                    rang: u.konst_wert("", &l.rang),
                    span: l.name.span,
                },
            );
        }
    });

    // Wer einen `Held(…)`-Zeugen verlangt, darf aus einem geteilten Block nicht gerufen
    // werden -- bis Pass 8 die Staerke des Zeugen wirklich prueft (S005).
    // **Aus dem Aufrufgraphen, nicht aus einem eigenen Durchgang.** Er traegt die Staerke
    // je Forderung -- genau das, was die Zwischenregel nicht hatte.
    let g = crate::aufrufgraph::erhebe(baum);
    let verlangt: BTreeMap<String, Vec<(String, bool)>> = g
        .knoten
        .iter()
        .filter(|(_, k)| !k.verlangt.is_empty())
        .map(|(n, k)| (n.clone(), k.verlangt.clone()))
        .collect();

    let mut geteilt_genommen: Vec<String> = Vec::new();
    let mut ueberhaupt_genommen: Vec<String> = Vec::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let FnRumpf::Block(b) = &f.rumpf else {
            return;
        };
        block(b, &[], &[], &[], &sperren, &verlangt, &mut geteilt_genommen, absagen);
    });

    // **H007 -- K11.2.1: `protects` beisst.**
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else { return };
        // **Ein `spec fn` fasst zur Laufzeit nichts an.** Es ist Beweisersache, und eine
        // Sperre dort zu verlangen hiesse, eine Laufzeitdisziplin auf einen Geistausdruck
        // anzuwenden. *Gefunden bei der Vorabmessung: beide gemeldeten Stellen des Korpus
        // waren dieselbe `spec fn`.*
        if matches!(f.klasse, Some(FnKlasse::Spec)) {
            return;
        }
        let FnRumpf::Block(b) = &f.rumpf else { return };
        let mut da: Vec<String> = Vec::new();
        sperrnahmen(b, &mut ueberhaupt_genommen);
        if let Some(w) = &f.effects {
            for e in &w.liste {
                // **Geteilt genommen zaehlt mit.** `H001` entscheidet danach, ob ein
                // SCHREIBEN unter geteilter Nahme zulaessig ist -- das ist die Staerke, und
                // sie ist eine andere Frage als die Nahme selbst.
                if let WirkungArt::Sperrt(o) | WirkungArt::SperrtGeteilt(o) = &e.art {
                    da.push(o.text());
                    if !ueberhaupt_genommen.contains(&o.text()) {
                        ueberhaupt_genommen.push(o.text());
                    }
                }
            }
        }
        for p in &f.requires {
            let mut h = Vec::new();
            crate::aufrufgraph::held_aus_pred(p, &mut h);
            da.extend(h.into_iter().map(|(n, _)| n));
        }
        schutz(b, &da, &sperren, &f.name.text, absagen);
    });

    // **H008 -- die Gegenrichtung von H007, und sie haette den Befund zuerst gefunden.**
    //
    // `lock BERICHT protects { farbbericht } rank 2 held <= 50 ops;` stand seit dem Bestehen
    // von `beispiele/05` im Ordner und wurde **nirgends genommen** -- der Platz ist ueber die
    // Paarung `publishes`/`awaits` synchronisiert, nicht ueber eine Sperre. *Zwei Mechanismen
    // fuer denselben Platz, und einer davon war Zierde.*
    //
    // > **Eine `protects`-Klausel, die niemand einhaelt, ist schlimmer als keine:** sie
    // > sieht aus wie eine Zusage und ist eine Behauptung. Dieselbe Bauart wie `S004`.
    for (name, sp) in &sperren {
        if !ueberhaupt_genommen.contains(name)
            && !verlangt.values().any(|v| v.iter().any(|(n, _)| n == name))
        {
            absagen.schiebe(
                Absage::hinweis(
                    "H008",
                    sp.span,
                    format!("`{name}` schuetzt {:?}, wird aber nirgends genommen", sp.schuetzt),
                )
                .mit_notiz(
                    "weder ein `locks`-Block noch ein `effects { locks … }` noch ein \
                     `requires Held(…)` nennt sie",
                )
                .mit_notiz(
                    "ist der Platz anders synchronisiert -- etwa ueber `publishes`/`awaits` \
                     --, gehoert die Sperre weg; sonst fehlt die Nahme",
                ),
            );
        }
    }

    // S004 -- eine Zahl ohne Messstelle. Kein Konstrukt ohne gemessenen Bedarf, und keine
    // Zusage ohne Ort, an dem sie faellt.
    for (name, s) in &sperren {
        if s.hat_geteilte_zeit && !geteilt_genommen.contains(name) {
            absagen.schiebe(
                Absage::hinweis(
                    "H004",
                    s.span,
                    format!("`{name}` declares `shared held` but is never taken shared"),
                )
                .mit_notiz(
                    "eine Zusage ohne Stelle, an der sie faellt, ist eine Behauptung -- \
                     dieselbe Regel, an der `locks ordered` gestorben ist",
                ),
            );
        }
    }
}

/// `offen` ist der Stapel der geteilt gehaltenen Sperren — er trägt die Verschachtelung.
/// Alle Sperren, die ein Rumpf nimmt -- fuer `H008`.
fn sperrnahmen(b: &Block, aus: &mut Vec<String>) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Sperrt(l) => {
                let n = l.sperre.text();
                if !aus.contains(&n) {
                    aus.push(n);
                }
                sperrnahmen(&l.rumpf, aus);
            }
            StmtArt::Wenn(w) => {
                for (_, r) in &w.zweige {
                    sperrnahmen(r, aus);
                }
                if let Some(r) = &w.sonst {
                    sperrnahmen(r, aus);
                }
            }
            StmtArt::Match(m) => {
                for z in &m.zweige {
                    sperrnahmen(&z.rumpf, aus);
                }
            }
            StmtArt::Bricht(x) => sperrnahmen(&x.rumpf, aus),
            StmtArt::Narrow(x) => sperrnahmen(&x.sonst, aus),
            StmtArt::LetSonst(x) => sperrnahmen(&x.sonst, aus),
            StmtArt::Schleife(sch) => match sch.as_ref() {
                Schleife::Traverse(t) => sperrnahmen(&t.rumpf, aus),
                Schleife::Retry(r) => sperrnahmen(&r.rumpf, aus),
                Schleife::Forever(f) => sperrnahmen(&f.rumpf, aus),
            },
            _ => {}
        }
    }
}

/// **`H007` — jeder Zugriff auf einen geschuetzten Platz steht unter seiner Sperre.**
///
/// **Gemessen am 2026-08-17, und es war der Befund, mit dem K11.2 anfing:**
///
/// ```gabbro
/// lock KAPPEN protects { K } rank 3 held <= 40 ops;
/// impl fn schreib(i : index into K) -> bool effects { writes K } costs <= 4 ops
/// { K.slots[i].a = 1; return true; }          -- kein `locks KAPPEN`
/// → 4 Items, 0 Fehler, 0 Hinweise
/// ```
///
/// `H001`–`H006` pruefen die **Disziplin** einer genommenen Sperre — geteilt gegen exklusiv,
/// Rang, Haltezeit. **Sie pruefen nicht, dass sie genommen wird.**
///
/// > *Die Klasse Rennen hing damit nicht am Speichermodell — sie hing an einer Regel, die
/// > niemand gebaut hatte.*
///
/// **Als „genommen" gilt dreierlei**, und das ist keine Nachsicht, sondern die Bauart der
/// Sprache: ein umschliessender `locks`-Block, ein `effects { locks L }` (dann ist die Nahme
/// die Pflicht des Rufers, und `E006` haelt Rumpf gegen Klausel), und ein
/// `requires Held(L)` — der Zeuge IST die Aussage, dass sie gehalten wird.
fn schutz(
    b: &Block,
    da: &[String],
    sperren: &BTreeMap<String, Sperre>,
    wo: &str,
    absagen: &mut Absagen,
) {
    let deckt = |ort: &str| -> Option<String> {
        sperren
            .iter()
            .find(|(_, sp)| sp.schuetzt.iter().any(|p| beruehrt(p, ort)))
            .map(|(n, _)| n.clone())
    };
    let pruefe = |o: &Ort, absagen: &mut Absagen| {
        let t = o.text();
        let Some(sperre) = deckt(&t) else { return };
        if da.iter().any(|d| d == &sperre) {
            return;
        }
        absagen.schiebe(
            Absage::fehler(
                "H007",
                o.span,
                format!("`{t}` ist von `{sperre}` geschuetzt, `{wo}` haelt sie nicht"),
            )
            .mit_notiz(
                "als gehalten gilt: ein umschliessender `locks`-Block, ein \
                 `effects { locks … }` (dann ist die Nahme die Pflicht des Rufers) oder ein \
                 `requires Held(…)`",
            )
            .mit_notiz(
                "`protects` nannte die Plaetze schon; bis K11.2.1 pruefte niemand, dass die \
                 Sperre auch GENOMMEN wird",
            ),
        );
    };
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Sperrt(l) => {
                let mut innen = da.to_vec();
                innen.push(l.sperre.text());
                schutz(&l.rumpf, &innen, sperren, wo, absagen);
            }
            StmtArt::Zuweisung(z) => {
                pruefe(&z.ziel, absagen);
                orte_in(&z.wert, &mut |o| pruefe(o, absagen));
            }
            StmtArt::Publish(p) => {
                pruefe(&p.ziel, absagen);
                orte_in(&p.wert, &mut |o| pruefe(o, absagen));
            }
            StmtArt::Let(l) => orte_in(&l.wert, &mut |o| pruefe(o, absagen)),
            StmtArt::Return(Some(x)) => orte_in(x, &mut |o| pruefe(o, absagen)),
            StmtArt::Ruf(r) => {
                for a in &r.argumente {
                    orte_in(a, &mut |o| pruefe(o, absagen));
                }
            }
            StmtArt::Wenn(w) => {
                for (bed, r) in &w.zweige {
                    orte_in(bed, &mut |o| pruefe(o, absagen));
                    schutz(r, da, sperren, wo, absagen);
                }
                if let Some(r) = &w.sonst {
                    schutz(r, da, sperren, wo, absagen);
                }
            }
            StmtArt::Match(m) => {
                for z in &m.zweige {
                    schutz(&z.rumpf, da, sperren, wo, absagen);
                }
            }
            StmtArt::Bricht(x) => schutz(&x.rumpf, da, sperren, wo, absagen),
            StmtArt::Narrow(x) => schutz(&x.sonst, da, sperren, wo, absagen),
            StmtArt::LetSonst(x) => schutz(&x.sonst, da, sperren, wo, absagen),
            StmtArt::Schleife(sch) => match sch.as_ref() {
                Schleife::Traverse(t) => schutz(&t.rumpf, da, sperren, wo, absagen),
                Schleife::Retry(r) => schutz(&r.rumpf, da, sperren, wo, absagen),
                Schleife::Forever(f) => schutz(&f.rumpf, da, sperren, wo, absagen),
            },
            _ => {}
        }
    }
}

/// Die Orte eines Ausdrucks, **einschliesslich der Indizes** -- `c.slots[naechster]` liest
/// beides.
fn orte_in(e: &Expr, f: &mut impl FnMut(&Ort)) {
    match &e.art {
        ExprArt::Ort(o) => {
            f(o);
            for suf in &o.suffixe {
                if let OrtSuffix::Index(ix) = suf {
                    orte_in(ix, f);
                }
            }
        }
        ExprArt::Klammer(x) | ExprArt::Unaer(_, x) => orte_in(x, f),
        ExprArt::Binaer(_, a, b) => {
            orte_in(a, f);
            orte_in(b, f);
        }
        ExprArt::Ruf(r) => {
            for a in &r.argumente {
                orte_in(a, f);
            }
        }
        _ => {}
    }
}

fn block(
    b: &Block,
    offen: &[String],
    // **Alle** gehaltenen Sperren in Nahmereihenfolge, geteilt wie exklusiv -- die
    // Rangordnung gilt fuer beide Nahmearten gleich. `offen`/`exklusiv` trennen die
    // Staerke; `kette` traegt die REIHENFOLGE.
    kette: &[(String, Option<i128>)],
    // Exklusiv gehaltene Sperren -- eine Schreibstelle unter ihnen ist gedeckt, auch wenn
    // dieselbe Sperre aussen herum geteilt gehalten wird. **Diese Verschachtelung faellt
    // ohnehin mit `H003`; sie soll nicht ZWEIMAL fallen** -- eine Absage, die eine zweite
    // nach sich zieht, laesst den Leser den Fehler an der falschen Stelle suchen.
    exklusiv: &[String],
    sperren: &BTreeMap<String, Sperre>,
    verlangt: &BTreeMap<String, Vec<(String, bool)>>,
    genommen: &mut Vec<String>,
    absagen: &mut Absagen,
) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Sperrt(l) => {
                let name = l.sperre.text();
                if l.geteilt {
                    if !genommen.contains(&name) {
                        genommen.push(name.clone());
                    }
                    match sperren.get(&name) {
                        Some(sp) if !sp.hat_geteilte_zeit => absagen.schiebe(
                            Absage::fehler(
                                "H002",
                                l.sperre.span,
                                format!(
                                    "`{name}` wird geteilt genommen, erklaert aber kein \
                                     `shared held <= … ops`"
                                ),
                            )
                            .mit_notiz(
                                "`held` ist fuer EXKLUSIVE Halter gedacht; auf der geteilten \
                                 Seite ist die Rechengroesse die Schreiberwartezeit unter \
                                 Leserdruck, nicht die Haltezeit eines Lesers",
                            )
                            .mit_notiz(
                                "ohne diese Zahl hat die Latenzaussage aus SPRACHE.md §9.3 \
                                 fuer diese Sperre keinen Zweig",
                            ),
                        ),
                        _ => {}
                    }
                    let mut tiefer = offen.to_vec();
                    tiefer.push(name.clone());
                    let kette2 = rangprobe(&name, l.sperre.span, kette, sperren, absagen);
                    block(&l.rumpf, &tiefer, &kette2, exklusiv, sperren, verlangt, genommen, absagen);
                } else {
                    // S003 -- Hochstufung. Auf einer Drehsperre ist das kein Stilfehler.
                    if offen.contains(&name) {
                        absagen.schiebe(
                            Absage::fehler(
                                "H003",
                                l.sperre.span,
                                format!(
                                    "`{name}` wird exklusiv genommen, obwohl sie hier schon \
                                     geteilt gehalten wird"
                                ),
                            )
                            .mit_notiz(
                                "eine Hochstufung von geteilt nach exklusiv wartet auf die \
                                 eigene Lesernahme -- auf einer Drehsperre ist das ein \
                                 Deadlock, kein Stilfehler",
                            )
                            .mit_notiz(
                                "die ehrliche Form ist Uebergabe mit Neuvalidierung: freigeben, \
                                 exklusiv nehmen, die tragende Bedingung ERNEUT pruefen",
                            ),
                        );
                    }
                    let mut tiefer = exklusiv.to_vec();
                    tiefer.push(name.clone());
                    let kette2 = rangprobe(&name, l.sperre.span, kette, sperren, absagen);
                    block(&l.rumpf, offen, &kette2, &tiefer, sperren, verlangt, genommen, absagen);
                }
            }
            StmtArt::Zuweisung(z) => {
                schreibprobe(&z.ziel, s.span, offen, exklusiv, sperren, absagen);
                rufprobe_expr(&z.wert, s.span, offen, verlangt, absagen);
            }
            StmtArt::Ruf(r) => rufprobe(r, s.span, offen, verlangt, absagen),
            StmtArt::Let(l) => rufprobe_expr(&l.wert, s.span, offen, verlangt, absagen),
            StmtArt::Return(Some(e)) => rufprobe_expr(e, s.span, offen, verlangt, absagen),
            StmtArt::Publish(p) => schreibprobe(&p.ziel, s.span, offen, exklusiv, sperren, absagen),
            StmtArt::Exchange(e) => {
                schreibprobe(&e.ort, s.span, offen, exklusiv, sperren, absagen);
                if let XForm::Update { rumpf, .. } = &e.form {
                    block(rumpf, offen, kette, exklusiv, sperren, verlangt, genommen, absagen);
                }
            }
            StmtArt::Wenn(w) => {
                for (b, _) in &w.zweige {
                    rufprobe_expr(b, s.span, offen, verlangt, absagen);
                }
                for (_, r) in &w.zweige {
                    block(r, offen, kette, exklusiv, sperren, verlangt, genommen, absagen);
                }
                if let Some(r) = &w.sonst {
                    block(r, offen, kette, exklusiv, sperren, verlangt, genommen, absagen);
                }
            }
            StmtArt::Match(m) => {
                for z in &m.zweige {
                    block(&z.rumpf, offen, kette, exklusiv, sperren, verlangt, genommen, absagen);
                }
            }
            StmtArt::Bricht(x) => block(&x.rumpf, offen, kette, exklusiv, sperren, verlangt, genommen, absagen),
            StmtArt::Narrow(x) => block(&x.sonst, offen, kette, exklusiv, sperren, verlangt, genommen, absagen),
            StmtArt::LetSonst(x) => {
                if let Some(r) = x.als_ruf() {
                    rufprobe(r, s.span, offen, verlangt, absagen);
                }
                block(&x.sonst, offen, kette, exklusiv, sperren, verlangt, genommen, absagen);
            }
            StmtArt::Schleife(sch) => match sch.as_ref() {
                Schleife::Traverse(x) => block(&x.rumpf, offen, kette, exklusiv, sperren, verlangt, genommen, absagen),
                Schleife::Retry(x) => block(&x.rumpf, offen, kette, exklusiv, sperren, verlangt, genommen, absagen),
                Schleife::Forever(x) => block(&x.rumpf, offen, kette, exklusiv, sperren, verlangt, genommen, absagen),
            },
            _ => {}
        }
    }
}

/// **S001 — die tragende Regel.** Ein Schreibziel unter geteilter Nahme, das die Sperre
/// schützt, ist ein Übersetzungsfehler. Der Abgleich ist derselbe wie in `E006`.
fn schreibprobe(
    ziel: &Ort,
    span: Span,
    offen: &[String],
    exklusiv: &[String],
    sperren: &BTreeMap<String, Sperre>,
    absagen: &mut Absagen,
) {
    let ort = ziel.text();
    for name in offen {
        if exklusiv.contains(name) {
            continue; // innen exklusiv genommen -- die Schreibstelle ist gedeckt (siehe S003)
        }
        let Some(sp) = sperren.get(name) else { continue };
        let Some(platz) = sp.schuetzt.iter().find(|p| beruehrt(p, &ort)) else {
            continue;
        };
        absagen.schiebe(
            Absage::fehler(
                "H001",
                span,
                format!("`{ort}` is written while `{name}` is held only shared"),
            )
            .mit_notiz(format!(
                "`{name}` schuetzt `{platz}` -- geteilt halten heisst: die geschuetzten \
                 Plaetze lesen, sie nicht schreiben"
            ))
            .mit_notiz(
                "genau dieser Abgleich macht `locks shared` zu einem Konstrukt und nicht zu \
                 einem Kommentar: `protects` nennt die Plaetze, der Rumpf nennt seine Ziele",
            ),
        );
        return;
    }
}

/// Trifft das Schreibziel `getan` den geschützten Platz `platz`? Der Platz kann als
/// Grundname (`slots`) oder als Pfad (`c.slots`) stehen; das Ziel trägt seinen Zeiger vorn.
fn beruehrt(platz: &str, getan: &str) -> bool {
    let kern = platz.rsplit('.').next().unwrap_or(platz);
    getan.split(['.', '[']).any(|t| t == kern)
}

/// **S005 — die Zwischenregel.** Absichtlich grob: *jeder* `Held(…)`-Zeuge zählt, nicht nur
/// der der gerade geteilt gehaltenen Sperre. Der Preis ist benannt, die Richtung ist sicher.
/// **H005 — die ECHTE Prüfung, seit der Aufrufgraph steht (2026-08-15).**
///
/// Die Zwischenregel sperrte **jeden** `Held(…)`-Zeugen unter geteilter Nahme und nannte
/// ihren Preis in der eigenen Absage. Ersetzt, nicht gelockert:
///
/// > Ein geteilter Block darf `requires Held(L, shared)` rufen. Eine **exklusive** Forderung
/// > auf **der hier geteilt gehaltenen** Sperre fällt.
fn rufprobe(
    r: &Ruf,
    span: Span,
    offen: &[String],
    verlangt: &BTreeMap<String, Vec<(String, bool)>>,
    absagen: &mut Absagen,
) {
    if offen.is_empty() {
        return;
    }
    let Some(name) = r.pfad.teile.last() else {
        return;
    };
    let Some(forderungen) = verlangt.get(&name.text) else {
        return;
    };
    for (sperre, geteilt) in forderungen {
        if *geteilt || !offen.iter().any(|o| o == sperre) {
            continue;
        }
        absagen.schiebe(
            Absage::fehler(
                "H005",
                span,
                format!(
                    "`{}` verlangt `Held({sperre})` exklusiv, wird hier aber unter geteilter \
                     Nahme von `{sperre}` gerufen",
                    name.text
                ),
            )
            .mit_notiz(
                "der Gerufene schreibt exklusiv-berechtigt, der Rufer haelt nur geteilt -- \
                 das waere H001 durch die Hintertuer",
            )
            .mit_notiz(
                "`requires Held(L, shared)` waere hier zulaessig -- die Staerke des Zeugen \
                 entscheidet, seit der Aufrufgraph steht",
            ),
        );
    }
}

fn rufprobe_expr(
    e: &Expr,
    span: Span,
    offen: &[String],
    verlangt: &BTreeMap<String, Vec<(String, bool)>>,
    absagen: &mut Absagen,
) {
    match &e.art {
        ExprArt::Ruf(r) => {
            rufprobe(r, span, offen, verlangt, absagen);
            for a in &r.argumente {
                rufprobe_expr(a, span, offen, verlangt, absagen);
            }
        }
        ExprArt::Klammer(x) | ExprArt::Unaer(_, x) => {
            rufprobe_expr(x, span, offen, verlangt, absagen)
        }
        ExprArt::Binaer(_, a, b) => {
            rufprobe_expr(a, span, offen, verlangt, absagen);
            rufprobe_expr(b, span, offen, verlangt, absagen);
        }
        _ => {}
    }
}


/// **`H006` — die Sperrordnung wird geprueft, nicht nur deklariert.**
///
/// `lock … rank N` steht seit der ersten Fassung in der Grammatik, und der Ordner beruft sich
/// an mehreren Stellen darauf: die Deadlockfreiheit des Bestands ruht darauf, und die
/// Traegergruppe sagt seit dem 2026-08-16 ausdruecklich *„die Ordnung wird nicht an der Gruppe
/// deklariert, sie steht in den `rank`-Zahlen."*
///
/// **Bis zu dieser Funktion hat sie niemand nachgerechnet.** Ein `grep '.rang'` ueber dem
/// Pruefer lieferte genau eine Fundstelle, und die verglich auf *Gleichheit*. Eine Zusage, die
/// deklariert, nie geprueft und von einem zweiten Konstrukt als Grundlage benutzt wird, ist
/// schlechter als gar keine: sie sieht aus wie ein Beleg.
///
/// **Gleicher Rang faellt mit.** Zwei Sperren desselben Rangs haben keine Ordnung; wer sie
/// verschachtelt, kann es in zwei Richtungen tun, und genau daraus entsteht die Verklemmung.
/// *Dieselbe Sperre zweimal ist kein Rangfehler* -- das ist `H003`, und eine Absage, die eine
/// zweite nach sich zieht, laesst den Leser den Fehler an der falschen Stelle suchen.
fn rangprobe(
    name: &str,
    span: gabbro_syntax::span::Span,
    kette: &[(String, Option<i128>)],
    sperren: &BTreeMap<String, Sperre>,
    absagen: &mut Absagen,
) -> Vec<(String, Option<i128>)> {
    let rang = sperren.get(name).and_then(|s| s.rang);
    if let Some(neu) = rang {
        for (aussen, alt) in kette {
            if aussen == name {
                continue; // dieselbe Sperre -- das ist H003
            }
            let Some(alt) = alt else { continue };
            if *alt >= neu {
                absagen.schiebe(
                    Absage::fehler(
                        "H006",
                        span,
                        format!(
                            "`{name}` (rank {neu}) is taken under `{aussen}` (rank {alt})"
                        ),
                    )
                    .mit_notiz(
                        "die Sperrordnung laeuft AUFSTEIGEND: eine Sperre wird nur unter \
                         Sperren KLEINEREN Rangs genommen -- sonst gibt es einen Zyklus, und \
                         der ist die Verklemmung",
                    )
                    .mit_notiz(if *alt == neu {
                        "gleicher Rang ist keine Ordnung: zwei Halter koennen sie in zwei \
                         Richtungen nehmen"
                    } else {
                        "die ehrliche Form ist, die aeussere Sperre vorher freizugeben und \
                         die tragende Bedingung danach ERNEUT zu pruefen"
                    }),
                );
            }
        }
    }
    let mut aus = kette.to_vec();
    aus.push((name.to_string(), rang));
    aus
}
