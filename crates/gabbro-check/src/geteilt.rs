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
    span: Span,
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    let mut sperren: BTreeMap<String, Sperre> = BTreeMap::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Lock(l) = &item.art {
            sperren.insert(
                l.name.text.clone(),
                Sperre {
                    schuetzt: l.schuetzt.iter().map(|o| o.text()).collect(),
                    hat_geteilte_zeit: l.geteilte_haltezeit.is_some(),
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
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let FnRumpf::Block(b) = &f.rumpf else {
            return;
        };
        block(b, &[], &[], &sperren, &verlangt, &mut geteilt_genommen, absagen);
    });

    // S004 -- eine Zahl ohne Messstelle. Kein Konstrukt ohne gemessenen Bedarf, und keine
    // Zusage ohne Ort, an dem sie faellt.
    for (name, s) in &sperren {
        if s.hat_geteilte_zeit && !geteilt_genommen.contains(name) {
            absagen.schiebe(
                Absage::hinweis(
                    "H004",
                    s.span,
                    format!("`{name}` erklaert `shared held`, wird aber nirgends geteilt genommen"),
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
fn block(
    b: &Block,
    offen: &[String],
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
                    tiefer.push(name);
                    block(&l.rumpf, &tiefer, exklusiv, sperren, verlangt, genommen, absagen);
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
                    tiefer.push(name);
                    block(&l.rumpf, offen, &tiefer, sperren, verlangt, genommen, absagen);
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
                    block(rumpf, offen, exklusiv, sperren, verlangt, genommen, absagen);
                }
            }
            StmtArt::Wenn(w) => {
                for (b, _) in &w.zweige {
                    rufprobe_expr(b, s.span, offen, verlangt, absagen);
                }
                for (_, r) in &w.zweige {
                    block(r, offen, exklusiv, sperren, verlangt, genommen, absagen);
                }
                if let Some(r) = &w.sonst {
                    block(r, offen, exklusiv, sperren, verlangt, genommen, absagen);
                }
            }
            StmtArt::Match(m) => {
                for z in &m.zweige {
                    block(&z.rumpf, offen, exklusiv, sperren, verlangt, genommen, absagen);
                }
            }
            StmtArt::Bricht(x) => block(&x.rumpf, offen, exklusiv, sperren, verlangt, genommen, absagen),
            StmtArt::Narrow(x) => block(&x.sonst, offen, exklusiv, sperren, verlangt, genommen, absagen),
            StmtArt::LetSonst(x) => {
                rufprobe(&x.ruf, s.span, offen, verlangt, absagen);
                block(&x.sonst, offen, exklusiv, sperren, verlangt, genommen, absagen);
            }
            StmtArt::Schleife(sch) => match sch.as_ref() {
                Schleife::Traverse(x) => block(&x.rumpf, offen, exklusiv, sperren, verlangt, genommen, absagen),
                Schleife::Retry(x) => block(&x.rumpf, offen, exklusiv, sperren, verlangt, genommen, absagen),
                Schleife::Forever(x) => block(&x.rumpf, offen, exklusiv, sperren, verlangt, genommen, absagen),
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
                format!("`{ort}` wird geschrieben, waehrend `{name}` nur geteilt gehalten wird"),
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
