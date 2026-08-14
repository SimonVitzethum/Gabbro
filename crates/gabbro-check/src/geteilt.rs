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
//! ## Die vier Absagen
//!
//! * **`S001`** — Schreiben auf einen geschützten Platz unter geteilter Nahme. *Die
//!   tragende Regel.*
//! * **`S002`** — geteilt genommen, aber die Sperre erklärt kein `shared held <= … ops`.
//!   Ohne die Zahl hat die Latenzaussage aus §9.3 für diese Sperre keinen Zweig
//!   (Nebenbefund **N3**: `held` war für **exklusive** Halter gedacht; auf der geteilten
//!   Seite ist die Rechengrösse die **Schreiberwartezeit unter Leserdruck**).
//! * **`S003`** — Hochstufung: exklusive Nahme derselben Sperre **innerhalb** einer
//!   geteilten. Auf einer Drehsperre ist das kein Stilfehler, sondern ein Deadlock.
//! * **`S004`** — `shared held` erklärt, aber die Sperre wird nirgends geteilt genommen.
//!   *Eine Zahl ohne Messstelle ist eine Behauptung; dieselbe Regel wie beim toten
//!   Kandidaten — kein Konstrukt ohne gemessenen Bedarf.*
//! * **`S005`** — **die Zwischenregel an der Aufrufgrenze.** Siehe unten.
//!
//! ## `S005` — warum eine absichtlich zu strenge Regel besser ist als keine
//!
//! Die tragende Regel `S001` sieht nur, was der Block **selbst** schreibt. Ein Aufruf trägt
//! sie nicht mit: ruft ein geteilter Block eine Funktion mit `requires Held(N)`, so schreibt
//! **der Gerufene** exklusiv-berechtigt, während **der Rufer** nur geteilt hält. **Das ist
//! `S001` durch die Hintertür**, und bis Pass 8 steht, ist dieses Loch nicht bloss offen,
//! sondern **durchlässig**: der Zeuge existiert, seine Stärke wird nicht geprüft.
//!
//! Die richtige Prüfung braucht den Aufrufgraphen — denselben, an dem heute schon die
//! Aufrufwirkungen in Pass 8 hängen. Bis dahin gilt die grobe Fassung:
//!
//! > **Ein geteilter Block ruft keine Funktion mit `requires Held(…)`. Punkt.**
//!
//! Das ist **zu streng** — es verbietet auch den Aufruf über eine *andere* Sperre, der
//! harmlos wäre. Aber es irrt in die sichere Richtung, und der Preis dafür ist bekannt und
//! benannt. **Die Alternative wäre, dass die tragende Regel des neuen Konstrukts ausgerechnet
//! an der Aufrufgrenze eine stille Ausnahme hat** — und eine stille Ausnahme ist teurer als
//! eine laute Übertreibung, weil niemand sie sucht.
//!
//! Mit Pass 8 wird sie **ersetzt**, nicht gelockert: ein geteilter Zeuge deckt dann genau
//! `requires Held-shared`, und die Asymmetrie steht eine Ebene höher noch einmal so, wie
//! `E007` sie unten schneidet.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::BTreeMap;

/// Nennt die `requires`-Klausel einen `Held(…)`-Zeugen? — der Prädikatbaum, flach gelesen.
fn verlangt_held(p: &Pred) -> Option<String> {
    match &p.art {
        PredArt::Vergleich(e) => held_im_ausdruck(e),
        PredArt::Klammer(x) | PredArt::Nicht(x) => verlangt_held(x),
        PredArt::Und(a, b) | PredArt::Oder(a, b) => verlangt_held(a).or_else(|| verlangt_held(b)),
        PredArt::Element(e, _) => held_im_ausdruck(e),
        _ => None,
    }
}

fn held_im_ausdruck(e: &Expr) -> Option<String> {
    match &e.art {
        ExprArt::Ruf(r) if r.pfad.teile.last().is_some_and(|i| i.text == "Held") => Some(
            r.argumente
                .first()
                .map(|a| match &a.art {
                    ExprArt::Ort(o) => o.text(),
                    _ => "…".to_string(),
                })
                .unwrap_or_else(|| "…".to_string()),
        ),
        ExprArt::Klammer(x) | ExprArt::Unaer(_, x) => held_im_ausdruck(x),
        ExprArt::Binaer(_, a, b) => held_im_ausdruck(a).or_else(|| held_im_ausdruck(b)),
        _ => None,
    }
}

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
    let mut verlangt: BTreeMap<String, String> = BTreeMap::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Funktion(f) = &item.art {
            for r in &f.requires {
                if let Some(sperre) = verlangt_held(r) {
                    verlangt.insert(f.name.text.clone(), sperre);
                    break;
                }
            }
        }
    });

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
                    "S004",
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
    // ohnehin mit `S003`; sie soll nicht ZWEIMAL fallen** -- eine Absage, die eine zweite
    // nach sich zieht, laesst den Leser den Fehler an der falschen Stelle suchen.
    exklusiv: &[String],
    sperren: &BTreeMap<String, Sperre>,
    verlangt: &BTreeMap<String, String>,
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
                                "S002",
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
                                "S003",
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
                "S001",
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
fn rufprobe(
    r: &Ruf,
    span: Span,
    offen: &[String],
    verlangt: &BTreeMap<String, String>,
    absagen: &mut Absagen,
) {
    if offen.is_empty() {
        return;
    }
    let Some(name) = r.pfad.teile.last() else {
        return;
    };
    let Some(sperre) = verlangt.get(&name.text) else {
        return;
    };
    absagen.schiebe(
        Absage::fehler(
            "S005",
            span,
            format!(
                "`{}` verlangt `Held({sperre})`, wird hier aber unter geteilter Nahme von \
                 `{}` gerufen",
                name.text,
                offen.join("`, `")
            ),
        )
        .mit_notiz(
            "der Gerufene schreibt exklusiv-berechtigt, der Rufer haelt nur geteilt -- das \
             waere S001 durch die Hintertuer",
        )
        .mit_notiz(
            "ZWISCHENREGEL, absichtlich zu streng: bis der Aufrufgraph steht (Pass 8, \
             Aufrufwirkungen), faellt JEDER `Held(…)`-Zeuge unter geteilter Nahme -- auch \
             der einer anderen Sperre, der harmlos waere",
        )
        .mit_notiz(
            "eine laute Uebertreibung ist billiger als eine stille Ausnahme: nach der \
             stillen sucht niemand",
        ),
    );
}

fn rufprobe_expr(
    e: &Expr,
    span: Span,
    offen: &[String],
    verlangt: &BTreeMap<String, String>,
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
