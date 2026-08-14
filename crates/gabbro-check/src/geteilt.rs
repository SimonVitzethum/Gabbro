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

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::BTreeMap;

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

    let mut geteilt_genommen: Vec<String> = Vec::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let FnRumpf::Block(b) = &f.rumpf else {
            return;
        };
        block(b, &[], &[], &sperren, &mut geteilt_genommen, absagen);
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
                    block(&l.rumpf, &tiefer, exklusiv, sperren, genommen, absagen);
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
                    block(&l.rumpf, offen, &tiefer, sperren, genommen, absagen);
                }
            }
            StmtArt::Zuweisung(z) => {
                schreibprobe(&z.ziel, s.span, offen, exklusiv, sperren, absagen)
            }
            StmtArt::Publish(p) => schreibprobe(&p.ziel, s.span, offen, exklusiv, sperren, absagen),
            StmtArt::Exchange(e) => {
                schreibprobe(&e.ort, s.span, offen, exklusiv, sperren, absagen);
                if let XForm::Update { rumpf, .. } = &e.form {
                    block(rumpf, offen, exklusiv, sperren, genommen, absagen);
                }
            }
            StmtArt::Wenn(w) => {
                for (_, r) in &w.zweige {
                    block(r, offen, exklusiv, sperren, genommen, absagen);
                }
                if let Some(r) = &w.sonst {
                    block(r, offen, exklusiv, sperren, genommen, absagen);
                }
            }
            StmtArt::Match(m) => {
                for z in &m.zweige {
                    block(&z.rumpf, offen, exklusiv, sperren, genommen, absagen);
                }
            }
            StmtArt::Bricht(x) => block(&x.rumpf, offen, exklusiv, sperren, genommen, absagen),
            StmtArt::Narrow(x) => block(&x.sonst, offen, exklusiv, sperren, genommen, absagen),
            StmtArt::LetSonst(x) => block(&x.sonst, offen, exklusiv, sperren, genommen, absagen),
            StmtArt::Schleife(sch) => match sch.as_ref() {
                Schleife::Traverse(x) => block(&x.rumpf, offen, exklusiv, sperren, genommen, absagen),
                Schleife::Retry(x) => block(&x.rumpf, offen, exklusiv, sperren, genommen, absagen),
                Schleife::Forever(x) => block(&x.rumpf, offen, exklusiv, sperren, genommen, absagen),
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
