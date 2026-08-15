//! **Pass 8 -- `effects`, und der Grund, warum dieser Pass ueberhaupt existiert.**
//!
//! `SPRACHE.md` §7 und `SYNTAX.md` §6:
//!
//! > **`effects` ist NICHT fail-open.** Eine Funktion **ohne** `effects` ist ein
//! > Uebersetzungsfehler; wer nichts anfasst, schreibt `effects { pure }`. Die frueher
//! > moegliche Auslassung war zugleich **die staerkste Zusage und die kuerzeste
//! > Spezifikation** -- der Anreiz stand gegen die Vollstaendigkeit.
//!
//! Genau deshalb faellt die Pflicht **an der Abwesenheit**, nicht am Inhalt: der Parser laesst
//! die Klausel weg, wenn sie fehlt, und dieser Pass sieht das Loch. Ein Werkzeug, das eine
//! fehlende Klausel als „keine Wirkungen" liest, belohnt das Weglassen.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    // **Der Aufrufgraph, seit 2026-08-15.** Ohne ihn deckte eine `effects`-Liste nur die
    // ERSTE Ebene: `effects { pure }` galt fuer eine Funktion, die eine schreibende rief.
    // Damit war „nur die eingetragene Logik ist aktiv" eine halbe Aussage, und die
    // Klempnerei-Klasse *Rahmen* hing genau daran.
    let g = crate::aufrufgraph::erhebe(baum);
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Funktion(f) => funktion(f, &g, absagen),
        ItemArt::Axiom(a) => rein_allein(&a.effects, absagen),
        _ => {}
    });
}

/// Was ein Rumpf tut -- Ort und Fundstelle je Tat.
/// Die **lokalen** Namen eines Rumpfes: alles, was `let` einfuehrt, plus die Laufvariablen
/// der Schleifen. **Ein Schreibzugriff auf einen lokalen Namen ist keine Wirkung.**
///
/// `effects` beschreibt, was eine Funktion mit der WELT tut, nicht mit ihrem eigenen Stapel.
/// Bis 2026-08-15 verlangte `E005` fuer `let mut i = 0; i += 1;` einen Eintrag in der
/// Wirkungsliste -- eine Funktion, die nur zaehlt, konnte nicht `pure` sein. Gefunden am
/// Fragmentlauf (`FRAGMENTE.md`, kstackmark), wo genau das aufschlug.
fn lokale(b: &Block, aus: &mut Vec<String>) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Let(l) => aus.push(l.name.text.clone()),
            StmtArt::LetSonst(l) => aus.push(l.name.text.clone()),
            StmtArt::AwaitLoad(a) => aus.push(a.name.text.clone()),
            StmtArt::Exchange(e) => aus.push(e.name.text.clone()),
            StmtArt::Narrow(x) => lokale(&x.sonst, aus),
            StmtArt::Sperrt(x) => lokale(&x.rumpf, aus),
            StmtArt::Bricht(x) => lokale(&x.rumpf, aus),
            StmtArt::Wenn(w) => {
                for (_, r) in &w.zweige {
                    lokale(r, aus);
                }
                if let Some(r) = &w.sonst {
                    lokale(r, aus);
                }
            }
            StmtArt::Match(m) => {
                for z in &m.zweige {
                    lokale(&z.rumpf, aus);
                }
            }
            StmtArt::Schleife(sch) => match sch.as_ref() {
                Schleife::Traverse(x) => {
                    aus.push(x.variable.text.clone());
                    lokale(&x.rumpf, aus);
                }
                Schleife::Retry(x) => lokale(&x.rumpf, aus),
                Schleife::Forever(x) => lokale(&x.rumpf, aus),
            },
            _ => {}
        }
    }
}

#[derive(Default)]
struct Taten {
    schreibt: Vec<(String, Span)>,
    /// Ort, Fundstelle, und **ob geteilt genommen** -- die Richtung ist nicht symmetrisch.
    sperrt: Vec<(String, Span, bool)>,
}

/// Der Kopf eines Ortes, so wie eine Wirkung ihn nennt: `c.slots[s].benutzt` wird von
/// `writes c.slots` gedeckt, also zaehlt jeder Praefix.
fn deckt(erklaert: &str, getan: &str) -> bool {
    getan == erklaert
        || getan.starts_with(erklaert)
            && matches!(
                getan.as_bytes().get(erklaert.len()).copied(),
                Some(b'.') | Some(b'[') | Some(b'-')
            )
}

fn sammle_taten(b: &Block, t: &mut Taten) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Zuweisung(z) => t.schreibt.push((z.ziel.text(), z.ziel.span)),
            StmtArt::Publish(p) => t.schreibt.push((p.ziel.text(), p.ziel.span)),
            StmtArt::Exchange(e) => {
                t.schreibt.push((e.ort.text(), e.ort.span));
                if let XForm::Update { rumpf, .. } = &e.form {
                    sammle_taten(rumpf, t);
                }
            }
            StmtArt::Sperrt(l) => {
                t.sperrt.push((l.sperre.text(), l.sperre.span, l.geteilt));
                sammle_taten(&l.rumpf, t);
            }
            StmtArt::Wenn(w) => {
                for (_, r) in &w.zweige {
                    sammle_taten(r, t);
                }
                if let Some(r) = &w.sonst {
                    sammle_taten(r, t);
                }
            }
            StmtArt::Match(m) => {
                for z in &m.zweige {
                    sammle_taten(&z.rumpf, t);
                }
            }
            StmtArt::Bricht(x) => sammle_taten(&x.rumpf, t),
            StmtArt::Narrow(x) => sammle_taten(&x.sonst, t),
            StmtArt::LetSonst(x) => sammle_taten(&x.sonst, t),
            StmtArt::Schleife(sch) => match sch.as_ref() {
                // Eine `traverse` mit `touches` traegt ihre eigene Wirkungsliste; sie muss
                // trotzdem von der Funktion gedeckt sein, also zaehlt der Rumpf mit.
                Schleife::Traverse(x) => sammle_taten(&x.rumpf, t),
                Schleife::Retry(x) => sammle_taten(&x.rumpf, t),
                Schleife::Forever(x) => sammle_taten(&x.rumpf, t),
            },
            _ => {}
        }
    }
}

/// **Der Rumpfabgleich.** Bis zum 2026-08-14 pruefte dieser Pass nur die DEKLARATION --
/// Anwesenheit, `pure` allein, `diverges`. Ein `effects { pure }` ueber einer Funktion, die
/// schreibt, kam durch, und damit war die Zusage *„`effects` ist nicht fail-open"* auf ihrer
/// wichtigsten Haelfte leer: sie erzwang eine Liste, nicht ihre Wahrheit.
///
/// **Was hier geprueft wird und was nicht:** jedes **Schreiben** und jedes **`locks`** muss
/// von einer erklaerten Wirkung gedeckt sein. **Lesen wird nicht geprueft** — `FRAGMENTE.md`
/// liest in jeder Funktion Stellen, die keine `reads`-Zeile nennt, und ob das ein Befund ist
/// oder die gemeinte Bedeutung, entscheidet nicht dieser Pass. **Aufrufwirkungen ebenso
/// nicht:** dazu muessten die Wirkungen des Gerufenen auf die Argumente des Aufrufers
/// abgebildet werden, und das ist ein eigener Posten.
fn rumpf_gegen_wirkungen(f: &FnDecl, w: &Wirkungen, b: &Block, absagen: &mut Absagen) {
    let mut taten = Taten::default();
    sammle_taten(b, &mut taten);

    let ist_rein = w.liste.iter().any(|e| matches!(e.art, WirkungArt::Rein));
    let schreibrechte: Vec<String> = w
        .liste
        .iter()
        .filter_map(|e| match &e.art {
            WirkungArt::Schreibt(o)
            | WirkungArt::Verbraucht(o)
            | WirkungArt::Veroeffentlicht(o) => Some(o.text()),
            WirkungArt::Belegt(i) | WirkungArt::Maskiert(i) => Some(i.text.clone()),
            _ => None,
        })
        .collect();
    // Exklusiv erklaerte Sperren -- sie decken BEIDE Nahmen, denn exklusiv ist staerker.
    let sperren: Vec<String> = w
        .liste
        .iter()
        .filter_map(|e| match &e.art {
            WirkungArt::Sperrt(o) => Some(o.text()),
            _ => None,
        })
        .collect();
    // Geteilt erklaerte Sperren -- sie decken NUR die geteilte Nahme. Die Umkehrung waere
    // die gefaehrliche Richtung: ein Aufrufer, der `locks shared` liest, rechnet mit
    // Nebenlaeufigkeit, die es nicht gibt.
    let geteilte: Vec<String> = w
        .liste
        .iter()
        .filter_map(|e| match &e.art {
            WirkungArt::SperrtGeteilt(o) => Some(o.text()),
            _ => None,
        })
        .collect();

    // **Lokale Namen sind keine Wirkung.** Der Vergleich geht ueber den GRUNDNAMEN: ein
    // Schreibzugriff auf `i` oder `i.feld` gehoert dem Stapel, einer auf `p.slots[i]` der Welt.
    let mut lok = Vec::new();
    lokale(b, &mut lok);
    for (ort, span) in &taten.schreibt {
        let grund = ort.split(['.', '[', '-']).next().unwrap_or(ort);
        if lok.iter().any(|l| l == grund) {
            continue;
        }
        if ist_rein {
            absagen.schiebe(
                Absage::fehler(
                    "E005",
                    *span,
                    format!("`{}` schreibt `{ort}`, erklaert aber `pure`", f.name.text),
                )
                .mit_notiz("`pure` heisst: fasst nichts an"),
            );
            continue;
        }
        if !schreibrechte.iter().any(|e| deckt(e, ort)) {
            absagen.schiebe(
                Absage::fehler(
                    "E005",
                    *span,
                    format!(
                        "`{ort}` wird geschrieben, steht aber in keiner Wirkung von `{}`",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "SPRACHE.md §7: `effects` ist Pflicht und nicht fail-open -- eine Liste, \
                     die der Rumpf ueberschreitet, ist dieselbe Auslassung mit mehr Zeichen",
                )
                .mit_notiz(format!(
                    "erklaert sind: {}",
                    if schreibrechte.is_empty() {
                        "keine Schreibwirkung".to_string()
                    } else {
                        schreibrechte.join(", ")
                    }
                )),
            );
        }
    }

    for (ort, span, geteilt) in &taten.sperrt {
        if sperren.iter().any(|e| deckt(e, ort)) {
            continue; // exklusiv erklaert deckt beide Nahmen
        }
        if *geteilt && geteilte.iter().any(|e| deckt(e, ort)) {
            continue;
        }
        // **E007 ist die gefaehrliche Richtung und bekommt darum eigenen Text:** der Rumpf
        // nimmt exklusiv, die Wirkung sagt geteilt. Wer die Signatur liest, rechnet mit
        // Nebenlaeufigkeit, die es nicht gibt -- und baut seine Latenzrechnung darauf.
        if !*geteilt && geteilte.iter().any(|e| deckt(e, ort)) {
            absagen.schiebe(
                Absage::fehler(
                    "E007",
                    *span,
                    format!(
                        "`{}` nimmt `{ort}` EXKLUSIV, erklaert aber `locks shared {ort}`",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "geteilt erklaeren und exklusiv nehmen ist die gefaehrliche Richtung: der \
                     Aufrufer rechnet mit Nebenlaeufigkeit, die es nicht gibt, und legt seine \
                     Latenzrechnung darauf an",
                )
                .mit_notiz("umgekehrt ist es zulaessig -- exklusiv erklaeren deckt die geteilte Nahme"),
            );
            continue;
        }
        absagen.schiebe(
            Absage::fehler(
                "E006",
                *span,
                format!(
                    "`locks {}{ort}` steht im Rumpf, aber nicht in den Wirkungen von `{}`",
                    if *geteilt { "shared " } else { "" },
                    f.name.text
                ),
            )
            .mit_notiz("die Sperrordnung faellt aus den erklaerten Sperren, nicht aus dem Rumpf"),
        );
    }
}

fn funktion(f: &FnDecl, g: &crate::aufrufgraph::Graph, absagen: &mut Absagen) {
    match &f.effects {
        None => {
            // `spec fn` hat keine Laufzeitwirkung; fuer sie ist die Klausel freigestellt.
            if f.klasse != Some(FnKlasse::Spec) {
                absagen.schiebe(
                    Absage::fehler(
                        "E001",
                        f.name.span,
                        format!("`{}` hat keine `effects`-Klausel", f.name.text),
                    )
                    .mit_notiz(
                        "SPRACHE.md §7: `effects` ist Pflicht und nicht fail-open -- \
                         wer nichts anfasst, schreibt `effects { pure }`",
                    )
                    .mit_notiz(
                        "die Auslassung war zugleich die staerkste Zusage und die kuerzeste \
                         Spezifikation; der Anreiz stand gegen die Vollstaendigkeit",
                    ),
                );
            }
        }
        Some(w) => {
            rein_allein(w, absagen);
            if let FnRumpf::Block(b) = &f.rumpf {
                rumpf_gegen_wirkungen(f, w, b, absagen);
                aufrufwirkungen(f, w, g, absagen);
            }
        }
    }

    if f.klasse == Some(FnKlasse::Divergent) {
        let divergiert = f
            .effects
            .as_ref()
            .map(|w| w.liste.iter().any(|e| matches!(e.art, WirkungArt::Divergiert)))
            .unwrap_or(false);
        if !divergiert {
            absagen.schiebe(
                Absage::hinweis(
                    "E003",
                    f.name.span,
                    format!(
                        "`divergent fn {}` nennt `diverges` nicht in seinen Wirkungen",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "SYNTAX.md §14 schreibt `divergent fn idle() effects { diverges };` -- \
                     die ausgesprochene Nichtterminierung gehoert in die Wirkungsliste",
                ),
            );
        }
    }

    // Eine `spec fn` mit `= pred;` ist die einzige Form, in der ein Quantor im Rumpf steht.
    if f.klasse != Some(FnKlasse::Spec) {
        if let FnRumpf::Pred(p) = &f.rumpf {
            absagen.schiebe(
                Absage::fehler(
                    "E004",
                    p.span,
                    "ein Praedikat als Rumpf steht nur einer `spec fn` zu",
                )
                .mit_notiz("`fndecl`: `= pred ;` nur fuer `spec fn`"),
            );
        }
    }
}

/// `pure` heisst „fasst nichts an". Eine zweite Wirkung daneben ist ein Widerspruch, kein
/// Zusatz -- und der Widerspruch faellt hier, nicht beim Leser.
fn rein_allein(w: &Wirkungen, absagen: &mut Absagen) {
    let rein: Vec<&Wirkung> = w
        .liste
        .iter()
        .filter(|e| matches!(e.art, WirkungArt::Rein))
        .collect();
    if rein.is_empty() {
        return;
    }
    if w.liste.len() > 1 {
        let andere: Vec<&str> = w
            .liste
            .iter()
            .filter(|e| !matches!(e.art, WirkungArt::Rein))
            .map(|e| e.art.benennung())
            .collect();
        let stelle = rein[0].span;
        absagen.schiebe(
            Absage::fehler(
                "E002",
                stelle,
                format!(
                    "`pure` steht neben {} -- `pure` heisst, dass nichts angefasst wird",
                    andere.join(", ")
                ),
            )
            .mit_notiz("entweder `effects { pure }` allein, oder die Wirkungen ohne `pure`"),
        );
    }
    if rein.len() > 1 {
        absagen.schiebe(Absage::fehler(
            "E002",
            rein[1].span,
            "`pure` steht zweimal in derselben Wirkungsliste",
        ));
    }
}

/// **E008 — die Wirkungen der Gerufenen gehoeren in die Liste des Rufers.**
///
/// *„Das ist der Posten, der `effects` erst kompositional macht"* (`TODO.md`). Ohne ihn galt
/// `effects { pure }` fuer eine Funktion, die eine schreibende rief — und die Rahmenaussage
/// endete an der ersten Aufrufgrenze.
///
/// **Die Fassung ist grob und in die sichere Richtung grob:** die Wirkung des Gerufenen wird
/// mit SEINEM Parameternamen gesehen, nicht auf die Argumente des Rufers abgebildet. Ein
/// `writes p.slots` beim Gerufenen verlangt beim Rufer eine Schreibwirkung — irgendeine.
/// **Das sieht mehr Wirkungen als da sind, nie weniger.** Die Abbildung auf Argumente ist
/// der naechste Schritt und braucht eine Alias-Analyse, die es nicht gibt.
///
/// **Und wo die Huelle unvollstaendig ist, sagt sie es** (R16): ein Zyklus oder ein
/// Gerufener ohne `effects` macht die Menge zu einer unteren Schranke, und dann wird nicht
/// abgesagt — eine Absage aus einer unteren Schranke waere eine Behauptung.
fn aufrufwirkungen(
    f: &FnDecl,
    w: &Wirkungen,
    g: &crate::aufrufgraph::Graph,
    absagen: &mut Absagen,
) {
    let h = g.huelle(&f.name.text);
    if h.unvollstaendig.is_some() {
        return; // untere Schranke -- daraus wird nicht abgesagt
    }
    let ist_rein = w.liste.iter().any(|e| matches!(e.art, WirkungArt::Rein));
    let eigene: Vec<String> = w.liste.iter().map(|e| e.art.benennung().to_string()).collect();
    for wirkung in &h.wirkungen {
        // **Die Benennung ist zweiwortig, wo sie es ist.** `locks shared X` heisst
        // `locks shared`, nicht `locks` -- ein Vergleich am ersten Leerzeichen liess eine
        // Funktion an ihrer EIGENEN Wirkung scheitern. Gefunden an `beispiele/10`, sofort
        // beim ersten Lauf des neuen Passes.
        let art = if wirkung.starts_with("locks shared") {
            "locks shared"
        } else {
            wirkung.split_whitespace().next().unwrap_or("")
        };
        if art == "pure" {
            continue;
        }
        // **`diverges` wandert NICHT nach oben.** Wer eine divergierende Funktion ruft,
        // divergiert nicht -- nur wer sie auf JEDEM Weg ruft. Das ist eine Aussage ueber
        // Pfade, und dieser Pass rechnet ueber Mengen. Die grobe Fassung waere hier in die
        // UNSICHERE Richtung grob: sie erzwaenge `diverges` an Funktionen, die zurueckkehren.
        // (`beispiele/11a`: der Fehlerzweig ruft `abbruch()`, der Normalfall kehrt zurueck.)
        if art == "diverges" {
            continue;
        }
        // Eine geteilte Nahme ist von einer exklusiven Erklaerung gedeckt -- dieselbe
        // Asymmetrie wie `E007`, eine Ebene hoeher.
        if art == "locks shared" && eigene.iter().any(|e| e == "locks") {
            continue;
        }
        if ist_rein {
            absagen.schiebe(
                Absage::fehler(
                    "E008",
                    f.name.span,
                    format!(
                        "`{}` erklaert `pure`, ruft aber etwas mit `{wirkung}`",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "`effects` ist kompositional: die Wirkungen der Gerufenen gehoeren in \
                     die Liste des Rufers -- sonst endet die Rahmenaussage an der ersten \
                     Aufrufgrenze",
                ),
            );
            return;
        }
        if !eigene.iter().any(|e| e == art) {
            absagen.schiebe(
                Absage::fehler(
                    "E008",
                    f.name.span,
                    format!(
                        "`{}` ruft etwas mit `{wirkung}`, nennt aber keine `{art}`-Wirkung",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "die Wirkung stammt aus einem Gerufenen -- `effects` deckte bis \
                     2026-08-15 nur die erste Ebene",
                )
                .mit_notiz(format!(
                    "erklaert sind: {}",
                    if eigene.is_empty() { "nichts".into() } else { eigene.join(", ") }
                )),
            );
        }
    }
}
