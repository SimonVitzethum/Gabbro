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
    // **Eine Konstante ist kein Weltzustand.** `const GRENZE: u32 = 1000000;` steht zur
    // Uebersetzungszeit fest; sie zu lesen ist kein Zugriff, sondern eine Zahl. Ohne diese
    // Ausnahme waere `pure` praktisch unerreichbar -- die erste Fassung von `E010` meldete
    // `v1_erhoehen liest GRENZE, erklaert aber pure` und hatte damit recht im Wortlaut und
    // unrecht in der Sache.
    //
    // **Und die Umkehrung derselben Einsicht, gefunden am Korpus:** `E010` spricht nur ueber
    // **bekannten Weltzustand** -- `static`, `atomic`, `table`, `device`, `state`. Der erste
    // Lauf meldete `IpcResult.Ok` (eine Variante, kein Ort) und `MAX_SECTORS` (ein Name, den
    // ein AUSSCHNITT gar nicht deklariert) als ungenannte Lesungen. Beides sind keine
    // Wirkungen, und beide Meldungen waeren Laerm gewesen, der die echten zudeckt.
    //
    // *Verloren geht dabei nichts:* in einer vollstaendigen Uebersetzungseinheit muss jeder
    // Name aufloesen -- ein unbekannter faellt bereits im Namenspass. Die Einschraenkung
    // kostet also nur im Ausschnitt, und dort ist sie richtig.
    let mut konstanten: Vec<String> = Vec::new();
    let mut weltnamen: Vec<String> = Vec::new();
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Konst(k) => konstanten.push(k.name.text.clone()),
        ItemArt::Statisch(x) => weltnamen.push(x.name.text.clone()),
        ItemArt::Atomic(x) => weltnamen.push(x.name.text.clone()),
        ItemArt::Tabelle(x) => weltnamen.push(x.name.text.clone()),
        ItemArt::Device(x) => weltnamen.push(x.name.text.clone()),
        ItemArt::State(x) => weltnamen.push(x.name.text.clone()),
        _ => {}
    });
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| match &item.art {
        ItemArt::Funktion(f) => funktion(f, modul, &g, &konstanten, &weltnamen, absagen),
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
            StmtArt::Exchange(e) => {
                aus.push(e.name.text.clone());
                // Der Binder von `update(v)` ist der ALTE Wert -- ein Name des Rumpfes,
                // keine Stelle der Welt.
                if let XForm::Update { binder, .. } = &e.form {
                    aus.push(binder.text.clone());
                }
            }
            StmtArt::Match(m) => {
                for z in &m.zweige {
                    // **Der Binder eines `match`-Zweiges ist ein lokaler Name**, und dass er
                    // hier gefehlt hat, war eine Luecke mit zwei Gesichtern: `E010` meldete
                    // ihn beim ersten Lauf als Weltzustand, und `E005` haette dasselbe fuer
                    // ein `Some(p) => { p.feld = … }` getan. **Die Lesehaelfte hat einen
                    // Fehler der SCHREIBhaelfte aufgedeckt** -- gefunden erst, weil Binder
                    // fast immer gelesen und fast nie geschrieben werden.
                    if let Some(bi) = &z.binder {
                        aus.push(bi.text.clone());
                    }
                }
            }
            StmtArt::Schleife(sch) => {
                if let Schleife::Traverse(x) = sch.as_ref() {
                    aus.push(x.variable.text.clone());
                }
            }
            _ => {}
        }
        for k in crate::unterbloecke(s) {
            lokale(k, aus);
        }
    }
}

#[derive(Default)]
struct Taten {
    schreibt: Vec<(String, Span)>,
    /// **Lesart A (2026-08-16).** Jedes Lesen eines nicht-lokalen Ortes. Die Entscheidung
    /// steht in `TODO.md`, der Preis daneben: A laesst 10 von 32 Fragmentfunktionen fallen,
    /// die gruebere Lesart C nur drei. **A ist die Lesart, deren Verletzung dieser Pass
    /// PRAEZISE melden kann** -- welche Funktion welchen Ort ungenannt liest; C koennte nur
    /// *„irgendwo ausserhalb von `mmio`/`dma`/`atomic`"* sagen. *Was man nicht genau melden
    /// kann, setzt kein Pass durch* -- dieselbe Begruendung, an der Lesart B gestorben ist.
    liest: Vec<(String, Span)>,
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

/// Jedes Lesen eines Ortes in einem Ausdruck. **Der Index ist selbst ein Lesen** --
/// `c.slots[i]` liest `c.slots` *und* `i`; der lokale Anteil faellt spaeter am Grundnamen weg.
fn liest_expr(e: &Expr, t: &mut Taten) {
    match &e.art {
        ExprArt::Ort(o) => {
            t.liest.push((o.text(), o.span));
            for suf in &o.suffixe {
                if let OrtSuffix::Index(ix) = suf {
                    liest_expr(ix, t);
                }
            }
        }
        ExprArt::Klammer(x) | ExprArt::Unaer(_, x) => liest_expr(x, t),
        ExprArt::Binaer(_, a, b) => {
            liest_expr(a, t);
            liest_expr(b, t);
        }
        ExprArt::Ruf(r) => {
            for a in &r.argumente {
                liest_expr(a, t);
            }
        }
        _ => {}
    }
}

/// Ein **Schreib**ziel liest seine Indizes mit: `c.slots[naechster] = x` liest `naechster`.
/// Der Ort selbst wird geschrieben, nicht gelesen.
fn ziel_indizes(o: &Ort, t: &mut Taten) {
    for suf in &o.suffixe {
        if let OrtSuffix::Index(ix) = suf {
            liest_expr(ix, t);
        }
    }
}

fn sammle_taten(b: &Block, t: &mut Taten) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Zuweisung(z) => {
                t.schreibt.push((z.ziel.text(), z.ziel.span));
                ziel_indizes(&z.ziel, t);
                liest_expr(&z.wert, t);
            }
            StmtArt::Publish(p) => {
                t.schreibt.push((p.ziel.text(), p.ziel.span));
                ziel_indizes(&p.ziel, t);
                liest_expr(&p.wert, t);
            }
            StmtArt::Let(l) => liest_expr(&l.wert, t),
            StmtArt::Return(Some(x)) => liest_expr(x, t),
            StmtArt::Ruf(r) => {
                for a in &r.argumente {
                    liest_expr(a, t);
                }
            }
            // **Ein `awaits`-Laden IST ein Lesen**, und zwar das gefaehrlichste: es liest
            // eine Nutzlast, die ein anderer Kern geschrieben hat.
            StmtArt::AwaitLoad(a) => t.liest.push((a.quelle.text(), a.quelle.span)),
            StmtArt::Exchange(e) => {
                t.schreibt.push((e.ort.text(), e.ort.span));
                t.liest.push((e.ort.text(), e.ort.span));
            }
            StmtArt::Sperrt(l) => t.sperrt.push((l.sperre.text(), l.sperre.span, l.geteilt)),
            StmtArt::Wenn(w) => {
                for (bed, _) in &w.zweige {
                    liest_expr(bed, t);
                }
            }
            StmtArt::Match(m) => liest_expr(&m.gegenstand, t),
            StmtArt::Narrow(x) => t.liest.push((x.ort.text(), x.ort.span)),
            StmtArt::Schleife(sch) => {
                // Eine `traverse` mit `touches` traegt ihre eigene Wirkungsliste; sie muss
                // trotzdem von der Funktion gedeckt sein, also zaehlt der Rumpf mit.
                // **Die Domaene selbst wird gelesen** -- `slots of c` liest `c`.
                if let Schleife::Traverse(x) = sch.as_ref() {
                    domaene_liest(&x.domaene, t);
                }
            }
            _ => {}
        }
        for k in crate::unterbloecke(s) {
            sammle_taten(k, t);
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
/// **`E011` -- `touches` wird gegen den Rumpf gehalten («NL.2.2», 2026-08-19).**
///
/// `pruefe-klauseln.py` fuehrte `touches` als ZUSAGE mit dem Satz *„die Wirkungsmenge eines
/// `traverse`; deklariert, nie gegen den Rumpf gehalten."* Gemessen am selben Tag:
///
/// ```gabbro
/// traverse i over slots of w by unvisited
///     touches reads w.slots
/// { fremd = 1; }              -- 0 Fehler
/// ```
///
/// ## Warum die Zeile ueberhaupt dasteht, wenn `effects` sie schon deckt
///
/// Die `effects` der Funktion decken den ganzen Rumpf, Schleifen eingeschlossen. `touches`
/// ist die **engere, oertliche** Zusage: *diese Traversierung fasst genau DAS an.* Sie ist
/// die Grundlage der Kostenrechnung und der Sperrargumente -- und sie war bis heute
/// unverbindlich.
///
/// > **Eine engere Zusage, die niemand haelt, ist schlimmer als keine:** wer sie liest,
/// > rechnet mit weniger Beruehrung, als der Rumpf hat.
///
/// **Gedeckt wird `writes` und `reads` gegen die genannten Orte**, mit derselben `deckt`
/// -Funktion wie `E005`/`E010`. *Konstanten und lokale Namen zaehlen nicht* -- dieselbe
/// Ausnahme, aus demselben Grund.
fn traverse_gegen_touches(
    b: &Block,
    fname: &str,
    konstanten: &[String],
    weltnamen: &[String],
    absagen: &mut Absagen,
) {
    for s in &b.anweisungen {
        if let StmtArt::Schleife(sch) = &s.art {
            if let Schleife::Traverse(t) = sch.as_ref() {
                if let Some(w) = &t.touches {
                    pruefe_touches(t, w, fname, konstanten, weltnamen, absagen);
                }
            }
        }
        let unter = crate::unterbloecke(s);
        for u in unter {
            traverse_gegen_touches(u, fname, konstanten, weltnamen, absagen);
        }
    }
}

fn pruefe_touches(
    t: &Traverse,
    w: &Wirkungen,
    fname: &str,
    konstanten: &[String],
    weltnamen: &[String],
    absagen: &mut Absagen,
) {
    let mut taten = Taten::default();
    sammle_taten(&t.rumpf, &mut taten);
    let schreibt: Vec<String> = w
        .liste
        .iter()
        .filter_map(|e| match &e.art {
            WirkungArt::Schreibt(o) | WirkungArt::Verbraucht(o) | WirkungArt::Veroeffentlicht(o) => {
                Some(o.text())
            }
            _ => None,
        })
        .collect();
    let liest: Vec<String> = w
        .liste
        .iter()
        .filter_map(|e| match &e.art {
            WirkungArt::Liest(o) => Some(o.text()),
            WirkungArt::Schreibt(o) => Some(o.text()), // schreiben deckt lesen
            _ => None,
        })
        .collect();
    let bekannt = |o: &String| {
        !konstanten.iter().any(|k| k == o)
            && weltnamen
                .iter()
                .any(|n| o == n || o.starts_with(&format!("{n}.")) || o.starts_with(&format!("{n}[")))
    };
    let mut gemeldet: Vec<String> = Vec::new();
    for (ort, span) in taten.schreibt.iter().chain(taten.liest.iter()) {
        if !bekannt(ort) || gemeldet.contains(ort) {
            continue;
        }
        let schreibend = taten.schreibt.iter().any(|(o, _)| o == ort);
        let gedeckt = if schreibend {
            schreibt.iter().any(|e| deckt(e, ort))
        } else {
            liest.iter().any(|e| deckt(e, ort))
        };
        if gedeckt {
            continue;
        }
        gemeldet.push(ort.clone());
        absagen.schiebe(
            Absage::fehler(
                "E011",
                *span,
                format!(
                    "`{ort}` is touched by this `traverse` in `{fname}` but stands in no `touches` effect"
                ),
            )
            .mit_notiz(
                "`touches` is the NARROWER, local promise beside `effects` -- whoever \
                    reads it counts on less contact than the body has",
            ),
        );
    }
}

fn rumpf_gegen_wirkungen(
    f: &FnDecl,
    w: &Wirkungen,
    b: &Block,
    konstanten: &[String],
    weltnamen: &[String],
    absagen: &mut Absagen,
) {
    let mut taten = Taten::default();
    sammle_taten(b, &mut taten);
    traverse_gegen_touches(b, &f.name.text, konstanten, weltnamen, absagen);

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
                    format!("`{}` writes `{ort}` but declares `pure`", f.name.text),
                )
                .mit_notiz("`pure` means: touches nothing -- not even by reading"),
            );
            continue;
        }
        if !schreibrechte.iter().any(|e| deckt(e, ort)) {
            absagen.schiebe(
                Absage::fehler(
                    "E005",
                    *span,
                    format!(
                        "`{ort}` is written but appears in no effect of `{}`",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "SPRACHE.md §7: `effects` is obligatory and not fail-open -- a \
                        missing clause is a missing promise, not an empty one",
                )
                .mit_notiz(format!(
                    "declared are: {}",
                    if schreibrechte.is_empty() {
                        "no write effect".to_string()
                    } else {
                        schreibrechte.join(", ")
                    }
                )),
            );
        }
    }

    // **Die Lesehaelfte -- Lesart A, seit 2026-08-16.**
    //
    // Bis hierher prueft der Pass Schreiben und `locks`. Das Lesen blieb offen, weil
    // `FRAGMENTE.md` ueberall ohne `reads`-Zeile liest und die Frage war, ob das ein Befund
    // ist oder die gemeinte Bedeutung. **Sie ist ein Befund.** Der Grund steht im `TODO.md`
    // und hat zwei Teile: E3-Konsistenz (nichts ist implizit, auch kein Lesen), und
    // Meldbarkeit -- diese Absage nennt Funktion UND Ort, die gruebere Lesart koennte nur
    // eine Gegend nennen.
    let leserechte: Vec<String> = w
        .liste
        .iter()
        .filter_map(|e| match &e.art {
            WirkungArt::Liest(o) => Some(o.text()),
            // **Ein `awaits`-Laden liest den Ort, den `publishes` nennt** -- wer
            // veroeffentlicht, hat ihn vorher gelesen zu duerfen; das ist keine Grosszuegigkeit,
            // sondern dieselbe Stelle unter zwei Namen.
            WirkungArt::Veroeffentlicht(o) => Some(o.text()),
            _ => None,
        })
        .collect();
    let mut gemeldet: Vec<String> = Vec::new();
    for (ort, span) in &taten.liest {
        let grund = ort.split(['.', '[', '-']).next().unwrap_or(ort);
        if lok.iter().any(|l| l == grund) {
            continue;
        }
        // **Ein Parameter ist kein Weltzustand.** Was der Aufrufer hereingibt, gehoert ihm;
        // seine `effects` decken es. Sonst muesste jede Funktion ihre eigene Signatur
        // nachdeklarieren -- eine Zeile, die nichts sagt.
        if f.parameter.iter().any(|p| p.name.text == grund) {
            continue;
        }
        if konstanten.iter().any(|k| k == grund) {
            continue; // Konstante -- keine Stelle der Welt
        }
        if !weltnamen.iter().any(|k| k == grund) {
            continue; // kein bekannter Weltzustand -- der Pass sagt nichts (s. Kopf)
        }
        if ist_rein {
            if gemeldet.iter().any(|g| g == ort) {
                continue;
            }
            gemeldet.push(ort.clone());
            absagen.schiebe(
                Absage::fehler(
                    "E010",
                    *span,
                    format!("`{}` reads `{ort}` but declares `pure`", f.name.text),
                )
                .mit_notiz("`pure` means: touches nothing -- not even by reading"),
            );
            continue;
        }
        if !leserechte.iter().any(|e| deckt(e, ort)) {
            if gemeldet.iter().any(|g| g == ort) {
                continue; // eine Fundstelle je Ort reicht; zehn Meldungen sind eine
            }
            gemeldet.push(ort.clone());
            absagen.schiebe(
                Absage::fehler(
                    "E010",
                    *span,
                    format!(
                        "`{ort}` is read but appears in no `reads` effect of `{}`",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "reading A: reads are declared as completely as writes -- a frame \
                        promise that knows only the write side says nothing about WHAT the \
                        function saw",
                )
                .mit_notiz(format!(
                    "declared are: {}",
                    if leserechte.is_empty() {
                        "no read effect".to_string()
                    } else {
                        leserechte.join(", ")
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
                        "`{}` takes `{ort}` EXCLUSIVELY but declares `locks shared {ort}`",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "declaring shared and taking exclusively is the dangerous direction: \
                        whoever reads the signature counts on concurrency that does not \
                        exist",
                )
                .mit_notiz("the converse is allowed -- declaring exclusive covers the shared acquisition"),
            );
            continue;
        }
        absagen.schiebe(
            Absage::fehler(
                "E006",
                *span,
                format!(
                    "`locks {}{ort}` is in the body but not in the effects of `{}`",
                    if *geteilt { "shared " } else { "" },
                    f.name.text
                ),
            )
            .mit_notiz("the lock order follows from the declared locks, not from the body"),
        );
    }
}

fn funktion(
    f: &FnDecl,
    modul: &str,
    g: &crate::aufrufgraph::Graph,
    konstanten: &[String],
    weltnamen: &[String],
    absagen: &mut Absagen,
) {
    match &f.effects {
        None => {
            // `spec fn` hat keine Laufzeitwirkung; fuer sie ist die Klausel freigestellt.
            if f.klasse != Some(FnKlasse::Spec) {
                absagen.schiebe(
                    Absage::fehler(
                        "E001",
                        f.name.span,
                        format!("`{}` has no `effects` clause", f.name.text),
                    )
                    .mit_notiz(
                        "SPRACHE.md §7: `effects` is obligatory and not fail-open",
                    )
                    .mit_notiz(
                        "the omission was at once the strongest promise and the cheapest \
                            one to write",
                    ),
                );
            }
        }
        Some(w) => {
            rein_allein(w, absagen);
            if let FnRumpf::Block(b) = &f.rumpf {
                rumpf_gegen_wirkungen(f, w, b, konstanten, weltnamen, absagen);
                aufrufwirkungen(f, modul, w, g, absagen);
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
                        "`divergent fn {}` does not name `diverges` among its effects",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "SYNTAX.md §14 writes `divergent fn idle() effects { diverges }` --\
                        the clause carries the divergence",
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
                    "a predicate as a body is allowed only for a `spec fn`",
                )
                .mit_notiz("`fndecl`: `= pred ;` only for `spec fn`"),
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
                    "`pure` stands next to {} -- `pure` means nothing is touched",
                    andere.join(", ")
                ),
            )
            .mit_notiz("either `effects { pure }` alone, or the effects without `pure`"),
        );
    }
    if rein.len() > 1 {
        absagen.schiebe(Absage::fehler(
            "E002",
            rein[1].span,
            "`pure` appears twice in the same effect list",
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
/// **Die Grobheit hat eine Richtung, und nur deshalb ist sie zulaessig.** Dieser Pass rechnet
/// ueber **Mengen**, nicht ueber **Pfade** — das ist die richtige Grobheit, *aber nur weil sie
/// hier in die SICHERE Richtung grob ist*: er sieht mehr Wirkungen als da sind, nie weniger.
/// **Wo dieselbe Grobheit in die unsichere Richtung zeigte, wird sie nicht angewandt** — s.
/// `diverges` unten. *Das ist R8 auf Analysen statt auf Absagen: bevor eine Analyse
/// vergroebert, wird die Richtung geprueft, nicht die Bequemlichkeit.* **Der naechste Pass,
/// der ueber Mengen rechnet, faengt mit dieser Frage an.**
///
/// **Und wo die Huelle unvollstaendig ist, gibt es einen DRITTEN Zustand** (R16 + R15): ein
/// Zyklus oder ein Gerufener ohne `effects` macht die Menge zu einer unteren Schranke. Daraus
/// wird **nicht abgesagt** — eine Absage aus einer unteren Schranke waere eine Behauptung.
/// **Aber auch nicht bestaetigt**: eine untere Schranke ist eine *unsichere* Deckung fuer
/// `pure`, und ein stilles Durchlassen waere die Ausweg-Zusicherung aus R15 durch die
/// Hintertuer — *„erfuellt, weil nichts passiert ist"*. Der ehrliche dritte Zustand heisst
/// **`E009` — unentscheidbar**, und er ist sichtbar, nicht gruen.
fn aufrufwirkungen(
    f: &FnDecl,
    modul: &str,
    w: &Wirkungen,
    g: &crate::aufrufgraph::Graph,
    absagen: &mut Absagen,
) {
    // **Eine Wirkung auf einen EIGENEN lokalen Namen ist hier eingelöst** (2026-08-19).
    //
    // Seit der Aufrufgraph die Parameternamen des Gerufenen durch die Argumente des Rufers
    // ersetzt, kommt `consumes p` beim Rufer als `consumes y` an — und `y` ist ein Name, den
    // niemand ausserhalb dieser Funktion kennt. **Ihn in der eigenen `effects`-Liste zu
    // verlangen hiesse, über eine Stelle zu sprechen, die es draussen nicht gibt.**
    //
    // *Vorher war beides falsch:* der Rufer musste `consumes p` schreiben — den Parameter
    // des GERUFENEN — und `E008` fiel auf sauberem Code.
    let mut hier: Vec<String> = Vec::new();
    if let FnRumpf::Block(b) = &f.rumpf {
        lokale(b, &mut hier);
    }
    let h = g.huelle(&g.schluessel_von(modul, &f.name.text));
    if let Some(grund) = &h.unvollstaendig {
        // Weder Absage noch Bestaetigung: der dritte Zustand, und er steht da.
        absagen.schiebe(
            Absage::hinweis(
                "E009",
                f.name.span,
                format!(
                    "the call effects of `{}` are undecidable: {grund}",
                    f.name.text
                ),
            )
            .mit_notiz(
                "the effect set is only a LOWER bound here -- no completeness follows from it",
            )
            .mit_notiz(
                "in particular a `pure` promise is NOT checkable at this site",
            ),
        );
        return;
    }
    let ist_rein = w.liste.iter().any(|e| matches!(e.art, WirkungArt::Rein));
    let eigene: Vec<String> = w.liste.iter().map(|e| e.art.benennung().to_string()).collect();
    for wirkung in &h.wirkungen {
        // Der Ort steht am Ende; `y.slots` und `y` zaehlen beide.
        if let Some((_, ort)) = wirkung.rsplit_once(' ') {
            let grund = ort.split(['.', '[']).next().unwrap_or(ort);
            if hier.iter().any(|l| l == grund) {
                continue;
            }
        }
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
                        "`{}` declares `pure` but calls something with `{wirkung}`",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "`effects` is compositional: the effects of the callees belong to the \
                        caller",
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
                        "`{}` calls something with `{wirkung}` but names no `{art}` effect",
                        f.name.text
                    ),
                )
                .mit_notiz(
                    "the effect comes from a callee -- `effects` covered only the first \
                        level until 2026-08-15",
                )
                .mit_notiz(format!(
                    "declared are: {}",
                    if eigene.is_empty() { "nichts".into() } else { eigene.join(", ") }
                )),
            );
        }
    }
}

/// **Die Domaene einer `traverse` ist ein Lesen.** `traverse s of c over slots of c` liest
/// `c` -- wer die Sammlung laeuft, greift sie an, auch wenn der Rumpf nur schreibt.
fn domaene_liest(d: &Domaene, t: &mut Taten) {
    match d {
        Domaene::SlotsVon(o)
        | Domaene::NachfahrenVon(o)
        | Domaene::VorfahrenVon(o)
        | Domaene::Schlange(o)
        | Domaene::ElementeVon(o)
        | Domaene::AbbildungenVon(o)
        | Domaene::KetteIn { ort: o, .. } => t.liest.push((o.text(), o.span)),
        // `fields of <pfad>` nennt einen TYP, keinen Ort; `threads` nennt gar nichts.
        Domaene::FelderVon(_) | Domaene::Threads => {}
    }
}
