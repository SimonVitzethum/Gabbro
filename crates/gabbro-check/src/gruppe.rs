//! **Die Traegergruppe — der Pass zur Verbindungs-Invariante.**
//!
//! ## Woher der Bedarf kommt, und er ist gemessen
//!
//! `MESSUNGEN.md`, *SWEEP der Verbindungs-Invarianten* (2026-08-16): vier Invarianten
//! zwischen je zwei Traegern im Bestand. **Drei liegen unter EINER Sperre** (`refcount`,
//! Spendenkanten, `queued` gegen Bereitliste). **Die vierte nicht:**
//!
//! > **V4 — die Endpoint-Warteschlange gegen den Thread-Zustand.** `t ∈ ep.receivers`
//! > genau dann, wenn `IPC ∈ tcbs[t].reasons`. Zwei Strukturen, **zwei Kisten, zwei
//! > Sperrklassen** mit deklarierter Ordnung `EPS[i] < SCHEDS[core]`.
//!
//! Und der Bestand traegt sie **von Hand**: `caprock-microkit/src/lib.rs`:1303 ist ein
//! Kommentar, der erklaert, warum eine Funktion dort steht, wo sie steht — naehme sie `EPS`
//! unter `SCHEDS`, drehte sie die Ordnung um. *Genau diesen Kommentar macht `U003`
//! ueberfluessig.*
//!
//! ## Was dieser Pass NICHT ist
//!
//! **Er prueft keine Invariante.** Die Gruppe hat heute keine `invariant`-Klausel; sie nennt
//! ihre Traeger. Was hier faellt, ist der **Sperrabdruck** — die Vorbedingung dafuer, dass
//! eine Invariante ueberhaupt formulierbar waere. *Das steht hier, damit niemand die Deckung
//! groesser liest, als sie ist: `U003` sagt „du haeltst nicht alles, was du anfasst", nicht
//! „deine Invariante haelt".*

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::BTreeMap;

/// Welche Sperre schuetzt welchen Traeger, und mit welchem Rang.
fn sperren_je_traeger(baum: &Programm, u: &crate::umgebung::Umgebung) -> BTreeMap<String, (String, i128)> {
    let mut aus = BTreeMap::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Lock(l) = &item.art {
            let rang = u.konst_wert("", &l.rang).unwrap_or(0);
            for o in &l.schuetzt {
                aus.insert(o.basis.text.clone(), (l.name.text.clone(), rang));
            }
        }
    });
    aus
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let schutz = sperren_je_traeger(baum, &u);
    let mut traeger_namen: Vec<String> = Vec::new();
    // **Alle deklarierten Namen, nicht nur die Traeger** -- der Unterschied entscheidet, ob
    // `U001` spricht. Ein Name, der ueberhaupt nicht deklariert ist, gehoert dem Namenspass;
    // in einem AUSSCHNITT ist er normal (`SYNTAX.md` zeigt Formen, keine Programme). Ein
    // Name, der deklariert ist und **kein Traeger**, ist der Fall, den nur dieser Pass sieht:
    // `group G over { GRENZE, Faeden }` -- eine Konstante in einer Traegergruppe.
    //
    // *Dieselbe Entscheidung wie bei `E010` am selben Tag, und aus demselben Grund: eine
    // Absage ueber einem unaufloesbaren Namen ist Laerm, der die echten zudeckt.*
    let mut alle_namen: Vec<String> = Vec::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let Some(n) = item.art.name() {
            alle_namen.push(n.text.clone());
        }
        match &item.art {
            ItemArt::Tabelle(t) => traeger_namen.push(t.name.text.clone()),
            ItemArt::Statisch(s) => traeger_namen.push(s.name.text.clone()),
            ItemArt::State(s) => traeger_namen.push(s.name.text.clone()),
            _ => {}
        }
    });

    let mut gruppen: Vec<GruppeDecl> = Vec::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Gruppe(g) = &item.art {
            gruppen.push(g.clone());
        }
    });

    for g in &gruppen {
        // **U004 -- eine Gruppe mit einem Mitglied ist eine Tabelle.**
        if g.traeger.len() < 2 {
            absagen.schiebe(
                Absage::fehler(
                    "U004",
                    g.span,
                    format!("`group {}` names only one carrier", g.name.text),
                )
                .mit_notiz(
                    "a group exists for an invariant BETWEEN carriers -- what holds over a \
                     single one is a `table … invariant`",
                ),
            );
        }
        let mut raenge: Vec<(String, String, i128)> = Vec::new();
        for t in &g.traeger {
            if !alle_namen.iter().any(|n| n == &t.text) {
                continue; // unbekannt -- das ist der Namenspass, nicht dieser
            }
            if !traeger_namen.iter().any(|n| n == &t.text) {
                absagen.schiebe(
                    Absage::fehler(
                        "U001",
                        t.span,
                        format!("`group {}` names `{}`, which is not a carrier", g.name.text, t.text),
                    )
                    .mit_notiz("carriers are `table`, `static` and `state`"),
                );
                continue;
            }
            match schutz.get(&t.text) {
                Some((sperre, rang)) => raenge.push((t.text.clone(), sperre.clone(), *rang)),
                None => {
                    absagen.schiebe(
                        Absage::fehler(
                            "U002",
                            t.span,
                            format!(
                                "`{}` is in `group {}` but sits under no lock",
                                t.text, g.name.text
                            ),
                        )
                        .mit_notiz(
                            "a connecting invariant over an unprotected carrier says nothing on a \
                             multicore machine -- the footprint of the group operation \
                             would be incomplete",
                        ),
                    );
                }
            }
        }
        // **Gleicher Rang bei ZWEI Sperren: die Ordnung ist undefiniert.**
        //
        // Das ist die Absage, die der Sweep-Befund verlangt. Zwei Traeger unter EINER Sperre
        // sind in Ordnung (V1-V3); zwei unter ZWEI Sperren brauchen eine Ordnung, und die
        // kommt aus `rank`. Sind die Raenge gleich, gibt es keine -- und eine
        // Gruppenoperation koennte sie in zwei Richtungen nehmen.
        for (i, a) in raenge.iter().enumerate() {
            for b in raenge.iter().skip(i + 1) {
                if a.1 != b.1 && a.2 == b.2 {
                    absagen.schiebe(
                        Absage::fehler(
                            "U005",
                            g.span,
                            format!(
                                "`group {}` spans `{}` and `{}` -- both `rank {}`",
                                g.name.text, a.1, b.1, a.2
                            ),
                        )
                        .mit_notiz(
                            "two locks of equal rank have no order; a group operation could take \
                             them in either direction, and that is exactly where the \
                             deadlock comes from",
                        )
                        .mit_notiz(
                            "the order is NOT declared at the group -- it lives in the `rank` \
                             numbers, and that is where it must be corrected",
                        ),
                    );
                }
            }
        }
    }

    // **U007 -- die Verbindungs-Invariante muss verbinden.**
    //
    // Die dritte der drei S17-Pflichten ist die Invariante selbst, und der Pruefer kann sie
    // nicht BEWEISEN -- das ist Beweisersache. Was er kann, ist die Frage stellen, die die
    // Gruppe ueberhaupt rechtfertigt:
    //
    // > **Nennt diese Aussage mehr als einen Traeger der Gruppe?**
    //
    // Tut sie es nicht, gehoert sie an die Tabelle. Das ist dieselbe Absage wie `U004`, nur
    // eine Ebene tiefer: dort ist die DEKLARATION einelementig, hier die AUSSAGE. *Ohne diese
    // Pruefung waere `group` eine bequemere Schreibweise fuer `table … invariant` -- und ein
    // Konstrukt, das nur bequemer ist, hat in diesem Ordner keinen Beleg.*
    for g in &gruppen {
        for inv in &g.invarianten {
            let mut genannt: Vec<String> = Vec::new();
            pred_namen(&inv.pred, &mut genannt);
            let treffer: Vec<&Ident> = g
                .traeger
                .iter()
                .filter(|t| genannt.iter().any(|n| n == &t.text))
                .collect();
            if treffer.len() < 2 {
                absagen.schiebe(
                    Absage::fehler(
                        "U007",
                        inv.span,
                        format!(
                            "`invariant {}` in `group {}` names {} carriers",
                            inv.name.text,
                            g.name.text,
                            treffer.len()
                        ),
                    )
                    .mit_notiz(
                        "a connecting invariant quantifies over SEVERAL carriers -- what holds \
                         over a single one belongs on the `table … invariant`",
                    )
                    .mit_notiz(
                        "the same refusal as `U004`, one level down: there the DECLARATION is \
                         a singleton, here the STATEMENT is",
                    ),
                );
            }
        }
    }

    if gruppen.is_empty() {
        return;
    }
    // **U003 -- der Sperrabdruck am Rumpf.**
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let FnRumpf::Block(b) = &f.rumpf else {
            return;
        };
        let mut geschrieben: Vec<String> = Vec::new();
        let mut gehalten: Vec<String> = Vec::new();
        sammle(b, &mut geschrieben, &mut gehalten);
        for g in &gruppen {
            let beruehrt: Vec<&String> = g
                .traeger
                .iter()
                .map(|t| &t.text)
                .filter(|t| geschrieben.iter().any(|w| w == *t))
                .collect();
            // **Ein Traeger allein ist kein Gruppenzug.** Erst zwei machen den
            // Zwischenzustand beobachtbar, und nur dann verlangt die Gruppe ihren Abdruck.
            if beruehrt.len() < 2 {
                continue;
            }
            // **Der Abdruck gilt JE SCHREIBSTELLE.** Vorher wurde er ueber den ganzen
            // Rumpf summiert -- zwei `locks`-Bloecke NACHEINANDER sahen damit aus wie zwei
            // gleichzeitig gehaltene Sperren. *Zwischen ihnen ist die Gruppe offen.*
            let traeger_namen: Vec<String> = g.traeger.iter().map(|t| t.text.clone()).collect();
            let mut stellen_sperren: Vec<(String, Span, Vec<String>)> = Vec::new();
            schreibstellen(b, &traeger_namen, &mut Vec::new(), &mut stellen_sperren);
            let noetig: Vec<String> = g
                .traeger
                .iter()
                .filter_map(|t| schutz.get(&t.text).map(|(s, _)| s.clone()))
                .fold(Vec::new(), |mut acc, s| {
                    if !acc.contains(&s) {
                        acc.push(s);
                    }
                    acc
                });
            let mut fehlend: Vec<String> = Vec::new();
            for (_, _, hier) in &stellen_sperren {
                for s in &noetig {
                    if !hier.contains(s) && !fehlend.contains(s) {
                        fehlend.push(s.clone());
                    }
                }
            }
            let _ = &gehalten;
            // **U006 -- der Zwischenaustritt.** Erst pruefen, wenn die Gruppe wirklich
            // beruehrt ist (>= 2 Traeger), sonst gibt es keinen Zug, den man verlassen kann.
            let mut ev = Vec::new();
            let traeger_liste: Vec<String> = g.traeger.iter().map(|t| t.text.clone()).collect();
            ereignisse(b, &traeger_liste, &mut ev);
            let erste = ev.iter().position(|e| matches!(e, Ereignis::Schreibt(..)));
            let letzte = ev.iter().rposition(|e| matches!(e, Ereignis::Schreibt(..)));
            if let (Some(i), Some(j)) = (erste, letzte) {
                let mut verschieden = Vec::new();
                for e in &ev {
                    if let Ereignis::Schreibt(n, _) = e {
                        if !verschieden.contains(n) {
                            verschieden.push(n.clone());
                        }
                    }
                }
                if verschieden.len() >= 2 {
                    // Der erste Schreibzugriff -- er macht den Zwischenzustand auf, und die
                    // Absage nennt ihn, weil die Stelle des AUSTRITTS allein nicht sagt,
                    // wovon man austritt.
                    let anfang = match &ev[i] {
                        Ereignis::Schreibt(n, sp) => Some((n.clone(), *sp)),
                        _ => None,
                    };
                    for e in &ev[i..j] {
                        if let Ereignis::Austritt(art, span) = e {
                            absagen.schiebe(
                                Absage::fehler(
                                    "U006",
                                    *span,
                                    format!(
                                        "`{}` leaves `group {}` via `{art}` while in the \
                                         intermediate state",
                                        f.name.text, g.name.text
                                    ),
                                )
                                .mit_notiz(
                                    "between the first and the last write to the carriers of the \
                                     group the connecting invariant does NOT hold -- a path \
                                     leaving here leaves it broken",
                                )
                                .mit_notiz(
                                    "S17, third obligation: no intermediate exit. The error path is \
                                     where this happens, because nobody looks there",
                                )
                                .mit_notiz(match &anfang {
                                    Some((n, sp)) => format!(
                                        "the move starts at `{n}` (character {})",
                                        sp.von
                                    ),
                                    None => "the move starts at the first write".into(),
                                }),
                            );
                            break; // eine Meldung je Funktion und Gruppe reicht
                        }
                    }
                }
            }
            if !fehlend.is_empty() {
                absagen.schiebe(
                    Absage::fehler(
                        "U003",
                        f.name.span,
                        format!(
                            "`{}` writes {} carriers of `group {}` but does not hold {}",
                            f.name.text,
                            beruehrt.len(),
                            g.name.text,
                            fehlend.join(", ")
                        ),
                    )
                    .mit_notiz(
                        "the connecting invariant holds at the start and at the end of the \
                         move, not in between -- locking only one half leaves the \
                         intermediate state visible to another core",
                    )
                    .mit_notiz(
                        "measured at V4 (`MESSUNGEN.md`, SWEEP): in the existing tree this \
                         very case is carried by a COMMENT, not by a promise",
                    ),
                );
            }
        }
    });
}

/// Ein Ereignis im Rumpf, **in Quellreihenfolge** -- fuer `U006`.
enum Ereignis {
    /// Ein Traeger wird geschrieben.
    Schreibt(String, Span),
    /// Der Rumpf verlaesst den Zug: `return`, `leave`, der Sonst-Zweig von `let … else`.
    Austritt(&'static str, Span),
}

/// **U006 -- der Zwischenaustritt, die dritte Pflicht aus S17.**
///
/// Die Schablone verlangt dreierlei: (a) die Sperren in Rangordnung, (b) die Invariante am
/// Anfang UND am Ende des Zuges, (c) **kein Zwischenaustritt**. (a) traegt `U003`/`U005`.
/// (b) braucht die Invariantenklausel, die es noch nicht gibt. **(c) ist heute pruefbar**, und
/// zwar ohne jede Erzeugung:
///
/// > Wer Traeger A geschrieben hat und den Rumpf verlaesst, **bevor** er B geschrieben hat,
/// > hinterlaesst die Gruppe im Zwischenzustand -- und der Fehlerpfad ist genau die Stelle,
/// > an der das passiert, weil dort niemand hinsieht.
///
/// Die Reihenfolge ist die **Quellreihenfolge** des rekursiven Abstiegs. Das ist grob, und
/// die Richtung stimmt (W9): ein Austritt in einem Zweig, der den zweiten Schreibzugriff gar
/// nicht erreichen kann, wird trotzdem gemeldet. **Zu viel zu melden ist hier die sichere
/// Seite** -- die Absage sagt „hier verlaesst ein Weg den Zug", und wer weiss, dass dieser
/// Weg nicht existiert, hat den Beweis dafuer zu schreiben, nicht der Pass.
fn ereignisse(b: &Block, traeger: &[String], aus: &mut Vec<Ereignis>) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Zuweisung(z) => merke(&z.ziel.basis.text, s.span, traeger, aus),
            StmtArt::Publish(p) => merke(&p.ziel.basis.text, s.span, traeger, aus),
            StmtArt::Exchange(e) => merke(&e.ort.basis.text, s.span, traeger, aus),
            StmtArt::Return(_) => aus.push(Ereignis::Austritt("return", s.span)),
            StmtArt::Leave(_) => aus.push(Ereignis::Austritt("leave", s.span)),
            StmtArt::LetSonst(_) => {
                // **Die stillste der drei.** `let x = f() else (e) { … }` sieht wie eine
                // Zuweisung aus und ist ein Austritt -- die einzige Fehlerfortpflanzung der
                // Sprache. Genau deshalb steht sie hier einzeln.
                aus.push(Ereignis::Austritt("let … else", s.span));
            }
            _ => {}
        }
        // **Der Abstieg über `crate::unterbloecke`** — vorher fehlte `observes`, und ein
        // Schreiben an einem Gruppenträger in einem RCU-Leseblock kam im Abdruck nicht an.
        for k in crate::unterbloecke(s) {
            ereignisse(k, traeger, aus);
        }
    }
}

fn merke(name: &str, span: Span, traeger: &[String], aus: &mut Vec<Ereignis>) {
    if traeger.iter().any(|t| t == name) {
        aus.push(Ereignis::Schreibt(name.to_string(), span));
    }
}

fn sammle(b: &Block, schreibt: &mut Vec<String>, haelt: &mut Vec<String>) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Zuweisung(z) => schreibt.push(z.ziel.basis.text.clone()),
            StmtArt::Publish(p) => schreibt.push(p.ziel.basis.text.clone()),
            StmtArt::Exchange(e) => schreibt.push(e.ort.basis.text.clone()),
            StmtArt::Sperrt(l) => haelt.push(l.sperre.basis.text.clone()),
            _ => {}
        }
        for k in crate::unterbloecke(s) {
            sammle(k, schreibt, haelt);
        }
    }
}

/// **Jeder Schreibzugriff mit den Sperren, die IN DIESEM AUGENBLICK gehalten werden**
/// (Rezension 2026-08-20).
///
/// `sammle` sammelt flach über den ganzen Rumpf. Damit sahen
///
/// ```gabbro
/// locks PUNKTE { Endpunkte.slots[e].wartet = t; }
/// locks PLAN   { Faeden.slots[t].gruende  = 1; }
/// ```
///
/// aus wie *„beide Sperren gehalten"* — und die Gruppe `over { Endpunkte, Faeden }` ging mit
/// **null Fehlern** durch. Geschachtelt fiel dieselbe Datei an `U006`.
///
/// > **Ein Sperrabdruck ist eine Aussage über einen ZEITPUNKT, nicht über eine Datei.**
/// > Zwischen den beiden Blöcken ist die Gruppe offen und jeder andere Faden sieht sie so.
///
/// *Der Fall lag einen syntaktischen Schritt neben der bestehenden Giftprobe* — genau die
/// Klasse, die diese Rezension über den ganzen Korpus benennt.
fn schreibstellen(
    b: &Block,
    traeger: &[String],
    gehalten: &mut Vec<String>,
    aus: &mut Vec<(String, Span, Vec<String>)>,
) {
    for s in &b.anweisungen {
        let ziel = match &s.art {
            StmtArt::Zuweisung(z) => Some(&z.ziel.basis.text),
            StmtArt::Publish(p) => Some(&p.ziel.basis.text),
            StmtArt::Exchange(e) => Some(&e.ort.basis.text),
            _ => None,
        };
        if let Some(n) = ziel {
            if traeger.iter().any(|t| t == n) {
                aus.push((n.clone(), s.span, gehalten.clone()));
            }
        }
        // Ein `locks L { … }` gilt GENAU in seinem Block -- danach ist es wieder weg.
        let neu = matches!(&s.art, StmtArt::Sperrt(_));
        if let StmtArt::Sperrt(l) = &s.art {
            gehalten.push(l.sperre.basis.text.clone());
        }
        for k in crate::unterbloecke(s) {
            schreibstellen(k, traeger, gehalten, aus);
        }
        if neu {
            gehalten.pop();
        }
    }
}

/// Wie `pred_namen`, öffentlich — `N022` stellt dieselbe Frage an ein `floor`.
pub fn pred_namen_oeffentlich(p: &Pred, aus: &mut Vec<String>) {
    pred_namen(p, aus)
}

/// Alle **Grundnamen**, die ein Praedikat nennt -- fuer `U007`.
fn pred_namen(p: &Pred, aus: &mut Vec<String>) {
    match &p.art {
        PredArt::Vergleich(e) => expr_namen(e, aus),
        PredArt::Element(e, d) => {
            expr_namen(e, aus);
            domaene_namen(d, aus);
        }
        PredArt::Erreicht { von, nach, .. } => {
            aus.push(von.basis.text.clone());
            aus.push(nach.basis.text.clone());
        }
        PredArt::Quantor(q) => {
            domaene_namen(&q.domaene, aus);
            pred_namen(&q.rumpf, aus);
        }
        PredArt::Klammer(x) | PredArt::Nicht(x) => pred_namen(x, aus),
        PredArt::Und(a, b) | PredArt::Oder(a, b) | PredArt::Folgt(a, b) => {
            pred_namen(a, aus);
            pred_namen(b, aus);
        }
        PredArt::Held { .. } => {}
    }
}

fn domaene_namen(d: &Domaene, aus: &mut Vec<String>) {
    match d {
        Domaene::SlotsVon(o)
        | Domaene::NachfahrenVon(o)
        | Domaene::VorfahrenVon(o)
        | Domaene::Schlange(o)
        | Domaene::ElementeVon(o)
        | Domaene::AbbildungenVon(o)
        | Domaene::KetteIn { ort: o, .. } => aus.push(o.basis.text.clone()),
        Domaene::FelderVon(pf) => {
            if let Some(i) = pf.teile.last() {
                aus.push(i.text.clone());
            }
        }
        Domaene::Threads => {}
    }
}

fn expr_namen(e: &Expr, aus: &mut Vec<String>) {
    match &e.art {
        ExprArt::Ort(o) => {
            aus.push(o.basis.text.clone());
            for suf in &o.suffixe {
                if let OrtSuffix::Index(ix) = suf {
                    expr_namen(ix, aus);
                }
            }
        }
        ExprArt::Klammer(x) | ExprArt::Unaer(_, x) => expr_namen(x, aus),
        ExprArt::Binaer(_, a, b) => {
            expr_namen(a, aus);
            expr_namen(b, aus);
        }
        ExprArt::Ruf(r) => {
            for a in &r.argumente {
                expr_namen(a, aus);
            }
        }
        _ => {}
    }
}
