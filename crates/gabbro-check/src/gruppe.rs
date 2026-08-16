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
                    format!("`group {}` nennt nur einen Traeger", g.name.text),
                )
                .mit_notiz(
                    "eine Gruppe existiert fuer eine Invariante ZWISCHEN Traegern -- was \
                     ueber einem einzigen gilt, ist eine `table … invariant`",
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
                        format!("`group {}` nennt `{}`, das kein Traeger ist", g.name.text, t.text),
                    )
                    .mit_notiz("Traeger sind `table`, `static` und `state`"),
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
                                "`{}` liegt in `group {}`, steht aber unter keiner Sperre",
                                t.text, g.name.text
                            ),
                        )
                        .mit_notiz(
                            "eine Verbindungs-Invariante ueber einem ungeschuetzten Traeger \
                             ist auf einem Mehrkerner keine Aussage -- der Abdruck der \
                             Gruppenoperation waere unvollstaendig",
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
                                "`group {}` spannt `{}` und `{}` -- beide `rank {}`",
                                g.name.text, a.1, b.1, a.2
                            ),
                        )
                        .mit_notiz(
                            "zwei Sperren gleichen Rangs haben keine Ordnung; eine \
                             Gruppenoperation koennte sie in zwei Richtungen nehmen, und \
                             genau daraus entsteht die Verklemmung",
                        )
                        .mit_notiz(
                            "die Ordnung wird NICHT an der Gruppe deklariert -- sie steht in \
                             den `rank`-Zahlen, und dort ist sie zu berichtigen",
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
                            "`invariant {}` in `group {}` nennt {} Traeger",
                            inv.name.text,
                            g.name.text,
                            treffer.len()
                        ),
                    )
                    .mit_notiz(
                        "eine Verbindungs-Invariante quantifiziert ueber MEHREREN Traegern -- \
                         was ueber einem einzigen gilt, gehoert an die `table … invariant`",
                    )
                    .mit_notiz(
                        "dieselbe Absage wie `U004`, eine Ebene tiefer: dort ist die \
                         Deklaration einelementig, hier die Aussage",
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
            let mut fehlend: Vec<String> = Vec::new();
            for t in &g.traeger {
                if let Some((sperre, _)) = schutz.get(&t.text) {
                    if !gehalten.iter().any(|h| h == sperre) && !fehlend.contains(sperre) {
                        fehlend.push(sperre.clone());
                    }
                }
            }
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
                                        "`{}` verlaesst `group {}` mit `{art}` im \
                                         Zwischenzustand",
                                        f.name.text, g.name.text
                                    ),
                                )
                                .mit_notiz(
                                    "zwischen dem ersten und dem letzten Schreibzugriff auf \
                                     die Traeger der Gruppe gilt die Verbindungs-Invariante \
                                     NICHT -- ein Weg, der hier hinausfuehrt, hinterlaesst \
                                     sie gebrochen",
                                )
                                .mit_notiz(
                                    "S17, dritte Pflicht: kein Zwischenaustritt. Der \
                                     Fehlerpfad ist die Stelle, an der das passiert, weil \
                                     dort niemand hinsieht",
                                )
                                .mit_notiz(match &anfang {
                                    Some((n, sp)) => format!(
                                        "der Zug faengt bei `{n}` an (Zeichen {})",
                                        sp.von
                                    ),
                                    None => "der Zug faengt am ersten Schreibzugriff an".into(),
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
                            "`{}` schreibt {} Traeger von `group {}`, haelt aber {} nicht",
                            f.name.text,
                            beruehrt.len(),
                            g.name.text,
                            fehlend.join(", ")
                        ),
                    )
                    .mit_notiz(
                        "die Verbindungs-Invariante gilt am Anfang und am Ende des Zuges, \
                         nicht dazwischen -- wer nur eine Haelfte sperrt, laesst den \
                         Zwischenzustand fuer einen anderen Kern sichtbar",
                    )
                    .mit_notiz(
                        "gemessen an V4 (`MESSUNGEN.md`, SWEEP): genau dieser Fall wird im \
                         Bestand von einem KOMMENTAR getragen, nicht von einer Zusage",
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
            StmtArt::LetSonst(x) => {
                // **Die stillste der drei.** `let x = f() else (e) { … }` sieht wie eine
                // Zuweisung aus und ist ein Austritt -- die einzige Fehlerfortpflanzung der
                // Sprache. Genau deshalb steht sie hier einzeln.
                aus.push(Ereignis::Austritt("let … else", s.span));
                ereignisse(&x.sonst, traeger, aus);
            }
            StmtArt::Sperrt(l) => ereignisse(&l.rumpf, traeger, aus),
            StmtArt::Wenn(w) => {
                for (_, r) in &w.zweige {
                    ereignisse(r, traeger, aus);
                }
                if let Some(r) = &w.sonst {
                    ereignisse(r, traeger, aus);
                }
            }
            StmtArt::Match(m) => {
                for z in &m.zweige {
                    ereignisse(&z.rumpf, traeger, aus);
                }
            }
            StmtArt::Bricht(x) => ereignisse(&x.rumpf, traeger, aus),
            StmtArt::Narrow(x) => ereignisse(&x.sonst, traeger, aus),
            StmtArt::Schleife(sch) => match sch.as_ref() {
                Schleife::Traverse(x) => ereignisse(&x.rumpf, traeger, aus),
                Schleife::Retry(x) => ereignisse(&x.rumpf, traeger, aus),
                Schleife::Forever(x) => ereignisse(&x.rumpf, traeger, aus),
            },
            _ => {}
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
            StmtArt::Sperrt(l) => {
                haelt.push(l.sperre.basis.text.clone());
                sammle(&l.rumpf, schreibt, haelt);
            }
            StmtArt::Wenn(w) => {
                for (_, r) in &w.zweige {
                    sammle(r, schreibt, haelt);
                }
                if let Some(r) = &w.sonst {
                    sammle(r, schreibt, haelt);
                }
            }
            StmtArt::Match(m) => {
                for z in &m.zweige {
                    sammle(&z.rumpf, schreibt, haelt);
                }
            }
            StmtArt::Bricht(x) => sammle(&x.rumpf, schreibt, haelt),
            StmtArt::Narrow(x) => sammle(&x.sonst, schreibt, haelt),
            StmtArt::LetSonst(x) => sammle(&x.sonst, schreibt, haelt),
            StmtArt::Schleife(sch) => match sch.as_ref() {
                Schleife::Traverse(x) => sammle(&x.rumpf, schreibt, haelt),
                Schleife::Retry(x) => sammle(&x.rumpf, schreibt, haelt),
                Schleife::Forever(x) => sammle(&x.rumpf, schreibt, haelt),
            },
            _ => {}
        }
    }
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
