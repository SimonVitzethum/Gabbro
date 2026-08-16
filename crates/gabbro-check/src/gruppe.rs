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
