//! **«K5.3» -- die Ausführungskontexte, und was sie einander verbieten.**
//!
//! `H013` nahm seit dem 2026-08-19 die **grobe** Antwort: *jeder `entry` ist ein Kontext, und
//! ein Platz, den einer davon schreibt, ist geteilt.* Grob in die sichere Richtung — aber zu
//! grob an drei Stellen, und alle drei stehen längst in der Grammatik:
//!
//! | Form | was sie sagt |
//! |---|---|
//! | `masks IRQ` | schliesst den Interruptkontext aus |
//! | `nested never` | der Eintritt unterbricht sich nicht selbst |
//! | `per cpu` | gehört genau einem Kern |
//!
//! ## Die Zeile, die ehrlich bleiben muss
//!
//! **Auf mehr als einem Kern schliesst `masks IRQ` gar nichts aus.** Ein zweiter Kern läuft
//! weiter, gleichgültig wie die Interruptmaske dieses Kerns steht. Die Ausnahmen dieser Matrix
//! gelten also **nur unter einer Annahme**, und die muss dastehen:
//!
//! ```gabbro
//! assume ein_kern "Dieser Kern läuft auf genau einem Prozessor."
//!     falsifier sonde_zweiter_kern;
//! ```
//!
//! **Ohne diese Zeile wird nichts ausgenommen** — `H013` bleibt, was es war. *Das ist der
//! Unterschied zwischen einer Lockerung, die man sieht, und einer, die der Prüfer sich selbst
//! erlaubt:* die Annahme steht im Zeugnis, unter „bewiesen unter A1…An", und ihr Falsifikator
//! ist eine Probe, die auf zwei Kernen bootet.
//!
//! > **Und darum ist `ein_kern` falsifizierbar und A10 nicht.** Ein zweiter Kern ist eine
//! > Tatsache, die man herstellen kann; eine Umordnung im Speichermodell ist es nicht.

use gabbro_syntax::ast::*;

/// Ein Ausführungskontext — heute ist das genau ein `entry`.
pub struct Kontext {
    pub name: String,
    /// `dispatch` — die Wurzel, von der aus die Wirkungen zählen.
    pub wurzel: String,
    pub modul: String,
    /// `nested never` — der Eintritt unterbricht sich selbst nicht.
    pub nie_verschachtelt: bool,
    /// Ein Eintritt über die IDT ist ein Interruptkontext; er kann preemptieren.
    pub unterbricht: bool,
    pub span: gabbro_syntax::span::Span,
}

pub fn erhebe(baum: &Programm) -> Vec<Kontext> {
    let mut aus = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Entry(e) = &item.art {
            aus.push(Kontext {
                name: e.name.text.clone(),
                wurzel: e.dispatch.text(),
                modul: modul.to_string(),
                nie_verschachtelt: matches!(e.verschachtelt, Some(Verschachtelt::Nie)),
                // **Was einen Eintritt zum Interruptkontext macht**, syntaktisch: er kommt
                // über die IDT. *Ein Syscall auch — aber der wird gerufen, nicht geworfen,
                // und er preemptiert niemanden.* `via` ist die einzige Stelle, an der die
                // Sprache den Unterschied heute ausspricht.
                unterbricht: e.via.as_ref().is_some_and(|v| v.text == "idt"),
                span: e.name.span,
            });
        }
    });
    aus
}

/// **Läuft unter der Annahme `ein_kern` überhaupt noch etwas gleichzeitig?**
///
/// Die Antwort ist eine Aussage über den ZUGRIFF, nicht über den Kontext: greift jeder
/// schreibende Weg mit maskierten Interrupts zu, kann ihn auf einem Kern nichts unterbrechen.
pub fn ein_kern_deckt(maskiert: bool, k: &Kontext) -> bool {
    // Maskiert schliesst jeden Interruptkontext aus; `nested never` den Eintritt selbst.
    maskiert && (k.nie_verschachtelt || !k.unterbricht)
}

/// **`gabbro kontexte` — je Platz die Kontextmenge, und daneben die ZAHL.**
///
/// Der Bericht steht in `PLAN.md` als Tor, und der Grund ist W1: *ohne die Zahl der berührten
/// Plätze sieht ein leerer Lauf aus wie ein bestandener.* Auf diesem Korpus ist er leer, weil
/// alle vier `dispatch`-Ziele `extern fn` sind — **und genau das soll man sehen.**
pub fn zeige(baum: &Programm, datei: &str) -> String {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let g = crate::aufrufgraph::erhebe_mit(baum, &u);
    let kontexte = erhebe(baum);
    let annahmen = crate::annahmen(baum);
    let ein_kern = annahmen.contains_key("ein_kern");

    let mut aus = format!("# {datei}\n\n");
    aus.push_str(&format!(
        "contexts: {}   ·   assumption `ein_kern`: {}\n\n",
        kontexte.len(),
        if ein_kern {
            "YES -- the matrix grants exemptions"
        } else {
            "no -- nothing is exempt"
        }
    ));
    if kontexte.is_empty() {
        aus.push_str("  (no `entry` -- without a context root the question is not asked)\n");
        return aus;
    }

    let mut zeilen: Vec<String> = Vec::new();
    let mut plaetze = 0usize;
    let mut ohne_rumpf = 0usize;
    for k in &kontexte {
        let Some(voll) = g.aufloesen(&u, &k.modul, &k.wurzel) else {
            ohne_rumpf += 1;
            zeilen.push(format!("  {:<16} {} -- unknown", k.name, k.wurzel));
            continue;
        };
        let h = g.huelle(&voll);
        if let Some(grund) = &h.unvollstaendig {
            ohne_rumpf += 1;
            zeilen.push(format!("  {:<16} {} -- incomplete: {grund}", k.name, k.wurzel));
            continue;
        }
        let maskiert = h.wirkungen.iter().any(|w| w.starts_with("masks "));
        let geschrieben: Vec<&str> = h
            .wirkungen
            .iter()
            .filter_map(|w| w.strip_prefix("writes "))
            .collect();
        plaetze += geschrieben.len();
        zeilen.push(format!(
            "  {:<16} {:<32} writes {:>3}{}{}",
            k.name,
            k.wurzel,
            geschrieben.len(),
            if maskiert { "  masks" } else { "" },
            if k.nie_verschachtelt { "  nested-never" } else { "" },
        ));
        for p in geschrieben {
            zeilen.push(format!("      {p}"));
        }
    }
    aus.push_str(&zeilen.join("\n"));
    aus.push('\n');
    // **Die Zahl daneben, und sie ist der Zweck des Berichts.**
    aus.push_str(&format!(
        "\nplaces touched: {plaetze}   ·   context roots with no visible body: {ohne_rumpf} of {}\n",
        kontexte.len()
    ));
    if plaetze == 0 {
        aus.push_str(
            "\n  **ZERO BITE.** No context reaches a place Gabbro can see -- the rule\n\
             \x20 `H013` does not fall here a single time. *An empty run is not a passed\n\
             \x20 one* (W1).\n",
        );
    }
    aus
}
