//! **«ABI» — die Bibliotheksschnittstelle, und sie ist eine BRÜCKE MIT MAUT.**
//!
//! Gemessen 2026-08-20: ohne Brücke fällt eine Zusage an der Dateigrenze **laut**, nicht
//! lautlos — `use bib::tu;` über die Grenze gibt `E009` *(„unknown to the graph")* und
//! `K003` *(„promises costs, but `tu` is not declared here")*, also einen **Fehler**. *Es
//! fehlte kein Riegel, es fehlte eine Brücke.*
//!
//! ## Die Form, und warum sie so billig ist
//!
//! Ein `.gabi` ist **gültiger Gabbro-Quelltext**: die exportierten Deklarationen einer
//! Einheit, ohne Rümpfe. Damit liest ihn derselbe Parser, prüfen ihn dieselben Pässe, und es
//! gibt **kein zweites Format, das auseinanderlaufen kann** — genau die Klasse, die dieser
//! Ordner sonst „zwei Register über derselben Sache" nennt.
//!
//! ```text
//! -- @gabi 1  lib bib
//! module bib {
//! static mut z : u32 = 0;
//! extern fn tu() effects { writes z } costs <= 1 ops;
//! }
//! ```
//!
//! ## Was hier NICHT drinsteht, und das ist Absicht
//!
//! **Keine Hardwareannahmen.** Eine Bibliothek, die ihre `assume`-Zeilen mitschickt, zwingt
//! jedem Importeur ihre Maschine auf; und ein `override` beim Import ist keine Ersetzung,
//! sondern eine **Beweispflicht** (siehe «ABI4» in `PLAN.md`). *Solange die Pflicht nicht
//! gezählt wird, ist es ehrlicher, die Annahmen gar nicht erst über die Grenze zu tragen.*
//!
//! **Und keine Sperrränge.** `lock … rank 0` ist eine **absolute Zahl**; zwei unabhängig
//! geschriebene Bibliotheken vergeben beide `rank 0`. *Absolute Zahlen komponieren nicht* —
//! das braucht «ABI2» (Ordnung statt Rang), und das ist eine Sprachänderung.
//!
//! > **Was eine ABI ausdrücklich nicht darf: eine Klasse von geprüft auf behauptet
//! > absenken.** Was noch nicht sauber über die Grenze geht, geht gar nicht über sie.
//!
//! ## Die C-Seite ist keine
//!
//! Das Erzeugnis benutzt **die gewöhnliche C-ABI** — Prototyp, äusserer Bindungsname, sonst
//! nichts. Es gibt keine Gabbro-Aufrufkonvention und keine Laufzeit. *Eine Bibliothek, die
//! man nur mit ihrem eigenen Übersetzer benutzen kann, ist keine Bibliothek.*

use gabbro_syntax::ast::*;

/// Die Kopfzeile, an der ein `.gabi` erkennbar ist.
pub const MARKE: &str = "-- @gabi 1";

/// **Schreibt die Schnittstelle einer Einheit.** Nur `pub`-Items, nur Deklarationen.
///
/// Was mitgeht, ist genau das, was der Rufer zum PRÜFEN braucht:
///
/// * die Signatur mit `requires`/`ensures`/`effects`/`costs` — die Sprache der Aufrufgrenze,
/// * die WELTZUSTÄNDE, die eine `effects`-Liste nennt (sonst nennt sie ins Leere),
/// * die Trägerdeklarationen, ohne die ein `index into T` keine Schranke hat.
pub fn schreibe(baum: &Programm, quelle: &str) -> String {
    let mut aus = String::new();
    let mut nach_modul: std::collections::BTreeMap<String, Vec<String>> = Default::default();
    aus.push_str(MARKE);
    aus.push_str("\n-- Written by `gabbro abi`. Do not edit: the source is the `.gab`, and a\n");
    aus.push_str("-- second register over the same thing is the very class this folder is\n");
    aus.push_str("-- written against.\n");
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let zeile = match &item.art {
            ItemArt::Funktion(f) => {
                if !f.oeffentlich || matches!(f.klasse, Some(FnKlasse::Spec)) {
                    return;
                }
                Some(kopf_von(f, quelle))
            }
            // **Die Welt, die eine `effects`-Liste nennen darf.** Ohne sie zeigt `writes z`
            // beim Importeur auf nichts, und `E010` haette recht.
            ItemArt::Statisch(x) if x.oeffentlich => Some(text_von(item, quelle)),
            ItemArt::Konst(k) if k.oeffentlich => Some(text_von(item, quelle)),
            ItemArt::Tabelle(_) | ItemArt::Atomic(_) => Some(text_von(item, quelle)),
            ItemArt::Typ(t) if t.oeffentlich => Some(text_von(item, quelle)),
            _ => None,
        };
        if let Some(z) = zeile {
            nach_modul.entry(modul.to_string()).or_default().push(z);
        }
    });
    // **EIN Block je Modul.** Die erste Fassung schrieb je ITEM einen -- und `N001` (*„`bib`
    // is declared twice in this scope"*) hatte recht. *Gefunden vom eigenen Namenspass, an
    // der eigenen Schnittstelle.*
    for (modul, zeilen) in &nach_modul {
        aus.push_str(&format!("\nmodule {modul} {{\n{}\n}}\n", zeilen.join("\n")));
    }
    aus
}

/// Der Quelltext eines Items, wörtlich — der Parser hat ihn schon gelesen, also gibt es
/// keinen zweiten Schreiber, der ihn anders schreiben könnte.
fn text_von(item: &Item, quelle: &str) -> String {
    quelle[item.span.von as usize..item.span.bis as usize].to_string()
}

/// **Der Kopf einer Funktion ohne ihren Rumpf** — aus der Quelle geschnitten, bis zur
/// öffnenden Klammer, und mit `extern` davor.
///
/// *Warum `extern`:* der Rumpf steht woanders. **Dass er GEPRÜFT woanders steht und nicht
/// bloss angenommen, ist die Aussage, die diese Datei noch nicht trägt** — sie steht in
/// «ABI3», der Vereinigung der Zeugnisse. Bis dahin ist ein Import ehrlich ein `extern fn`
/// mit Vertrag: *dieselbe Vertrauensfläche wie heute, aber die Namen lösen auf.*
fn kopf_von(f: &FnDecl, quelle: &str) -> String {
    let von = f.span.von as usize;
    let rest = &quelle[von..];
    let bis = match &f.rumpf {
        FnRumpf::Block(b) => (b.span.von as usize).saturating_sub(von),
        _ => rest.find(';').map(|i| i + 1).unwrap_or(rest.len()),
    };
    let kopf = rest[..bis.min(rest.len())].trim_end();
    // **Die Klasse faellt weg, `extern` tritt an ihre Stelle.** Die Spanne beginnt HINTER
    // `pub` (das Wort steht im Flag, nicht in der Spanne) -- gemessen am ersten `.gabi`, das
    // `extern impl fn` schrieb.
    let mut ohne_klasse = kopf.trim_start();
    for w in ["pub ", "impl ", "raw ", "prim ", "divergent ", "const "] {
        if let Some(r) = ohne_klasse.strip_prefix(w) {
            ohne_klasse = r.trim_start();
        }
    }
    // **`pub` bleibt.** Das Item steht im `.gabi`, WEIL es oeffentlich ist -- ihm die
    // Sichtbarkeit zu nehmen hiesse, `N025` gegen den Importeur zu wenden, der alles richtig
    // gemacht hat. *Gemessen am ersten Import, den die eigene Schnittstelle abwies.*
    format!("pub extern {};", ohne_klasse.trim_end_matches(';').trim_end())
}
