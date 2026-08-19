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

/// Ein Item ohne eigenen Namen (ein `use`) -- es wird nie ueber seinen Namen geholt.
static LEER: String = String::new();

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
    // **Die Schnittstelle ist ein FIXPUNKT, kein Durchgang** (2026-08-20).
    //
    // `table` und `atomic` haben kein `pub` -- die Grammatik kennt keins -- und standen
    // darum als einzige Item-Arten UNBEDINGT im `.gabi`. Gemessen an
    // `beispiele/34-markierter-wert.gab`, wo nichts oeffentlich ist: die Schnittstelle trug
    // die Tabelle samt `count NANFRAGEN` und `was : Nachricht` hinaus -- **zwei Namen, die
    // sie selbst nicht erklaert.**
    //
    // > *Eine Schnittstelle, die einen Namen nennt und nicht erklaert, ist keine.*
    //
    // Und ein Durchgang reicht nicht: `T` kommt mit, weil ein `index into T` es nennt --
    // dann nennt `T` seinerseits `count N`, und `N` muss ebenfalls mit. Darum wird bis zum
    // Stillstand gesammelt statt einmal gefiltert.
    //
    // **Was das NICHT heisst:** dass eine oeffentliche Signatur einen privaten Namen nennen
    // DARF. Sie tut es heute, und diese Schleife macht die Folge nur ehrlich; die Frage, ob
    // die Sprache es abweisen sollte, steht in `TODO.md` und ist eine Sprachentscheidung.
    struct Anwaerter {
        modul: String,
        name: String,
        text: String,
        von_anfang: bool,
    }
    let mut alle: Vec<Anwaerter> = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let (name, text, von_anfang) = match &item.art {
            ItemArt::Funktion(f) => {
                if matches!(f.klasse, Some(FnKlasse::Spec)) {
                    return;
                }
                (&f.name.text, kopf_von(f, quelle), f.oeffentlich)
            }
            // **Die Welt, die eine `effects`-Liste nennen darf.** Ohne sie zeigt `writes z`
            // beim Importeur auf nichts, und `E010` haette recht.
            ItemArt::Statisch(x) => (&x.name.text, text_von(item, quelle), x.oeffentlich),
            ItemArt::Konst(k) => (&k.name.text, text_von(item, quelle), k.oeffentlich),
            ItemArt::Typ(y) => (&y.name.text, text_von(item, quelle), y.oeffentlich),
            ItemArt::Tabelle(y) => (&y.name.text, text_von(item, quelle), false),
            ItemArt::Atomic(y) => (&y.name.text, text_von(item, quelle), y.oeffentlich),
            // **Ein `use` ist Teil der Schnittstelle, nicht des Rumpfs.** Ohne es nennt der
            // Kopf `Pa`, und `Pa` ist in DIESEM Modul kein Name. *Gefunden am selben
            // Beispiel: der Parserfehler hat den fehlenden Namen zugedeckt.*
            ItemArt::Use(_) => (&LEER, text_von(item, quelle), true),
            _ => return,
        };
        alle.push(Anwaerter {
            modul: modul.to_string(),
            name: name.clone(),
            text,
            von_anfang,
        });
    });
    let mut drin: Vec<bool> = alle.iter().map(|a| a.von_anfang).collect();
    loop {
        let flaeche: String = alle
            .iter()
            .zip(&drin)
            .filter(|(_, d)| **d)
            .map(|(a, _)| a.text.as_str())
            .collect::<Vec<_>>()
            .join("\n");
        let mut gewachsen = false;
        for i in 0..alle.len() {
            if !drin[i] && nennt(&flaeche, &alle[i].name) {
                drin[i] = true;
                gewachsen = true;
            }
        }
        if !gewachsen {
            break;
        }
    }
    for (a, _) in alle.iter().zip(&drin).filter(|(_, d)| **d) {
        nach_modul
            .entry(a.modul.clone())
            .or_default()
            .push(a.text.clone());
    }
    // **EIN Block je Modul.** Die erste Fassung schrieb je ITEM einen -- und `N001` (*„`bib`
    // is declared twice in this scope"*) hatte recht. *Gefunden vom eigenen Namenspass, an
    // der eigenen Schnittstelle.*
    for (modul, zeilen) in &nach_modul {
        aus.push_str(&format!("\nmodule {modul} {{\n{}\n}}\n", zeilen.join("\n")));
    }
    aus
}

/// **Nennt die exportierte Flaeche diesen Namen?** Als WORT, nicht als Teilzeichenkette --
/// sonst zoege ein `Anfragen` auch ein `Anfragenzaehler` mit herein.
fn nennt(flaeche: &str, name: &str) -> bool {
    let grenze = |c: char| !(c.is_alphanumeric() || c == '_');
    flaeche.match_indices(name).any(|(i, _)| {
        let davor = flaeche[..i].chars().next_back().is_none_or(grenze);
        let danach = flaeche[i + name.len()..].chars().next().is_none_or(grenze);
        davor && danach
    })
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
    // `"extern "` steht mit in der Liste: eine Deklaration, die schon `extern` IST -- ein
    // Import ueber die Modulgrenze -- bekam sonst ein zweites davor, und `P001` sagte
    // *„`fn` erwartet, `extern` gefunden"*. Gefunden 2026-08-20 an
    // `beispiele/29-undurchsichtig.gab`, dem einzigen Beispiel mit zwei Modulen.
    for w in ["pub ", "impl ", "raw ", "prim ", "divergent ", "const ", "extern "] {
        if let Some(r) = ohne_klasse.strip_prefix(w) {
            ohne_klasse = r.trim_start();
        }
    }
    // **`pub` bleibt.** Das Item steht im `.gabi`, WEIL es oeffentlich ist -- ihm die
    // Sichtbarkeit zu nehmen hiesse, `N025` gegen den Importeur zu wenden, der alles richtig
    // gemacht hat. *Gemessen am ersten Import, den die eigene Schnittstelle abwies.*
    format!("pub extern {};", ohne_klasse.trim_end_matches(';').trim_end())
}
