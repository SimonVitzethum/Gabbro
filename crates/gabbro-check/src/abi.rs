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
//! **The lock ranks DO travel, since 2026-08-21 -- and until then their absence was a false
//! green.** The first version left them out with the argument that `lock … rank 0` is an
//! ABSOLUTE number and two independently written libraries both pick `rank 0`. The argument
//! is right and the conclusion was wrong: leaving the ranks out did not avoid the collision,
//! it made the whole lock order unenforceable at the boundary. *Measured: a ring across two
//! libraries -- `SPEICHER` under `GERAET` and `GERAET` under `SPEICHER` -- passed with 0
//! errors and 0 hints* (`messung/ABI.md`).
//!
//! > What remains true is the narrower statement: **absolute numbers do not COMPOSE.** The
//! > union is ordered by whichever integers the two authors happened to pick, so a
//! > legitimate mixing can be refused with no repair short of editing the library. That is a
//! > completeness gap, not a soundness one -- a rank function into the integers cannot
//! > produce a cycle -- and «ABI2» (order instead of rank) is where it is answered. *A false
//! > refusal is a bad day; a false green is a deadlock.*
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
    // **The interface is a WRITTEN set, not a fixpoint** (2026-08-25).
    //
    // Until that day a loop stood here that collected to a standstill: `T` came along
    // because an `index into T` names it, then `N` because `count N` names it, and so on.
    // The reason was that `table`, `lock`, `device` and `format` **could carry no `pub`** --
    // the grammar had the word at seven item kinds and not at them.
    //
    // > *The fixpoint was the honest consequence of a missing production, not the decision
    // > it looked like.* It made the export set **implicit**: it stood written nowhere, it
    // > simply resulted. **D2 says "nothing is implicit".**
    //
    // Since the four carriers carry `pub`, it stands written -- and the question the
    // fixpoint answered has become a REFUSAL: `N038` in `bindung.rs` rejects an exported
    // declaration that names something private. **The same class, from the other side:**
    // there the consequence was made honest, here the cause falls.
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        // **A gated item is not in the interface, and the interface is the SHIPPING one**
        // («TB», 2026-08-28).
        //
        // *Measured before this line stood here:* a `when TESTBUILD pub fn geruest_melden`
        // came out of `gabbro abi` as a plain `pub extern fn` -- the gate was **lost**,
        // because a function's text is cut from the `FnDecl` span and the `when` stands in
        // front of it. The consumer then loaded a `.gabi` that promises a symbol the
        // shipping build does not define, and `emit --with` lowers exactly that to a **C
        // prototype**. *The gate would have held in the unit and leaked through its
        // interface.*
        //
        // **A `.gabi` names no build**, and that is why the answer here is a filter and not
        // a flag: an interface promises what BINDS, a gated item binds only in a build the
        // interface cannot name. So there is one interface, and it is the one that ships.
        // *What this does not offer is an interface for the CHECK build* -- a consumer's
        // harness cannot call a library's gated helper across the `.gabi`. Booked in
        // `saetze::namen.baugatter`, not silently absent.
        if crate::gatter::ist_gegattert(item) {
            return;
        }
        // **A `use` is part of the interface, not of the body.** Without it the head names
        // `Pa`, and `Pa` is no name in THIS module. *Found at the example with two modules:
        // the parser error covered up the missing name.*
        //
        // It carries a `pub` of its own and is taken unconditionally anyway: a `use` binds
        // nothing and declares nothing -- it makes a name findable inside the module, and
        // that is exactly what the head naming it needs.
        let text = if matches!(item.art, ItemArt::Use(_)) {
            text_von(item, quelle)
        } else {
            // Everything else goes out BECAUSE it carries `pub` -- and only then. The
            // question which name that is has exactly one reader (W7).
            if crate::bindung::ausgefuehrter_name(item).is_none() {
                return;
            }
            match &item.art {
                ItemArt::Funktion(f) => kopf_von(f, quelle),
                _ => text_von(item, quelle),
            }
        };
        nach_modul.entry(modul.to_string()).or_default().push(text);
    });
    // **ONE block per module.** The first version wrote one per ITEM -- and `N001` (*"`bib`
    // is declared twice in this scope"*) was right. *Found by this compiler's own name pass,
    // on this compiler's own interface.*
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

// =======================================================================================
// «A4» -- DIE BERECHNETE HUELLE
// =======================================================================================

/// **The verdict over ONE function: does the computed effect list agree with the written
/// one?**
///
/// The largest single item of the usability measure reads *"COMPUTE the caller's effect
/// list instead of demanding it"*. The call graph computes one half already
/// (`huelle_der_gerufenen`), `wirkungen::rumpfwirkungen_mit` the other -- **nothing is
/// built here; what is measured is whether it would be worth building.**
///
/// > **And the directions are NOT equivalent.** *Narrower* means: the declaration promises
/// > more than the body does -- a loss of sharpness, not a hole. *Broader* means: the body
/// > does more than the declaration names -- **and by `E005`, `E008` and `E010` that must
/// > not occur at all.** Should this column move off zero, the finding is not one about the
/// > elaborator but one about those three passes.
#[derive(Debug, Clone, PartialEq)]
pub enum Urteil {
    /// Every computed effect is covered, and every declared one carries something.
    Identisch,
    /// Declared, but demanded neither by the body nor by the callees.
    Enger(Vec<String>),
    /// Performed, but not declared. **This column belongs empty** -- as far as the places
    /// are known world names at all. The `bool` says whether at least ONE of them is.
    ///
    /// > `E008` and `E010` compare the place only *"where the place is comparable at all:
    /// > at known world state"*. A `writes halde` out of an `extern fn` whose `halde`
    /// > nothing in this unit declares falls at NEITHER of the two -- **with a reason**,
    /// > not by oversight. Whoever writes those cases into the same column as a real frame
    /// > breach reports a gap that does not exist.
    Breiter(Vec<String>, bool),
    /// The hull tears, and the edge is named (R16).
    Unvollstaendig(String),
    /// No `effects` clause or no body -- there is nothing to compare.
    Nichts,
}

#[derive(Debug, Clone)]
pub struct Vergleich {
    pub modul: String,
    pub name: String,
    pub klasse: Option<FnKlasse>,
    pub deklariert: Vec<String>,
    pub berechnet: Vec<String>,
    pub urteil: Urteil,
}

/// **Does a DECLARED effect cover a COMPUTED one?** -- and by the same rules with which
/// `E005`/`E010`/`H007` hold the written list against the body.
///
/// * `consumes`, `publishes`, `allocs`, `masks` are write rights (`schreibrechte` there),
/// * `publishes` additionally grants a read right (*"the same place under two names"*),
/// * `locks X` also covers `locks shared X` -- exclusive is stronger; **not the reverse.**
///
/// *Every one of those three lines stands over there just so. Whoever writes them
/// differently here measures the difference between two filters, not between two lists.*
fn deckt_a4(erklaert: &str, berechnet: &str) -> bool {
    fn schreibt(s: &str) -> Option<&str> {
        ["writes ", "consumes ", "publishes ", "allocs ", "masks "]
            .iter()
            .find_map(|v| s.strip_prefix(v))
    }
    if let Some(getan) = berechnet.strip_prefix("writes ") {
        if let Some(erlaubt) = schreibt(erklaert) {
            return crate::wirkungen::deckt_wirkung(
                &format!("writes {erlaubt}"),
                &format!("writes {getan}"),
            );
        }
        return false;
    }
    if let Some(getan) = berechnet.strip_prefix("reads ") {
        for v in ["reads ", "publishes "] {
            if let Some(erlaubt) = erklaert.strip_prefix(v) {
                return crate::wirkungen::deckt_wirkung(
                    &format!("reads {erlaubt}"),
                    &format!("reads {getan}"),
                );
            }
        }
        return false;
    }
    if let Some(getan) = berechnet.strip_prefix("locks shared ") {
        for v in ["locks shared ", "locks "] {
            if let Some(erlaubt) = erklaert.strip_prefix(v) {
                return erlaubt == getan;
            }
        }
        return false;
    }
    crate::wirkungen::deckt_wirkung(erklaert, berechnet)
}

/// Effects without a place -- they say nothing about a place of the world and stand in
/// neither direction. `pure` thereby falls to "the empty set", and that is exactly what it
/// is.
fn ortlos(w: &str) -> bool {
    w == "pure" || w == "diverges"
}

/// **The computed hull of ONE function:** what the body itself does, united with what
/// comes from the callees.
pub fn berechne(
    f: &FnDecl,
    modul: &str,
    g: &crate::aufrufgraph::Graph,
    konstanten: &[String],
    weltnamen: &[String],
) -> (std::collections::BTreeSet<String>, Option<String>) {
    berechne_mit(f, modul, g, konstanten, weltnamen, false)
}

/// `weit = true` also computes the reads over parameters and over undeclared names -- see
/// `wirkungen::rumpfwirkungen_mit`.
pub fn berechne_mit(
    f: &FnDecl,
    modul: &str,
    g: &crate::aufrufgraph::Graph,
    konstanten: &[String],
    weltnamen: &[String],
    weit: bool,
) -> (std::collections::BTreeSet<String>, Option<String>) {
    let FnRumpf::Block(b) = &f.rumpf else {
        return (Default::default(), Some("no body".into()));
    };
    let mut menge = crate::wirkungen::rumpfwirkungen_mit(f, b, konstanten, weltnamen, weit);
    let h = g.huelle_der_gerufenen(&g.schluessel_von(modul, &f.name.text));
    menge.extend(h.wirkungen.iter().cloned());
    (menge, h.unvollstaendig)
}

/// **The comparison over a whole unit.** One row per function with `effects` and a body.
pub fn vergleiche(baum: &Programm) -> Vec<Vergleich> {
    vergleiche_mit(baum, false)
}

pub fn vergleiche_mit(baum: &Programm, weit: bool) -> Vec<Vergleich> {
    let g = crate::aufrufgraph::erhebe(baum);
    let (konstanten, weltnamen) = crate::wirkungen::welt_und_konstanten(baum);
    let mut aus = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let (Some(w), FnRumpf::Block(_)) = (&f.effects, &f.rumpf) else {
            return;
        };
        let deklariert: Vec<String> = w.liste.iter().map(|e| e.art.text()).collect();
        let (berechnet_menge, offen) =
            berechne_mit(f, modul, &g, &konstanten, &weltnamen, weit);
        let berechnet: Vec<String> = berechnet_menge.iter().cloned().collect();
        let urteil = if let Some(grund) = offen {
            Urteil::Unvollstaendig(grund)
        } else {
            let ungedeckt: Vec<String> = berechnet
                .iter()
                .filter(|b| !ortlos(b) && !deklariert.iter().any(|d| deckt_a4(d, b)))
                .cloned()
                .collect();
            let bekannt = ungedeckt.iter().any(|b| {
                b.rsplit_once(' ').is_some_and(|(_, o)| {
                    let gr = o.split(['.', '[']).next().unwrap_or(o);
                    weltnamen.iter().any(|k| k == gr)
                })
            });
            let unbegruendet: Vec<String> = deklariert
                .iter()
                .filter(|d| !ortlos(d) && !berechnet.iter().any(|b| deckt_a4(d, b)))
                .cloned()
                .collect();
            // **Broader beats narrower.** A list that promises too little is a finding;
            // one that promises too much is merely blunt.
            if !ungedeckt.is_empty() {
                Urteil::Breiter(ungedeckt, bekannt)
            } else if !unbegruendet.is_empty() {
                Urteil::Enger(unbegruendet)
            } else {
                Urteil::Identisch
            }
        };
        aus.push(Vergleich {
            modul: modul.to_string(),
            name: f.name.text.clone(),
            klasse: f.klasse,
            deklariert,
            berechnet,
            urteil,
        });
    });
    aus
}

/// **The interface with the COMPUTED effect list instead of the written one.**
///
/// The same `.gabi` as `schreibe`, only that in every function head the `effects` clause is
/// replaced by the computed one. *If the hull is incomplete the written line stays and the
/// reason stands beside it* -- issuing a lower bound as an interface would be exactly the
/// lowering from checked to claimed that the head of this file rules out.
pub fn schreibe_berechnet(baum: &Programm, quelle: &str) -> String {
    let g = crate::aufrufgraph::erhebe(baum);
    let (konstanten, weltnamen) = crate::wirkungen::welt_und_konstanten(baum);
    let mut ersatz: std::collections::BTreeMap<(u32, u32), String> = Default::default();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let Some(w) = &f.effects else { return };
        let (menge, offen) = berechne(f, modul, &g, &konstanten, &weltnamen);
        let text = match offen {
            Some(grund) => format!(
                "effects {{ {} }} -- HULL INCOMPLETE, written line kept: {grund}",
                w.liste.iter().map(|e| e.art.text()).collect::<Vec<_>>().join(", ")
            ),
            None if menge.is_empty() => "effects { pure }".to_string(),
            None => format!(
                "effects {{ {} }}",
                menge.iter().cloned().collect::<Vec<_>>().join(", ")
            ),
        };
        ersatz.insert((w.span.von, w.span.bis), text);
    });
    let roh = schreibe(baum, quelle);
    // The replacement runs over the TEXT of the clause, not over the span: `schreibe` has
    // already cut the head out of the source, and a span of the source points somewhere
    // else in the result.
    let mut aus = roh;
    for ((von, bis), neu) in &ersatz {
        let alt = &quelle[*von as usize..*bis as usize];
        if aus.contains(alt) {
            aus = aus.replacen(alt, neu, 1);
        }
    }
    aus
}
