//! **Lane 132: `Geteilt.Bau`, built from this unit -- beside `H013`, not instead.**
//!
//! The proof (`grammatik/Grammatik/Geteilt.lean`) speaks about one closed-world
//! declaration per unit -- `Bau`: who starts (`eintritt`), who calls whom
//! (`ruft`), who touches what (`schreibtFn`), what is shared (`geteilt`), the
//! carrier domain (`traeger`), and which pairs run together (`neben`). The
//! checker never built it: `H013` answers the shared question by hand, from the
//! same declarations. This module computes the `Bau` out of the bodies, field
//! by field the way `grammatik/Grammatik/Extraktion.lean` prescribes it (read-only
//! reference -- every shape below names its section):
//!
//! | `Bau` field | Lean shape | Rust source, each line read, none written |
//! |---|---|---|
//! | `ruft` | `ruftDirekt` (W-EXT, §1) over `ruftNorm` (§2) | the graph's resolved direct calls (`Knoten::rufe`), filtered to the declared-function domain; an indirect call carries no edge (cut S2) |
//! | `schreibtFn` | `fussAus` (§3) | the DECLARED `writes` effects per function, reduced to carrier roots, filtered to the world domain |
//! | `geteilt` / `traeger` | `geteiltAus` / `traegerAus` (§4) | the same declarations `H013` reads (`welt`, `geschuetzt`, handed in); unknown means shared (cut S5, fail-closed to the loud side) |
//! | `ist_tab` | `splitVonCarrier`'s `istTab` (§7) | the table roots among `welt` (`tabellen`, handed in); every other world member is the Glob half -- carried, not re-collected |
//! | `neben` | `nebenAus` (§5) | the `concurrent` sets, both ends resolved, unordered and deduplicated |
//! | `eintritt` | `bauAus` entry codes (§6) | the `entry` roots (`kontexte::erhebe`), resolved to graph keys in context order |
//!
//! The W5 premise (`pruefeUngeteilt`: every unshared carrier is reached by at most
//! one thread) is evaluated by `pruefe_ungeteilt` over fuel-bounded reachability
//! (`schritt_bis` / `traeger_bis`, mirroring `schrittBis` / `traegerBis`). The one
//! caller is the `H013` section of `geteilt.rs`, where the answer stands BESIDE the
//! verdict and decides nothing -- pinned silent, so the observable behaviour is
//! unchanged by construction. Per-probe agreement is booked in
//! `messung/BAU-NOTIZ.md`.
//!
//! Booked cuts, not hidden ones: S2 (indirect call, no edge -- the refusal belongs
//! to `E009`, not here), S3 (writes only -- for W5 reaching means touching for
//! writing, as in `Extraktion.lean` S3), S4 (a declared pair whose member does not
//! resolve is dropped from the list -- the refusal belongs to `W003`, not here),
//! S5 (unknown carrier reads shared). What stays a premise is the dynamic coverage
//! (`BauLauf`): every access is covered by static reachability -- stated, not shown.

use gabbro_syntax::ast::*;
use std::collections::{BTreeMap, BTreeSet};

/// The closed-world declaration of one unit -- the Rust shape of `Geteilt.Bau`.
///
/// Functions and carriers are named by strings, not by `Nat` codes: a qualified
/// key (`modul::name`) plays the role of `fnCode`, a world root (`z`, `T`) the
/// role of `tabCode` / `globCode`. Field for field the Lean type, now computed.
///
/// The Tab/Glob split (`Geteilt.lean` §7, `TabCarrier ⊕ GlobCarrier`) rides
/// along as the `ist_tab` tag: `true` for table roots (the Tab half), `false`
/// for globals -- `static mut` and `state` (the Glob half). The collapsed
/// `Carrier` stays the working domain (cut C1); the tag only records which
/// half each member came from, so a later lane can state the `hinj`/`hdisj`
/// premises (`tabInjForm` / `globInjForm` / `halvesDisjointForm`, §8) over the
/// two halves instead of re-collecting them.
#[derive(Debug, Default)]
pub struct Bau {
    /// Thread `f` starts in `eintritt[f]` -- resolved entry roots, context order.
    pub eintritt: Vec<String>,
    /// Static call edges, over-approximated, function domain only.
    pub ruft: BTreeMap<String, Vec<String>>,
    /// Direct carrier footprint per function -- declared `writes` roots.
    pub schreibt_fn: BTreeMap<String, Vec<String>>,
    /// `shared`: the flag under test. Unknown carriers read `true` (S5).
    pub geteilt: BTreeMap<String, bool>,
    /// All carriers of the unit -- the checker's domain.
    pub traeger: Vec<String>,
    /// Which half each carrier belongs to (`splitVonCarrier`'s `istTab`):
    /// `true` for table roots, `false` for globals. One entry per `traeger`
    /// member; a member outside the handed-in table list reads Glob.
    pub ist_tab: BTreeMap<String, bool>,
    /// Declared concurrent pairs -- unordered (`a < b`), deduplicated.
    pub neben: Vec<(String, String)>,
}

/// One half of the Tab/Glob split -- the Rust shape of
/// `TabCarrier ⊕ GlobCarrier` (`Geteilt.lean` §7).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Seite {
    /// A table root -- the `Sum.inl` half.
    Tab(String),
    /// A global root (`static mut`, `state`) -- the `Sum.inr` half.
    Glob(String),
}

/// The split of one collapsed carrier (`splitVonCarrier`): the tag decides,
/// the name rides along unchanged -- folding mirrors through the same `Nat`
/// on both halves (cut C1), so neither direction computes anything.
pub fn teile(bau: &Bau, traeger: &str) -> Seite {
    if bau.ist_tab.get(traeger).copied().unwrap_or(false) {
        Seite::Tab(traeger.to_string())
    } else {
        Seite::Glob(traeger.to_string())
    }
}

/// The fold of one split carrier (`carrierVonSplit`): either half folds back
/// to the collapsed name it came from.
pub fn falte(seite: &Seite) -> &str {
    match seite {
        Seite::Tab(t) | Seite::Glob(t) => t,
    }
}

/// The carrier root of a `writes` place -- `T` of `writes T.slots`, `z` of
/// `writes z`. The same cut `H013` makes: the check speaks about world names,
/// and a parameter-rooted place (`writes p.slots`) belongs to the caller, not
/// to this domain -- it falls out through the `welt` filter below, the way an
/// out-of-domain effect falls out of `fussAus`.
fn wurzel_von(schreibt: &str) -> &str {
    schreibt.split(['.', '[']).next().unwrap_or(schreibt)
}

/// The `beruehrt` match, mirrored from `geteilt.rs` (read-only reference): a
/// protected place may stand as a base name or as a path, and the written root
/// touches it through its last segment.
fn beruehrt(platz: &str, getan: &str) -> bool {
    let kern = platz.rsplit('.').next().unwrap_or(platz);
    getan.split(['.', '[']).any(|t| t == kern)
}

/// **The build from the unit (`bauAus`, §6).** Every argument is read, none is
/// written: `welt` and `geschuetzt` are the vectors the `H013` section computed
/// two pages up, `kontexte` the entry list it iterated. `tabellen` names the
/// table roots among `welt` -- the Tab half of the split (§7); every other
/// world member (`static mut`, `state`) is the Glob half.
pub fn erhebe(
    baum: &Programm,
    u: &crate::umgebung::Umgebung,
    g: &crate::aufrufgraph::Graph,
    kontexte: &[crate::kontexte::Kontext],
    welt: &[String],
    geschuetzt: &[String],
    tabellen: &[String],
) -> Bau {
    // The declared-function domain: only calls into it survive (`ruftNorm`).
    // Device transitions, generated `ops` heads and the integer conversions are
    // graph nodes but not functions -- they are no edge here, as in §2.
    let mut fns: BTreeSet<String> = BTreeSet::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Funktion(f) = &item.art {
            fns.insert(crate::umgebung::qualifiziere(modul, &f.name.text));
        }
    });

    // Call edges from the bodies: the graph's resolved direct calls per body,
    // filtered to the domain. Unresolved names stay as written in `rufe` and
    // fall out here -- the refusal belongs to `E009` (cut S2), not to the edge
    // list. Indirect calls never entered `rufe` in the first place.
    let mut ruft: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for f in &fns {
        let mut ziele: Vec<String> = Vec::new();
        if let Some(k) = g.knoten.get(f) {
            for (ziel, _) in &k.rufe {
                if fns.contains(ziel) && !ziele.contains(ziel) {
                    ziele.push(ziel.clone());
                }
            }
        }
        ziele.sort();
        ruft.insert(f.clone(), ziele);
    }

    // Footprints from the effects (`fussAus`): the declared `writes` roots per
    // function, filtered to the world domain.
    let mut schreibt_fn: BTreeMap<String, Vec<String>> = BTreeMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let schluessel = crate::umgebung::qualifiziere(modul, &f.name.text);
        let mut fuesse: Vec<String> = Vec::new();
        if let Some(w) = &f.effects {
            for e in &w.liste {
                if let WirkungArt::Schreibt(o) = &e.art {
                    let grund = wurzel_von(&o.text()).to_string();
                    if welt.contains(&grund) && !fuesse.contains(&grund) {
                        fuesse.push(grund);
                    }
                }
            }
        }
        fuesse.sort();
        schreibt_fn.insert(schluessel, fuesse);
    });

    // Entries in context order; an unresolvable root is skipped, as at `H013`.
    let mut eintritt: Vec<String> = Vec::new();
    for k in kontexte {
        if let Some(voll) = g.aufloesen(u, &k.modul, &k.wurzel) {
            eintritt.push(voll);
        }
    }

    // The shared flag (`geteiltAus`): declared shared wins either direction, as
    // at `H013`; outside the domain it reads shared (S5).
    let mut geteilt: BTreeMap<String, bool> = BTreeMap::new();
    for t in welt {
        let teilt = geschuetzt
            .iter()
            .any(|p| beruehrt(p, t) || beruehrt(t, p));
        geteilt.insert(t.clone(), teilt);
    }

    // The Tab/Glob tag (`splitVonCarrier`'s `istTab`, §7): table roots are the
    // Tab half, every other world member the Glob half. Handed in, not
    // re-collected -- the `H013` section owns the domain, and a second
    // register over the same thing would be `W7`.
    let mut ist_tab: BTreeMap<String, bool> = BTreeMap::new();
    for t in welt {
        ist_tab.insert(t.clone(), tabellen.contains(t));
    }

    // The pair list (`nebenAus`): declared sets, both ends resolved, unordered
    // and deduplicated. A member that resolves to nothing drops out (S4 -- the
    // refusal belongs to `W003`); a self-pair is no pair.
    let mut neben: Vec<(String, String)> = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Concurrent(c) = &item.art {
            let mut glieder: Vec<String> = Vec::new();
            for pfad in &c.koerper {
                if let Some(voll) = g.aufloesen(u, modul, &pfad.text()) {
                    if !glieder.contains(&voll) {
                        glieder.push(voll);
                    }
                }
            }
            for (i, a) in glieder.iter().enumerate() {
                for b in &glieder[i + 1..] {
                    let paar = if a < b {
                        (a.clone(), b.clone())
                    } else {
                        (b.clone(), a.clone())
                    };
                    if !neben.contains(&paar) {
                        neben.push(paar);
                    }
                }
            }
        }
    });
    neben.sort();

    Bau {
        eintritt,
        ruft,
        schreibt_fn,
        geteilt,
        traeger: welt.to_vec(),
        ist_tab,
        neben,
    }
}

/// Fuel that saturates a finite call graph: with `n` functions no simple call
/// chain is longer than `n` edges, so `n` steps reach every reachable function.
pub fn sattigung(bau: &Bau) -> usize {
    bau.ruft.len()
}

/// Functions reachable from `e` within `fuel` steps (`schrittBis`).
fn schritt_bis(ruft: &BTreeMap<String, Vec<String>>, fuel: usize, e: &str) -> Vec<String> {
    let mut erreicht: Vec<String> = vec![e.to_string()];
    for _ in 0..fuel {
        let mut runde = erreicht.clone();
        for f in &erreicht {
            if let Some(ziele) = ruft.get(f) {
                for z in ziele {
                    if !runde.contains(z) {
                        runde.push(z.clone());
                    }
                }
            }
        }
        runde.sort();
        if runde == erreicht {
            break;
        }
        erreicht = runde;
    }
    erreicht
}

/// The carrier set of thread `f` (`traegerBis`): footprints of everything its
/// entry reaches. A thread past the end reaches nothing.
pub fn traeger_bis(bau: &Bau, fuel: usize, f: usize) -> Vec<String> {
    let Some(e) = bau.eintritt.get(f) else {
        return Vec::new();
    };
    let mut traeger: Vec<String> = Vec::new();
    for g in schritt_bis(&bau.ruft, fuel, e) {
        if let Some(fuesse) = bau.schreibt_fn.get(&g) {
            for c in fuesse {
                if !traeger.contains(c) {
                    traeger.push(c.clone());
                }
            }
        }
    }
    traeger.sort();
    traeger
}

/// The W5 premise over the built `Bau` (`pruefeUngeteilt` / `ungeteiltOk`):
/// every carrier of the domain that is NOT shared and is reached by more than
/// one thread. Unknown carriers read shared (S5) and never appear here.
pub fn pruefe_ungeteilt(bau: &Bau, fuel: usize) -> Vec<String> {
    let mut verletzt: Vec<String> = Vec::new();
    for c in &bau.traeger {
        if bau.geteilt.get(c).copied().unwrap_or(true) {
            continue;
        }
        let mut faeden = 0;
        for f in 0..bau.eintritt.len() {
            if traeger_bis(bau, fuel, f).contains(c) {
                faeden += 1;
                if faeden > 1 {
                    break;
                }
            }
        }
        if faeden > 1 {
            verletzt.push(c.clone());
        }
    }
    verletzt
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bau_mini() -> Bau {
        Bau {
            eintritt: vec!["m::mitte".to_string(), "m::seite".to_string()],
            ruft: BTreeMap::from([
                ("m::mitte".to_string(), vec!["m::tief".to_string()]),
                ("m::tief".to_string(), Vec::new()),
                ("m::seite".to_string(), Vec::new()),
            ]),
            schreibt_fn: BTreeMap::from([
                ("m::mitte".to_string(), Vec::new()),
                ("m::tief".to_string(), vec!["z".to_string()]),
                ("m::seite".to_string(), vec!["z".to_string()]),
            ]),
            geteilt: BTreeMap::from([("z".to_string(), false)]),
            traeger: vec!["z".to_string()],
            ist_tab: BTreeMap::from([("z".to_string(), false)]),
            neben: Vec::new(),
        }
    }

    #[test]
    fn wurzel_schneidet_pfad_und_index_ab() {
        assert_eq!(wurzel_von("T.slots"), "T");
        assert_eq!(wurzel_von("T.slots[i].v"), "T");
        assert_eq!(wurzel_von("z"), "z");
    }

    #[test]
    fn schritt_bis_folgt_der_transitiven_kante() {
        let b = bau_mini();
        let direkt = schritt_bis(&b.ruft, 0, "m::mitte");
        assert_eq!(direkt, ["m::mitte"]);
        let voll = schritt_bis(&b.ruft, sattigung(&b), "m::mitte");
        assert_eq!(voll, ["m::mitte", "m::tief"]);
    }

    #[test]
    fn w5_findet_den_von_zwei_faeden_erreichten_traeger() {
        let b = bau_mini();
        assert_eq!(pruefe_ungeteilt(&b, sattigung(&b)), ["z"]);
    }

    #[test]
    fn w5_schweigt_ueber_geteilte_und_einzelne_traeger() {
        let mut b = bau_mini();
        b.geteilt.insert("z".to_string(), true);
        assert!(pruefe_ungeteilt(&b, sattigung(&b)).is_empty());
        let mut c = bau_mini();
        c.eintritt.truncate(1);
        assert!(pruefe_ungeteilt(&c, sattigung(&c)).is_empty());
    }

    #[test]
    fn w5_liest_unbekannt_als_geteilt() {
        let mut b = bau_mini();
        b.traeger.push("fremd".to_string());
        b.schreibt_fn
            .get_mut("m::tief")
            .unwrap()
            .push("fremd".to_string());
        b.schreibt_fn
            .get_mut("m::seite")
            .unwrap()
            .push("fremd".to_string());
        // No `geteilt` entry: unknown reads shared (S5), so only `z` is refused.
        assert_eq!(pruefe_ungeteilt(&b, sattigung(&b)), ["z"]);
    }

    /// Fold after split is the identity, whatever the tag says (`faltTeile_holds`,
    /// §8): both halves fold back to the carrier they came from.
    #[test]
    fn fold_after_split_is_the_identity() {
        let mut b = bau_mini();
        b.traeger.push("T".to_string());
        b.ist_tab.insert("T".to_string(), true);
        for c in b.traeger.clone() {
            assert_eq!(falte(&teile(&b, &c)), c.as_str());
        }
    }

    /// Split after fold returns the injected side, provided the tag marks the
    /// folded carrier accordingly (`teileFaltTab_holds` / `teileFaltGlob_holds`,
    /// §8).
    #[test]
    fn split_returns_the_tagged_side() {
        let mut b = bau_mini();
        b.traeger.push("T".to_string());
        b.ist_tab.insert("T".to_string(), true);
        assert_eq!(teile(&b, "T"), Seite::Tab("T".to_string()));
        assert_eq!(teile(&b, "z"), Seite::Glob("z".to_string()));
        // Outside the tag table the split reads Glob -- the same direction as
        // S5 (unknown reads the loud side is `geteilt`'s; here the tag only
        // ever claims Tab for a handed-in table root).
        assert_eq!(teile(&b, "fremd"), Seite::Glob("fremd".to_string()));
    }
}
