//! **The build gate -- `when TESTBUILD`, and the one place that redeems it.**
//!
//! ## The finding this module answers
//!
//! `messung/GEGENRECHNUNG.md` §8 is the one item of the Caprock measurement that survives
//! the recount without a deduction, and it got LARGER: the measurement and self-test
//! scaffolding is **29,8 % of the tree, 19 849 lines, of which 15 154 are code** -- as big
//! as the concurrent core and the tables together, and almost ten times the 1 545 lines of
//! proof in the whole tree. *Rust says nothing about it, Verus says nothing about it, Loom
//! says nothing about it.*
//!
//! Gabbro said nothing about it either. `SPRACHE.md` booked `check … when TESTBUILD` twice
//! as the answer, and on 2026-08-28 the string `TESTBUILD` stood in **zero** lines of
//! `crates/`. **`when` was worse than absent: it was PARSED.** `Item::when` and
//! `FnDecl::when` have existed since the grammar did, `SYNTAX.md` said *"it lowers to
//! `#if`"* -- and the emitter never read the field. An item carrying `when` produced exactly
//! the same C as one without.
//!
//! > *A clause nobody checks is worse than none* -- the finding that cost `beispiele/05` its
//! > `lock BERICHT protects { … }` (`H007`/`H008`). Here it was a clause nobody LOWERED,
//! > which is the same shape one floor down.
//!
//! ## What the gate is, and where it lives
//!
//! **It is a filter in front of the emitter, not a branch inside it.** [`ohne_gatter`]
//! returns the tree without the gated items, and `emit::emittiere` runs on that tree. The
//! emitter therefore never sees a gated item and *cannot forget* it at one of its twenty
//! walks -- the same reason a ghost type is erased in `ist_geist` and not at each of the
//! three sites that would have had to remember.
//!
//! **And the default is the SHIPPING build.** `emittiere` is the closed gate; the open one
//! needs `emittiere_mit(…, Bau::Pruefbau)` and, at the command line, `--testbuild`.
//! *Forgetting the flag loses test code from a test build, which is loud; the other default
//! would ship it, which is silent.*
//!
//! ## The three refusals
//!
//! | | |
//! |---|---|
//! | `G001` | ungated code calls a gated function -- **the shipping build would not link** |
//! | `G002` | a `when` condition other than `TESTBUILD` -- the word promises exactly one |
//! | `G003` | `TESTBUILD` declared as a name -- the reserved identifier with two meanings |
//!
//! `G002` is the one that keeps this module from being a new fail-open. Giving one name a
//! meaning and leaving every other `when` condition silently ignored would have made the
//! word *look* implemented at 335 Caprock sites and be implemented at one.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use std::collections::{BTreeMap, BTreeSet};

/// **The reserved identifier.** A `G6` special form in `SYNTAX.md`: a terminal of the
/// grammar that is deliberately **not a word of the vocabulary**, exactly like `O` in a
/// `costexpr` and `Held` in a `heldpred`. It stands as an identifier in a fixed position.
///
/// *Why not a keyword.* `messung/SCHLEIFENINVARIANTE.md` §3: a second word for an existing
/// concept is dearer than a second site for an existing word. "Compile this only in build
/// X" is the concept `when` was put into the grammar for -- `SYNTAX.md` §1 says so in those
/// words. What was missing was not a word but a READER.
pub const TESTBUILD: &str = "TESTBUILD";

/// Which build is being generated. **The default is the shipping build** -- see the module
/// header for why the safe value is the one you get by forgetting.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Bau {
    /// The artefact that ships. A gated item produces **no line of C**.
    Auslieferung,
    /// The artefact the checks run in. Every item is present.
    Pruefbau,
}

/// Is this expression the bare name `TESTBUILD`?
///
/// **`suffixe.is_empty()` is load-bearing.** `TESTBUILD.feld` is a place expression that
/// happens to start with the reserved name; it is not the gate, and treating it as one
/// would make the gate depend on a field nobody declared.
fn ist_testbuild(e: &Expr) -> bool {
    matches!(&e.art, ExprArt::Ort(o) if o.suffixe.is_empty() && o.basis.text == TESTBUILD)
}

/// **Every `when` condition an item carries, and there can be two.**
///
/// The grammar puts one before the item (`item = [ "when" constexpr ] …`) and one at the
/// end of a function signature (`fndecl = … [ "arch" ident ] [ "when" constexpr ]`). Both
/// predate this module. *Reading only one of them would have left the other as the
/// fail-open this module exists to close* -- so both are read, and `G002` holds both to the
/// same single condition.
fn bedingungen(item: &Item) -> Vec<&Expr> {
    let mut aus = Vec::new();
    if let Some(w) = &item.when {
        aus.push(w);
    }
    if let ItemArt::Funktion(f) = &item.art {
        if let Some(w) = &f.when {
            aus.push(w);
        }
    }
    aus
}

/// **Does this item exist only in the check build?**
pub fn ist_gegattert(item: &Item) -> bool {
    bedingungen(item).into_iter().any(ist_testbuild)
}

/// **The tree the shipping build sees: the gated items are not in it.**
///
/// Recursive through `module`, because a gate inside a module is the same gate. A module
/// that becomes empty is KEPT -- an empty `module` lowers to nothing anyway, and dropping
/// it would make the gate silently rename the surrounding scopes.
pub fn ohne_gatter(baum: &Programm) -> Programm {
    Programm {
        items: baum.items.iter().filter(|i| !ist_gegattert(i)).map(ohne_gatter_item).collect(),
    }
}

fn ohne_gatter_item(item: &Item) -> Item {
    let mut kopie = item.clone();
    if let ItemArt::Modul(m) = &mut kopie.art {
        m.items = m.items.iter().filter(|i| !ist_gegattert(i)).map(ohne_gatter_item).collect();
    }
    kopie
}

/// Every call of a block, through sub-blocks and sub-expressions.
///
/// Literally `pflichten.rs::rufe_im_block`, and for the same reason: without the descent
/// only the top level is seen, and a call under a `locks` block or in an `update` body is
/// the same call.
fn rufe_im_block<'a>(b: &'a Block, aus: &mut Vec<&'a Ruf>) {
    for s in &b.anweisungen {
        if let StmtArt::Ruf(r) = &s.art {
            aus.push(r);
        }
        for e in crate::eigene_ausdruecke(s) {
            for x in crate::alle_ausdruecke(e) {
                if let ExprArt::Ruf(r) = &x.art {
                    aus.push(r);
                }
            }
        }
        for k in crate::unterbloecke(s) {
            rufe_im_block(k, aus);
        }
    }
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    bedingung_und_name(baum, absagen);
    ruf_ueber_das_gatter(baum, absagen);
}

/// `G002` and `G003` -- the two that hold the word and the name.
fn bedingung_und_name(baum: &Programm, absagen: &mut Absagen) {
    crate::fuer_jedes_item(baum, &mut |item| {
        for w in bedingungen(item) {
            if !ist_testbuild(w) {
                absagen.schiebe(
                    Absage::fehler(
                        "G002",
                        w.span,
                        format!("a `when` condition other than `{TESTBUILD}`"),
                    )
                    .mit_notiz(
                        "`when` gates an item on the BUILD, and this compiler knows exactly \
                         one build to gate on. Every other condition was parsed and then \
                         ignored by the generator until 2026-08-28 -- the item reached the \
                         C either way. A refusal is the honest width of the promise."
                            .to_string(),
                    ),
                );
            }
        }
        // **`ItemArt::name()` and not a second table of my own** (W7). The name pass reads
        // that one; a copy here would be a chance to disagree with it about which items
        // declare a name at all.
        if let Some(n) = item.art.name() {
            if n.text == TESTBUILD {
                absagen.schiebe(
                    Absage::fehler(
                        "G003",
                        n.span,
                        format!("`{TESTBUILD}` is declared here, and it is a reserved name"),
                    )
                    .mit_notiz(
                        "`when TESTBUILD` is decided by the BUILD, not by a declaration in \
                         the unit. A declaration of the same name would give the gate a \
                         second meaning that nothing reads -- and two units could disagree \
                         about it and still link."
                            .to_string(),
                    ),
                );
            }
        }
    });
}

/// `G001` -- **the direction that breaks.**
///
/// In the check build everything is present, so a gated caller reaching an ungated callee is
/// fine. In the SHIPPING build the gated function is not there: an ungated caller becomes an
/// undefined reference, and the artefact that was supposed to be smaller does not link at
/// all.
fn ruf_ueber_das_gatter(baum: &Programm, absagen: &mut Absagen) {
    let umg = crate::umgebung::Umgebung::sammle(baum);
    // key -> is it gated? Only functions: they are what a call reaches.
    let mut funktionen: BTreeMap<String, bool> = BTreeMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Funktion(f) = &item.art {
            funktionen.insert(
                crate::umgebung::qualifiziere(modul, &f.name.text),
                ist_gegattert(item),
            );
        }
    });
    let gegattert: BTreeSet<&String> =
        funktionen.iter().filter(|(_, g)| **g).map(|(k, _)| k).collect();
    if gegattert.is_empty() {
        return;
    }

    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if ist_gegattert(item) {
            return;
        }
        let ItemArt::Funktion(f) = &item.art else { return };
        let FnRumpf::Block(b) = &f.rumpf else { return };
        let mut rufe = Vec::new();
        rufe_im_block(b, &mut rufe);
        for r in rufe {
            // An indirect call names a PLACE, not a function. It is not caught here, and
            // the sentence in `saetze.rs` says so: a function pointer that carries a gated
            // body across the gate is a hole this rule does not close.
            let Some(p) = r.path() else { continue };
            let pfad = p.text();
            let Some(ziel) = umg
                .kandidaten_aufloesbar(modul, &pfad)
                .into_iter()
                .find(|k| funktionen.contains_key(k))
            else {
                continue;
            };
            if !gegattert.contains(&ziel) {
                continue;
            }
            absagen.schiebe(
                Absage::fehler(
                    "G001",
                    r.ziel.span(),
                    format!(
                        "`{}` is not gated and calls `{ziel}`, which is `when {TESTBUILD}`",
                        crate::umgebung::qualifiziere(modul, &f.name.text)
                    ),
                )
                .mit_notiz(format!(
                    "In the shipping build `{ziel}` produces no C at all, so this call has \
                     no callee -- the artefact does not link. Either gate the caller with \
                     `when {TESTBUILD}` as well, or the callee belongs in the shipping \
                     build."
                )),
            );
        }
    });
}
