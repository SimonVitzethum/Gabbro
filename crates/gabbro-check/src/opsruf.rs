//! **`T::insert(t, n)` -- the CALL FORM of a generated operation, and the one place where
//! the proof's premises become duties.**
//!
//! Since 2026-08-28 `table … ops insert, remove;` has a generator (`emit.rs::ops`), cut to
//! `beweise/Table_Ops_Erhaltung.thy`. And it shipped with two holes that this module closes:
//!
//! 1. **Nothing could call the generated functions.** They carried
//!    `__attribute__((unused))`, because inside their own translation unit nobody calls them
//!    -- *a prohibition (`D001`) with a replacement no one can reach.*
//! 2. **The premises stood in a C COMMENT.** `einfuegen_erhaelt` demands that the slot is
//!    FRESH and the parent REACHABLE; `blatt_loeschen_erhaelt` demands that the slot is a
//!    LEAF. A comment is not a duty.
//!
//! ## The form costs nothing, and that is the finding
//!
//! `Verzeichnis::insert(v, i);` **parses today**, without one line of grammar: `pfad`
//! reads a path, and `erwarte_feldname` admits a vocabulary word as a segment. Measured
//! before deciding -- the file went through the parser and came out at `K003`/`E009`:
//! *"`insert` is not declared here"*. **The call form was never missing. The CALLEE was.**
//!
//! > `messung/OPS-RUFFORM.md` weighs both sides of three forms. The decision is the same
//! > move as `SCHLEIFENINVARIANTE.md`: *a second word for a concept the language already
//! > carries is dearer than a second site for a word it already has.*
//!
//! ## What this module is, structurally: ONE producer, five readers
//!
//! [`koepfe`] turns a `table` declaration into the list of generated operations **as
//! callees** -- parameters, premises, effects, cost. Everything else asks it:
//!
//! | reader | what it takes |
//! |---|---|
//! | `umgebung.rs` | the `Signatur`, so M1 types the arguments and `M115` reads the premises |
//! | `aufrufgraph.rs` | a node with `writes t.slots`, so `E008` stays compositional |
//! | `kosten.rs` | the declared cost, so `K001` is a number and not `K003` |
//! | `emit.rs` | the C body, its prototype, and whether anyone calls it |
//! | this module | **`D012`** -- the premises must STAND at the call site |
//!
//! *A second producer would be the second reader of one promise, and this folder has paid
//! for that twice.*

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::HashMap;

/// **One premise the proof charges to the caller.**
///
/// The positions are ARGUMENT positions, not text: a premise is a statement about the
/// values written at the call site, and it must be rendered against them. Rendering it
/// against the parameter names instead gives the head form the emitter prints.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Forderung {
    /// `sigma n = None` -- the slot is FRESH. In Gabbro: `!<t>.slots[<n>].<occupied>`.
    Frei {
        traeger: usize,
        index: usize,
        feld: String,
    },
    /// `erreicht sigma p` -- the parent is REACHABLE. In Gabbro:
    /// `<t>.slots[<p>] reaches <root> via <parent>`.
    ///
    /// **The ROOT is the caller's choice, and that is not laxity.** `erreicht` in the theory
    /// is reachability of *a* root; which slot plays it stands in the table's own
    /// `reaches`-invariant, not in the `tree` clause. Demanding a particular root here would
    /// be a claim the proof does not make.
    Erreichbar {
        traeger: usize,
        index: usize,
        via: String,
    },
    /// `blatt sigma s` -- **nobody names `s` as parent**. In Gabbro:
    /// `forall x in slots of <t> : <t>.slots[x].<parent> != Some(<s>)`.
    ///
    /// > **Deliberately NOT `<t>.slots[<s>].<child> == None`.** That is what
    /// > `beispiele/01`'s hand-written `ist_blatt` says, and it is WEAKER: it holds of a slot
    /// > whose child list has drifted from its parent pointers. A weaker premise than the
    /// > theorem's is fail-open at exactly the point where the theorem is the whole value.
    Blatt {
        traeger: usize,
        index: usize,
        via: String,
    },
    /// `\<not> ueber sigma p s` -- **the new parent does not lie under the slot being
    /// re-hung, that slot itself included.** In Gabbro:
    /// `!(<t>.slots[<p>] reaches <t>.slots[<s>] via <parent>)`.
    ///
    /// > **The TARGET is named here, and that is the difference to [`Forderung::Erreichbar`].**
    /// > There the root is the caller's choice, because `erreicht` is reachability of *a*
    /// > root. This one is reachability of ONE named slot, and reading the target loosely
    /// > would turn the premise into a different statement.
    ///
    /// **And it is REFLEXIVE-transitive, as the theory's relation is.** The strict reading --
    /// Gabbro's `ancestors of`, which starts the chain at the PARENT -- lets
    /// `relabel(t, s, s)` through, and that self-loop breaks `wohlgeformt` exactly like the
    /// two-slot cycle. *`messung/OPS-RELABEL.md` §3 weighs the two forms; this one won.*
    NichtUeber {
        traeger: usize,
        /// argument position of `p` -- the NEW parent
        elter: usize,
        /// argument position of `s` -- the slot being re-hung
        platz: usize,
        via: String,
    },
}

/// A premise **rendered against real places** -- either demanded at a call, or standing
/// above it. Comparison is on this form and not on free text: `reaches` carries a root the
/// caller picks, so text equality would be the wrong question.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Steht {
    Frei(String),
    Erreichbar { von: String, via: String },
    Blatt { traeger: String, via: String, s: String },
    NichtUeber { von: String, nach: String, via: String },
}

impl Steht {
    /// How the premise reads in Gabbro -- for the refusal and for the emitted head.
    pub fn text(&self) -> String {
        match self {
            Steht::Frei(o) => format!("!{o}"),
            Steht::Erreichbar { von, via } => format!("{von} reaches <root> via {via}"),
            Steht::Blatt { traeger, via, s } => format!(
                "forall x in slots of {traeger} : {traeger}.slots[x].{via} != Some({s})"
            ),
            Steht::NichtUeber { von, nach, via } => {
                format!("!({von} reaches {nach} via {via})")
            }
        }
    }
}

impl Forderung {
    /// Render against a list of argument texts (or parameter names -- the head form).
    fn gegen(&self, args: &[String]) -> Option<Steht> {
        match self {
            Forderung::Frei {
                traeger,
                index,
                feld,
            } => Some(Steht::Frei(format!(
                "{}.slots[{}].{feld}",
                args.get(*traeger)?,
                args.get(*index)?
            ))),
            Forderung::Erreichbar {
                traeger,
                index,
                via,
            } => Some(Steht::Erreichbar {
                von: format!("{}.slots[{}]", args.get(*traeger)?, args.get(*index)?),
                via: via.clone(),
            }),
            Forderung::Blatt {
                traeger,
                index,
                via,
            } => Some(Steht::Blatt {
                traeger: args.get(*traeger)?.clone(),
                via: via.clone(),
                s: args.get(*index)?.clone(),
            }),
            Forderung::NichtUeber {
                traeger,
                elter,
                platz,
                via,
            } => Some(Steht::NichtUeber {
                von: format!("{}.slots[{}]", args.get(*traeger)?, args.get(*elter)?),
                nach: format!("{}.slots[{}]", args.get(*traeger)?, args.get(*platz)?),
                via: via.clone(),
            }),
        }
    }
}

/// **A generated operation, seen as a CALLEE.**
#[derive(Debug, Clone)]
pub struct Kopf {
    /// The table's short name -- the first segment of the call path.
    pub tabelle: String,
    pub wort: &'static str,
    /// `(name, declared type)` in call order. The names are the ones the head form prints.
    pub parameter: Vec<(String, TypExpr)>,
    pub forderungen: Vec<Forderung>,
    /// The declared effects, normalised the way `WirkungArt::text` writes them.
    pub wirkungen: Vec<String>,
    /// **The cost is COUNTED, not estimated:** one op per store the generator writes.
    pub kosten: i128,
    pub span: Span,
}

impl Kopf {
    /// `Verzeichnis::insert` -- as a caller writes it.
    pub fn pfad(&self) -> String {
        format!("{}::{}", self.tabelle, self.wort)
    }

    /// `Verzeichnis_insert` -- as the C carries it.
    pub fn c_name(&self) -> String {
        format!("{}_{}", self.tabelle, self.wort)
    }

    /// The premises with the PARAMETER names in them -- the head form.
    pub fn kopfform(&self) -> Vec<String> {
        let namen: Vec<String> = self.parameter.iter().map(|(n, _)| n.clone()).collect();
        self.forderungen
            .iter()
            .filter_map(|f| f.gegen(&namen))
            .map(|s| s.text())
            .collect()
    }
}

/// **The generated operations of one table -- cut to the proof, exactly as `emit.rs` cuts
/// the C.**
///
/// | theorem | word | premises charged to the caller |
/// |---|---|---|
/// | `einfuegen_erhaelt` | `insert` | slot FRESH; and, where a `parent` edge exists, parent REACHABLE |
/// | `blatt_loeschen_erhaelt` | `remove` | where a `parent` edge exists, `s` is a LEAF |
/// | `umhaengen_erhaelt` | `relabel` | the new parent REACHABLE, and `s` NOT on its chain |
///
/// **`relabel` became a callee on 2026-08-28, evening, and the order was the rule**
/// (`messung/OPS-RELABEL.md`). Until then the third word of a CLOSED vocabulary emitted
/// nothing and could be called by nobody -- *a clause with no redeemer*, the shape `N037`
/// and `H007`/`H008` were paid for. What was missing was not the form but the condition:
/// `umhaengen_faellt` said the re-hanging breaks `wohlgeformt`, never what it breaks on.
/// **A table without a `parent` edge has no `relabel` callee at all** -- there is nothing
/// to re-hang, and `emit.rs` refuses it by name.
///
/// **Where the table has no `parent` edge, `remove` owes NOTHING, and that is a
/// statement.** `blatt sigma s` says *"no slot names `s` as parent"*; with no field that can
/// name a parent it holds of every `s`. *An invented duty would have looked stricter and
/// meant less.*
pub fn koepfe(t: &Tabelle) -> Vec<Kopf> {
    let mut aus = Vec::new();
    // `D011` already refuses a `table` with `ops` and no `occupied`. Returning empty here
    // keeps this producer from inventing a field name -- the same reason `emit.rs::ops`
    // returns instead of guessing.
    let Some(belegt) = &t.belegt else {
        return aus;
    };
    let elter = t.baum.as_ref().and_then(|b| b.elter.as_ref());
    let sp = t.name.span;
    let traeger = || {
        (
            "t".to_string(),
            TypExpr::Zeiger(Box::new(PtrTy {
                raum: Raum::Normal,
                rechte: vec![Recht::LesenSchreiben],
                ziel: TypExpr::Pfad(Pfad {
                    teile: vec![t.name.clone()],
                    span: sp,
                }),
                span: sp,
            })),
        )
    };
    let idx = |n: &str| {
        (
            n.to_string(),
            TypExpr::Index {
                tabelle: t.name.clone(),
                optional: false,
                span: sp,
            },
        )
    };
    let felderzahl = t.slot.iter().flat_map(|s| s.felder.iter()).count() as i128;
    for w in &t.ops {
        match w.text.as_str() {
            "insert" => {
                let mut parameter = vec![traeger(), idx("n")];
                let mut forderungen = vec![Forderung::Frei {
                    traeger: 0,
                    index: 1,
                    feld: belegt.text.clone(),
                }];
                if let Some(e) = elter {
                    parameter.push(idx("p"));
                    forderungen.push(Forderung::Erreichbar {
                        traeger: 0,
                        index: 2,
                        via: e.text.clone(),
                    });
                }
                aus.push(Kopf {
                    tabelle: t.name.text.clone(),
                    wort: "insert",
                    // One store for the occupancy flag, one more for the parent edge.
                    kosten: if elter.is_some() { 2 } else { 1 },
                    parameter,
                    forderungen,
                    wirkungen: vec!["writes t.slots".to_string()],
                    span: w.span,
                });
            }
            "remove" => {
                let mut forderungen = Vec::new();
                if let Some(e) = elter {
                    forderungen.push(Forderung::Blatt {
                        traeger: 0,
                        index: 1,
                        via: e.text.clone(),
                    });
                }
                aus.push(Kopf {
                    tabelle: t.name.text.clone(),
                    wort: "remove",
                    // `sigma(s := None)` resets EVERY field -- one store each.
                    kosten: felderzahl,
                    parameter: vec![traeger(), idx("s")],
                    forderungen,
                    wirkungen: vec!["writes t.slots".to_string()],
                    span: w.span,
                });
            }
            // **`relabel` since 2026-08-28, evening, and it took a THEOREM to get here.**
            //
            // Until then the generator refused the word by naming `umhaengen_faellt`, and
            // the refusal was not wrong -- it was incomplete. It said that re-hanging
            // breaks `wohlgeformt`, and not WHAT it breaks on.
            // `beweise/Table_Ops_Erhaltung.thy` now says: `umhaengen_erhaelt` (U-3), under
            // *"the new parent is reachable"* and *"the re-hung slot does not lie on its
            // chain"*. `G-1`/`G-2` show the old counterexample fails at the second premise
            // and at no other.
            //
            // > **No `parent` edge, no callee.** There is no field to re-hang, `emit.rs`
            // > refuses such a table by name (`C001`), and a callee whose body is never
            // > emitted would be the prohibition-without-replacement again, one level up.
            "relabel" => {
                let Some(e) = elter else { continue };
                aus.push(Kopf {
                    tabelle: t.name.text.clone(),
                    wort: "relabel",
                    // ONE store: the parent edge, and nothing else. `remove` resets every
                    // field because `sigma(s := None)` is a slot without a value; a re-hung
                    // slot keeps its value and changes where it hangs.
                    kosten: 1,
                    parameter: vec![traeger(), idx("s"), idx("p")],
                    forderungen: vec![
                        Forderung::Erreichbar {
                            traeger: 0,
                            index: 2,
                            via: e.text.clone(),
                        },
                        Forderung::NichtUeber {
                            traeger: 0,
                            elter: 2,
                            platz: 1,
                            via: e.text.clone(),
                        },
                    ],
                    wirkungen: vec!["writes t.slots".to_string()],
                    span: w.span,
                });
            }
            // An invented word is the business of `P039`, not of this module.
            _ => {}
        }
    }
    aus
}

/// Every generated operation of the unit, keyed by its QUALIFIED path (`m::T::insert`).
pub fn alle(baum: &Programm) -> HashMap<String, Kopf> {
    let mut aus = HashMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Tabelle(t) = &item.art else {
            return;
        };
        for k in koepfe(t) {
            aus.insert(crate::umgebung::qualifiziere(modul, &k.pfad()), k);
        }
    });
    aus
}

/// The declared cost per generated operation, for `kosten.rs`'s `deklariert` map.
pub fn kosten(baum: &Programm) -> HashMap<String, i128> {
    alle(baum).into_iter().map(|(k, v)| (k, v.kosten)).collect()
}

/// **Which generated operations does this unit actually CALL?** -- as written, `T::insert`.
///
/// The emitter asks, and the answer decides one attribute: a generated function that nobody
/// calls needs `__attribute__((unused))` to survive `-Werror=unused-function`, and one that
/// IS called must not carry it, or the attribute would say something false about the unit.
/// *That attribute was the visible form of the hole this module closes.*
pub fn gerufene(baum: &Programm) -> std::collections::BTreeSet<String> {
    let mut aus = std::collections::BTreeSet::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Funktion(f) = &item.art {
            if let FnRumpf::Block(b) = &f.rumpf {
                rufe_im_block(b, &mut aus);
            }
        }
    });
    aus
}

fn rufe_im_block(b: &Block, aus: &mut std::collections::BTreeSet<String>) {
    for s in &b.anweisungen {
        if let StmtArt::Ruf(r) = &s.art {
            if let Some(p) = r.path() {
                aus.insert(p.text());
            }
        }
        for e in crate::eigene_ausdruecke(s) {
            for x in crate::alle_ausdruecke(e) {
                if let ExprArt::Ruf(r) = &x.art {
                    if let Some(p) = r.path() {
                        aus.insert(p.text());
                    }
                }
            }
        }
        for k in crate::unterbloecke(s) {
            rufe_im_block(k, aus);
        }
    }
}

// =======================================================================================
//  D012 -- the premises must STAND at the call site
// =======================================================================================

/// **`D012` -- a generated operation is called where its premises stand.**
///
/// `M115` is the weak reading of a precondition: it refuses where the argument's RANGE
/// excludes the clause and stays silent otherwise. These premises are not range statements,
/// so `M115` would be silent about every one of them -- *and a clause nobody checks is worse
/// than no clause* (`H007`/`H008`, and `beispiele/05` paid for it).
///
/// So this rule asks a structural question instead of an undecidable one:
///
/// > **Does the premise STAND somewhere above this call?**
///
/// Three places count, and they are the three places in which this language writes a fact
/// that holds where the call is:
///
/// | source | why it counts |
/// |---|---|
/// | the routine's own `requires` | the caller's caller owes it -- `pflichten` books it as `V` |
/// | an enclosing `if` condition | the branch is entered only when it holds |
/// | an enclosing loop `invariant` | *"what holds across the passes"* (2026-08-28) |
///
/// **What this rule does NOT do:** it does not prove the premise. A `requires` that stands
/// is a duty pushed one frame outwards, exactly as `blatt_loeschen`'s `ist_blatt(c, s)` has
/// been since `beispiele/01` -- and `gabbro pflichten` counts it there. *What it removes is
/// the case where the duty is written NOWHERE, which is what the generator shipped with.*
pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    let koepfe = alle(baum);
    if koepfe.is_empty() {
        return;
    }
    let u = crate::umgebung::Umgebung::sammle(baum);
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let FnRumpf::Block(b) = &f.rumpf else {
            return;
        };
        let mut steht: Vec<Steht> = Vec::new();
        for p in &f.requires {
            aus_pred(p, &mut steht);
        }
        block(b, &steht, &koepfe, &u, modul, absagen);
    });
}

fn block(
    b: &Block,
    steht: &[Steht],
    koepfe: &HashMap<String, Kopf>,
    u: &crate::umgebung::Umgebung,
    modul: &str,
    absagen: &mut Absagen,
) {
    for s in &b.anweisungen {
        // **Every call, not only the one in statement position.** A generated operation
        // returns nothing, so `T::insert(v, i)` as an argument or inside a `retry … until`
        // is nonsense -- and *nonsense that goes through unchecked is exactly the shape this
        // rule exists to stop*. The walkers are the exhaustive ones from `lib.rs`, so a new
        // statement kind cannot quietly grow a place a call can hide in.
        if let StmtArt::Ruf(r) = &s.art {
            pruefe_ruf(r, s.span, steht, koepfe, u, modul, absagen);
        }
        if let StmtArt::LetSonst(l) = &s.art {
            if let Some(r) = l.als_ruf() {
                pruefe_ruf(r, s.span, steht, koepfe, u, modul, absagen);
            }
        }
        let mut ausdruecke: Vec<&Expr> = crate::eigene_ausdruecke(s);
        for p in crate::eigene_praedikate(s) {
            ausdruecke.extend(crate::ausdruecke_im_praedikat(p));
        }
        for e in ausdruecke {
            for x in crate::alle_ausdruecke(e) {
                if let ExprArt::Ruf(r) = &x.art {
                    pruefe_ruf(r, x.span, steht, koepfe, u, modul, absagen);
                }
            }
        }
        match &s.art {
            // **A branch condition holds inside its branch.** Only the taken arm: the
            // negation of a previous arm is a fact too, and it is not one this rule can
            // render -- so it is left out rather than half-read.
            StmtArt::Wenn(w) => {
                for (bed, k) in &w.zweige {
                    let mut tiefer = steht.to_vec();
                    aus_expr(bed, &mut tiefer);
                    block(k, &tiefer, koepfe, u, modul, absagen);
                }
                if let Some(k) = &w.sonst {
                    block(k, steht, koepfe, u, modul, absagen);
                }
            }
            StmtArt::Schleife(sch) => {
                let (inv, rumpf) = match sch.as_ref() {
                    Schleife::Traverse(x) => (&x.invariante, &x.rumpf),
                    Schleife::Retry(x) => (&x.invariante, &x.rumpf),
                    Schleife::Forever(x) => (&x.invariante, &x.rumpf),
                };
                let mut tiefer = steht.to_vec();
                if let Some(p) = inv {
                    aus_pred(p, &mut tiefer);
                }
                block(rumpf, &tiefer, koepfe, u, modul, absagen);
            }
            // Every other statement that carries blocks keeps the standing set unchanged --
            // over `crate::unterbloecke`, so a new statement kind cannot silently drop out.
            _ => {
                for k in crate::unterbloecke(s) {
                    block(k, steht, koepfe, u, modul, absagen);
                }
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn pruefe_ruf(
    r: &Ruf,
    span: Span,
    steht: &[Steht],
    koepfe: &HashMap<String, Kopf>,
    u: &crate::umgebung::Umgebung,
    modul: &str,
    absagen: &mut Absagen,
) {
    let Some(p) = r.path() else { return };
    let Some(kopf) = u
        .kandidaten_aufloesbar(modul, &p.text())
        .into_iter()
        .find_map(|k| koepfe.get(&k))
    else {
        return;
    };
    if kopf.forderungen.is_empty() {
        return;
    }
    let mut args = Vec::new();
    for a in &r.argumente {
        match ausdruckstext(a) {
            Some(x) => args.push(x),
            None => {
                absagen.schiebe(
                    Absage::fehler(
                        "D012",
                        a.span,
                        format!(
                            "`{}` charges its caller a premise about this argument, and this \
                             argument is not a form the premise can name",
                            kopf.pfad()
                        ),
                    )
                    .mit_notiz(
                        "the premises of beweise/Table_Ops_Erhaltung.thy speak about a SLOT: \
                         write the index as a place, so that the clause above the call and the \
                         clause here name the same one",
                    ),
                );
                return;
            }
        }
    }
    for f in &kopf.forderungen {
        let Some(verlangt) = f.gegen(&args) else {
            continue;
        };
        if steht.contains(&verlangt) {
            continue;
        }
        absagen.schiebe(
            Absage::fehler(
                "D012",
                span,
                format!(
                    "`{}` requires `{}` here, and nothing above this call says so",
                    kopf.pfad(),
                    verlangt.text()
                ),
            )
            .mit_notiz(
                "the premise comes from beweise/Table_Ops_Erhaltung.thy -- the generator \
                 discharges the preservation proof ONCE per operation, and this is the half \
                 the caller owes in exchange",
            )
            .mit_notiz(
                "write it in the routine's `requires`, in an enclosing `if`, or in an \
                 enclosing loop `invariant` -- those are the three places a fact holds where \
                 the call stands",
            ),
        );
    }
}

// ---------------------------------------------------------------------------------------
//  Reading a standing fact
// ---------------------------------------------------------------------------------------

/// The premises a predicate STATES. Conjunction and parentheses are walked; nothing else is
/// -- a premise under an `||` or behind a `=>` does not hold, and reading it as if it did
/// would be the fail-open direction.
fn aus_pred(p: &Pred, aus: &mut Vec<Steht>) {
    match &p.art {
        PredArt::Klammer(i) => aus_pred(i, aus),
        PredArt::Und(a, b) => {
            aus_pred(a, aus);
            aus_pred(b, aus);
        }
        // **A negated atom -- and since 2026-08-28 there are two of them.** `!<place>` is
        // the FRESH premise; `!(<a> reaches <b> via <f>)` is the one `relabel` charges.
        // The parentheses are stripped first: `!(x)` and `!x` say the same thing, and a
        // reader that only knew one of them would refuse the form its own head prints.
        PredArt::Nicht(i) => match &entklammere(i).art {
            PredArt::Vergleich(e) => {
                if let Some(o) = ortstext(e) {
                    aus.push(Steht::Frei(o));
                }
            }
            PredArt::Erreicht { von, nach, via } => aus.push(Steht::NichtUeber {
                von: ort_voll(von),
                nach: ort_voll(nach),
                via: via.text.clone(),
            }),
            _ => {}
        },
        PredArt::Vergleich(e) => aus_expr(e, aus),
        PredArt::Erreicht { von, via, .. } => aus.push(Steht::Erreichbar {
            von: ort_voll(von),
            via: via.text.clone(),
        }),
        PredArt::Quantor(q) => {
            if let Some(s) = blattform(q) {
                aus.push(s);
            }
        }
        PredArt::Element(_, _) | PredArt::Held { .. } | PredArt::Oder(_, _) | PredArt::Folgt(_, _) => {}
    }
}

/// The same question at an expression -- an `if` condition is one, and so is a `requires`
/// atom.
fn aus_expr(e: &Expr, aus: &mut Vec<Steht>) {
    match &e.art {
        ExprArt::Klammer(i) => aus_expr(i, aus),
        ExprArt::Binaer(BinOp::Und, a, b) => {
            aus_expr(a, aus);
            aus_expr(b, aus);
        }
        ExprArt::Unaer(UnOp::Nicht, i) => {
            if let Some(o) = ortstext(i) {
                aus.push(Steht::Frei(o));
            }
        }
        _ => {}
    }
}

/// `forall x in slots of t : t.slots[x].<via> != Some(s)` -- the LEAF premise, read back.
///
/// The bound variable is matched by NAME against the index of the quantified place: that is
/// what makes the clause say *"no slot at all"* rather than *"this one slot"*.
fn blattform(q: &Quantor) -> Option<Steht> {
    if q.art != QuantorArt::Alle {
        return None;
    }
    let Domaene::SlotsVon(traeger) = &q.domaene else {
        return None;
    };
    let PredArt::Vergleich(e) = &q.rumpf.art else {
        return None;
    };
    let ExprArt::Binaer(BinOp::Ungleich, links, rechts) = &e.art else {
        return None;
    };
    let ExprArt::Ort(o) = &links.art else {
        return None;
    };
    // `<t>.slots[<x>].<feld>`
    let [OrtSuffix::Feld(slots), OrtSuffix::Index(i), OrtSuffix::Feld(feld)] = &o.suffixe[..]
    else {
        return None;
    };
    if slots.text != "slots" || o.basis.text != ort_voll(traeger) {
        return None;
    }
    let ExprArt::Ort(iv) = &i.art else { return None };
    if !iv.suffixe.is_empty() || iv.basis.text != q.variable.text {
        return None;
    }
    let ExprArt::Ruf(some) = &rechts.art else {
        return None;
    };
    if !some.heisst("Some") || some.argumente.len() != 1 {
        return None;
    }
    Some(Steht::Blatt {
        traeger: o.basis.text.clone(),
        via: feld.text.clone(),
        s: ausdruckstext(&some.argumente[0])?,
    })
}

/// `((p))` and `p` state the same fact. Only parentheses are stripped -- nothing else,
/// because every other wrapper (`!`, `=>`, `||`) changes what is being said.
fn entklammere(p: &Pred) -> &Pred {
    match &p.art {
        PredArt::Klammer(i) => entklammere(i),
        _ => p,
    }
}

fn ortstext(e: &Expr) -> Option<String> {
    match &e.art {
        ExprArt::Klammer(i) => ortstext(i),
        ExprArt::Ort(o) => Some(ort_voll(o)),
        _ => None,
    }
}

/// A place, written out **with its index expressions** -- `Ort::text` renders them as `[…]`,
/// which is right for a manifest and wrong here: the whole question is WHICH slot.
fn ort_voll(o: &Ort) -> String {
    let mut s = o.basis.text.clone();
    for x in &o.suffixe {
        match x {
            OrtSuffix::Feld(i) => {
                s.push('.');
                s.push_str(&i.text);
            }
            OrtSuffix::Ueber(i) => {
                s.push_str("->");
                s.push_str(&i.text);
            }
            OrtSuffix::Index(e) => {
                s.push('[');
                s.push_str(&ausdruckstext(e).unwrap_or_else(|| "?".to_string()));
                s.push(']');
            }
        }
    }
    s
}

/// **`None` where the expression is not one this rule can name.** It is not a fallback
/// string: two different expressions must never render the same, or a premise about one slot
/// would discharge a call about another.
fn ausdruckstext(e: &Expr) -> Option<String> {
    match &e.art {
        ExprArt::Zahl(n) => Some(n.to_string()),
        ExprArt::Wahr => Some("true".to_string()),
        ExprArt::Falsch => Some("false".to_string()),
        ExprArt::Ort(o) => {
            let mut s = o.basis.text.clone();
            for x in &o.suffixe {
                match x {
                    OrtSuffix::Feld(i) => {
                        s.push('.');
                        s.push_str(&i.text);
                    }
                    OrtSuffix::Ueber(i) => {
                        s.push_str("->");
                        s.push_str(&i.text);
                    }
                    OrtSuffix::Index(x) => {
                        s.push('[');
                        s.push_str(&ausdruckstext(x)?);
                        s.push(']');
                    }
                }
            }
            Some(s)
        }
        ExprArt::Klammer(i) => ausdruckstext(i),
        ExprArt::Unaer(UnOp::Nicht, i) => Some(format!("!{}", ausdruckstext(i)?)),
        ExprArt::Unaer(UnOp::Negativ, i) => Some(format!("-{}", ausdruckstext(i)?)),
        ExprArt::Binaer(op, a, b) => Some(format!(
            "({}{}{})",
            ausdruckstext(a)?,
            zeichen(*op),
            ausdruckstext(b)?
        )),
        _ => None,
    }
}

const fn zeichen(op: BinOp) -> &'static str {
    match op {
        BinOp::Oder => "||",
        BinOp::Und => "&&",
        BinOp::Gleich => "==",
        BinOp::Ungleich => "!=",
        BinOp::Kleiner => "<",
        BinOp::KleinerGleich => "<=",
        BinOp::Groesser => ">",
        BinOp::GroesserGleich => ">=",
        BinOp::BitUnd => "&",
        BinOp::BitOder => "|",
        BinOp::BitXor => "^",
        BinOp::SchiebLinks => "<<",
        BinOp::SchiebRechts => ">>",
        BinOp::Plus => "+",
        BinOp::Minus => "-",
        BinOp::Mal => "*",
        BinOp::Geteilt => "/",
        BinOp::Rest => "%",
    }
}

/// **Three tables over one thing, held together by one test.**
///
/// `zeichen` here, `zeichen` in `fremdverengung.rs` and `op_zeichen` in `m1.rs` all turn a
/// `BinOp` into the sign the source wrote. Until 2026-08-31 only this one was complete: the
/// other two ended in `_ => "?"` and answered a question mark for thirteen and for two
/// operators. Measured over 499 corpus files neither arm ever fired -- *and `M136`, which
/// `m1.rs` issues, had already printed `x | y ? z` for `x | y == z`: a refusal that cannot
/// quote the line it is about.*
///
/// **Three registers over one thing is `W7`.** Merging them is a bigger move than this lane
/// carries; holding them to the same answer is not, and it is what makes a divergence a red
/// test instead of a question mark in a message.
#[cfg(test)]
mod operatortafeln {
    use super::*;

    /// Every `BinOp`, written out -- the list a `_` would have hidden.
    const ALLE: &[BinOp] = &[
        BinOp::Oder,
        BinOp::Und,
        BinOp::Gleich,
        BinOp::Ungleich,
        BinOp::Kleiner,
        BinOp::KleinerGleich,
        BinOp::Groesser,
        BinOp::GroesserGleich,
        BinOp::BitUnd,
        BinOp::BitOder,
        BinOp::BitXor,
        BinOp::SchiebLinks,
        BinOp::SchiebRechts,
        BinOp::Plus,
        BinOp::Minus,
        BinOp::Mal,
        BinOp::Geteilt,
        BinOp::Rest,
    ];

    #[test]
    fn zwei_operatortafeln_stimmen_ueberein() {
        for op in ALLE {
            assert_eq!(
                zeichen(*op),
                crate::fremdverengung::zeichen(*op),
                "{op:?}"
            );
        }
    }

    /// **And none of them is a question mark.** A table that agrees with a second one on `?`
    /// would pass the test above and still print nothing about the source.
    #[test]
    fn kein_operator_heisst_fragezeichen() {
        for op in ALLE {
            assert_ne!(zeichen(*op), "?", "{op:?}");
            assert_ne!(crate::fremdverengung::zeichen(*op), "?", "{op:?}");
        }
    }
}
