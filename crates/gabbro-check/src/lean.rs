//! **The BODY channel: a Gabbro body as a Lean 4 term, and its obligation as a theorem.**
//!
//! `refinement.rs` writes the same register as Isabelle quoted and refuses seventeen of its
//! obligations with one word: `body-effect` -- *"speaks about the world AFTER a body ran,
//! and there is no semantics of a Gabbro body"*. **This module is that semantics' other
//! half.** The meaning itself lives in `programmlogik/Gabbro/Body.lean`, written once by
//! hand; what stands here only translates a body into a datum of it.
//!
//! ## Why the meaning is not in this file
//!
//! A translator that both *defines* what a body means and *decides* whether the obligation
//! holds has no independent reader. `Body.lean` is readable Lean with its own theorems, and
//! this file emits data against it. *That split is the whole reason a prover is worth
//! anything here* -- the same relation `lean4export` has to the Lean kernel.
//!
//! ## What the plumbing pays for, and it is the reason this file is short
//!
//! Nine of eleven classes are carried by the language, so the model underneath needs no
//! heap, no separation logic, no pointers and no concurrency (`Body.lean`, header). The
//! places a body touches are the declared `effects` list, and that this covers the
//! transitive effect is proved -- `Passlogik.Wirkung.huelle_deckt`.
//!
//! ## The two gates, and they carry the same weight as in `refinement.rs`
//!
//! 1. **A typing hypothesis is read from the DECLARATION, never from the use.** Guessing
//!    `c.slots[s].elter` is an option because the body matches on it would make the goal
//!    easier, not harder -- the exact shape of quiet weakening this channel exists against.
//! 2. **The goal is the STRONG form**: the body runs to an end *and* the postcondition
//!    holds. `\forall l', end = some l' -> P l'` would be vacuously true for a body that
//!    gets stuck, and a vacuous theorem reads exactly like a proved one.

use gabbro_syntax::ast::*;
use std::collections::HashMap;

/// **Why an obligation carries no Lean goal.** Exhaustive, and each arm names a different
/// missing thing -- a single "not supported" would hide that they have different prices.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LeanReason {
    /// An `ensures` at a body Gabbro never sees. **An assumption, not a goal.**
    ForeignBody,
    /// `maintains I` -- a table invariant, and a table invariant is a QUANTIFIED statement
    /// over every slot. This channel has no quantifier, and inventing one that ranges over
    /// `Int` instead of over the declared capacity would prove a different sentence.
    Invariant,
    /// A precondition at a call site. **Not a gap:** the Isabelle channel carries these, and
    /// twelve of them are discharged by the lock passes before any prover sees them.
    CallSite,
    /// A promise at a device register -- hardware Gabbro does not see.
    DevicePromise,
    /// A CALL. **The biggest single item of the register, and it is not an oversight**: a
    /// call is to be taken compositionally over the callee's CONTRACT, never over its body.
    /// Inlining the body would make the goal a statement about a program nobody wrote.
    CallStatement,
    /// A loop -- `traverse`, `retry`, `forever`. The measure is carried by the language
    /// (`K008`/`K009`); what is missing is the INVARIANT, and Gabbro has no word for one at
    /// a loop (`Traverse`/`Retry`/`Forever` have no such field, `Tabelle` does).
    Loop,
    /// `locks`, `publishes`, `awaits`, `exchange`, `observes`. **Here one state and one
    /// transition stop carrying** -- it would take a memory model with visibility.
    Concurrent,
    /// `let … else` -- the one error propagation, two exits out of a call. It waits on the
    /// call gate and on nothing else.
    ErrorPropagation,
    /// `narrow … to … else` -- and the range lattice underneath is already proved
    /// (`Passlogik.Bereich`, 46 theorems). This one is close.
    Narrowing,
    /// `leave`, `next`, `breaking` -- a non-local exit out of a named loop. Meaningless
    /// without the loop gate.
    NonLocalExit,
    /// `+=` and its kin. It desugars to `x = x + e` -- **but the two are not the same
    /// statement in Gabbro's overflow accounting, and this channel does not get to decide
    /// that.**
    CompoundAssign,
    /// A `match` over something other than an `option`. A declared sum type would need one
    /// value constructor per variant.
    MatchNotOption,
    /// An expression or predicate form with no Lean term here.
    Expression,
    /// A place whose carrier cannot be resolved to a declared `table`. **Without the
    /// declaration there is no field shape**, and without the field shape the hypothesis
    /// would have to be guessed -- see gate 1.
    Carrier,
    /// A field whose declared type has no shape in this channel -- `wrapping`, a float, a
    /// record, or an OPAQUE new type whose representation `D1` forbids reading.
    ///
    /// **It stands beside `Carrier` and not inside it**, and the split was measured: the
    /// first run reported `carrier-not-a-table` for `Buch.slots[p].wert`, where `Buch` is a
    /// table and `wert` is a `Zaehler`. *A refusal filed under the wrong reason names a
    /// missing declaration where a missing translation stands* -- the same lesson
    /// `messung/P6.md` §3.2 books for twelve obligations.
    FieldShape,
    /// A `refines` whose named `spec fn` is not a plain expression body.
    SpecShape,
}

impl LeanReason {
    pub fn tag(self) -> &'static str {
        match self {
            LeanReason::ForeignBody => "foreign-body",
            LeanReason::Invariant => "table-invariant",
            LeanReason::CallSite => "call-site",
            LeanReason::DevicePromise => "device-promise",
            LeanReason::CallStatement => "call-not-compositional",
            LeanReason::Loop => "loop",
            LeanReason::Concurrent => "concurrent-statement",
            LeanReason::ErrorPropagation => "let-else",
            LeanReason::Narrowing => "narrow",
            LeanReason::NonLocalExit => "non-local-exit",
            LeanReason::CompoundAssign => "compound-assignment",
            LeanReason::MatchNotOption => "match-not-option",
            LeanReason::Expression => "no-term",
            LeanReason::Carrier => "carrier-not-a-table",
            LeanReason::FieldShape => "no-shape-for-field",
            LeanReason::SpecShape => "spec-not-an-expression",
        }
    }
    pub fn sentence(self) -> &'static str {
        match self {
            LeanReason::ForeignBody => {
                "an `ensures` at a body Gabbro never sees: an ASSUMPTION, not a goal"
            }
            LeanReason::Invariant => {
                "`maintains` names a table invariant, and that is quantified over every slot"
            }
            LeanReason::CallSite => {
                "a precondition at a call site -- the Isabelle channel carries these"
            }
            LeanReason::DevicePromise => "a promise at hardware Gabbro does not see",
            LeanReason::CallStatement => {
                "a call -- compositional over the CONTRACT, and that gate is not built"
            }
            LeanReason::Loop => "a loop -- the measure is carried, the INVARIANT has no word",
            LeanReason::Concurrent => {
                "a concurrent statement -- one state and one transition stop carrying here"
            }
            LeanReason::ErrorPropagation => "`let … else` -- two exits out of a call",
            LeanReason::Narrowing => "`narrow` -- the range lattice under it is proved",
            LeanReason::NonLocalExit => "a non-local exit out of a named loop",
            LeanReason::CompoundAssign => "`+=` and its kin -- a different overflow accounting",
            LeanReason::MatchNotOption => "a `match` over something other than an `option`",
            LeanReason::Expression => "a form this channel has no Lean term for",
            LeanReason::Carrier => {
                "the carrier of a place is not a declared `table`, so no field shape is known"
            }
            LeanReason::FieldShape => {
                "the declared type of a slot field has no shape in this channel"
            }
            LeanReason::SpecShape => "the named `spec fn` is not a plain expression body",
        }
    }
    /// **All of them, so a report cannot omit one by forgetting to ask.**
    pub const ALL: [LeanReason; 16] = [
        LeanReason::ForeignBody,
        LeanReason::Invariant,
        LeanReason::CallSite,
        LeanReason::DevicePromise,
        LeanReason::CallStatement,
        LeanReason::Loop,
        LeanReason::Concurrent,
        LeanReason::ErrorPropagation,
        LeanReason::Narrowing,
        LeanReason::NonLocalExit,
        LeanReason::CompoundAssign,
        LeanReason::MatchNotOption,
        LeanReason::Expression,
        LeanReason::Carrier,
        LeanReason::FieldShape,
        LeanReason::SpecShape,
    ];
}

/// One closed Lean goal over a body.
pub struct LeanGoal {
    /// `duty_7` -- the position in the register `gabbro pflichten` prints.
    pub name: String,
    /// The body, as a `Gabbro.Body.Stmt` list term.
    pub body: String,
    /// `(label, term, where it came from)` -- every hypothesis, read from a declaration.
    pub hypotheses: Vec<(String, String, String)>,
    /// The postcondition, as a `Gabbro.Body.Expr` that must evaluate to `true`.
    pub conclusion: String,
    /// **The `obtain` lines the proof opens with.** A hypothesis `\exists n, l.locals "p" =
    /// .z n` tells `simp` nothing until the witness is named; without these the goal stalls
    /// on an unreduced `match` over `l.locals "p"`. *Measured on the first run of this
    /// emitter, and it is why the tactic is generated rather than fixed.*
    pub opening: Vec<String>,
    /// The equation names those `obtain`s bind, for the `simp` set.
    pub equations: Vec<String>,
    /// **The `rcases` fragments, and they are kept apart from `opening` because they must
    /// be CHAINED.** An `rcases` splits the goal, and a plain next line applies only to the
    /// first half -- measured: the second split reported its own witness as an unknown
    /// identifier in every branch the first split had left behind.
    pub splits: Vec<String>,
}

pub enum LeanVerdict {
    Proved(Box<LeanGoal>),
    Refused(LeanReason),
}

/// **What a table declares.** Field name to the shape its declaration gives it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Shape {
    Int,
    Bool,
    Opt,
}

impl Shape {
    fn predicate(self) -> &'static str {
        match self {
            Shape::Int => "isInt",
            Shape::Bool => "isBool",
            Shape::Opt => "isOption",
        }
    }
}

/// The shape a declared type gives a value. `None` where this channel has no shape for it --
/// **and a place of such a field is refused, not defaulted.**
///
/// **The option distinction is read SYNTACTICALLY and the rest through the environment**,
/// and the split is not tidiness. `option index into T` and `index into T` both resolve to
/// an integer -- the sentinel lowering is the point of `Option_Sonderwert.thy` -- so a
/// resolved type cannot tell them apart. *Asking the resolved type here would silently make
/// every option field a number, and a `match` over it would then be unreachable rather than
/// refused.*
fn shape_of(t: &TypExpr, u: &crate::umgebung::Umgebung, module: &str) -> Option<Shape> {
    if let TypExpr::Index { optional, .. } = t {
        return Some(if *optional { Shape::Opt } else { Shape::Int });
    }
    shape_of_typ(&u.typ_von_ausdruck_decl(module, t))
}

fn shape_of_typ(t: &crate::typen::Typ) -> Option<Shape> {
    use crate::typen::Typ;
    match t {
        Typ::Ganzzahl(_) => Some(Shape::Int),
        Typ::Wahrheit => Some(Shape::Bool),
        Typ::Tabelle(_) => Some(Shape::Int),
        // **An OPAQUE new type stops here and a transparent one does not.** Reading the
        // representation of an `opaque` is exactly the implicit conversion `D1` forbids;
        // a transparent one is a range with a name, and a name is not a wall.
        Typ::Benannt {
            undurchsichtig: false,
            unter,
            ..
        } => shape_of_typ(unter),
        // `wrapping` gives no shape: overflow is the POINT of the type, so unbounded `Int`
        // arithmetic over it would compute something Gabbro does not.
        Typ::Umlaufend(_)
        | Typ::Benannt { .. }
        | Typ::Gleitkomma(_)
        | Typ::Nie
        | Typ::Zeiger(_)
        | Typ::Summe { .. }
        | Typ::Verbund(_)
        | Typ::Feld { .. }
        | Typ::Register { .. }
        | Typ::Verbundname(_)
        | Typ::FnPtr(_)
        | Typ::Unbekannt
        | Typ::Grund(_) => None,
    }
}

/// Everything the translation of one body may look at.
struct Ctx<'a> {
    /// Table name to its slot fields, as declared.
    tables: &'a HashMap<String, Vec<(String, Option<Shape>)>>,
    /// The declaring function's parameters: name to the table its type points at, if any.
    carrier: HashMap<String, String>,
    /// Parameter and `let` names -- these read from `locals`, not from the world.
    locals: Vec<String>,
    /// Collected while translating: `(carrier, field, form, origin)`, deduplicated.
    seen: Vec<(String, String, Shape, String)>,
    /// **Every `(carrier, field, index-parameter)` read at an option-shaped field.**
    ///
    /// `istWahl` is a DISJUNCTION, and `simp` cannot open one: without the case split the
    /// goal stalls on an unreduced `match` over the field. *Measured on the first corpus
    /// run of this channel -- `aushaengen` was the one red module of sixty-eight, and the
    /// reason was this and nothing else.*
    option_reads: Vec<(String, String, String)>,
}

impl Ctx<'_> {
    /// **Which table does this base name stand for?** A bare table name stands for itself;
    /// a parameter stands for the table its pointer type names.
    fn table_of(&self, base: &str) -> Option<&String> {
        self.carrier.get(base)
    }

    /// A place whose index is a bare parameter, at an option-shaped field: the proof will
    /// have to split on it.
    fn note_option(&mut self, carrier: &str, feld: &str, form: Shape, index: &Expr) {
        if form != Shape::Opt {
            return;
        }
        let ExprArt::Ort(o) = &index.art else { return };
        if !o.suffixe.is_empty() {
            return;
        }
        let p = o.basis.text.clone();
        if !self
            .option_reads
            .iter()
            .any(|(t, f, i)| t == carrier && f == feld && *i == p)
        {
            self.option_reads
                .push((carrier.to_string(), feld.to_string(), p));
        }
    }

    fn note(&mut self, carrier: &str, feld: &str, f: Shape, origin: &str) {
        if !self
            .seen
            .iter()
            .any(|(t, n, _, _)| t == carrier && n == feld)
        {
            self.seen.push((
                carrier.to_string(),
                feld.to_string(),
                f,
                origin.to_string(),
            ));
        }
    }
}

fn quoted(s: &str) -> String {
    // Gabbro identifiers are ASCII words; this fires on nothing in today's corpus, and that
    // is exactly why it stands here instead of being assumed.
    format!("\"{}\"", s.replace('\\', "").replace('"', ""))
}

/// **Carrier, field, shape -- and the two refusals are DIFFERENT ones.**
///
/// A base that names no table is `Carrier`; a field the table does declare but whose type
/// this channel has no shape for is `FieldShape`. *The first says a declaration is missing,
/// the second says a translation is.* Folding them would report `Buch.slots[p].wert` as an
/// unknown carrier, and `Buch` is right there in the file.
fn field_shape(base: &str, feld: &str, c: &Ctx) -> Result<(String, Shape, String), LeanReason> {
    let tab = c.table_of(base).ok_or(LeanReason::Carrier)?.clone();
    let fields = c.tables.get(&tab).ok_or(LeanReason::Carrier)?;
    let (_, form) = fields
        .iter()
        .find(|(n, _)| n == feld)
        .ok_or(LeanReason::Carrier)?;
    let form = form.ok_or(LeanReason::FieldShape)?;
    Ok((base.to_string(), form, tab))
}

/// A place, as a `Gabbro.Body.Expr`. **Two forms and nothing else:** a bare name, and
/// `carrier.slots[i].field`.
fn place_term(o: &Ort, c: &mut Ctx) -> Result<String, LeanReason> {
    if o.suffixe.is_empty() {
        let n = &o.basis.text;
        return Ok(if c.locals.iter().any(|l| l == n) {
            format!("(.name {})", quoted(n))
        } else {
            format!("(.global {})", quoted(n))
        });
    }
    let [OrtSuffix::Feld(slots), OrtSuffix::Index(i), OrtSuffix::Feld(f)] = &o.suffixe[..] else {
        return Err(LeanReason::Carrier);
    };
    if slots.text != "slots" {
        return Err(LeanReason::Carrier);
    }
    let (base, shape, tab) = field_shape(&o.basis.text, &f.text, c)?;
    let idx = expr_term(i, c)?;
    c.note(&base, &f.text, shape, &format!("`{}` in `{}`", f.text, tab));
    c.note_option(&base, &f.text, shape, i);
    Ok(format!(
        "(.place {} {} {})",
        quoted(&base),
        idx,
        quoted(&f.text)
    ))
}

/// An expression as a `Gabbro.Body.Expr`.
///
/// **The `match` has no catch-all**, and that is deliberate even though every unlisted arm
/// would refuse: a new expression form must be DECIDED here, not defaulted.
fn expr_term(e: &Expr, c: &mut Ctx) -> Result<String, LeanReason> {
    match &e.art {
        ExprArt::Zahl(n) => Ok(format!("(.lit (.int {n}))")),
        ExprArt::Wahr => Ok("(.lit (.bool true))".into()),
        ExprArt::Falsch => Ok("(.lit (.bool false))".into()),
        ExprArt::Klammer(x) => expr_term(x, c),
        ExprArt::Ort(o) => place_term(o, c),
        ExprArt::Unaer(UnOp::Nicht, x) => Ok(format!("(.un .not {})", expr_term(x, c)?)),
        ExprArt::Unaer(UnOp::Negativ, x) => Ok(format!("(.un .neg {})", expr_term(x, c)?)),
        ExprArt::Binaer(op, a, b) => {
            let z = match op {
                BinOp::Plus => "add",
                BinOp::Minus => "sub",
                BinOp::Mal => "mul",
                BinOp::Gleich => "eq",
                BinOp::Ungleich => "ne",
                BinOp::Kleiner => "lt",
                BinOp::KleinerGleich => "le",
                BinOp::Groesser => "gt",
                BinOp::GroesserGleich => "ge",
                BinOp::Und => "and",
                BinOp::Oder => "or",
                // Division and the bit operations are refused for the reason
                // `refinement.rs` already books: Lean's `Int` division rounds toward minus
                // infinity, C's truncates toward zero. A goal that mixed the two would be
                // provable for a reason the machine does not have.
                BinOp::BitUnd
                | BinOp::BitOder
                | BinOp::BitXor
                | BinOp::SchiebLinks
                | BinOp::SchiebRechts
                | BinOp::Geteilt
                | BinOp::Rest => return Err(LeanReason::Expression),
            };
            Ok(format!(
                "(.bin .{z} {} {})",
                expr_term(a, c)?,
                expr_term(b, c)?
            ))
        }
        // `None` is a value of the option shape and the commonest right-hand side in the
        // corpus. `Some(e)` is refused: it would need a second value constructor, and no
        // obligation in today's corpus asks for one.
        ExprArt::Ruf(r) => match r.path().and_then(|p| p.teile.last()).map(|i| &i.text) {
            Some(n) if n == "None" && r.argumente.is_empty() => Ok("(.lit .absent)".into()),
            Some(n) if n == "Some" && r.argumente.len() == 1 => {
                Ok(format!("(.someOf {})", expr_term(&r.argumente[0], c)?))
            }
            _ => Err(LeanReason::Expression),
        },
        ExprArt::Gleitkomma { .. }
        | ExprArt::FnWert(_)
        | ExprArt::Eingebaut(_)
        | ExprArt::Alt(_)
        | ExprArt::Ergebnis
        | ExprArt::Grund { .. } => Err(LeanReason::Expression),
    }
}

/// A predicate as a `Gabbro.Body.Expr` that must evaluate to `true`.
fn pred_term(p: &Pred, c: &mut Ctx) -> Result<String, LeanReason> {
    match &p.art {
        PredArt::Vergleich(e) => expr_term(e, c),
        PredArt::Klammer(q) => pred_term(q, c),
        PredArt::Nicht(q) => Ok(format!("(.un .not {})", pred_term(q, c)?)),
        PredArt::Und(a, b) => Ok(format!(
            "(.bin .and {} {})",
            pred_term(a, c)?,
            pred_term(b, c)?
        )),
        PredArt::Oder(a, b) => Ok(format!(
            "(.bin .or {} {})",
            pred_term(a, c)?,
            pred_term(b, c)?
        )),
        // `a -> b` is `!a || b`. **Not a shortcut:** `Value` has no implication, and adding
        // one to the model for a form that desugars exactly would be a second way to say
        // one thing.
        PredArt::Folgt(a, b) => Ok(format!(
            "(.bin .or (.un .not {}) {})",
            pred_term(a, c)?,
            pred_term(b, c)?
        )),
        PredArt::Held { .. } | PredArt::Quantor(_) | PredArt::Element(_, _)
        | PredArt::Erreicht { .. } => Err(LeanReason::Expression),
    }
}

/// A block as a `Gabbro.Body.Stmt` list term.
fn block_term(b: &Block, c: &mut Ctx) -> Result<String, LeanReason> {
    let depth = c.locals.len();
    let mut teile = Vec::new();
    for s in &b.anweisungen {
        teile.push(stmt_term(s, c)?);
    }
    // A `let` name leaves scope with its block -- the model binds by name, so a name that
    // outlived its block would silently shadow one further out.
    c.locals.truncate(depth);
    Ok(format!("[{}]", teile.join(", ")))
}

fn stmt_term(s: &Stmt, c: &mut Ctx) -> Result<String, LeanReason> {
    match &s.art {
        StmtArt::Let(l) => {
            let w = expr_term(&l.wert, c)?;
            c.locals.push(l.name.text.clone());
            Ok(format!("(.bindName {} {})", quoted(&l.name.text), w))
        }
        StmtArt::Zuweisung(z) => {
            if z.op != ZuwOp::Setzt {
                return Err(LeanReason::CompoundAssign);
            }
            let w = expr_term(&z.wert, c)?;
            if z.ziel.suffixe.is_empty() {
                return Ok(format!("(.assignGlobal {} {})", quoted(&z.ziel.basis.text), w));
            }
            let [OrtSuffix::Feld(slots), OrtSuffix::Index(i), OrtSuffix::Feld(f)] =
                &z.ziel.suffixe[..]
            else {
                return Err(LeanReason::Carrier);
            };
            if slots.text != "slots" {
                return Err(LeanReason::Carrier);
            }
            let (base, shape, tab) = field_shape(&z.ziel.basis.text, &f.text, c)?;
            let idx = expr_term(i, c)?;
            c.note(&base, &f.text, shape, &format!("`{}` in `{}`", f.text, tab));
            Ok(format!(
                "(.assign {} {} {} {})",
                quoted(&base),
                idx,
                quoted(&f.text),
                w
            ))
        }
        StmtArt::Wenn(w) => {
            // An `else if` chain folds from the back: one conditional statement per branch.
            let mut otherwise = match &w.sonst {
                Some(b) => block_term(b, c)?,
                None => "[]".to_string(),
            };
            for (bed, blk) in w.zweige.iter().rev() {
                let b = expr_term(bed, c)?;
                let d = block_term(blk, c)?;
                otherwise = format!("[(.ite {b} {d} {otherwise})]");
            }
            // The fold produced a one-element list; a statement is wanted, so unwrap it.
            Ok(otherwise
                .strip_prefix('[')
                .and_then(|s| s.strip_suffix(']'))
                .unwrap_or(&otherwise)
                .to_string())
        }
        StmtArt::Match(m) => {
            // **Exactly the option shape, and nothing else.** A `match` over a declared sum
            // type would need a value constructor per variant; refusing here is a number,
            // guessing would be a meaning.
            let g = expr_term(&m.gegenstand, c)?;
            let mut onp = None;
            let mut ona = None;
            for z in &m.zweige {
                match (z.variante.text.as_str(), &z.binder) {
                    ("Some", Some(b)) => {
                        let depth = c.locals.len();
                        c.locals.push(b.text.clone());
                        let blk = block_term(&z.rumpf, c)?;
                        c.locals.truncate(depth);
                        onp = Some((b.text.clone(), blk));
                    }
                    ("None", None) => ona = Some(block_term(&z.rumpf, c)?),
                    _ => return Err(LeanReason::MatchNotOption),
                }
            }
            match (onp, ona) {
                (Some((b, present)), Some(absent)) => {
                    Ok(format!("(.onOption {g} {} {present} {absent})", quoted(&b)))
                }
                _ => Err(LeanReason::MatchNotOption),
            }
        }
        StmtArt::Return(None) => Ok("(.ret none)".into()),
        StmtArt::Return(Some(e)) => Ok(format!("(.ret (some {}))", expr_term(e, c)?)),
        // Everything else is refused BY NAME. `Ruf` and `LetSonst` belong to the sequential
        // core and are the next two to build: a call is compositional over the CONTRACT of
        // the callee, never over its body, and that gate is not built.
        StmtArt::Ruf(_) => Err(LeanReason::CallStatement),
        StmtArt::LetSonst(_) => Err(LeanReason::ErrorPropagation),
        StmtArt::Schleife(_) => Err(LeanReason::Loop),
        StmtArt::Narrow(_) => Err(LeanReason::Narrowing),
        StmtArt::Bricht(_) | StmtArt::Leave(_) | StmtArt::Next(_) => {
            Err(LeanReason::NonLocalExit)
        }
        StmtArt::Sperrt(_)
        | StmtArt::Observiert(_)
        | StmtArt::Publish(_)
        | StmtArt::AwaitLoad(_)
        | StmtArt::Exchange(_) => Err(LeanReason::Concurrent),
    }
}

/// **Every table of the unit, with the shape its declaration gives each slot field.**
///
/// A field whose type has no shape is kept with `None` and NOT dropped -- a dropped field
/// looks like an undeclared one, and the refusal would then name the wrong thing.
fn tables(
    baum: &Programm,
    u: &crate::umgebung::Umgebung,
) -> HashMap<String, Vec<(String, Option<Shape>)>> {
    let mut out = HashMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, module| {
        let ItemArt::Tabelle(tb) = &item.art else { return };
        let mut fields = Vec::new();
        if let Some(s) = &tb.slot {
            for f in &s.felder {
                let form = match &f.typ {
                    SlotTyp::Typ(te) => shape_of(te, u, module),
                    SlotTyp::Wrapping(_) => None,
                };
                fields.push((f.name.text.clone(), form));
            }
        }
        out.insert(tb.name.text.clone(), fields);
    });
    out
}

/// **Which base name stands for which table**, for one function.
fn carriers_of(
    f: &FnDecl,
    tab: &HashMap<String, Vec<(String, Option<Shape>)>>,
    statics: &HashMap<String, String>,
) -> HashMap<String, String> {
    let mut out = HashMap::new();
    // A table name stands for itself.
    for name in tab.keys() {
        out.insert(name.clone(), name.clone());
    }
    // A `static` that points at a table stands for it, in every function.
    for (n, table) in statics {
        out.insert(n.clone(), table.clone());
    }
    // A parameter stands for the table its pointer type names.
    for p in &f.parameter {
        if let Some(table) = points_at_table(&p.typ, tab) {
            out.insert(p.name.text.clone(), table);
        }
    }
    out
}

/// Does this declared type point at a declared table? **Through a pointer or directly.**
fn points_at_table(
    typ: &TypExpr,
    tab: &HashMap<String, Vec<(String, Option<Shape>)>>,
) -> Option<String> {
    let target = match typ {
        TypExpr::Zeiger(z) => &z.ziel,
        t => t,
    };
    let TypExpr::Pfad(pf) = target else { return None };
    let last = pf.teile.last()?;
    tab.contains_key(&last.text).then(|| last.text.clone())
}

/// **Every `static` that points at a table.** Read once per program, not per function.
///
/// *Measured, and the refusal had been naming the wrong thing:* `beispiele/38` writes
/// `tz.slots[i].a` where `tz` is a `static ptr<normal, rw> Platz`. `carriers_of` looked only
/// at parameters, so the place was refused as `carrier-not-a-table` -- and `Platz` is
/// declared four lines above. **A static is not a parameter, and it is a carrier all the
/// same.**
fn static_carriers(
    baum: &Programm,
    tab: &HashMap<String, Vec<(String, Option<Shape>)>>,
) -> HashMap<String, String> {
    let mut out = HashMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, _| {
        let ItemArt::Statisch(st) = &item.art else { return };
        if let Some(table) = points_at_table(&st.typ, tab) {
            out.insert(st.name.text.clone(), table);
        }
    });
    out
}

/// **The one function this module exists for**: a body obligation as a Lean goal, or a
/// named refusal.
fn judge(
    f: &FnDecl,
    post: &Pred,
    u: &crate::umgebung::Umgebung,
    module: &str,
    tab: &HashMap<String, Vec<(String, Option<Shape>)>>,
    statics: &HashMap<String, String>,
    number: usize,
) -> LeanVerdict {
    let FnRumpf::Block(b) = &f.rumpf else {
        return LeanVerdict::Refused(LeanReason::ForeignBody);
    };
    let mut c = Ctx {
        tables: tab,
        carrier: carriers_of(f, tab, statics),
        locals: f.parameter.iter().map(|p| p.name.text.clone()).collect(),
        seen: Vec::new(),
        option_reads: Vec::new(),
    };
    let body = match block_term(b, &mut c) {
        Ok(t) => t,
        Err(r) => return LeanVerdict::Refused(r),
    };
    let conclusion = match pred_term(post, &mut c) {
        Ok(t) => t,
        Err(r) => return LeanVerdict::Refused(r),
    };
    // **The hypotheses, and every one of them read from a declaration.**
    let mut hypotheses = Vec::new();
    let mut opening = Vec::new();
    let mut splits: Vec<String> = Vec::new();
    let mut equations = Vec::new();
    for p in &f.parameter {
        if let Some(form) = shape_of(&p.typ, u, module) {
            let n = &p.name.text;
            hypotheses.push((
                format!("p_{n}"),
                format!("{} (s.local' {})", form.predicate(), quoted(n)),
                format!("the declared type of `{n}`"),
            ));
            // `istWahl` is a DISJUNCTION, not an existential -- there is no single witness
            // to name, so it stays whole and the goal that needs it is refused rather than
            // half-opened.
            if form != Shape::Opt {
                opening.push(format!("  obtain \\<langle>w_{n}, e_{n}\\<rangle> := p_{n}"));
                equations.push(format!("e_{n}"));
            }
        }
    }
    for (carrier, feld, form, origin) in &c.seen {
        hypotheses.push((
            format!("f_{carrier}_{feld}"),
            format!(
                "\\<forall> k, {} (s.world (.slot {} k {}))",
                form.predicate(),
                quoted(carrier),
                quoted(feld)
            ),
            origin.clone(),
        ));
    }
    // **The case split, one per option-shaped field read at a parameter index.**
    //
    // The split is emitted only where the WITNESS exists -- a parameter whose declared type
    // gave a shape and was therefore opened above. Without the witness there is no `w_p` to
    // apply the hypothesis to, and a split written anyway would not elaborate.
    for (carrier, field, index) in &c.option_reads {
        if !equations.iter().any(|g| *g == format!("e_{index}")) {
            continue;
        }
        let h = format!("h_{carrier}_{field}_{index}");
        splits.push(format!(
            "rcases f_{carrier}_{field} w_{index} with {h} | \\<langle>m_{carrier}_{field}_{index}, {h}\\<rangle>"
        ));
        equations.push(h);
    }
    LeanVerdict::Proved(Box::new(LeanGoal {
        name: format!("duty_{number}"),
        body,
        hypotheses,
        conclusion,
        opening,
        equations,
        splits,
    }))
}

/// **The whole register, judged for the Lean channel.** One entry per obligation of
/// `pflichten::sammle`, in the same order -- so the two channels can be held against each
/// other, obligation by obligation.
pub fn verdicts(baum: &Programm) -> Vec<(crate::pflichten::Pflicht, LeanVerdict)> {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let tab = tables(baum, &u);
    let statics = static_carriers(baum, &tab);
    // The module a function is declared in travels with it: `typ_von_ausdruck_decl` is
    // module-aware, and asking it from the wrong module answers about the wrong type.
    let mut fns: HashMap<String, (String, FnDecl)> = HashMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, module| {
        if let ItemArt::Funktion(f) = &item.art {
            fns.insert(f.name.text.clone(), (module.to_string(), f.clone()));
        }
    });

    crate::pflichten::sammle(baum)
        .into_iter()
        .enumerate()
        .map(|(i, p)| {
            let n = i + 1;
            let v = match p.art {
                crate::pflichten::Art::Vorbedingung => LeanVerdict::Refused(LeanReason::CallSite),
                crate::pflichten::Art::Geraetezusage => {
                    LeanVerdict::Refused(LeanReason::DevicePromise)
                }
                crate::pflichten::Art::Fremdpflicht => {
                    LeanVerdict::Refused(LeanReason::ForeignBody)
                }
                crate::pflichten::Art::Erhaltung => LeanVerdict::Refused(LeanReason::Invariant),
                crate::pflichten::Art::Nachbedingung => match fns.get(&p.funktion) {
                    Some((module, f)) => {
                        // `ensures #k` -- the index is in the register's own wording.
                        let k = p
                            .gegenstand
                            .rsplit('#')
                            .next()
                            .and_then(|s| s.parse::<usize>().ok())
                            .unwrap_or(0);
                        match f.ensures.get(k.wrapping_sub(1)) {
                            Some(q) => judge(f, q, &u, module, &tab, &statics, n),
                            None => LeanVerdict::Refused(LeanReason::Expression),
                        }
                    }
                    None => LeanVerdict::Refused(LeanReason::Expression),
                },
                crate::pflichten::Art::Verfeinerung => match fns.get(&p.funktion) {
                    Some((module, f)) => match specification(f, &fns) {
                        Ok(q) => judge(f, &q, &u, module, &tab, &statics, n),
                        Err(r) => LeanVerdict::Refused(r),
                    },
                    None => LeanVerdict::Refused(LeanReason::SpecShape),
                },
            };
            (p, v)
        })
        .collect()
}

/// **`refines g` -- the head form.** The obligation is *what this body establishes is what
/// `g` describes*, so the postcondition IS the `spec fn`'s expression body, with its own
/// parameter names replaced by the implementation's. `M132` has already checked that both
/// carry the same number of parameters.
fn specification(
    f: &FnDecl,
    fns: &HashMap<String, (String, FnDecl)>,
) -> Result<Pred, LeanReason> {
    let path = f.verfeinert.as_ref().ok_or(LeanReason::SpecShape)?;
    let name = path.teile.last().ok_or(LeanReason::SpecShape)?;
    let (_, spec) = fns.get(&name.text).ok_or(LeanReason::SpecShape)?;
    let FnRumpf::Pred(p) = &spec.rumpf else {
        return Err(LeanReason::SpecShape);
    };
    let pairs: Vec<(String, String)> = spec
        .parameter
        .iter()
        .zip(f.parameter.iter())
        .map(|(s, i)| (s.name.text.clone(), i.name.text.clone()))
        .collect();
    Ok(renamed_pred(p, &pairs))
}

fn renamed_pred(p: &Pred, pairs: &[(String, String)]) -> Pred {
    let art = match &p.art {
        PredArt::Vergleich(e) => PredArt::Vergleich(renamed_expr(e, pairs)),
        PredArt::Klammer(q) => PredArt::Klammer(Box::new(renamed_pred(q, pairs))),
        PredArt::Nicht(q) => PredArt::Nicht(Box::new(renamed_pred(q, pairs))),
        PredArt::Und(a, b) => PredArt::Und(
            Box::new(renamed_pred(a, pairs)),
            Box::new(renamed_pred(b, pairs)),
        ),
        PredArt::Oder(a, b) => PredArt::Oder(
            Box::new(renamed_pred(a, pairs)),
            Box::new(renamed_pred(b, pairs)),
        ),
        PredArt::Folgt(a, b) => PredArt::Folgt(
            Box::new(renamed_pred(a, pairs)),
            Box::new(renamed_pred(b, pairs)),
        ),
        other => other.clone(),
    };
    Pred { art, ..p.clone() }
}

fn renamed_expr(e: &Expr, pairs: &[(String, String)]) -> Expr {
    let art = match &e.art {
        ExprArt::Ort(o) => {
            let mut o = o.clone();
            if let Some((_, fresh)) = pairs.iter().find(|(old, _)| *old == o.basis.text) {
                o.basis.text = fresh.clone();
            }
            for s in &mut o.suffixe {
                if let OrtSuffix::Index(i) = s {
                    *i = renamed_expr(i, pairs);
                }
            }
            ExprArt::Ort(o)
        }
        ExprArt::Klammer(x) => ExprArt::Klammer(Box::new(renamed_expr(x, pairs))),
        ExprArt::Unaer(op, x) => ExprArt::Unaer(*op, Box::new(renamed_expr(x, pairs))),
        ExprArt::Binaer(op, a, b) => ExprArt::Binaer(
            *op,
            Box::new(renamed_expr(a, pairs)),
            Box::new(renamed_expr(b, pairs)),
        ),
        other => other.clone(),
    };
    Expr { art, ..e.clone() }
}

/// **The module name of a unit.** Lean demands that it match the file, so the stem is what
/// this derives from.
pub fn module_name(datei: &str) -> String {
    let stem = datei
        .rsplit('/')
        .next()
        .unwrap_or(datei)
        .trim_end_matches(".gab");
    let mut s = String::from("Duty");
    let mut gross = true;
    for ch in stem.chars() {
        if ch.is_ascii_alphanumeric() {
            s.push(if gross { ch.to_ascii_uppercase() } else { ch });
            gross = false;
        } else {
            gross = true;
        }
    }
    s
}

/// **The unit's obligation register, as a Lean 4 module.**
pub fn module(baum: &Programm, datei: &str) -> String {
    let entries = verdicts(baum);
    let proved = entries
        .iter()
        .filter(|(_, v)| matches!(v, LeanVerdict::Proved(_)))
        .count();
    let refused = entries.len() - proved;
    let name = module_name(datei);
    let mut s = String::new();
    s.push_str("/-  Written by `gabbro pflichten --lean`. Do not edit -- the source is the\n");
    s.push_str("    `.gab`, and a second register over the same thing is the very class this\n");
    s.push_str("    folder is written against.\n\n");
    s.push_str("    Every obligation of the register appears below, as a theorem or as a\n");
    s.push_str("    NAMED refusal. The line that has to add up:\n\n");
    s.push_str(&format!(
        "        @duty 1  {datei}  total {}  goals {proved}  refused {refused}\n",
        entries.len()
    ));
    s.push_str("\n    The meaning of a body is `Gabbro.Body`, written by hand and read by a\n");
    s.push_str("    person. What stands here is a DATUM of it -- this file defines nothing.\n\n");
    s.push_str("    ASSUMED, and visible because it is written down: two different carrier\n");
    s.push_str("    names are two different objects. That is the alias statement, and the\n");
    s.push_str("    alias passes carry it -- no line of this file does.\n-/\n\n");
    s.push_str("import Gabbro.Body\n\n");
    // **`autoImplicit` off, and it is a GUARD, not tidiness.** With it on, a name Lean does
    // not know becomes an implicitly bound variable of unknown type -- measured on the very
    // first run of this emitter: a hypothesis `istZahl (l.locals "p")` whose predicate was
    // not in scope elaborated to a BINDER instead of failing. *A misspelt hypothesis that
    // silently turns into an unconstrained variable is a theorem about nothing, and it
    // reads exactly like a proved one.*
    s.push_str("set_option autoImplicit false\n\nopen Gabbro.Body\n\n");
    s.push_str(&format!("namespace GabbroDuty.{name}\n\n"));

    s.push_str("/-! ## What is NOT here, and why -/\n\n");
    if refused == 0 {
        s.push_str("-- Nothing was refused in this unit.\n\n");
    } else {
        s.push_str("/-\n  These obligations of the register carry no theorem. A duty that\n");
        s.push_str("  vanishes is noticed; one that gets weaker is not -- so each stands\n");
        s.push_str("  here with its reason.\n\n");
        for r in LeanReason::ALL {
            let mine: Vec<(usize, &crate::pflichten::Pflicht)> = entries
                .iter()
                .enumerate()
                .filter(|(_, (_, v))| matches!(v, LeanVerdict::Refused(x) if *x == r))
                .map(|(i, (p, _))| (i, p))
                .collect();
            if mine.is_empty() {
                continue;
            }
            s.push_str(&format!("  {} ({}): {}\n", r.tag(), mine.len(), r.sentence()));
            for (i, p) in mine {
                s.push_str(&format!(
                    "    duty_{}  {}  {} :: {}\n",
                    i + 1,
                    p.art.marke(),
                    p.funktion,
                    p.gegenstand
                ));
            }
            s.push('\n');
        }
        s.push_str("-/\n\n");
    }

    if proved > 0 {
        s.push_str("/-! ## The obligations that stand closed -/\n\n");
    }
    for (p, v) in entries.iter() {
        let LeanVerdict::Proved(g) = v else { continue };
        s.push_str(&format!(
            "/-- {} -- `{}` :: `{}` -/\n",
            p.art.name(),
            p.funktion,
            p.gegenstand
        ));
        s.push_str(&format!("def body_{} : List Stmt :=\n  {}\n\n", g.name, g.body));
        s.push_str(&format!("def post_{} : Expr :=\n  {}\n\n", g.name, g.conclusion));
        s.push_str(&format!("theorem {} (s : State)\n", g.name));
        for (label, term, origin) in &g.hypotheses {
            s.push_str(&format!("    -- {origin}\n"));
            s.push_str(&format!("    ({label} : {term})\n"));
        }
        s.push_str(&format!(
            "    : \\<exists> s', finalState (exec body_{} s) = some s'\n",
            g.name
        ));
        s.push_str(&format!(
            "        \\<and> eval s' post_{} = some (.bool true) := by\n",
            g.name
        ));
        for z in &g.opening {
            s.push_str(z);
            s.push('\n');
        }
        let mut set = vec![
            format!("body_{}", g.name),
            format!("post_{}", g.name),
            "exec".into(),
            "step".into(),
            "eval".into(),
            "unop".into(),
            "binop".into(),
            "finalState".into(),
            "store".into(),
            "bindLocal".into(),
        ];
        set.extend(g.equations.iter().cloned());
        // **Every `rcases` splits the goal, so the whole chain is joined with `<;>`.** A
        // line standing on its own would serve only the first half -- and the other half,
        // in a file nobody builds, looks exactly like a proved one.
        let tactic = format!("simp [{}]", set.join(", "));
        if g.splits.is_empty() {
            s.push_str(&format!("  {tactic}\n\n"));
        } else {
            s.push_str(&format!("  {}\n", g.splits.join(" <;>\n    ")));
            s.push_str(&format!("    <;> {tactic}\n\n"));
        }
    }
    s.push_str(&format!("end GabbroDuty.{name}\n"));
    s.replace("\\<forall>", "∀")
        .replace("\\<exists>", "∃")
        .replace("\\<and>", "∧")
        .replace("\\<langle>", "⟨")
        .replace("\\<rangle>", "⟩")
}

// ===========================================================================================
// THE PROGRAM EXPORT -- a whole Gabbro program as a Lean 4 datum, so that a HAND-WRITTEN
// specification can be held against it.
//
// **This is a different artefact from `module` above, and the difference is the direction.**
// `gabbro pflichten --lean` takes the obligations Gabbro's own `spec fn`/`refines` pair
// states and writes them as theorems. This one takes NO specification at all: it writes the
// program -- bodies, contracts, the shape of every declared place -- and stops. *What is to
// be proved about it is then said in Lean, by a person, in a file this emitter never sees.*
//
// ## Why the specification is not in Gabbro
//
// A `spec fn` is a Gabbro expression, so it has Gabbro's expressiveness: no quantifier, no
// recursion, no induction. That is exactly the ceiling `maintains` runs into -- a table
// invariant is quantified over every slot, and this channel refuses all six of them. **A
// specification written in Lean has none of those limits.**
//
// And it costs no second register, which is the objection that would otherwise stand
// (`W7`): the program is stated once, here; the specification is stated once, in the user's
// file. *Nothing is said twice, and that is the whole difference from naming a Lean identifier
// inside the Gabbro source.*
//
// ## The one hazard, and it gets a guard
//
// A hand-written specification names places by STRING -- `.slot "Konten" k "offen"`. A typo
// there is a specification about a place that does not exist, and a theorem about a place
// that does not exist is vacuous rather than false. **Hence the export carries the place
// dictionary**, and `instrumente/pruefe-lean-programm.sh` holds every place a specification
// mentions against it.
// ===========================================================================================

/// One routine of the program, as a datum -- or a named refusal.
pub struct Routine {
    pub name: String,
    /// The body as a `Stmt` list term. `None` where the body is outside the fragment.
    pub body: Option<String>,
    pub refused: Option<LeanReason>,
    /// `(parameter, shape)` -- the shape is what the declaration gives, `None` where this
    /// channel has none.
    pub params: Vec<(String, Option<Shape>)>,
    /// The `requires` this channel can express, as `Expr` terms.
    pub pre: Vec<String>,
    /// The `requires` it cannot -- **dropped, not refused.**
    ///
    /// A precondition is a HYPOTHESIS. Dropping one can only make the theorem harder to
    /// prove, never wrong -- the same direction `refinement.rs` argues for its caller
    /// `requires`. *Refusing the whole routine over a `Held(L)` it cannot say would cost a
    /// body for a clause that carries nothing here.* They are listed by name.
    pub dropped: Vec<String>,
}

/// Every place the program declares, with the shape its declaration gives it.
fn dictionary(tab: &HashMap<String, Vec<(String, Option<Shape>)>>) -> Vec<(String, String, Shape)> {
    let mut out: Vec<(String, String, Shape)> = Vec::new();
    let mut names: Vec<&String> = tab.keys().collect();
    names.sort();
    for t in names {
        for (f, shape) in &tab[t] {
            if let Some(shape) = shape {
                out.push((t.clone(), f.clone(), *shape));
            }
        }
    }
    out
}

/// Every routine of the program, in declaration order.
pub fn routines(baum: &Programm) -> Vec<Routine> {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let tab = tables(baum, &u);
    let statics = static_carriers(baum, &tab);
    let mut out = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, module| {
        let ItemArt::Funktion(f) = &item.art else { return };
        if f.klasse == Some(FnKlasse::Spec) {
            return;
        }
        let params: Vec<(String, Option<Shape>)> = f
            .parameter
            .iter()
            .map(|p| (p.name.text.clone(), shape_of(&p.typ, &u, module)))
            .collect();
        let FnRumpf::Block(b) = &f.rumpf else {
            out.push(Routine {
                name: f.name.text.clone(),
                body: None,
                refused: Some(LeanReason::ForeignBody),
                params,
                pre: Vec::new(),
                dropped: Vec::new(),
            });
            return;
        };
        let mut c = Ctx {
            tables: &tab,
            carrier: carriers_of(f, &tab, &statics),
            locals: f.parameter.iter().map(|p| p.name.text.clone()).collect(),
            seen: Vec::new(),
            option_reads: Vec::new(),
        };
        let body = block_term(b, &mut c);
        let mut pre = Vec::new();
        let mut dropped = Vec::new();
        for (i, q) in f.requires.iter().enumerate() {
            match pred_term(q, &mut c) {
                Ok(t) => pre.push(t),
                Err(r) => dropped.push(format!("requires #{} ({})", i + 1, r.tag())),
            }
        }
        match body {
            Ok(t) => out.push(Routine {
                name: f.name.text.clone(),
                body: Some(t),
                refused: None,
                params,
                pre,
                dropped,
            }),
            Err(r) => out.push(Routine {
                name: f.name.text.clone(),
                body: None,
                refused: Some(r),
                params,
                pre,
                dropped,
            }),
        }
    });
    out
}

/// **The whole program, as a Lean 4 module.**
pub fn program(baum: &Programm, quellen: &[String]) -> String {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let tab = tables(baum, &u);
    let dict = dictionary(&tab);
    let rs = routines(baum);
    let carried = rs.iter().filter(|r| r.body.is_some()).count();
    let refused = rs.len() - carried;

    let mut s = String::new();
    s.push_str("/-  Written by `gabbro lean`. Do not edit -- the source is the `.gab` files,\n");
    s.push_str("    and a second register over the same thing is the very class this folder\n");
    s.push_str("    is written against.\n\n");
    s.push_str("    THIS FILE CARRIES NO SPECIFICATION. It carries the PROGRAM: every body\n");
    s.push_str("    this channel can express, every precondition it can say, and the shape of\n");
    s.push_str("    every declared place. What is to hold about it is said in Lean, by a\n");
    s.push_str("    person, in a file this emitter never sees.\n\n");
    s.push_str("    The line that has to add up:\n\n");
    s.push_str(&format!(
        "        @program 1  units {}  routines {}  bodies {carried}  refused {refused}  places {}\n",
        quellen.len(),
        rs.len(),
        dict.len()
    ));
    s.push_str("\n    Sources:\n");
    for q in quellen {
        s.push_str(&format!("        {q}\n"));
    }
    s.push_str("\n    ASSUMED, and visible because it is written down: two different carrier\n");
    s.push_str("    names are two different objects. That is the alias statement, and the\n");
    s.push_str("    alias passes carry it -- no line of this file does.\n-/\n\n");
    s.push_str("import Gabbro.Body\n\n");
    s.push_str("set_option autoImplicit false\n\nopen Gabbro.Body\n\n");
    s.push_str("namespace GabbroProgram\n\n");

    // ---- the place dictionary -----------------------------------------------------------
    s.push_str("/-! ## The declared places\n\n");
    s.push_str("    **A specification names a place by STRING, and a typo in that string is a\n");
    s.push_str("    specification about a place that does not exist** -- vacuous rather than\n");
    s.push_str("    false, and vacuous reads like proved. This list is what a specification is\n");
    s.push_str("    held against; `instrumente/pruefe-lean-programm.sh` does the holding.\n-/\n\n");
    s.push_str("/-- `(carrier, field, shape)` for every declared slot field. -/\n");
    s.push_str("def places : List (String \\<times> String \\<times> String) :=\n");
    if dict.is_empty() {
        s.push_str("  []\n\n");
    } else {
        s.push_str("  [ ");
        let items: Vec<String> = dict
            .iter()
            .map(|(t, f, sh)| format!("({}, {}, {})", quoted(t), quoted(f), quoted(sh.predicate())))
            .collect();
        s.push_str(&items.join("\n  , "));
        s.push_str("\n  ]\n\n");
    }

    // ---- the well-formed state ----------------------------------------------------------
    s.push_str("/-- **The well-formed state** -- that a slot field carries a value of its\n");
    s.push_str("    declared shape. It is a HYPOTHESIS and not a consequence (`Body.lean`, U2);\n");
    s.push_str("    it stands here once for the whole program instead of once per theorem. -/\n");
    s.push_str("def wellFormed (s : State) : Prop :=\n");
    if dict.is_empty() {
        s.push_str("  True\n\n");
    } else {
        let parts: Vec<String> = dict
            .iter()
            .map(|(t, f, sh)| {
                format!(
                    "(\\<forall> k, {} (s.world (.slot {} k {})))",
                    sh.predicate(),
                    quoted(t),
                    quoted(f)
                )
            })
            .collect();
        s.push_str(&format!("  {}\n\n", parts.join("\n  \\<and> ")));
    }

    // ---- the routines -------------------------------------------------------------------
    s.push_str("/-! ## The routines -/\n\n");
    for r in &rs {
        if let Some(reason) = r.refused {
            s.push_str(&format!(
                "-- REFUSED  {}  ({}): {}\n\n",
                r.name,
                reason.tag(),
                reason.sentence()
            ));
            continue;
        }
        let Some(body) = &r.body else { continue };
        s.push_str(&format!("/-- `{}` -- the body, statement by statement.", r.name));
        if !r.dropped.is_empty() {
            s.push_str(&format!(
                "\n\n    DROPPED from the precondition (a hypothesis fewer makes the goal harder,\n    never the proof wrong): {}",
                r.dropped.join(", ")
            ));
        }
        s.push_str(" -/\n");
        s.push_str(&format!("def {}_body : List Stmt :=\n  {}\n\n", r.name, body));
        s.push_str(&format!(
            "/-- `{}` -- what the caller grants: the declared parameter shapes and the\n    `requires` this channel can say. -/\n",
            r.name
        ));
        s.push_str(&format!("def {}_pre (s : State) : Prop :=\n", r.name));
        let mut parts: Vec<String> = r
            .params
            .iter()
            .filter_map(|(n, sh)| {
                sh.map(|sh| format!("{} (s.local' {})", sh.predicate(), quoted(n)))
            })
            .collect();
        for t in &r.pre {
            parts.push(format!("eval s {t} = some (.bool true)"));
        }
        if parts.is_empty() {
            s.push_str("  True\n\n");
        } else {
            s.push_str(&format!("  {}\n\n", parts.join("\n  \\<and> ")));
        }
    }

    s.push_str("/-! ## Proving something about this program\n\n");
    s.push_str("    A specification is a Lean predicate over `State`; the obligation is that a\n");
    s.push_str("    body establishes it. The tactic that unfolds the model is `gabbro_simp`,\n");
    s.push_str("    and it lives in `Gabbro.Body` -- not here, so that a change to the model\n");
    s.push_str("    reaches every proof through one place.\n\n");
    s.push_str("        theorem meets_spec (s : State) (k : Int)\n");
    s.push_str("            (wf : wellFormed s) (hk : s.local\' \"k\" = .int k)\n");
    s.push_str("            : \\<exists> s\', finalState (exec f_body s) = some s\'\n");
    s.push_str("                \\<and> mySpec k s\' := by\n");
    s.push_str("          gabbro_simp [mySpec, hk]\n-/\n\n");
    s.push_str("end GabbroProgram\n");
    s.replace("\\<forall>", "∀")
        .replace("\\<exists>", "∃")
        .replace("\\<and>", "∧")
        .replace("\\<times>", "×")
}
