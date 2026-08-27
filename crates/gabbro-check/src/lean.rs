//! **The BODY channel: a Gabbro body as a Lean 4 term, and its obligation as a theorem.**
//!
//! `refinement.rs` writes the same register as Isabelle text and refuses seventeen of its
//! obligations with one word: `body-effect` -- *"speaks about the world AFTER a body ran,
//! and there is no semantics of a Gabbro body"*. **This module is that semantics' other
//! half.** The meaning itself lives in `passlogik/Passlogik/Rumpf.lean`, written once by
//! hand; what stands here only translates a body into a datum of it.
//!
//! ## Why the meaning is not in this file
//!
//! A translator that both *defines* what a body means and *decides* whether the obligation
//! holds has no independent reader. `Rumpf.lean` is readable Lean with its own theorems, and
//! this file emits data against it. *That split is the whole reason a prover is worth
//! anything here* -- the same relation `lean4export` has to the Lean kernel.
//!
//! ## What the plumbing pays for, and it is the reason this file is short
//!
//! Nine of eleven classes are carried by the language, so the model underneath needs no
//! heap, no separation logic, no pointers and no concurrency (`Rumpf.lean`, header). The
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
    /// A statement kind outside the sequential core this channel covers.
    Statement,
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
            LeanReason::Statement => "statement-outside-core",
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
            LeanReason::Statement => {
                "the body uses a statement kind outside the sequential core"
            }
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
    pub const ALL: [LeanReason; 9] = [
        LeanReason::ForeignBody,
        LeanReason::Invariant,
        LeanReason::CallSite,
        LeanReason::DevicePromise,
        LeanReason::Statement,
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
    /// The body, as a `Rumpf.Anweisung` list term.
    pub rumpf: String,
    /// `(label, term, where it came from)` -- every hypothesis, read from a declaration.
    pub hypothesen: Vec<(String, String, String)>,
    /// The postcondition, as a `Rumpf.Ausdruck` that must evaluate to `true`.
    pub schluss: String,
    /// **The `obtain` lines the proof opens with.** A hypothesis `\exists n, l.lokal "p" =
    /// .z n` tells `simp` nothing until the witness is named; without these the goal stalls
    /// on an unreduced `match` over `l.lokal "p"`. *Measured on the first run of this
    /// emitter, and it is why the tactic is generated rather than fixed.*
    pub zerlegung: Vec<String>,
    /// The equation names those `obtain`s bind, for the `simp` set.
    pub gleichungen: Vec<String>,
    /// **The `rcases` fragments, and they are kept apart from `zerlegung` because they must
    /// be CHAINED.** An `rcases` splits the goal, and a plain next line applies only to the
    /// first half -- measured: the second split reported its own witness as an unknown
    /// identifier in every branch the first split had left behind.
    pub verzweigung: Vec<String>,
}

pub enum LeanVerdict {
    Proved(Box<LeanGoal>),
    Refused(LeanReason),
}

/// **What a table declares.** Field name to the shape its declaration gives it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Form {
    Zahl,
    Wahrheit,
    Wahl,
}

impl Form {
    fn praedikat(self) -> &'static str {
        match self {
            Form::Zahl => "istZahl",
            Form::Wahrheit => "istWahrheit",
            Form::Wahl => "istWahl",
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
fn form_von(t: &TypExpr, u: &crate::umgebung::Umgebung, modul: &str) -> Option<Form> {
    if let TypExpr::Index { optional, .. } = t {
        return Some(if *optional { Form::Wahl } else { Form::Zahl });
    }
    form_von_typ(&u.typ_von_ausdruck_decl(modul, t))
}

fn form_von_typ(t: &crate::typen::Typ) -> Option<Form> {
    use crate::typen::Typ;
    match t {
        Typ::Ganzzahl(_) => Some(Form::Zahl),
        Typ::Wahrheit => Some(Form::Wahrheit),
        Typ::Tabelle(_) => Some(Form::Zahl),
        // **An OPAQUE new type stops here and a transparent one does not.** Reading the
        // representation of an `opaque` is exactly the implicit conversion `D1` forbids;
        // a transparent one is a range with a name, and a name is not a wall.
        Typ::Benannt {
            undurchsichtig: false,
            unter,
            ..
        } => form_von_typ(unter),
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
    tabellen: &'a HashMap<String, Vec<(String, Option<Form>)>>,
    /// The declaring function's parameters: name to the table its type points at, if any.
    traeger: HashMap<String, String>,
    /// Parameter and `let` names -- these read from `lokal`, not from the world.
    lokal: Vec<String>,
    /// Collected while translating: `(carrier, field, form, origin)`, deduplicated.
    gesehen: Vec<(String, String, Form, String)>,
    /// **Every `(carrier, field, index-parameter)` read at an option-shaped field.**
    ///
    /// `istWahl` is a DISJUNCTION, and `simp` cannot open one: without the case split the
    /// goal stalls on an unreduced `match` over the field. *Measured on the first corpus
    /// run of this channel -- `aushaengen` was the one red module of sixty-eight, and the
    /// reason was this and nothing else.*
    wahlstellen: Vec<(String, String, String)>,
}

impl Ctx<'_> {
    /// **Which table does this base name stand for?** A bare table name stands for itself;
    /// a parameter stands for the table its pointer type names.
    fn tabelle_von(&self, basis: &str) -> Option<&String> {
        self.traeger.get(basis)
    }

    /// A place whose index is a bare parameter, at an option-shaped field: the proof will
    /// have to split on it.
    fn merke_wahl(&mut self, traeger: &str, feld: &str, form: Form, index: &Expr) {
        if form != Form::Wahl {
            return;
        }
        let ExprArt::Ort(o) = &index.art else { return };
        if !o.suffixe.is_empty() {
            return;
        }
        let p = o.basis.text.clone();
        if !self
            .wahlstellen
            .iter()
            .any(|(t, f, i)| t == traeger && f == feld && *i == p)
        {
            self.wahlstellen
                .push((traeger.to_string(), feld.to_string(), p));
        }
    }

    fn merke(&mut self, traeger: &str, feld: &str, f: Form, herkunft: &str) {
        if !self
            .gesehen
            .iter()
            .any(|(t, n, _, _)| t == traeger && n == feld)
        {
            self.gesehen.push((
                traeger.to_string(),
                feld.to_string(),
                f,
                herkunft.to_string(),
            ));
        }
    }
}

fn text(s: &str) -> String {
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
fn feldform(basis: &str, feld: &str, c: &Ctx) -> Result<(String, Form, String), LeanReason> {
    let tab = c.tabelle_von(basis).ok_or(LeanReason::Carrier)?.clone();
    let felder = c.tabellen.get(&tab).ok_or(LeanReason::Carrier)?;
    let (_, form) = felder
        .iter()
        .find(|(n, _)| n == feld)
        .ok_or(LeanReason::Carrier)?;
    let form = form.ok_or(LeanReason::FieldShape)?;
    Ok((basis.to_string(), form, tab))
}

/// A place, as a `Rumpf.Ausdruck`. **Two forms and nothing else:** a bare name, and
/// `carrier.slots[i].field`.
fn ort_term(o: &Ort, c: &mut Ctx) -> Result<String, LeanReason> {
    if o.suffixe.is_empty() {
        let n = &o.basis.text;
        return Ok(if c.lokal.iter().any(|l| l == n) {
            format!("(.name {})", text(n))
        } else {
            format!("(.stat {})", text(n))
        });
    }
    let [OrtSuffix::Feld(slots), OrtSuffix::Index(i), OrtSuffix::Feld(f)] = &o.suffixe[..] else {
        return Err(LeanReason::Carrier);
    };
    if slots.text != "slots" {
        return Err(LeanReason::Carrier);
    }
    let (basis, form, tab) = feldform(&o.basis.text, &f.text, c)?;
    let idx = expr_term(i, c)?;
    c.merke(&basis, &f.text, form, &format!("`{}` in `{}`", f.text, tab));
    c.merke_wahl(&basis, &f.text, form, i);
    Ok(format!(
        "(.platz {} {} {})",
        text(&basis),
        idx,
        text(&f.text)
    ))
}

/// An expression as a `Rumpf.Ausdruck`.
///
/// **The `match` has no catch-all**, and that is deliberate even though every unlisted arm
/// would refuse: a new expression form must be DECIDED here, not defaulted.
fn expr_term(e: &Expr, c: &mut Ctx) -> Result<String, LeanReason> {
    match &e.art {
        ExprArt::Zahl(n) => Ok(format!("(.lit (.z {n}))")),
        ExprArt::Wahr => Ok("(.lit (.b true))".into()),
        ExprArt::Falsch => Ok("(.lit (.b false))".into()),
        ExprArt::Klammer(x) => expr_term(x, c),
        ExprArt::Ort(o) => ort_term(o, c),
        ExprArt::Unaer(UnOp::Nicht, x) => Ok(format!("(.un .nicht {})", expr_term(x, c)?)),
        ExprArt::Unaer(UnOp::Negativ, x) => Ok(format!("(.un .negativ {})", expr_term(x, c)?)),
        ExprArt::Binaer(op, a, b) => {
            let z = match op {
                BinOp::Plus => "plus",
                BinOp::Minus => "minus",
                BinOp::Mal => "mal",
                BinOp::Gleich => "gleich",
                BinOp::Ungleich => "ungleich",
                BinOp::Kleiner => "kleiner",
                BinOp::KleinerGleich => "kleinergleich",
                BinOp::Groesser => "groesser",
                BinOp::GroesserGleich => "groessergleich",
                BinOp::Und => "und",
                BinOp::Oder => "oder",
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
            Some(n) if n == "None" && r.argumente.is_empty() => Ok("(.lit .nichts)".into()),
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

/// A predicate as a `Rumpf.Ausdruck` that must evaluate to `true`.
fn pred_term(p: &Pred, c: &mut Ctx) -> Result<String, LeanReason> {
    match &p.art {
        PredArt::Vergleich(e) => expr_term(e, c),
        PredArt::Klammer(q) => pred_term(q, c),
        PredArt::Nicht(q) => Ok(format!("(.un .nicht {})", pred_term(q, c)?)),
        PredArt::Und(a, b) => Ok(format!(
            "(.bin .und {} {})",
            pred_term(a, c)?,
            pred_term(b, c)?
        )),
        PredArt::Oder(a, b) => Ok(format!(
            "(.bin .oder {} {})",
            pred_term(a, c)?,
            pred_term(b, c)?
        )),
        // `a -> b` is `!a || b`. **Not a shortcut:** `Wert` has no implication, and adding
        // one to the model for a form that desugars exactly would be a second way to say
        // one thing.
        PredArt::Folgt(a, b) => Ok(format!(
            "(.bin .oder (.un .nicht {}) {})",
            pred_term(a, c)?,
            pred_term(b, c)?
        )),
        PredArt::Held { .. } | PredArt::Quantor(_) | PredArt::Element(_, _)
        | PredArt::Erreicht { .. } => Err(LeanReason::Expression),
    }
}

/// A block as a `Rumpf.Anweisung` list term.
fn block_term(b: &Block, c: &mut Ctx) -> Result<String, LeanReason> {
    let tiefe = c.lokal.len();
    let mut teile = Vec::new();
    for s in &b.anweisungen {
        teile.push(stmt_term(s, c)?);
    }
    // A `let` name leaves scope with its block -- the model binds by name, so a name that
    // outlived its block would silently shadow one further out.
    c.lokal.truncate(tiefe);
    Ok(format!("[{}]", teile.join(", ")))
}

fn stmt_term(s: &Stmt, c: &mut Ctx) -> Result<String, LeanReason> {
    match &s.art {
        StmtArt::Let(l) => {
            let w = expr_term(&l.wert, c)?;
            c.lokal.push(l.name.text.clone());
            Ok(format!("(.binde {} {})", text(&l.name.text), w))
        }
        StmtArt::Zuweisung(z) => {
            if z.op != ZuwOp::Setzt {
                // `+=` is `x = x + e` and would translate -- but the two are not the same
                // statement in Gabbro's overflow accounting, and this channel does not get
                // to decide that. Refused by name.
                return Err(LeanReason::Statement);
            }
            let w = expr_term(&z.wert, c)?;
            if z.ziel.suffixe.is_empty() {
                return Ok(format!("(.zuwStat {} {})", text(&z.ziel.basis.text), w));
            }
            let [OrtSuffix::Feld(slots), OrtSuffix::Index(i), OrtSuffix::Feld(f)] =
                &z.ziel.suffixe[..]
            else {
                return Err(LeanReason::Carrier);
            };
            if slots.text != "slots" {
                return Err(LeanReason::Carrier);
            }
            let (basis, form, tab) = feldform(&z.ziel.basis.text, &f.text, c)?;
            let idx = expr_term(i, c)?;
            c.merke(&basis, &f.text, form, &format!("`{}` in `{}`", f.text, tab));
            Ok(format!(
                "(.zuw {} {} {} {})",
                text(&basis),
                idx,
                text(&f.text),
                w
            ))
        }
        StmtArt::Wenn(w) => {
            // An `else if` chain folds from the back: one conditional statement per branch.
            let mut sonst = match &w.sonst {
                Some(b) => block_term(b, c)?,
                None => "[]".to_string(),
            };
            for (bed, blk) in w.zweige.iter().rev() {
                let b = expr_term(bed, c)?;
                let d = block_term(blk, c)?;
                sonst = format!("[(.wenn {b} {d} {sonst})]");
            }
            // The fold produced a one-element list; a statement is wanted, so unwrap it.
            Ok(sonst
                .strip_prefix('[')
                .and_then(|s| s.strip_suffix(']'))
                .unwrap_or(&sonst)
                .to_string())
        }
        StmtArt::Match(m) => {
            // **Exactly the option shape, and nothing else.** A `match` over a declared sum
            // type would need a value constructor per variant; refusing here is a number,
            // guessing would be a meaning.
            let g = expr_term(&m.gegenstand, c)?;
            let mut etwas = None;
            let mut nichts = None;
            for z in &m.zweige {
                match (z.variante.text.as_str(), &z.binder) {
                    ("Some", Some(b)) => {
                        let tiefe = c.lokal.len();
                        c.lokal.push(b.text.clone());
                        let blk = block_term(&z.rumpf, c)?;
                        c.lokal.truncate(tiefe);
                        etwas = Some((b.text.clone(), blk));
                    }
                    ("None", None) => nichts = Some(block_term(&z.rumpf, c)?),
                    _ => return Err(LeanReason::Statement),
                }
            }
            match (etwas, nichts) {
                (Some((b, be)), Some(bk)) => {
                    Ok(format!("(.aufOption {g} {} {be} {bk})", text(&b)))
                }
                _ => Err(LeanReason::Statement),
            }
        }
        StmtArt::Return(None) => Ok("(.rueckgabe none)".into()),
        StmtArt::Return(Some(e)) => Ok(format!("(.rueckgabe (some {}))", expr_term(e, c)?)),
        // Everything else is refused BY NAME. `Ruf` and `LetSonst` belong to the sequential
        // core and are the next two to build: a call is compositional over the CONTRACT of
        // the callee, never over its body, and that gate is not built.
        StmtArt::LetSonst(_)
        | StmtArt::Ruf(_)
        | StmtArt::Schleife(_)
        | StmtArt::Bricht(_)
        | StmtArt::Narrow(_)
        | StmtArt::Sperrt(_)
        | StmtArt::Observiert(_)
        | StmtArt::Leave(_)
        | StmtArt::Next(_)
        | StmtArt::Publish(_)
        | StmtArt::AwaitLoad(_)
        | StmtArt::Exchange(_) => Err(LeanReason::Statement),
    }
}

/// **Every table of the unit, with the shape its declaration gives each slot field.**
///
/// A field whose type has no shape is kept with `None` and NOT dropped -- a dropped field
/// looks like an undeclared one, and the refusal would then name the wrong thing.
fn tabellen(
    baum: &Programm,
    u: &crate::umgebung::Umgebung,
) -> HashMap<String, Vec<(String, Option<Form>)>> {
    let mut aus = HashMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Tabelle(tb) = &item.art else { return };
        let mut felder = Vec::new();
        if let Some(s) = &tb.slot {
            for f in &s.felder {
                let form = match &f.typ {
                    SlotTyp::Typ(te) => form_von(te, u, modul),
                    SlotTyp::Wrapping(_) => None,
                };
                felder.push((f.name.text.clone(), form));
            }
        }
        aus.insert(tb.name.text.clone(), felder);
    });
    aus
}

/// **Which base name stands for which table**, for one function.
fn traeger_von(
    f: &FnDecl,
    tab: &HashMap<String, Vec<(String, Option<Form>)>>,
) -> HashMap<String, String> {
    let mut aus = HashMap::new();
    // A table name stands for itself.
    for name in tab.keys() {
        aus.insert(name.clone(), name.clone());
    }
    // A parameter stands for the table its pointer type names.
    for p in &f.parameter {
        let ziel = match &p.typ {
            TypExpr::Zeiger(z) => &z.ziel,
            t => t,
        };
        if let TypExpr::Pfad(pf) = ziel {
            if let Some(last) = pf.teile.last() {
                if tab.contains_key(&last.text) {
                    aus.insert(p.name.text.clone(), last.text.clone());
                }
            }
        }
    }
    aus
}

/// **The one function this module exists for**: a body obligation as a Lean goal, or a
/// named refusal.
fn urteil(
    f: &FnDecl,
    nachher: &Pred,
    u: &crate::umgebung::Umgebung,
    modul: &str,
    tab: &HashMap<String, Vec<(String, Option<Form>)>>,
    nummer: usize,
) -> LeanVerdict {
    let FnRumpf::Block(b) = &f.rumpf else {
        return LeanVerdict::Refused(LeanReason::ForeignBody);
    };
    let mut c = Ctx {
        tabellen: tab,
        traeger: traeger_von(f, tab),
        lokal: f.parameter.iter().map(|p| p.name.text.clone()).collect(),
        gesehen: Vec::new(),
        wahlstellen: Vec::new(),
    };
    let rumpf = match block_term(b, &mut c) {
        Ok(t) => t,
        Err(r) => return LeanVerdict::Refused(r),
    };
    let schluss = match pred_term(nachher, &mut c) {
        Ok(t) => t,
        Err(r) => return LeanVerdict::Refused(r),
    };
    // **The hypotheses, and every one of them read from a declaration.**
    let mut hypothesen = Vec::new();
    let mut zerlegung = Vec::new();
    let mut verzweigung: Vec<String> = Vec::new();
    let mut gleichungen = Vec::new();
    for p in &f.parameter {
        if let Some(form) = form_von(&p.typ, u, modul) {
            let n = &p.name.text;
            hypothesen.push((
                format!("p_{n}"),
                format!("{} (l.lokal {})", form.praedikat(), text(n)),
                format!("the declared type of `{n}`"),
            ));
            // `istWahl` is a DISJUNCTION, not an existential -- there is no single witness
            // to name, so it stays whole and the goal that needs it is refused rather than
            // half-opened.
            if form != Form::Wahl {
                zerlegung.push(format!("  obtain \\<langle>w_{n}, e_{n}\\<rangle> := p_{n}"));
                gleichungen.push(format!("e_{n}"));
            }
        }
    }
    for (traeger, feld, form, herkunft) in &c.gesehen {
        hypothesen.push((
            format!("f_{traeger}_{feld}"),
            format!(
                "\\<forall> k, {} (l.welt (.slot {} k {}))",
                form.praedikat(),
                text(traeger),
                text(feld)
            ),
            herkunft.clone(),
        ));
    }
    // **The case split, one per option-shaped field read at a parameter index.**
    //
    // The split is emitted only where the WITNESS exists -- a parameter whose declared type
    // gave a shape and was therefore opened above. Without the witness there is no `w_p` to
    // apply the hypothesis to, and a split written anyway would not elaborate.
    for (traeger, feld, index) in &c.wahlstellen {
        if !gleichungen.iter().any(|g| *g == format!("e_{index}")) {
            continue;
        }
        let h = format!("h_{traeger}_{feld}_{index}");
        verzweigung.push(format!(
            "rcases f_{traeger}_{feld} w_{index} with {h} | \\<langle>m_{traeger}_{feld}_{index}, {h}\\<rangle>"
        ));
        gleichungen.push(h);
    }
    LeanVerdict::Proved(Box::new(LeanGoal {
        name: format!("duty_{nummer}"),
        rumpf,
        hypothesen,
        schluss,
        zerlegung,
        gleichungen,
        verzweigung,
    }))
}

/// **The whole register, judged for the Lean channel.** One entry per obligation of
/// `pflichten::sammle`, in the same order -- so the two channels can be held against each
/// other, obligation by obligation.
pub fn verdicts(baum: &Programm) -> Vec<(crate::pflichten::Pflicht, LeanVerdict)> {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let tab = tabellen(baum, &u);
    // The module a function is declared in travels with it: `typ_von_ausdruck_decl` is
    // module-aware, and asking it from the wrong module answers about the wrong type.
    let mut fns: HashMap<String, (String, FnDecl)> = HashMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Funktion(f) = &item.art {
            fns.insert(f.name.text.clone(), (modul.to_string(), f.clone()));
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
                    Some((modul, f)) => {
                        // `ensures #k` -- the index is in the register's own wording.
                        let k = p
                            .gegenstand
                            .rsplit('#')
                            .next()
                            .and_then(|s| s.parse::<usize>().ok())
                            .unwrap_or(0);
                        match f.ensures.get(k.wrapping_sub(1)) {
                            Some(q) => urteil(f, q, &u, modul, &tab, n),
                            None => LeanVerdict::Refused(LeanReason::Expression),
                        }
                    }
                    None => LeanVerdict::Refused(LeanReason::Expression),
                },
                crate::pflichten::Art::Verfeinerung => match fns.get(&p.funktion) {
                    Some((modul, f)) => match spezifikation(f, &fns) {
                        Ok(q) => urteil(f, &q, &u, modul, &tab, n),
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
fn spezifikation(
    f: &FnDecl,
    fns: &HashMap<String, (String, FnDecl)>,
) -> Result<Pred, LeanReason> {
    let pfad = f.verfeinert.as_ref().ok_or(LeanReason::SpecShape)?;
    let name = pfad.teile.last().ok_or(LeanReason::SpecShape)?;
    let (_, spec) = fns.get(&name.text).ok_or(LeanReason::SpecShape)?;
    let FnRumpf::Pred(p) = &spec.rumpf else {
        return Err(LeanReason::SpecShape);
    };
    let paare: Vec<(String, String)> = spec
        .parameter
        .iter()
        .zip(f.parameter.iter())
        .map(|(s, i)| (s.name.text.clone(), i.name.text.clone()))
        .collect();
    Ok(umbenannt_pred(p, &paare))
}

fn umbenannt_pred(p: &Pred, paare: &[(String, String)]) -> Pred {
    let art = match &p.art {
        PredArt::Vergleich(e) => PredArt::Vergleich(umbenannt_expr(e, paare)),
        PredArt::Klammer(q) => PredArt::Klammer(Box::new(umbenannt_pred(q, paare))),
        PredArt::Nicht(q) => PredArt::Nicht(Box::new(umbenannt_pred(q, paare))),
        PredArt::Und(a, b) => PredArt::Und(
            Box::new(umbenannt_pred(a, paare)),
            Box::new(umbenannt_pred(b, paare)),
        ),
        PredArt::Oder(a, b) => PredArt::Oder(
            Box::new(umbenannt_pred(a, paare)),
            Box::new(umbenannt_pred(b, paare)),
        ),
        PredArt::Folgt(a, b) => PredArt::Folgt(
            Box::new(umbenannt_pred(a, paare)),
            Box::new(umbenannt_pred(b, paare)),
        ),
        other => other.clone(),
    };
    Pred { art, ..p.clone() }
}

fn umbenannt_expr(e: &Expr, paare: &[(String, String)]) -> Expr {
    let art = match &e.art {
        ExprArt::Ort(o) => {
            let mut o = o.clone();
            if let Some((_, neu)) = paare.iter().find(|(alt, _)| *alt == o.basis.text) {
                o.basis.text = neu.clone();
            }
            for s in &mut o.suffixe {
                if let OrtSuffix::Index(i) = s {
                    *i = umbenannt_expr(i, paare);
                }
            }
            ExprArt::Ort(o)
        }
        ExprArt::Klammer(x) => ExprArt::Klammer(Box::new(umbenannt_expr(x, paare))),
        ExprArt::Unaer(op, x) => ExprArt::Unaer(*op, Box::new(umbenannt_expr(x, paare))),
        ExprArt::Binaer(op, a, b) => ExprArt::Binaer(
            *op,
            Box::new(umbenannt_expr(a, paare)),
            Box::new(umbenannt_expr(b, paare)),
        ),
        other => other.clone(),
    };
    Expr { art, ..e.clone() }
}

/// **The module name of a unit.** Lean demands that it match the file, so the stem is what
/// this derives from.
pub fn modul_name(datei: &str) -> String {
    let stem = datei
        .rsplit('/')
        .next()
        .unwrap_or(datei)
        .trim_end_matches(".gab");
    let mut s = String::from("Pflicht");
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
pub fn modul(baum: &Programm, datei: &str) -> String {
    let entries = verdicts(baum);
    let proved = entries
        .iter()
        .filter(|(_, v)| matches!(v, LeanVerdict::Proved(_)))
        .count();
    let refused = entries.len() - proved;
    let name = modul_name(datei);
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
    s.push_str("\n    The meaning of a body is `Passlogik.Rumpf`, written by hand and read by a\n");
    s.push_str("    person. What stands here is a DATUM of it -- this file defines nothing.\n\n");
    s.push_str("    ASSUMED, and visible because it is written down: two different carrier\n");
    s.push_str("    names are two different objects. That is the alias statement, and the\n");
    s.push_str("    alias passes carry it -- no line of this file does.\n-/\n\n");
    s.push_str("import Passlogik.Rumpf\n\n");
    // **`autoImplicit` off, and it is a GUARD, not tidiness.** With it on, a name Lean does
    // not know becomes an implicitly bound variable of unknown type -- measured on the very
    // first run of this emitter: a hypothesis `istZahl (l.lokal "p")` whose predicate was
    // not in scope elaborated to a BINDER instead of failing. *A misspelt hypothesis that
    // silently turns into an unconstrained variable is a theorem about nothing, and it
    // reads exactly like a proved one.*
    s.push_str("set_option autoImplicit false\n\nopen Passlogik.Rumpf\n\n");
    s.push_str(&format!("namespace GabbroPflicht.{name}\n\n"));

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
        s.push_str(&format!("def rumpf_{} : List Anweisung :=\n  {}\n\n", g.name, g.rumpf));
        s.push_str(&format!("def nach_{} : Ausdruck :=\n  {}\n\n", g.name, g.schluss));
        s.push_str(&format!("theorem {} (l : Lage)\n", g.name));
        for (label, term, herkunft) in &g.hypothesen {
            s.push_str(&format!("    -- {herkunft}\n"));
            s.push_str(&format!("    ({label} : {term})\n"));
        }
        s.push_str(&format!(
            "    : \\<exists> l', endLage (fuehre rumpf_{} l) = some l'\n",
            g.name
        ));
        s.push_str(&format!(
            "        \\<and> werte l' nach_{} = some (.b true) := by\n",
            g.name
        ));
        for z in &g.zerlegung {
            s.push_str(z);
            s.push('\n');
        }
        let mut menge = vec![
            format!("rumpf_{}", g.name),
            format!("nach_{}", g.name),
            "fuehre".into(),
            "schritt".into(),
            "werte".into(),
            "unwert".into(),
            "binwert".into(),
            "endLage".into(),
            "setze".into(),
            "binde".into(),
        ];
        menge.extend(g.gleichungen.iter().cloned());
        // **Every `rcases` splits the goal, so the whole chain is joined with `<;>`.** A
        // line standing on its own would serve only the first half -- and the other half,
        // in a file nobody builds, looks exactly like a proved one.
        let tat = format!("simp [{}]", menge.join(", "));
        if g.verzweigung.is_empty() {
            s.push_str(&format!("  {tat}\n\n"));
        } else {
            s.push_str(&format!("  {}\n", g.verzweigung.join(" <;>\n    ")));
            s.push_str(&format!("    <;> {tat}\n\n"));
        }
    }
    s.push_str(&format!("end GabbroPflicht.{name}\n"));
    s.replace("\\<forall>", "∀")
        .replace("\\<exists>", "∃")
        .replace("\\<and>", "∧")
        .replace("\\<langle>", "⟨")
        .replace("\\<rangle>", "⟩")
}
