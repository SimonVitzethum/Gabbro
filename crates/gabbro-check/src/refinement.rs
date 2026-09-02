//! **P6 -- the obligation register in the form a PROVER reads.**
//!
//! `gabbro pflichten` prints what a human still owes. This module prints **the same
//! register** as an Isabelle/HOL theory. *The relation is the one the ABI already has:
//! `gabbro zeugnis` wrote for people, `gabbro abi` writes the same statement as a `.gabi`,
//! and `gabbro pruefe --with` reads it back.*
//!
//! ## The form, and why it is Isabelle text and not a neutral format
//!
//! This folder has **one** prover: thirteen theories in `beweise/`, Isabelle2025-2, no AFP.
//! Both sides of the choice, because the choice is not obvious:
//!
//! | | |
//! |---|---|
//! | **for a neutral intermediate format** (SMT-LIB, or one of our own) | it would not bind P6 to a single prover, and a second prover would then cost no second emitter |
//! | **for Isabelle text** | the consumer EXISTS. A neutral format needs a reader, nobody has written one, and an emitter whose output nothing reads is the same gap one file further along. And a second register over one statement is the class this folder writes against -- see `abi.rs`, on why a `.gabi` is Gabbro and not a format of its own |
//!
//! **The second argument wins on the same ground the ABI won on:** a `.gabi` is valid Gabbro
//! because the parser already existed; a `.thy` is Isabelle because the prover already
//! exists. *When a second prover ever arrives, this emitter is the thing that gets rewritten
//! -- and that is a cost paid then, not a format invented now.*
//!
//! ## What it does NOT do, and this is the load-bearing half
//!
//! **This emitter writes a goal only where the goal is CLOSED** -- where every hypothesis it
//! needs is available without a semantics of a Gabbro body. Everywhere else it refuses **by
//! name**, and the refusal is counted.
//!
//! > *A generator that quietly emits a weakened contract is worse than no generator: the
//! > prover then says "proved" about something other than what the checker meant.* An
//! > obligation that DISAPPEARS is noticed; one that gets WEAKER is not. Hence: every
//! > obligation of the register appears here, either as a goal or as a named refusal, and
//! > `goals + refused = total` stands in the header of every file this writes.
//!
//! ## The model
//!
//! Integers are Isabelle `int` -- unbounded -- and every bound a declared Gabbro type gives
//! is written down as an explicit hypothesis. *`nat` would have been the quiet trap:
//! subtraction on `nat` truncates at zero, so a goal about `a - b` would be provable for a
//! reason the machine does not have.* Overflow freedom is not assumed here and not needed:
//! an argument may be a literal or a bare parameter, never a computed term.

use crate::pflichten::{CallerParam, Material, Pflicht};
use gabbro_syntax::ast::*;

/// **Why an obligation carries no goal.** Exhaustive, and every arm names a different thing
/// that is missing -- a single "not supported" would hide that the six reasons have six
/// different prices.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Reason {
    /// `Held(L)`. **This is not an Isabelle obligation at all** -- the lock passes carry it
    /// (`H005`, `H006`, `H012`, and since 2026-08-21 `H016`, all issued in `geteilt.rs`).
    /// Writing it as a goal would move a discharged obligation back onto the open pile.
    LockWitness,
    /// An `ensures` at a body Gabbro never sees. **An assumption, not a goal** -- and
    /// emitting it as an Isabelle axiom would be the worst weakening available, because an
    /// axiom about foreign code proves everything downstream of it.
    ForeignBody,
    /// **A promise at hardware Gabbro does not see** -- `reg … requires` and
    /// `transition … requires`, the two clauses `pflichten` books as `Art::Geraetezusage`.
    ///
    /// **It stood under [`Reason::ForeignBody`] until 2026-09-02, and that sentence was
    /// wrong twice over the same duty:** it says *"an `ensures`"* where the clause is a
    /// `requires`, and *"a body"* where there is no body at all. The Lean channel had
    /// carried its own `DevicePromise` since it was built; this one dispatched on
    /// `Material` alone, and a device promise carries `Material::Foreign` for the unrelated
    /// reason that Gabbro never sees the device either.
    ///
    /// > *Two channels over ONE register gave the same three duties two different reasons,
    /// > and only one of them was about the thing in front of it.* The register itself was
    /// > right both times -- what differed was the sentence a reader takes away.
    DevicePromise,
    /// The obligation speaks about the world AFTER a body ran, and this folder has **no
    /// Isabelle semantics of a Gabbro body**. `Table_Absenkung.thy` stops at exactly this
    /// line and hands the rest to "the language definition of C and no assumption of this
    /// proof".
    BodyEffect,
    /// The predicate uses a form this emitter has no Isabelle term for: a place with
    /// suffixes, a quantifier, `reaches`, a call, `aligned`, `sizeof`, `lenof`, a float, a
    /// bit operation, a division.
    NoTerm,
    /// The actual argument is neither a literal nor a parameter the body leaves alone.
    /// **The gate that keeps `requires k < 64` from being used after the body wrote `k`.**
    ArgumentNotStable,
}

impl Reason {
    pub fn tag(self) -> &'static str {
        match self {
            Reason::LockWitness => "lock-witness",
            Reason::ForeignBody => "foreign-body",
            Reason::DevicePromise => "device-promise",
            Reason::BodyEffect => "body-effect",
            Reason::NoTerm => "no-term",
            Reason::ArgumentNotStable => "argument-not-stable",
        }
    }
    pub fn sentence(self) -> &'static str {
        match self {
            Reason::LockWitness => {
                "`Held(…)` -- carried by the lock passes (H005/H006/H012/H016), not by a prover"
            }
            Reason::ForeignBody => {
                "an `ensures` at a body Gabbro never sees: an ASSUMPTION, not a goal"
            }
            Reason::DevicePromise => {
                "a promise at hardware Gabbro does not see: an ASSUMPTION, not a goal"
            }
            Reason::BodyEffect => {
                concat!(
                    "speaks about the world AFTER a body ran, and there is no ",
                    "Isabelle semantics of a Gabbro body"
                )
            }
            Reason::NoTerm => "the predicate uses a form this emitter has no Isabelle term for",
            Reason::ArgumentNotStable => {
                "the actual argument is neither a literal nor a parameter the body leaves alone"
            }
        }
    }
    /// **All of them, so a report cannot omit one by forgetting to ask.**
    pub const ALL: [Reason; 6] = [
        Reason::LockWitness,
        Reason::ForeignBody,
        Reason::DevicePromise,
        Reason::BodyEffect,
        Reason::NoTerm,
        Reason::ArgumentNotStable,
    ];
}

/// One closed Isabelle goal.
pub struct Goal {
    /// `duty_7` -- the number is the position in the register `gabbro pflichten` prints.
    pub name: String,
    /// The free integer variables, already renamed.
    pub fixes: Vec<String>,
    /// `(label, term, where it came from)`.
    pub assumptions: Vec<(String, String, String)>,
    pub conclusion: String,
}

/// What became of one obligation.
pub enum Verdict {
    Proved(Box<Goal>),
    Refused(Reason),
}

/// **The whole register, judged.** One entry per obligation of `pflichten::sammle`, in the
/// same order -- so `verdicts(b).len() == sammle(b).len()` holds by construction, and a
/// probe says so.
pub fn verdicts(baum: &Programm) -> Vec<(Pflicht, Verdict)> {
    crate::pflichten::sammle(baum)
        .into_iter()
        .enumerate()
        .map(|(i, p)| {
            let v = verdict(&p, i + 1);
            (p, v)
        })
        .collect()
}

fn verdict(p: &Pflicht, number: usize) -> Verdict {
    // **The KIND decides before the material does, for the device promise.** It carries
    // `Material::Foreign` because Gabbro never sees the device -- the same field an
    // `ensures` at a foreign body carries for a different reason -- and dispatching on the
    // material alone therefore printed the foreign-body sentence over a `requires` at a
    // register. See [`Reason::DevicePromise`].
    if p.art == crate::pflichten::Art::Geraetezusage {
        return Verdict::Refused(Reason::DevicePromise);
    }
    match &p.material {
        // **E and N.** Both need the effect of a body, and neither is closer than the other:
        // `maintains I` needs `I` before and after, `ensures P` needs `P` after.
        Material::Body => Verdict::Refused(Reason::BodyEffect),
        Material::Foreign => Verdict::Refused(Reason::ForeignBody),
        Material::Call(c) => {
            // **The predicate is translated FIRST, and an argument is resolved only where
            // the predicate asks for one.**
            //
            // The order is a measurement, not a convenience. `requires Held(KAPPEN)` names
            // no parameter at all -- resolving the arguments before looking would report it
            // as *"the argument is not stable"*, and that is the wrong sentence about a duty
            // the LOCK PASSES already carry. *A refusal filed under the wrong reason counts
            // a carried obligation as an unbuilt one, and the number then says the opposite
            // of what happened.* Measured over the corpus: twelve obligations moved from one
            // column to the other when this order was corrected.
            let at_call = Binding::Call {
                names: &c.callee_params,
                arguments: &c.arguments,
                caller: &c.caller_params,
            };
            let conclusion = match pred_term(&c.condition, &at_call) {
                Ok(t) => t,
                Err(g) => return Verdict::Refused(g),
            };
            // **The hypotheses, and only the ones that hold AT THE CALL SITE.**
            //
            // A caller parameter the body may have written contributes nothing -- neither
            // its type bounds nor the `requires` that mentions it. *That is the difference
            // between a goal and a weakened goal.*
            let own = Binding::Own(&c.caller_params);
            let mut assumptions = Vec::new();
            for cp in c.caller_params.iter().filter(|p| p.untouched) {
                let Some((low, high)) = cp.bounds else { continue };
                assumptions.push((
                    format!("t_{}", cp.name),
                    format!("{low} \\<le> {v} \\<and> {v} \\<le> {high}", v = var(&cp.name)),
                    format!("the declared type of `{}`", cp.name),
                ));
            }
            for (i, q) in c.caller_requires.iter().enumerate() {
                // A caller `requires` this emitter cannot express is DROPPED, not refused --
                // dropping a hypothesis can only make the goal harder, never the proof
                // wrong. *The direction matters and is the reason this arm is not an error.*
                if let Ok(t) = pred_term(q, &own) {
                    assumptions.push((
                        format!("r_{}", i + 1),
                        t,
                        format!("`{}` requires #{}", p.funktion, i + 1),
                    ));
                }
            }
            // **`fixes` names every variable that actually OCCURS, and it is computed
            // last** -- a parameter whose declared type gives no bound still stands in the
            // goal, and a free variable without a `fixes` line leaves its type to Isabelle's
            // inference. *Measured at `type Klein = u32 in 0 .. 9`: the goal said `g_b` and
            // the lemma fixed nothing.* The statement was still the right one -- a free
            // variable is universally quantified -- but its type was decided somewhere the
            // emitter could not see, and that is one place too many.
            let fixes: Vec<String> = c
                .caller_params
                .iter()
                .filter(|p| p.untouched)
                .map(|p| var(&p.name))
                .filter(|v| {
                    occurs_in(&conclusion, v) || assumptions.iter().any(|(_, t, _)| occurs_in(t, v))
                })
                .collect();
            Verdict::Proved(Box::new(Goal {
                name: format!("duty_{number}"),
                fixes,
                assumptions,
                conclusion,
            }))
        }
    }
}

/// **Does this term name that variable -- as a WORD, not as a substring?**
///
/// `g_a` is a prefix of `g_ab`, and a `contains` would have fixed the wrong one. *The same
/// two lines `abi.rs` needed for the same reason, and the same reason it is not a
/// `contains`.*
fn occurs_in(term: &str, v: &str) -> bool {
    let edge = |c: char| !(c.is_alphanumeric() || c == '_');
    term.match_indices(v).any(|(i, _)| {
        let before = term[..i].chars().next_back().is_none_or(edge);
        let after = term[i + v.len()..].chars().next().is_none_or(edge);
        before && after
    })
}

/// An Isabelle free variable for a Gabbro name. **Prefixed, so no Gabbro identifier can
/// collide with an Isabelle keyword or a HOL constant.**
fn var(name: &str) -> String {
    format!("g_{name}")
}

/// **What a NAME inside a predicate may stand for.** Two vocabularies, and nothing else is
/// speakable: a name outside them is a name this goal may not mention.
enum Binding<'a> {
    /// Inside a CALLEE's `requires`: its parameters, standing for the actual arguments.
    Call {
        names: &'a [String],
        arguments: &'a [Expr],
        caller: &'a [CallerParam],
    },
    /// Inside the CALLER's own `requires`: its parameters, standing for themselves.
    Own(&'a [CallerParam]),
}

impl Binding<'_> {
    fn get(&self, name: &str) -> Result<String, Reason> {
        match self {
            Binding::Call {
                names,
                arguments,
                caller,
            } => {
                let i = names.iter().position(|n| n == name).ok_or(Reason::NoTerm)?;
                let a = arguments.get(i).ok_or(Reason::ArgumentNotStable)?;
                argument_term(a, caller)
            }
            Binding::Own(caller) => match caller.iter().find(|p| p.name == name) {
                Some(p) if p.untouched => Ok(var(&p.name)),
                Some(_) => Err(Reason::ArgumentNotStable),
                None => Err(Reason::NoTerm),
            },
        }
    }
}

/// **The actual argument at a call site.** A literal, or a parameter the body leaves alone.
/// Nothing else -- not even `k + 1`.
///
/// *Why no arithmetic:* `k + 1` on a `u32` is bounded arithmetic in Gabbro and unbounded in
/// the model. M1 has already refused the overflow, so the two agree -- but that agreement
/// would be an assumption of this file about another pass, and it would not be visible in
/// the theory. **A refused goal costs a number; an invisible assumption costs the number's
/// meaning.**
fn argument_term(a: &Expr, caller: &[CallerParam]) -> Result<String, Reason> {
    match &a.art {
        ExprArt::Zahl(n) => Ok(format!("({n} :: int)")),
        ExprArt::Wahr => Ok("True".to_string()),
        ExprArt::Falsch => Ok("False".to_string()),
        ExprArt::Ort(o) if o.suffixe.is_empty() => {
            match caller.iter().find(|p| p.name == o.basis.text) {
                Some(p) if p.untouched => Ok(var(&p.name)),
                _ => Err(Reason::ArgumentNotStable),
            }
        }
        ExprArt::Ort(_)
        | ExprArt::Gleitkomma { .. }
        | ExprArt::FnWert(_)
        | ExprArt::Ruf(_)
        | ExprArt::Klammer(_)
        | ExprArt::Eingebaut(_)
        | ExprArt::Alt(_)
        | ExprArt::Ergebnis
        | ExprArt::Grund { .. }
        | ExprArt::Unaer(_, _)
        | ExprArt::Binaer(_, _, _) => Err(Reason::ArgumentNotStable),
    }
}

/// A predicate as an Isabelle term. **`binding` is the whole vocabulary** -- a name outside
/// it is a name this goal may not speak about.
fn pred_term(p: &Pred, binding: &Binding) -> Result<String, Reason> {
    match &p.art {
        PredArt::Vergleich(e) => expr_term(e, binding),
        PredArt::Klammer(q) => Ok(format!("({})", pred_term(q, binding)?)),
        PredArt::Nicht(q) => Ok(format!("\\<not> ({})", pred_term(q, binding)?)),
        PredArt::Und(a, b) => Ok(format!(
            "({}) \\<and> ({})",
            pred_term(a, binding)?,
            pred_term(b, binding)?
        )),
        PredArt::Oder(a, b) => Ok(format!(
            "({}) \\<or> ({})",
            pred_term(a, binding)?,
            pred_term(b, binding)?
        )),
        PredArt::Folgt(a, b) => Ok(format!(
            "({}) \\<longrightarrow> ({})",
            pred_term(a, binding)?,
            pred_term(b, binding)?
        )),
        // **The lock witness gets its OWN refusal**, because it is not a gap: the lock
        // passes discharge it. Folding it into `NoTerm` would count a carried obligation as
        // an open one.
        PredArt::Held { .. } => Err(Reason::LockWitness),
        PredArt::Quantor(_) | PredArt::Element(_, _) | PredArt::Erreicht { .. } => {
            Err(Reason::NoTerm)
        }
    }
}

/// An expression as an Isabelle term over `int`.
///
/// **The `match` has no catch-all**, and that is deliberate even though every unlisted arm
/// would refuse: a new expression form must be DECIDED here, not defaulted. *An emitter that
/// silently refuses a form nobody looked at reports a smaller number and calls it a
/// measurement.*
fn expr_term(e: &Expr, binding: &Binding) -> Result<String, Reason> {
    match &e.art {
        ExprArt::Zahl(n) => Ok(format!("({n} :: int)")),
        ExprArt::Wahr => Ok("True".to_string()),
        ExprArt::Falsch => Ok("False".to_string()),
        ExprArt::Klammer(x) => Ok(format!("({})", expr_term(x, binding)?)),
        // A place is a value only when it is a bare name this goal has a binding for.
        // **With a suffix it is a place in the WORLD**, and the world is what this emitter
        // has no model of.
        ExprArt::Ort(o) if o.suffixe.is_empty() => binding.get(&o.basis.text),
        ExprArt::Unaer(UnOp::Nicht, x) => Ok(format!("\\<not> ({})", expr_term(x, binding)?)),
        ExprArt::Unaer(UnOp::Negativ, x) => Ok(format!("- ({})", expr_term(x, binding)?)),
        // **`~` joins the bit operations below, and for the same two reasons.** The
        // complement over `n` bits is `2^n - 1 - x`, and this emitter's terms are over
        // `int` -- there is no width in them. `HOL-Library` would carry `NOT`; this theory
        // imports `Main`.
        ExprArt::Unaer(UnOp::BitNicht, _) => Err(Reason::NoTerm),
        ExprArt::Binaer(op, a, b) => {
            let z = match op {
                BinOp::Oder => "\\<or>",
                BinOp::Und => "\\<and>",
                BinOp::Gleich => "=",
                BinOp::Ungleich => "\\<noteq>",
                BinOp::Kleiner => "<",
                BinOp::KleinerGleich => "\\<le>",
                BinOp::Groesser => ">",
                BinOp::GroesserGleich => "\\<ge>",
                BinOp::Plus => "+",
                BinOp::Minus => "-",
                BinOp::Mal => "*",
                // **Bit operations and division are refused, and neither is an oversight.**
                // Isabelle's `div`/`mod` on `int` round toward minus infinity, C's truncate
                // toward zero -- a goal that mixed the two would be provable for a reason
                // the machine does not have. The bit operations live in `HOL-Library`, and
                // this theory imports `Main`.
                BinOp::BitUnd
                | BinOp::BitOder
                | BinOp::BitXor
                | BinOp::SchiebLinks
                | BinOp::SchiebRechts
                | BinOp::Geteilt
                | BinOp::Rest => return Err(Reason::NoTerm),
            };
            Ok(format!(
                "({}) {z} ({})",
                expr_term(a, binding)?,
                expr_term(b, binding)?
            ))
        }
        ExprArt::Ort(_)
        | ExprArt::Gleitkomma { .. }
        | ExprArt::FnWert(_)
        | ExprArt::Ruf(_)
        | ExprArt::Eingebaut(_)
        | ExprArt::Alt(_)
        | ExprArt::Ergebnis
        | ExprArt::Grund { .. } => Err(Reason::NoTerm),
    }
}

/// **The theory name of a unit.** Isabelle demands that it equal the file's stem, so the
/// stem is what this derives from.
pub fn theory_name(datei: &str) -> String {
    let stem = datei
        .rsplit('/')
        .next()
        .unwrap_or(datei)
        .trim_end_matches(".gab");
    let mut s = String::from("Gabbro_Duty_");
    for c in stem.chars() {
        s.push(if c.is_ascii_alphanumeric() { c } else { '_' });
    }
    s
}

/// **The unit's obligation register, as an Isabelle theory.**
pub fn theory(baum: &Programm, datei: &str) -> String {
    let entries = verdicts(baum);
    let proved = entries
        .iter()
        .filter(|(_, v)| matches!(v, Verdict::Proved(_)))
        .count();
    let refused = entries.len() - proved;
    let name = theory_name(datei);
    let mut s = String::new();
    s.push_str("(*  Written by `gabbro pflichten --isabelle`. Do not edit -- the source is\n");
    s.push_str("    the `.gab`, and a second register over the same thing is the very class\n");
    s.push_str("    this folder is written against.\n\n");
    s.push_str("    P6 -- the GENERATED refinement obligation. `gabbro pflichten` prints this\n");
    s.push_str("    same register for a human; this file is the same statement for a prover.\n\n");
    s.push_str("    Every obligation of the register appears below, as a goal or as a NAMED\n");
    s.push_str("    refusal. The line that has to add up:\n\n");
    s.push_str(&format!(
        "        @duty 1  {datei}  total {}  goals {proved}  refused {refused}\n",
        entries.len()
    ));
    s.push_str("\n    Integers are `int`, unbounded, and every bound a declared Gabbro type\n");
    s.push_str("    gives stands below as an explicit assumption.\n*)\n\n");
    s.push_str(&format!("theory {name}\n  imports Main\nbegin\n\n"));

    s.push_str("section \\<open>What is NOT here, and why\\<close>\n\n");
    if refused == 0 {
        s.push_str("text \\<open>Nothing was refused in this unit.\\<close>\n\n");
    } else {
        s.push_str("text \\<open>\n");
        s.push_str("  These obligations of the register carry no goal.");
        s.push_str(" \\<open>A duty that vanishes is\n");
        s.push_str("  noticed; one that gets weaker is not\\<close>");
        s.push_str(" -- so each stands here with its reason.\n\n");
        for r in Reason::ALL {
            let mine: Vec<(usize, &Pflicht)> = entries
                .iter()
                .enumerate()
                .filter(|(_, (_, v))| matches!(v, Verdict::Refused(x) if *x == r))
                .map(|(i, (p, _))| (i, p))
                .collect();
            if mine.is_empty() {
                continue;
            }
            s.push_str(&format!(
                "  {} ({}): {}\n",
                r.tag(),
                mine.len(),
                safe(r.sentence())
            ));
            for (i, p) in mine {
                s.push_str(&format!(
                    "    duty_{}  {}  {} :: {}\n",
                    i + 1,
                    p.art.marke(),
                    safe(&p.funktion),
                    safe(&p.gegenstand)
                ));
            }
            s.push('\n');
        }
        s.push_str("\\<close>\n\n");
    }

    if proved > 0 {
        s.push_str("section \\<open>The obligations that stand closed\\<close>\n\n");
    }
    for (p, v) in entries.iter() {
        let Verdict::Proved(g) = v else { continue };
        s.push_str(&format!(
            "text \\<open>{} -- \\<open>{}\\<close> :: \\<open>{}\\<close>\\<close>\n",
            p.art.name(),
            safe(&p.funktion),
            safe(&p.gegenstand)
        ));
        s.push_str(&format!("lemma {}:\n", g.name));
        if !g.fixes.is_empty() {
            s.push_str(&format!("  fixes {} :: int\n", g.fixes.join(" :: int and ")));
        }
        for (label, term, origin) in &g.assumptions {
            s.push_str(&format!(
                "  assumes {label}: \"{term}\"  \\<comment> \\<open>{}\\<close>\n",
                safe(origin)
            ));
        }
        s.push_str(&format!("  shows \"{}\"\n", g.conclusion));
        if g.assumptions.is_empty() {
            s.push_str("  by presburger\n\n");
        } else {
            s.push_str("  using assms by presburger\n\n");
        }
    }
    s.push_str("end\n");
    s
}

/// **Nothing that closes an Isabelle bracket may reach the inside of one.** Gabbro
/// identifiers are ASCII words, so this fires on nothing in today's corpus -- and that is
/// exactly why it is here rather than assumed.
fn safe(t: &str) -> String {
    t.replace('\\', "/").replace('*', "")
}
