//! Const certificate from the source (lane 121).
//!
//! A `const fn` body in the accepted single-expression fragment is printed
//! to a Lean `Nat` function, and the evaluated table becomes a `List.all`
//! certificate over `zipIdx` with that function -- so Lean checks the values
//! against the translated SOURCE, not a hand-written formula. The assembly
//! into a certificate file lives in `konstanten::certificate`, which takes
//! the translated definition line from here and never a hand equation.
//!
//! Fragment: integer literals, `wahr`/`falsch`, the parameter, other named
//! consts, arithmetic and bit operators, comparisons and logic (as `0`/`1`),
//! and calls of other const fns. Refused (`None`): negation and `~` (no
//! `Nat` form; `lean.rs` refuses `~` for the same width reason), the
//! wrap/saturate operators (the checker does not fold them either),
//! division-shaped values the checker cannot evaluate (no table then, and
//! hence no certificate), floats, counts, built-ins and indirect calls.

use gabbro_syntax::ast::{BinOp, CallTarget, Expr, ExprArt, Ident, Pfad, UnOp};
use std::collections::HashMap;

/// Render one const-fragment expression to Lean `Nat` syntax.
/// `param` is the Lean binder of the function parameter; any other bare
/// name is a named const printed as-is. `funktionen` maps a called const
/// fn's short Gabbro name to its Lean function name.
pub fn ausdruck_lean(
    e: &Expr,
    param: &str,
    funktionen: &HashMap<String, String>,
) -> Option<String> {
    match &crate::ohne_klammern(e).art {
        ExprArt::Zahl(n) => Some(format!("{n}")),
        ExprArt::Wahr => Some("1".to_string()),
        ExprArt::Falsch => Some("0".to_string()),
        ExprArt::Ort(o) if o.suffixe.is_empty() => {
            if o.basis.text == param {
                Some(param.to_string())
            } else {
                Some(o.basis.text.clone())
            }
        }
        ExprArt::Unaer(UnOp::Nicht, x) => {
            Some(format!("(if {} == 0 then 1 else 0)", operand_lean(x, param, funktionen)?))
        }
        ExprArt::Unaer(_, _) => None,
        ExprArt::Binaer(op, a, b) => binaer_lean(*op, a, b, param, funktionen),
        ExprArt::Ruf(r) => {
            let pfad = match &r.ziel {
                CallTarget::Path(p) => p,
                CallTarget::Place(_) => return None,
            };
            let kurz = pfad.teile.last()?.text.clone();
            let lean = funktionen.get(&kurz)?.clone();
            let mut teile = vec![lean];
            for arg in &r.argumente {
                teile.push(operand_lean(arg, param, funktionen)?);
            }
            Some(teile.join(" "))
        }
        _ => None,
    }
}

/// One operand inside an operator or call: compound operands take
/// parentheses, atoms and nullary names stand bare (application binds
/// tightest, so a call with arguments needs parentheses as an operand).
fn operand_lean(
    e: &Expr,
    param: &str,
    funktionen: &HashMap<String, String>,
) -> Option<String> {
    let text = ausdruck_lean(e, param, funktionen)?;
    match &crate::ohne_klammern(e).art {
        ExprArt::Binaer(_, _, _) | ExprArt::Unaer(_, _) => Some(format!("({text})")),
        ExprArt::Ruf(r) if !r.argumente.is_empty() => Some(format!("({text})")),
        _ => Some(text),
    }
}

/// One binary operator in Lean `Nat` syntax. Comparisons and logic yield
/// `0`/`1` exactly as the checker's constant folder does.
fn binaer_lean(
    op: BinOp,
    a: &Expr,
    b: &Expr,
    param: &str,
    funktionen: &HashMap<String, String>,
) -> Option<String> {
    let x = operand_lean(a, param, funktionen)?;
    let y = operand_lean(b, param, funktionen)?;
    let text = match op {
        BinOp::Plus => format!("{x} + {y}"),
        BinOp::Minus => format!("{x} - {y}"),
        BinOp::Mal => format!("{x} * {y}"),
        BinOp::Geteilt => format!("{x} / {y}"),
        BinOp::Rest => format!("{x} % {y}"),
        BinOp::BitUnd => format!("Nat.land {x} {y}"),
        BinOp::BitOder => format!("Nat.lor {x} {y}"),
        BinOp::BitXor => format!("Nat.xor {x} {y}"),
        BinOp::SchiebLinks => format!("Nat.shiftLeft {x} {y}"),
        BinOp::SchiebRechts => format!("Nat.shiftRight {x} {y}"),
        BinOp::Gleich => format!("(if {x} == {y} then 1 else 0)"),
        BinOp::Ungleich => format!("(if !({x} == {y}) then 1 else 0)"),
        BinOp::Kleiner => format!("(if {x} < {y} then 1 else 0)"),
        BinOp::KleinerGleich => format!("(if {x} <= {y} then 1 else 0)"),
        BinOp::Groesser => format!("(if {x} > {y} then 1 else 0)"),
        BinOp::GroesserGleich => format!("(if {x} >= {y} then 1 else 0)"),
        BinOp::Und => format!("(if {x} == 0 || {y} == 0 then 0 else 1)"),
        BinOp::Oder => format!("(if {x} == 0 && {y} == 0 then 0 else 1)"),
        BinOp::PlusWrap
        | BinOp::MinusWrap
        | BinOp::MalWrap
        | BinOp::SchiebLinksWrap
        | BinOp::PlusSat => return None,
    };
    Some(text)
}

/// The Lean definition line of one const fn: `def name (param : Nat) : Nat`.
pub fn funktion_lean(
    lean_name: &str,
    param: &str,
    rumpf: &Expr,
    funktionen: &HashMap<String, String>,
) -> Option<String> {
    Some(format!(
        "def {lean_name} ({param} : Nat) : Nat := {}",
        ausdruck_lean(rumpf, param, funktionen)?
    ))
}

/// The evaluated table as a Lean `List Nat` literal.
pub fn tabelle_lean(werte: &[u128]) -> String {
    let zahlen: Vec<String> = werte.iter().map(|v| format!("{v}")).collect();
    format!("[{}]", zahlen.join(", "))
}

/// A call expression `name(arg0, arg1, ...)` for probing the checker's own
/// constant folder (`Umgebung::konst_wert`) at concrete arguments.
pub fn ruf_ausdruck(name: &str, args: &[u128]) -> Expr {
    use gabbro_syntax::span::Span;
    let span = Span::neu(0, 0);
    Expr {
        art: ExprArt::Ruf(gabbro_syntax::ast::Ruf {
            ziel: CallTarget::Path(Pfad {
                teile: vec![Ident { text: name.to_string(), span }],
                span,
            }),
            argumente: args
                .iter()
                .map(|v| Expr { art: ExprArt::Zahl(*v), span })
                .collect(),
            marken: vec![],
            span,
        }),
        span,
    }
}

/// Evaluate `name(0) .. name(n-1)` with the checker's own constant folder.
/// `None` where the checker bails (and then there is no table to certify).
pub fn werte_tabelle(
    u: &crate::umgebung::Umgebung,
    modul: &str,
    name: &str,
    n: u128,
) -> Option<Vec<u128>> {
    let mut werte = Vec::new();
    for k in 0..n {
        let ruf = ruf_ausdruck(name, &[k]);
        let w = u.konst_wert(modul, &ruf)?;
        werte.push(u128::try_from(w).ok()?);
    }
    Some(werte)
}
