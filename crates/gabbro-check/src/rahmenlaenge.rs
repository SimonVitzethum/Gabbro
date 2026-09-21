//! **`N463`/`N464` -- a transfer through a pointer is bounded by what the pointer reaches**
//! (fix lane F5, review G04 F2/F3, 2026-09-22).
//!
//! An array that meets a `ptr<…> T` parameter decays to a pointer at its first element
//! (`m1::zerfaellt_zu`, C's array-to-pointer decay) -- and with the decay its LENGTH is gone.
//! The review measured what that costs at a user-made gate: `beispiele/150` declared
//!
//! ```text
//! syscall gate_read(fd : Fd, buf : ptr<normal, w> u8, len : u64) … requires len <= MAXLEN
//!     effects { writes buf }
//! ```
//!
//! and `lies(fd, EIMER, 1024)` over a 64-byte `EIMER` checked CLEAN: the kernel writes 1024
//! bytes into 64. Nothing tied the pointer's extent to the length the kernel honours.
//!
//! **The tie is now spelled in the contract, and held where it can be decided.** A clause
//! `requires len <= lenof(buf)` (or `<`) names the transfer bound: `lenof` of a pointer
//! parameter is the number of `T` elements the caller's object holds from the pointer on.
//!
//! | code | rule | where |
//! |---|---|---|
//! | `N463` | at a call, every `x <= lenof(p)` clause of the callee HOLDS, decided: an array passed for `p` bounds `x`'s argument by its length (the range of the argument must lie inside), and a pointer passed for `p` must be the caller's own parameter `q` with `x`'s argument the caller's own parameter `y` and the caller carrying `y <= lenof(q)` itself | `m1.rs` (`transfer_bound_at_call`), one funnel for every call form |
//! | `N464` | a `syscall` that takes a pointer at numbers (a buffer the kernel moves bytes through) points at BYTES (`u8`/`i8`) and carries a `requires x <= lenof(p)` over one of its integer parameters | `syscall.rs` (`buffer_bound`) |
//!
//! **What this reading is: strong, not `M115`'s.** `M115` refuses a precondition only where
//! the argument's range EXCLUDES it and counts the rest as open obligations. `N463` refuses
//! every site where the bound is not DECIDED -- an array too short for the argument's range,
//! a pointer whose extent the caller does not carry, an argument shape it cannot read. Only
//! clauses of the `x <= lenof(p)` form are read this way; every other `requires` keeps
//! `M115`'s weak reading and its `V` obligation.
//!
//! **What it does NOT claim.** That the kernel honours `len` (that stays the gate's named
//! assumption); that `lenof` of a pointer is anything but the caller's promise at the
//! forwarding step (it is decided only where an array decays); and nothing about a byte
//! INSIDE the frame -- a NUL-terminated path is a named caller obligation in the contract
//! (`beispiele/149`, `spec fn path_nul_terminated`), counted as `V`, not decided here.

use gabbro_syntax::ast::*;
use gabbro_syntax::span::Span;

/// **One transfer bound `length <= lenof(pointer)`** (`strict`: `<`), both bare parameter
/// names of the declaration that carries the clause.
#[derive(Debug, Clone)]
pub struct LengthBound {
    pub length: String,
    pub pointer: String,
    pub strict: bool,
    pub span: Span,
}

/// A bare name -- an `Ort` without suffixes, through parentheses.
pub fn bare_name(e: &Expr) -> Option<&str> {
    match &e.art {
        ExprArt::Ort(o) if o.suffixe.is_empty() => Some(o.basis.text.as_str()),
        ExprArt::Klammer(i) => bare_name(i),
        _ => None,
    }
}

/// `lenof(p)` with `p` a bare name, in either spelling the parser may pick (`typ_oder_ort`
/// decides at the next token, so a lone lowercase name can stand as a one-part path).
fn lenof_name(e: &Expr) -> Option<&str> {
    match &e.art {
        ExprArt::Eingebaut(b) => match b.as_ref() {
            Eingebaut::Lenof(TypOderOrt::Ort(o)) if o.suffixe.is_empty() => {
                Some(o.basis.text.as_str())
            }
            Eingebaut::Lenof(TypOderOrt::Typ(TypExpr::Pfad(p))) if p.teile.len() == 1 => {
                Some(p.teile[0].text.as_str())
            }
            _ => None,
        },
        ExprArt::Klammer(i) => lenof_name(i),
        _ => None,
    }
}

fn bounds_in_expr(e: &Expr, aus: &mut Vec<LengthBound>) {
    match &e.art {
        ExprArt::Klammer(i) => bounds_in_expr(i, aus),
        // A conjunction binds both halves; a disjunction binds neither, and stays out.
        ExprArt::Binaer(BinOp::Und, a, c) => {
            bounds_in_expr(a, aus);
            bounds_in_expr(c, aus);
        }
        ExprArt::Binaer(op, a, c) => {
            let (x, p, strikt) = match op {
                BinOp::KleinerGleich => (bare_name(a), lenof_name(c), false),
                BinOp::Kleiner => (bare_name(a), lenof_name(c), true),
                BinOp::GroesserGleich => (bare_name(c), lenof_name(a), false),
                BinOp::Groesser => (bare_name(c), lenof_name(a), true),
                _ => return,
            };
            if let (Some(x), Some(p)) = (x, p) {
                aus.push(LengthBound {
                    length: x.to_string(),
                    pointer: p.to_string(),
                    strict: strikt,
                    span: e.span,
                });
            }
        }
        _ => {}
    }
}

fn bounds_in_pred(p: &Pred, aus: &mut Vec<LengthBound>) {
    match &p.art {
        PredArt::Vergleich(e) => bounds_in_expr(e, aus),
        PredArt::Klammer(i) => bounds_in_pred(i, aus),
        PredArt::Und(a, b) => {
            bounds_in_pred(a, aus);
            bounds_in_pred(b, aus);
        }
        // `or`, `not`, `=>`, quantifiers: no bound that holds on every path.
        _ => {}
    }
}

/// **Every transfer bound a contract states** -- read through conjunctions only.
pub fn bounds(preds: &[Pred]) -> Vec<LengthBound> {
    let mut aus = Vec::new();
    for p in preds {
        bounds_in_pred(p, &mut aus);
    }
    aus
}

/// Does the caller's own contract carry `y <= lenof(q)` (or the strict form, which implies
/// the non-strict one)? For a strict demand only a strict clause answers.
pub fn caller_carries(rufer: &[LengthBound], y: &str, q: &str, strikt: bool) -> bool {
    rufer
        .iter()
        .any(|a| a.length == y && a.pointer == q && (a.strict || !strikt))
}
