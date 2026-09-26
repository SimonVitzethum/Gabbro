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
//! | `N506` | an `extern fn` that takes a pointer at numbers (a buffer the foreign code moves bytes through) points at BYTES (`u8`/`i8`) and carries a `requires x <= lenof(p)` over one of its integer parameters (lane 262, OFFEN O23) | `rahmenlaenge.rs` (`buffer_bound_extern`) |
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
//! (`beispiele/149`, `spec fn path_nul_terminated`), counted as `V`, not decided here
//! (`N507` in `nulpfad.rs` decides the shapes the program builds itself).

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
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

/// **`N506` -- an `extern fn` byte buffer carries `requires x <= lenof(p)`**
/// (lane 262, OFFEN O23).
///
/// `N464` (`syscall.rs`, `buffer_bound`) holds `syscall` buffers only; an `extern fn`
/// taking a byte pointer and a length (`beispiele/64`'s `write`) was not held to the
/// clause, while `N463` (`m1.rs`, `transfer_bound_at_call`) already decides the clause at
/// every call of ANY callee -- including an `extern fn` that writes it. The declaration
/// half was missing, so a foreign edge could move bytes past the caller's object with a
/// contract no call site is held against.
///
/// The rule is `buffer_bound`'s twin at the other foreign shape: a parameter that points
/// at numbers (`u8`/`i8` pointee -- the callee counts bytes, `lenof` counts elements) beside
/// an integer parameter that can serve as its length is a buffer, and the declaration
/// carries `requires x <= lenof(p)` (or `<`) over one of its integer parameters. A lone
/// object pointer with no length beside it (`beispiele/22`'s `melde_roh`) is one object,
/// not a transfer, and is not held. Pointers at records, tables or other non-number types
/// are one object, not a buffer, and stay with the frame rules they always had -- exactly
/// the same cut `N464` makes.
///
/// **Not claimed:** which length the foreign code honours (that stays the callee's named
/// assumption, like the kernel's at a gate); anything about a byte inside the frame
/// (`N507` in `nulpfad.rs`).
pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else { return };
        if f.klasse != Some(FnKlasse::Extern) {
            return;
        }
        buffer_bound_extern(baum, modul, f, absagen);
    });
}

fn buffer_bound_extern(baum: &Programm, modul: &str, f: &FnDecl, absagen: &mut Absagen) {
    let u = crate::umgebung::Umgebung::sammle(baum);
    // **Only a buffer WITH a length parameter is held.** A lone object pointer
    // (`extern fn melde_roh(text : ptr<code, r> Text)` in `beispiele/22`: one
    // parameter, no length beside it) names one object, not a transfer: there is
    // no length the caller could set past it, and no clause could tie one. A
    // length-less callee that scans for a terminator instead (`puts`) is `N507`'s
    // shape (`nulpfad.rs`), not this rule's.
    let hat_laenge = f.parameter.iter().any(|q| {
        matches!(
            u.typ_von_ausdruck_decl(modul, &q.typ),
            crate::typen::Typ::Ganzzahl(_) | crate::typen::Typ::Umlaufend(_)
        )
    });
    if !hat_laenge {
        return;
    }
    let atome = bounds(&f.requires);
    for p in &f.parameter {
        let TypExpr::Zeiger(z) = &p.typ else { continue };
        let ziel = u.typ_von_ausdruck_decl(modul, &z.ziel);
        let mut ohne = &ziel;
        while let crate::typen::Typ::Benannt { unter, .. } = ohne {
            ohne = unter;
        }
        if !matches!(
            ohne,
            crate::typen::Typ::Ganzzahl(_) | crate::typen::Typ::Umlaufend(_)
        ) {
            continue;
        }
        let byte = matches!(
            &z.ziel,
            TypExpr::Int(i) if matches!(i.wort, gabbro_syntax::kw::Kw::U8 | gabbro_syntax::kw::Kw::I8)
        );
        let gebunden = atome.iter().any(|a| {
            a.pointer == p.name.text
                && f.parameter.iter().any(|q| {
                    q.name.text == a.length
                        && matches!(
                            u.typ_von_ausdruck_decl(modul, &q.typ),
                            crate::typen::Typ::Ganzzahl(_) | crate::typen::Typ::Umlaufend(_)
                        )
                })
        });
        let detail = if !byte {
            format!(
                "points at `{}`, and the callee counts BYTES -- `lenof({})` counts elements, \
                 and only for `u8`/`i8` are the two one number",
                ziel.text(),
                p.name.text
            )
        } else if !gebunden {
            format!(
                "carries no `requires <length> <= lenof({})` over one of its integer \
                 parameters -- nothing ties the bytes the callee moves to the object the \
                 caller passes",
                p.name.text
            )
        } else {
            continue;
        };
        absagen.schiebe(
            Absage::fehler(
                "N506",
                p.name.span,
                format!("`extern fn {}` takes the buffer `{}` and {detail}", f.name.text, p.name.text),
            )
            .mit_notiz(
                "a foreign edge promises its frame as a named assumption; a length the \
                 caller may set past the object makes that frame false by the caller's \
                 own call, not by the machine",
            )
            .mit_notiz(
                "with the clause, `N463` decides the bound at every call: an array passed \
                 there bounds the length argument by its own length, a forwarded pointer \
                 carries the same clause up its caller's contract",
            ),
        );
    }
}
