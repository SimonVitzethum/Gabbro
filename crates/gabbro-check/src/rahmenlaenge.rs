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
    let has_length = f.parameter.iter().any(|q| {
        matches!(
            u.typ_von_ausdruck_decl(modul, &q.typ),
            crate::typen::Typ::Ganzzahl(_) | crate::typen::Typ::Umlaufend(_)
        )
    });
    if !has_length {
        return;
    }
    let atoms = bounds(&f.requires);
    for p in &f.parameter {
        let TypExpr::Zeiger(z) = &p.typ else { continue };
        let target = u.typ_von_ausdruck_decl(modul, &z.ziel);
        let mut unwrapped = &target;
        while let crate::typen::Typ::Benannt { unter, .. } = unwrapped {
            unwrapped = unter;
        }
        if !matches!(
            unwrapped,
            crate::typen::Typ::Ganzzahl(_) | crate::typen::Typ::Umlaufend(_)
        ) {
            continue;
        }
        let byte = matches!(
            &z.ziel,
            TypExpr::Int(i) if matches!(i.wort, gabbro_syntax::kw::Kw::U8 | gabbro_syntax::kw::Kw::I8)
        );
        let is_bound = atoms.iter().any(|a| {
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
                target.text(),
                p.name.text
            )
        } else if !is_bound {
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

/// **One EXTENT fact of a pointer parameter: `name + k <= lenof(pointer)`** (`N571`, C-free
/// lane, 2026-09-30). `name` is `None` for a constant bound (`4 <= lenof(buf)`); the strict
/// form is normalised (`x < lenof(p)` is `x + 1 <= lenof(p)`). Read from `requires` through
/// conjunctions only, exactly like [`bounds`].
#[derive(Debug, Clone)]
pub struct Ausdehnung {
    pub name: Option<String>,
    pub k: i128,
    pub zeiger: String,
    /// The left side was a BARE name (`x <= lenof(p)`, `x < lenof(p)`) -- the form
    /// [`bounds`] reads and `N463` has decided since fix lane F5. The other forms (a
    /// constant, `v + k`) are decided by the widened call-site check.
    pub nackt: bool,
    /// Every NAME of the left side as written (a `+`-sum of names and numerals). The reader
    /// in `m1.rs` folds named constants into `k`; a clause left with more than one name
    /// speaks about no single parameter and is dropped (fail-closed).
    pub namen: Vec<String>,
}

/// **A `+`-sum of bare names and numerals** (`v`, `v + 4`, `TCP_V_KOPF + kopflen`): its
/// names and the sum of its numerals. Anything else is no sum this reading follows.
pub fn summanden(e: &Expr) -> Option<(Vec<String>, i128)> {
    match &e.art {
        ExprArt::Klammer(i) => summanden(i),
        ExprArt::Zahl(n) => Some((Vec::new(), i128::try_from(*n).ok()?)),
        ExprArt::Binaer(BinOp::Plus, a, b) => {
            let (mut na, ka) = summanden(a)?;
            let (nb, kb) = summanden(b)?;
            na.extend(nb);
            Some((na, ka.checked_add(kb)?))
        }
        // `c * x` with a small literal `c`: `c` copies of `x` (`base + 4 * t`).
        ExprArt::Binaer(BinOp::Mal, a, b) => {
            let (c, x) = match (&a.art, &b.art) {
                (ExprArt::Zahl(c), _) => (*c, b),
                (_, ExprArt::Zahl(c)) => (*c, a),
                _ => return None,
            };
            if c > 64 {
                return None;
            }
            let (namen, k) = summanden(x)?;
            let mut aus = Vec::new();
            for _ in 0..c {
                aus.extend(namen.iter().cloned());
            }
            Some((aus, k.checked_mul(i128::try_from(c).ok()?)?))
        }
        _ => bare_name(e).map(|n| (vec![n.to_string()], 0)),
    }
}

fn ausdehnung_expr(e: &Expr, aus: &mut Vec<Ausdehnung>) {
    match &e.art {
        ExprArt::Klammer(i) => ausdehnung_expr(i, aus),
        ExprArt::Binaer(BinOp::Und, a, c) => {
            ausdehnung_expr(a, aus);
            ausdehnung_expr(c, aus);
        }
        ExprArt::Binaer(op, a, c) => {
            let (links, p, strikt) = match op {
                BinOp::KleinerGleich => (summanden(a), lenof_name(c), false),
                BinOp::Kleiner => (summanden(a), lenof_name(c), true),
                BinOp::GroesserGleich => (summanden(c), lenof_name(a), false),
                BinOp::Groesser => (summanden(c), lenof_name(a), true),
                _ => return,
            };
            let nackt = match op {
                BinOp::KleinerGleich | BinOp::Kleiner => bare_name(a).is_some(),
                _ => bare_name(c).is_some(),
            };
            if let (Some((namen, k)), Some(p)) = (links, p) {
                aus.push(Ausdehnung {
                    name: None,
                    k: if strikt { k + 1 } else { k },
                    zeiger: p.to_string(),
                    nackt,
                    namen,
                });
            }
        }
        _ => {}
    }
}

fn ausdehnung_pred(p: &Pred, aus: &mut Vec<Ausdehnung>) {
    match &p.art {
        PredArt::Vergleich(e) => ausdehnung_expr(e, aus),
        PredArt::Klammer(i) => ausdehnung_pred(i, aus),
        PredArt::Und(a, b) => {
            ausdehnung_pred(a, aus);
            ausdehnung_pred(b, aus);
        }
        _ => {}
    }
}

/// **Every extent fact a contract states** (`N571`).
pub fn ausdehnungen(preds: &[Pred]) -> Vec<Ausdehnung> {
    let mut aus = Vec::new();
    for p in preds {
        ausdehnung_pred(p, &mut aus);
    }
    aus
}

/// Every bare name a body ASSIGNS (`x = …;`, `x += …;`), through every nested block. A
/// parameter in this set is not the value its entry clause spoke about (`N571`).
pub fn zugewiesene_namen(b: &Block, aus: &mut std::collections::HashSet<String>) {
    for s in &b.anweisungen {
        if let StmtArt::Zuweisung(z) = &s.art {
            if z.ziel.suffixe.is_empty() {
                aus.insert(z.ziel.basis.text.clone());
            }
        }
        for k in crate::unterbloecke(s) {
            zugewiesene_namen(k, aus);
        }
    }
}

/// **Every upper bound a contract states over a sum: `namen + k <= K`** (`N463`/`N571`,
/// C-free lane, 2026-09-30) -- `off + n <= 16384` beside a 16384-element array. Read through
/// conjunctions only; the right side is a `+`-sum too, whose names the reader folds.
pub fn obergrenzen(preds: &[Pred]) -> Vec<((Vec<String>, i128), (Vec<String>, i128))> {
    fn expr(e: &Expr, aus: &mut Vec<((Vec<String>, i128), (Vec<String>, i128))>) {
        match &e.art {
            ExprArt::Klammer(i) => expr(i, aus),
            ExprArt::Binaer(BinOp::Und, a, c) => {
                expr(a, aus);
                expr(c, aus);
            }
            ExprArt::Binaer(op, a, c) => {
                let (l, r, strikt) = match op {
                    BinOp::KleinerGleich => (a, c, false),
                    BinOp::Kleiner => (a, c, true),
                    BinOp::GroesserGleich => (c, a, false),
                    BinOp::Groesser => (c, a, true),
                    _ => return,
                };
                if lenof_name(r).is_some() {
                    return;
                }
                if let (Some((ln, lk)), Some((rn, rk))) = (summanden(l), summanden(r)) {
                    let lk = if strikt { lk + 1 } else { lk };
                    aus.push(((ln, lk), (rn, rk)));
                }
            }
            _ => {}
        }
    }
    let mut aus = Vec::new();
    for p in preds {
        let mut stapel = vec![p];
        while let Some(p) = stapel.pop() {
            match &p.art {
                PredArt::Vergleich(e) => expr(e, &mut aus),
                PredArt::Klammer(i) => stapel.push(i),
                PredArt::Und(a, b) => {
                    stapel.push(a);
                    stapel.push(b);
                }
                _ => {}
            }
        }
    }
    aus
}
