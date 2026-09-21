//! **Integer `match` coverage: `N411`–`N414`** (fix lane F1, 2026-09-21; review G07 F1).
//!
//! Lane 222 added integer arms (`3 =>`, `0 .. 255 =>`, `0 ..< 256 =>`), and lane 227 lowers
//! a match made of them to a C `switch` WITHOUT `default`. Until this file no checker pass
//! decided that the arms cover the scrutinee, so a value no arm names skipped the whole
//! statement -- and every flow pass had read the match as closed (G07 F1: an out-of-bounds
//! read behind a checker-clean `narrow`).
//!
//! **The rule:** an integer `match` is accepted only when its arms name every value the
//! scrutinee can hold, each value exactly once. "Can hold" is M1's range of the scrutinee
//! expression at the `match` -- the declared type range (`u8`, `u32 in 0 .. 9`, the
//! storage range of `u13`), narrowed by the flow facts M1 already trusts for every index
//! (`narrow`, a guarding `if`). *This adds no new assumption: a table index is used
//! unchecked on exactly the same range.* No catch-all arm exists in the language, and none
//! is invented here.
//!
//! Four refusals, all at the checker, so `gabbro pruefe` says it before `gabbro emit` does:
//!
//! * **`N411`** -- a value of the scrutinee's range that no arm names (the first gap is
//!   named). This is the one the emitter cannot see: the C compiles, and the miss skips.
//! * **`N412`** -- an arm that names a value an earlier arm already names, or no value at
//!   all (`5 .. 3`). C allows one `case` label per value; the emitter refuses both with
//!   `C001` too -- here the checker says it first, and both agree.
//! * **`N413`** -- an arm value outside the scrutinee's STORAGE type (`-1` over a `u32`, a
//!   bound past `i128`). C converts a `case` label to the promoted scrutinee type, so the
//!   label would fire for a different value; the emitter's `C001` (review G07, `d905a859`)
//!   stays as the second line.
//! * **`N414`** -- integer arms over a scrutinee that is not an integer (a `tagged` value,
//!   a pointer, an opaque new type, `bool`), or a variant arm among integer arms. `bool` is
//!   refused on purpose: it is no integer in M1 (`Typ::Wahrheit`) nor in the Lean model
//!   (`CFormMatch` denotes arms over `Int`), and `if` already says everything a two-arm
//!   match over it could. (Measured 2026-09-21, gcc 16.2.1: `switch` over a `bool`
//!   VARIABLE draws no `-Wswitch-bool`, so this is a choice, not a `cc` backstop.)
//!
//! The Lean side is `grammatik/Grammatik/CFormMatch.lean`: `erschoepfend m lo hi` is the
//! predicate `N411` decides with `lo`/`hi` = M1's range, by an interval sweep instead of the
//! value enumeration of `erschoepfendB` (the two agree on every input; the sweep does not
//! enumerate `2^64` values). The correspondence is by reading, not by a proof over this
//! code.

use crate::typen::{self, Typ};
use gabbro_syntax::ast::{IntBound, IntPat, MatchStmt};
use gabbro_syntax::diag::{Absage, Absagen};

/// The scrutinee's value range, and its storage range where it has one.
struct Spanne {
    min: i128,
    max: i128,
    /// `None` for a literal scrutinee (`match 3 { … }`): a literal has no width of its own
    /// (U10), so there is no storage to hold a label against.
    speicher: Option<(i128, i128)>,
}

/// M1's range of the scrutinee, or `None` when it is no integer. A transparent new type is
/// looked through; an opaque one is not (D1: no conversion without the declaring module),
/// and neither is a pointer.
fn spanne(t: &Typ) -> Option<Spanne> {
    match t {
        Typ::Ganzzahl(b) | Typ::Umlaufend(b) => Some(Spanne {
            min: b.min,
            max: b.max,
            speicher: (!b.literal).then(|| typen::grenzen(b.breite, b.vorzeichen)),
        }),
        Typ::Benannt {
            undurchsichtig: false,
            unter,
            ..
        } => spanne(unter),
        _ => None,
    }
}

/// One bound as an `i128`, or `None` when it does not fit (`-2^127` fits, `2^127` not).
fn grenze(g: &IntBound) -> Option<i128> {
    if g.negative {
        if g.value == 1u128 << 127 {
            Some(i128::MIN)
        } else {
            i128::try_from(g.value).ok().map(|b| -b)
        }
    } else {
        i128::try_from(g.value).ok()
    }
}

/// What one arm names: an inclusive interval, nothing, or a value past `i128`.
enum Arm {
    Werte(i128, i128),
    Leer,
    Unfassbar,
}

fn arm(p: &IntPat) -> Arm {
    match p {
        IntPat::Exact(g) => match grenze(g) {
            Some(w) => Arm::Werte(w, w),
            None => Arm::Unfassbar,
        },
        IntPat::Range { lo, hi, exclusive } => {
            let (Some(a), Some(b)) = (grenze(lo), grenze(hi)) else {
                return Arm::Unfassbar;
            };
            let b = if *exclusive {
                match b.checked_sub(1) {
                    Some(v) => v,
                    None => return Arm::Leer,
                }
            } else {
                b
            };
            if a > b {
                Arm::Leer
            } else {
                Arm::Werte(a, b)
            }
        }
    }
}

fn zahl(w: i128) -> String {
    w.to_string()
}

fn bereich(a: i128, b: i128) -> String {
    if a == b {
        format!("`{}`", zahl(a))
    } else {
        format!("`{} .. {}`", zahl(a), zahl(b))
    }
}

/// **The check.** Called by M1 for every `match` with an integer arm, and for the empty
/// `match` over an integer; `gegenstand` is M1's type of the scrutinee at the `match`.
pub fn pruefe(m: &MatchStmt, gegenstand: &Typ, absagen: &mut Absagen) {
    let Some(sp) = spanne(gegenstand) else {
        let was = match gegenstand {
            Typ::Wahrheit => "a `bool` -- branch on it with `if`".to_string(),
            anderer => format!("`{}`", anderer.text()),
        };
        absagen.schiebe(
            Absage::fehler(
                "N414",
                m.gegenstand.span,
                format!("integer `match` arms over a scrutinee that is no integer: {was}"),
            )
            .mit_notiz(
                "integer arms name values, and only an integer scrutinee has values for them \
                 to meet -- no conversion is inserted",
            ),
        );
        return;
    };
    let mut genannt: Vec<(i128, i128)> = Vec::new();
    for z in &m.zweige {
        let Some(p) = &z.intpat else {
            absagen.schiebe(
                Absage::fehler(
                    "N414",
                    z.span,
                    format!(
                        "variant arm `{}` among integer arms -- the arms name values, this one \
                         names a case, and one `switch` cannot meet both",
                        z.variante.text
                    ),
                )
                .mit_notiz("an integer `match` has integer arms only"),
            );
            continue;
        };
        let (a, b) = match arm(p) {
            Arm::Werte(a, b) => (a, b),
            Arm::Leer => {
                absagen.schiebe(
                    Absage::fehler(
                        "N412",
                        z.span,
                        "this integer arm names no value at all -- its range is empty, so \
                         it could never run",
                    )
                    .mit_notiz("`lo .. hi` includes both bounds, `lo ..< hi` excludes `hi`"),
                );
                continue;
            }
            Arm::Unfassbar => {
                absagen.schiebe(
                    Absage::fehler(
                        "N413",
                        z.span,
                        "this integer arm names a value past `2^127 - 1` in magnitude -- no \
                         scrutinee type holds it",
                    )
                    .mit_notiz("the widest integer types are `u64` and `i64`"),
                );
                continue;
            }
        };
        if let Some((smin, smax)) = sp.speicher {
            if a < smin || b > smax {
                let aussen = if a < smin { a } else { b };
                absagen.schiebe(
                    Absage::fehler(
                        "N413",
                        z.span,
                        format!(
                            "this integer arm names `{}`, outside the scrutinee's type \
                             `{}` ({} .. {})",
                            zahl(aussen),
                            gegenstand.text(),
                            zahl(smin),
                            zahl(smax)
                        ),
                    )
                    .mit_notiz(
                        "C converts a `case` label to the scrutinee's type, so the label \
                         would fire for a DIFFERENT value than the one written",
                    ),
                );
                continue;
            }
        }
        if let Some(&(c, d)) = genannt.iter().find(|(c, d)| a <= *d && *c <= b) {
            let erst = a.max(c);
            absagen.schiebe(
                Absage::fehler(
                    "N412",
                    z.span,
                    format!(
                        "this integer arm names `{}`, which the earlier arm {} already names \
                         -- for that value this arm could never run",
                        zahl(erst),
                        bereich(c, d)
                    ),
                )
                .mit_notiz(
                    "every value belongs to exactly one arm; C allows one `case` label per \
                     value, and no arm order decides anything here",
                ),
            );
            continue;
        }
        genannt.push((a, b));
    }
    // **The sweep.** The arms that stand are disjoint; sorted, they must tile `min ..
    // max` without a gap. Values outside `min .. max` but inside the storage type are
    // allowed: a label for a value the scrutinee cannot hold never fires, and the C is
    // still exact.
    genannt.sort();
    let mut naechster = Some(sp.min);
    let mut luecken: Vec<(i128, i128)> = Vec::new();
    for &(a, b) in &genannt {
        let Some(n) = naechster else { break };
        if n > sp.max {
            break;
        }
        if b < n {
            continue;
        }
        if a > n {
            luecken.push((n, (a - 1).min(sp.max)));
        }
        naechster = b.checked_add(1);
    }
    if let Some(n) = naechster {
        if n <= sp.max {
            luecken.push((n, sp.max));
        }
    }
    if let Some(&(a, b)) = luecken.first() {
        let weitere = if luecken.len() > 1 {
            format!(" (and {} more gap(s))", luecken.len() - 1)
        } else {
            String::new()
        };
        absagen.schiebe(
            Absage::fehler(
                "N411",
                m.gegenstand.span,
                format!(
                    "this integer `match` does not cover its scrutinee: no arm names {}{}; the \
                     scrutinee is `{}`",
                    bereich(a, b),
                    weitere,
                    gegenstand.text()
                ),
            )
            .mit_notiz(
                "the emitted `switch` has no `default`, so a value no arm names would skip \
                 the whole statement -- and there is no catch-all arm in this language",
            )
            .mit_notiz(
                "name the missing values in an arm, or narrow the scrutinee first \
                 (`narrow x to lo .. hi else { … }`) so its range is what the arms cover",
            ),
        );
    }
}
