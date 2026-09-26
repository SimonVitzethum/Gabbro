//! Statement certificates from Rust (T1 transfer printer, lanes 153/155).
//!
//! The Lean side holds statement/block certificates with decidable validity
//! (`ZeugnisStmt.lean`: `CertStmt`/`CertSeq`/`CertEnd`, `ZeugnisStmt2.lean`:
//! `CertStmt2`/`CertSeq2`/`CertEnd2`, `ZeugnisStmt104b.lean`: `CertEnd104`
//! with `consCall` for calls with arguments and `retDurch` for a return
//! through a pointer). The Rust side printed only expression
//! certificates (`certemit.rs`). This module prints, per function body, a Lean
//! term of the `CertEnd2`/`CertEnd104` shape for the forms both Lean files cover,
//! and REFUSES by name every body with a form outside them.
//!
//! ## Fragment boundary (measured, not hoped)
//!
//! Printable today: `return;`, `return <int-expr>;`, `return <ptr-read>;`
//! (`retDurch`, the pointer proof is filled at paste), `let x : <range> = ...;`,
//! direct table writes with recomputable indices, pointer writes with
//! recomputable indices (`assignDurch`, table number = declaration order),
//! integer locals, `if` with a printable condition and falling branches,
//! direct calls with arguments (`consCall`: the count and flow print, the
//! `RufPasst` travels as `?hp`, filled at paste like `refHpLiesAt` was).
//! Integer expressions cover literals, places, `+ - * / %`, unary minus,
//! `&`, `|`/`^`/`<<`/`>>` (with the smallest width both legs admit -- the
//! `maske` bound, so the claim is the checker's range exactly), `~` (as
//! `a ^ (2^B - 1)` in the storage word, exactly like the checker),
//! lossless integer conversions (the bare argument term, like the checker),
//! and `u32::max`-style limit words (the folded literal).
//! Everything else is a named refusal, never a truncation:
//!
//! * `CS001` statement form with no printed `CertStmt`/`CertStmt2` shape
//!   (indirect calls, matches, loops, `let-else`,
//!   `leave`/`next` outside loops, register/mark/float/global steps, ...)
//! * `CS002` expression with no `CertExpr` shape (calls that are not
//!   lossless integer conversions, wrapping/saturating operators,
//!   quantifiers, non-place call arguments, pointer reads outside
//!   `return`, ...)
//! * `CS003` index or variable with no recomputable range (reads of
//!   non-integer locals)
//! * `CS004` nullary direct call: the `CertStmt.call` shape exists but its
//!   `RufPasst` travels as proof (R-3), which plain data cannot carry
//! * `CS005` unresolvable name, count, rank or range for the claim (unknown
//!   table, callee or parameter, non-literal `count`, result type with no
//!   integer range, call argument count mismatch, ...)
//!
//! ## Conventions of the printed term
//!
//! Table, field and function names print as written in surface syntax; every
//! resource list prints as `[]` (the Lean side recomputes validity over it,
//! so a wrong flow fails `decide` loudly instead of passing silently).
//! Counts resolve from literals or `const` aliases, field ranges and alias
//! ranges from literal declarations, `const` bounds, or bare machine words
//! (`u32` is its full range, the `breite_von`/`grenzen` table the checker
//! computes with -- the same spelling `lean-g` exports); anything else is
//! `CS005`. Table
//! numbers are declaration order (the `tabNr` convention of `lean-g`).
//! Values print under `wide` exactly where the checker elaborates `weiter`
//! (a contained range narrows to the claim, an exact one prints bare); an
//! uncontained value is refused, since the checker would reject it as a type
//! error. Index positions print the same way: whatever `CertExpr` the index
//! elaborates to, narrowed to exactly `0 .. count - 1` (a literal index
//! prints exactly as before). `index into T` parameters and locals carry
//! `(0, count - 1)` like any integer, so an index variable prints as
//! `(.var k)` and recomputes. Pointer parameters are context entries with
//! their table and rights; only `rw` pointers write, only through the
//! `slots` field path the `lean-g` export uses. De Bruijn indices count the
//! FIRST parameter as 0 (the `gCtx` convention of `lean-g`: the head of the
//! context is the first parameter). The printed term is linked to
//! the checked body by construction of this printer only; term identity
//! (`print (elab x) = x`) is proved nowhere yet (the `ZeugnisStmt2.lean`
//! CUTS booking). Call arguments print nothing: each must name a bare
//! parameter place (checked here), and the elaborated `Args` travel as
//! proof, filled at paste.

use gabbro_syntax::ast::*;

/// A named refusal: the code plus the exact surface form that caused it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Refusal {
    /// One of `CS001`..=`CS005` (see the module docs).
    pub code: &'static str,
    /// Names the function and the form, never truncated.
    pub grund: String,
}

fn refuse(code: &'static str, grund: String) -> Refusal {
    Refusal { code, grund }
}

/// The per-body print: a Lean term or a named refusal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BodyCert {
    /// A Lean `CertEnd2` term (as text) for this body.
    Gedruckt { lean: String, neu: bool },
    /// The body has a form outside the covered fragment.
    Abgewiesen { weigerung: Refusal },
}

/// One table as the printer sees it: literal `count`, literal field ranges
/// with the storage representation of the field type (`~` needs the word).
struct TableInfo {
    name: String,
    count: Option<i128>,
    felder: Vec<(String, Option<(i128, i128)>, Option<(u8, bool)>)>,
}

/// What the printer resolves from the declarations: tables and int aliases.
/// An alias carries its range and the storage representation behind it.
struct DeclInfo {
    tabellen: Vec<TableInfo>,
    alias: Vec<(String, (i128, i128), Option<(u8, bool)>)>,
    konstanten: Vec<(String, i128)>,
    funktionen: Vec<(String, usize)>,
}

/// One context entry: an integer or boolean local, a pointer parameter, or
/// something else. An integer carries its storage representation
/// (`breite_von` width plus signedness, read off the declared type) beside
/// its range: `~` complements within the storage word, so the print needs
/// the word, not just the range.
enum CtxEintrag {
    Ganz(String, i128, i128, Option<(u8, bool)>),
    Wahr(String),
    Zeiger(String, usize, bool),
    Sonst(String),
}

/// The printer context: entries in binding order (head last).
struct Ctx {
    eintraege: Vec<CtxEintrag>,
}

impl Ctx {
    /// The de Bruijn index of a name: position from the head.
    fn index_von(&self, name: &str) -> Option<(usize, &CtxEintrag)> {
        let pos = self.eintraege.iter().rposition(|e| match e {
            CtxEintrag::Ganz(n, _, _, _)
            | CtxEintrag::Wahr(n)
            | CtxEintrag::Zeiger(n, _, _)
            | CtxEintrag::Sonst(n) => n == name,
        })?;
        Some((self.eintraege.len() - 1 - pos, &self.eintraege[pos]))
    }
}

/// A literal integer value of an expression: a literal, or a `const` name.
fn als_zahl_mit(info: &DeclInfo, e: &Expr) -> Option<i128> {
    match &e.art {
        ExprArt::Zahl(n) => i128::try_from(*n).ok(),
        ExprArt::Klammer(x) => als_zahl_mit(info, x),
        ExprArt::Ort(o) if o.suffixe.is_empty() => {
            info.konstanten.iter().find(|(n, _)| *n == o.basis.text).map(|(_, v)| *v)
        }
        _ => None,
    }
}

/// The storage representation behind an integer type: `breite_von` width
/// plus signedness, the same pair the checker computes with. The word
/// already names the storage (`u13` parses with `wort = u16`), so sugar
/// needs no special case here -- and `~` complements within that storage
/// word (`m1.rs`: `grenzen(b.breite)`), which is exactly what the print
/// below replays. An `index into T` has none here (its width lives in the
/// checker's index form, not in a word).
fn wort_repr(t: &TypExpr, info: &DeclInfo) -> Option<(u8, bool)> {
    match t {
        TypExpr::Int(i) => crate::umgebung::breite_von(i.wort),
        TypExpr::Pfad(p) => {
            let name = p.teile.last()?.text.clone();
            info.alias.iter().find(|(n, _, _)| *n == name).and_then(|(_, _, r)| *r)
        }
        _ => None,
    }
}

/// An integer range spelled in a type: a literal `in lo .. hi`, a bare
/// machine word, or an alias for one. A bare word (`u32`) travels as its
/// full range -- the same numbers the checker computes with
/// (`breite_von`/`grenzen`) and the same spelling `lean-g` exports
/// (`int_range` there): the Lean side recomputes validity over the printed
/// bounds, so a wrong table fails `decide` loudly instead of passing
/// silently. Bounds resolve `const` names exactly like counts do
/// (`als_zahl_mit`, and `numeral` in `lean-g`): the value is declared, not
/// guessed. A sugared width without its desugared range is refused: the
/// storage word is wider than the exact `N`-bit range, and the parser
/// always fills the range in, so meeting one without the other means the
/// tree is not what the parser builds.
fn bereich_von_typ(t: &TypExpr, info: &DeclInfo) -> Option<(i128, i128)> {
    match t {
        TypExpr::Int(i) => {
            if let Some(z) = i.zucker {
                // The exact `N`-bit range the sugar promises (`zucker_bereich`
                // over the same width, so the type and the constant can never
                // disagree -- and the desugared lower bound of a signed sugar
                // is a unary minus, not a literal, so reading the sugar is
                // also the only way that resolves). Checked shifts refuse a
                // width no parser builds instead of wrapping.
                if z.vorzeichen {
                    let halb = 1i128.checked_shl(z.breite.checked_sub(1)?)?;
                    Some((halb.checked_neg()?, halb.checked_sub(1)?))
                } else {
                    Some((0, 1i128.checked_shl(z.breite)?.checked_sub(1)?))
                }
            } else if let Some(b) = i.bereich.as_ref() {
                let lo = als_zahl_mit(info, &b.von)?;
                let hi = als_zahl_mit(info, &b.bis)?;
                Some((lo, if b.exklusiv { hi - 1 } else { hi }))
            } else {
                let (breite, vz) = crate::umgebung::breite_von(i.wort)?;
                Some(crate::typen::grenzen(breite, vz))
            }
        }
        TypExpr::Pfad(p) => {
            let name = p.teile.last()?.text.clone();
            info.alias
                .iter()
                .find(|(n, _, _)| *n == name)
                .map(|(_, r, _)| *r)
        }
        _ => None,
    }
}

/// Collect tables (literal counts and field ranges) and int aliases.
fn sammle(baum: &Programm) -> DeclInfo {
    let mut info = DeclInfo {
        tabellen: Vec::new(),
        alias: Vec::new(),
        konstanten: Vec::new(),
        funktionen: Vec::new(),
    };
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Konst(k) => {
            if let ExprArt::Zahl(n) = &k.wert.art {
                if let Ok(v) = i128::try_from(*n) {
                    info.konstanten.push((k.name.text.clone(), v));
                }
            }
        }
        ItemArt::Funktion(f) => {
            info.funktionen.push((f.name.text.clone(), f.parameter.len()));
        }
        ItemArt::Typ(t) => {
            if let Some(rumpf) = &t.rumpf {
                if let Some(r) = bereich_von_typ(rumpf, &info) {
                    let repr = wort_repr(rumpf, &info);
                    info.alias.push((t.name.text.clone(), r, repr));
                }
            }
        }
        ItemArt::Tabelle(t) => {
            let count = t
                .kapazitaet
                .as_ref()
                .and_then(|e| als_zahl_mit(&info, e));
            let mut felder = Vec::new();
            if let Some(slot) = &t.slot {
                for f in &slot.felder {
                    let r = match &f.typ {
                        SlotTyp::Typ(te) => bereich_von_typ(te, &info),
                        SlotTyp::Wrapping(_) => None,
                    };
                    let repr = match &f.typ {
                        SlotTyp::Typ(te) => wort_repr(te, &info),
                        SlotTyp::Wrapping(_) => None,
                    };
                    felder.push((f.name.text.clone(), r, repr));
                }
            }
            info.tabellen.push(TableInfo {
                name: t.name.text.clone(),
                count,
                felder,
            });
        }
        _ => {}
    });
    info
}

/// The context entry for one surface parameter: an `index into T` carries
/// `(0, count - 1)` like any integer (the `Ty.index` convention: an index
/// variable recomputes), a `normal` pointer its table and rights, an integer
/// range its bounds, a boolean its flag. Anything else is opaque.
fn param_eintrag(name: &str, typ: &TypExpr, info: &DeclInfo) -> CtxEintrag {
    match typ {
        TypExpr::Index { tabelle, optional, .. } => {
            if *optional {
                return CtxEintrag::Sonst(name.to_string());
            }
            match tabelle_text(tabelle, info) {
                Some((_, count)) => {
                    CtxEintrag::Ganz(name.to_string(), 0, count - 1, None)
                }
                None => CtxEintrag::Sonst(name.to_string()),
            }
        }
        TypExpr::Zeiger(p) => {
            if !matches!(p.raum, Raum::Normal) {
                return CtxEintrag::Sonst(name.to_string());
            }
            let ziel = match &p.ziel {
                TypExpr::Pfad(pfad) => pfad.teile.last().map(|i| i.text.clone()),
                _ => None,
            };
            match ziel.and_then(|z| tabellen_nr(info, &z)) {
                Some(ti) => {
                    let rw = p.rechte.iter().any(|r| {
                        matches!(r, Recht::LesenSchreiben | Recht::Schreiben)
                    });
                    CtxEintrag::Zeiger(name.to_string(), ti, rw)
                }
                None => CtxEintrag::Sonst(name.to_string()),
            }
        }
        _ => match bereich_von_typ(typ, info) {
            Some((lo, hi)) => {
                CtxEintrag::Ganz(name.to_string(), lo, hi, wort_repr(typ, info))
            }
            None if matches!(typ, TypExpr::Bool(_)) => CtxEintrag::Wahr(name.to_string()),
            None => CtxEintrag::Sonst(name.to_string()),
        },
    }
}

/// The table and count behind an `index into T` name.
fn tabelle_text(tabelle: &Ident, info: &DeclInfo) -> Option<(usize, i128)> {
    let ti = tabellen_nr(info, &tabelle.text)?;
    let count = info.tabellen[ti].count?;
    Some((ti, count))
}

fn tabelle<'a>(info: &'a DeclInfo, name: &str) -> Option<&'a TableInfo> {
    info.tabellen.iter().find(|t| t.name == name)
}

/// The table number: declaration order, the `tabNr` convention of `lean-g`.
fn tabellen_nr(info: &DeclInfo, name: &str) -> Option<usize> {
    info.tabellen.iter().position(|t| t.name == name)
}

/// The parameter count of a callee by its last path segment.
fn callee_nargs(info: &DeclInfo, ziel: &CallTarget) -> Option<(String, usize)> {
    match ziel {
        CallTarget::Path(p) => {            let name = p.teile.last()?.text.clone();
            let nargs = info.funktionen.iter().find(|(n, _)| *n == name)?.1;
            Some((name, nargs))
        }
        CallTarget::Place(_) => None,
    }
}

fn fehlschlag(
    funktion: &str,
    code: &'static str,
    detail: String,
) -> Result<String, Refusal> {
    Err(refuse(
        code,
        format!("function {funktion}: {detail}"),
    ))
}

/// Narrow a printed expression to a claimed range, mirroring the checker's
/// `weiter`: an exact range prints bare, a contained one under `wide`, and
/// anything else is refused (the checker would reject it as a type error).
fn verenge(
    funktion: &str,
    wo: &str,
    term: String,
    hat: (i128, i128),
    soll: (i128, i128),
) -> Result<String, Refusal> {
    if hat == soll {
        Ok(term)
    } else if soll.0 <= hat.0 && hat.1 <= soll.1 {
        Ok(format!("(.wide {} {} {term})", soll.0, soll.1))
    } else {
        Err(refuse(
            "CS005",
            format!(
                "function {funktion}: {wo} ranges ({}, {}) but needs ({}, {})",
                hat.0, hat.1, soll.0, soll.1
            ),
        ))
    }
}

/// Print an index position: whatever `CertExpr` the index elaborates to,
/// narrowed to exactly `0 .. count - 1` (mirrors `weiter`: a literal prints
/// exactly as before, an index variable as `(.var k)`).
fn drucke_index(
    funktion: &str,
    wo: &str,
    idx: &Expr,
    ctx: &Ctx,
    info: &DeclInfo,
    count: i128,
) -> Result<String, Refusal> {
    let (t, r, _) = drucke_expr(funktion, idx, ctx, info)?;
    verenge(funktion, wo, t, r, (0, count - 1))
}

/// The short name of an expression form, for refusals.
fn expr_name(e: &Expr) -> String {
    match &e.art {
        ExprArt::Zahl(_) => "literal".to_string(),
        ExprArt::Gleitkomma { .. } => "float literal".to_string(),
        ExprArt::Wahr | ExprArt::Falsch => "boolean literal".to_string(),
        ExprArt::Ort(o) => format!("place {}", o.text()),
        ExprArt::FnWert(p) => format!("function value {}", p.text()),
        ExprArt::Ruf(r) => format!("call {}", r.ziel.text()),
        ExprArt::LibraryCall(_) => "library call".to_string(),
        ExprArt::Klammer(x) => expr_name(x),
        ExprArt::Eingebaut(_) => "builtin".to_string(),
        ExprArt::Alt(o) => format!("old({})", o.text()),
        ExprArt::Ergebnis => "result".to_string(),
        ExprArt::Grund { grund, fall } => {
            format!("reason {}::{}", grund.text, fall.text)
        }
        ExprArt::Zaehle { .. } => "count".to_string(),
        ExprArt::Unaer(op, _) => match op {
            UnOp::Nicht => "negation".to_string(),
            UnOp::Negativ => "unary minus".to_string(),
            UnOp::BitNicht => "bitwise complement".to_string(),
        },
        ExprArt::Binaer(op, _, _) => format!("operator {}", binop_name(*op)),
        ExprArt::ArrayLit(_) => "array literal".to_string(),
        // **Lane 261:** a string literal names itself like any literal.
        ExprArt::Kette(_) => "string literal".to_string(),
    }
}

fn binop_name(op: BinOp) -> &'static str {
    match op {
        BinOp::Oder => "or",
        BinOp::Und => "and",
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
        BinOp::PlusWrap => "+%",
        BinOp::MinusWrap => "-%",
        BinOp::MalWrap => "*%",
        BinOp::SchiebLinksWrap => "<<%",
        BinOp::PlusSat => "+|",
    }
}

/// The smallest `w` with `bound < 2^w` (the `maske` bound of `typen.rs`):
/// what `|`/`^` carry, and the value leg of `<<`/`>>`. `None` for a
/// negative bound or one no `i128` shift reaches -- never a guess.
fn kleinste_breite(bound: i128) -> Option<u32> {
    if bound < 0 {
        return None;
    }
    for w in 0..127u32 {
        if bound < 1i128.checked_shl(w)? {
            return Some(w);
        }
    }
    None
}

/// The storage word a conversion call targets, if this call IS one: a
/// single-segment path naming an integer word (`u64(a)`, M144/M145 in
/// `m1.rs`) or a sugared width (which converts to its storage word,
/// PLAN-BITS section 1). Anything else -- including a word with the wrong
/// arity -- is an ordinary call, refused downstream as before.
fn umwandlung_ziel(r: &Ruf) -> Option<gabbro_syntax::kw::Kw> {
    use gabbro_syntax::kw::Kw;
    if r.argumente.len() != 1 {
        return None;
    }
    let name = r.path()?.einfach()?;
    if let Some(k) = Kw::suche(&name.text).filter(|k| k.ist_intty()) {
        return Some(k);
    }
    gabbro_syntax::zucker_speicher(&name.text)
}

/// Print an integer expression as `CertExpr` with its recomputed range
/// and, where the declared type names one, its storage representation
/// (`breite_von` width plus signedness).
///
/// The range mirrors `certRange` (`Zeugnis.lean`): unbounded `Int`
/// arithmetic would lie on overflow, so checked `i128` answers `CS005`.
/// Widths track declarations, never computations: a literal carries none
/// (it takes the other side's form), and neither does a computed value --
/// `~` over either refuses, exactly like the checker (M137).
fn drucke_expr(
    funktion: &str,
    e: &Expr,
    ctx: &Ctx,
    info: &DeclInfo,
) -> Result<(String, (i128, i128), Option<(u8, bool)>), Refusal> {
    match &e.art {
        ExprArt::Zahl(n) => {
            let v = i128::try_from(*n).map_err(|_| {
                refuse("CS005", format!("function {funktion}: literal {n} too large"))
            })?;
            Ok((format!("(.lit {v})"), (v, v), None))
        }
        ExprArt::Klammer(x) => drucke_expr(funktion, x, ctx, info),
        ExprArt::Binaer(op, a, b) => {
            let (ta, (l1, h1), _) = drucke_expr(funktion, a, ctx, info)?;
            let (tb, (l2, h2), _) = drucke_expr(funktion, b, ctx, info)?;
            // The bound mirrors `certRange` (`Zeugnis.lean`); `None` is
            // overflow (or an uncovered operator), never a guess. Division
            // and remainder claim M102 (`(0, h1)` under `0 <= l1`, `1 <= l2`;
            // `%` claims `(0, h2 - 1)`), `&` claims M137 (`(0, h1)` under
            // nonnegativity) -- the same arms `certemit.rs` recomputes.
            // `|`/`^` carry the smallest covering width (the `maske` bound
            // of `typen.rs`, so the claim is the checker's range exactly);
            // `<<`/`>>` carry the smallest width both legs admit (the value
            // and the claim ignore it -- `Zahl.shl/shr` compute `a * 2^b`
            // and `a / 2^b` whatever `w` says). A failed leg is `CS005`
            // (the shape exists, the instance has no range), never a weaker
            // claim.
            if matches!(op, BinOp::BitOder | BinOp::BitXor) {
                if !(0 <= l1 && 0 <= l2) {
                    return Err(refuse(
                        "CS005",
                        format!("function {funktion}: {} has no range", expr_name(e)),
                    ));
                }
                let w = kleinste_breite(h1.max(h2)).ok_or_else(|| {
                    refuse(
                        "CS005",
                        format!("function {funktion}: {} has no range", expr_name(e)),
                    )
                })?;
                let hi = 1i128
                    .checked_shl(w)
                    .and_then(|v| v.checked_sub(1))
                    .ok_or_else(|| {
                        refuse(
                            "CS005",
                            format!("function {funktion}: {} overflows", expr_name(e)),
                        )
                    })?;
                let name = if *op == BinOp::BitOder { "bor" } else { "bxor" };
                return Ok((format!("(.{name} {w} {ta} {tb})"), (0, hi), None));
            }
            if matches!(op, BinOp::SchiebLinks | BinOp::SchiebRechts) {
                if !(0 <= l1 && 0 <= l2) {
                    return Err(refuse(
                        "CS005",
                        format!("function {funktion}: {} has no range", expr_name(e)),
                    ));
                }
                let no_range = || {
                    refuse(
                        "CS005",
                        format!("function {funktion}: {} has no range", expr_name(e)),
                    )
                };
                let w = kleinste_breite(h1)
                    .ok_or_else(no_range)?
                    .max(u32::try_from(h2.checked_add(1).ok_or_else(no_range)?).map_err(
                        |_| no_range(),
                    )?);
                if *op == BinOp::SchiebLinks {
                    let h2u = u32::try_from(h2).map_err(|_| no_range())?;
                    let hi = h1
                        .checked_mul(1i128.checked_shl(h2u).ok_or_else(no_range)?)
                        .ok_or_else(|| {
                            refuse(
                                "CS005",
                                format!("function {funktion}: {} overflows", expr_name(e)),
                            )
                        })?;
                    return Ok((format!("(.shl {w} {ta} {tb})"), (0, hi), None));
                }
                return Ok((format!("(.shr {w} {ta} {tb})"), (0, h1), None));
            }
            let ecken: Option<((i128, i128), &'static str)> = match op {
                BinOp::Plus => l1
                    .checked_add(l2)
                    .and_then(|lo| h1.checked_add(h2).map(|hi| (lo, hi)))
                    .map(|r| (r, "add")),
                BinOp::Geteilt if 0 <= l1 && 1 <= l2 => Some(((0, h1), "div")),
                BinOp::Rest if 0 <= l1 && 1 <= l2 => h2
                    .checked_sub(1)
                    .map(|hi| ((0, hi), "rem")),
                BinOp::BitUnd if 0 <= l1 && 0 <= l2 => Some(((0, h1), "band")),
                BinOp::Geteilt | BinOp::Rest | BinOp::BitUnd => {
                    return Err(refuse(
                        "CS005",
                        format!("function {funktion}: {} has no range", expr_name(e)),
                    ))
                }
                BinOp::Minus => l1
                    .checked_sub(h2)
                    .and_then(|lo| h1.checked_sub(l2).map(|hi| (lo, hi)))
                    .map(|r| (r, "sub")),
                BinOp::Mal => {
                    let mut lo = i128::MAX;
                    let mut hi = i128::MIN;
                    let mut ok = true;
                    for &x in &[l1, h1] {
                        for &y in &[l2, h2] {
                            match x.checked_mul(y) {
                                Some(v) => {
                                    lo = lo.min(v);
                                    hi = hi.max(v);
                                }
                                None => ok = false,
                            }
                        }
                    }
                    if ok {
                        Some(((lo, hi), "mul"))
                    } else {
                        None
                    }
                }
                _ => {
                    return fehlschlag(
                        funktion,
                        "CS002",
                        format!("{} has no CertExpr shape", expr_name(e)),
                    )
                    .map(|s| (s, (0, 0), None));
                }
            };
            let ((lo, hi), name) = ecken.ok_or_else(|| {
                refuse(
                    "CS005",
                    format!("function {funktion}: {} overflows", expr_name(e)),
                )
            })?;
            Ok((format!("(.{name} {ta} {tb})"), (lo, hi), None))
        }
        ExprArt::Unaer(UnOp::Negativ, x) => {
            let (t, (l1, h1), _) = drucke_expr(funktion, x, ctx, info)?;
            let (lo, hi) = (h1.checked_neg().and_then(|a| l1.checked_neg().map(|b| (a, b))))
                .ok_or_else(|| {
                    refuse(
                        "CS005",
                        format!("function {funktion}: {} overflows", expr_name(e)),
                    )
                })?;
            Ok((format!("(.neg {t})"), (lo, hi), None))
        }
        ExprArt::Unaer(UnOp::BitNicht, x) => {
            let (t, (l1, h1), repr) = drucke_expr(funktion, x, ctx, info)?;
            // `~a` is `a ^ (2^B - 1)` within the storage word (`m1.rs`,
            // M137): unsigned and non-literal only, exactly like the
            // checker. A literal carries no width (its `None` IS the
            // refusal -- `~5` is a different number in every width), a
            // signed operand is C's `-x-1` (a different operation), and a
            // computed value carries no word (widths track declarations).
            let no_range = || {
                refuse(
                    "CS005",
                    format!("function {funktion}: {} has no range", expr_name(e)),
                )
            };
            let (breite, vz) = repr.ok_or_else(no_range)?;
            if vz {
                return Err(no_range());
            }
            let b = u32::from(breite);
            let voll = 1i128.checked_shl(b).ok_or_else(no_range)?;
            if !(0 <= l1 && h1 < voll) {
                return Err(no_range());
            }
            let maske = voll.checked_sub(1).ok_or_else(no_range)?;
            Ok((
                format!("(.bxor {b} {t} (.lit {maske}))"),
                (0, maske),
                Some((breite, false)),
            ))
        }
        ExprArt::Ort(o) => drucke_ort_wert(funktion, o, ctx, info),
        ExprArt::Ruf(r) => {
            let Some(ziel) = umwandlung_ziel(r) else {
                return fehlschlag(
                    funktion,
                    "CS002",
                    format!("{} has no CertExpr shape", expr_name(e)),
                )
                .map(|s| (s, (0, 0), None));
            };
            // An integer conversion (`u64(a)`, M144/M145): lossless only.
            // The checker keeps the proved range then (same value, wider
            // type), so the print is the bare argument term; a lossy
            // conversion wraps, and no `CertExpr` shape certifies a wrapped
            // value. The target representation travels for a later `~`.
            let (t, (l1, h1), _) = drucke_expr(funktion, &r.argumente[0], ctx, info)?;
            let (breite, vz) = crate::umgebung::breite_von(ziel).ok_or_else(|| {
                refuse(
                    "CS005",
                    format!("function {funktion}: {} has no range", expr_name(e)),
                )
            })?;
            let (zlo, zhi) = crate::typen::grenzen(breite, vz);
            if !(zlo <= l1 && h1 <= zhi) {
                return Err(refuse(
                    "CS005",
                    format!("function {funktion}: {} has no range", expr_name(e)),
                ));
            }
            Ok((t, (l1, h1), Some((breite, vz))))
        }
        _ => fehlschlag(
            funktion,
            "CS002",
            format!("{} has no CertExpr shape", expr_name(e)),
        )
        .map(|s| (s, (0, 0), None)),
    }
}

/// `u32::max` / `u13::min` -- the edge of the promised range, read off the
/// same words the checker folds (`grenzwort` for standard widths,
/// `zucker_bereich` for sugared ones, `m1.rs` W7): the print is the folded
/// literal, in the storage representation the checker types it at.
fn wort_grenze(o: &Ort) -> Option<(i128, (u8, bool))> {
    if o.suffixe.len() != 1 {
        return None;
    }
    let f = match o.suffixe.first() {
        Some(OrtSuffix::Feld(f)) => f.text.as_str(),
        _ => return None,
    };
    if let Some((lo, hi)) = gabbro_syntax::zucker_bereich(&o.basis.text) {
        let speicher = gabbro_syntax::zucker_speicher(&o.basis.text)
            .and_then(crate::umgebung::breite_von)?;
        let w = match f {
            "max" => hi,
            "min" => lo,
            _ => return None,
        };
        return Some((w, speicher));
    }
    let (breite, vz, w) = crate::umgebung::grenzwort(o)?;
    Some((w, (breite, vz)))
}

/// Print a place in value position: an integer local or a direct slot read
/// with a recomputable index. Pointer steps (`->`) and reads through a
/// pointer parameter have no `CertExpr` shape (a `return` through a pointer
/// prints as `retDurch` at the body level).
fn drucke_ort_wert(
    funktion: &str,
    o: &Ort,
    ctx: &Ctx,
    info: &DeclInfo,
) -> Result<(String, (i128, i128), Option<(u8, bool)>), Refusal> {
    if o.suffixe.is_empty() {
        match ctx.index_von(&o.basis.text) {
            Some((k, CtxEintrag::Ganz(_, lo, hi, repr))) => {
                Ok((format!("(.var {k})"), (*lo, *hi), *repr))
            }
            Some(_) => fehlschlag(
                funktion,
                "CS003",
                format!("place {} has no integer range", o.text()),
            )
            .map(|s| (s, (0, 0), None)),
            None => fehlschlag(
                funktion,
                "CS005",
                format!("unknown name {} in {funktion}", o.basis.text),
            )
            .map(|s| (s, (0, 0), None)),
        }
    } else if let Some((w, repr)) = wort_grenze(o) {
        Ok((format!("(.lit {w})"), (w, w), Some(repr)))
    } else if let [OrtSuffix::Feld(_), OrtSuffix::Index(idx), OrtSuffix::Feld(feld)] =
        o.suffixe.as_slice()
    {
        let tab = tabelle(info, &o.basis.text).ok_or_else(|| {
            if ctx.index_von(&o.basis.text).is_some() {
                refuse(
                    "CS002",
                    format!("pointer access {} has no CertExpr shape", o.text()),
                )
            } else {
                refuse(
                    "CS005",
                    format!("unknown table {} in {funktion}", o.basis.text),
                )
            }
        })?;
        let count = tab.count.ok_or_else(|| {
            refuse(
                "CS005",
                format!("count of table {} is not a literal", tab.name),
            )
        })?;
        let iterm = drucke_index(
            funktion,
            &format!("index of {}", o.text()),
            idx,
            ctx,
            info,
            count,
        )?;
        let (_, fr, frepr) = tab
            .felder
            .iter()
            .find(|(n, _, _)| *n == feld.text)
            .and_then(|(n, r, rp)| r.map(|rr| (n.clone(), rr, *rp)))
            .ok_or_else(|| {
                refuse(
                    "CS005",
                    format!("field {} has no integer range", o.text()),
                )
            })?;
        Ok((format!("(.slot {} {} {iterm})", tab.name, feld.text), fr, frepr))
    } else {
        fehlschlag(
            funktion,
            "CS002",
            format!("place {} has no CertExpr shape", o.text()),
        )
        .map(|s| (s, (0, 0), None))
    }
}

/// Print a boolean condition as `CertCond`. Order comparisons normalize
/// (`a > b` is `b < a`, `a != b` is `!(a == b)`); the rest must match.
fn drucke_bedingung(
    funktion: &str,
    e: &Expr,
    ctx: &Ctx,
    info: &DeclInfo,
) -> Result<String, Refusal> {
    match &e.art {
        ExprArt::Wahr => Ok(".wahr".to_string()),
        ExprArt::Falsch => Ok(".falsch".to_string()),
        ExprArt::Klammer(x) => drucke_bedingung(funktion, x, ctx, info),
        ExprArt::Ort(o) if o.suffixe.is_empty() => match ctx.index_von(&o.basis.text) {
            Some((k, CtxEintrag::Wahr(_))) => Ok(format!("(.var {k})")),
            _ => fehlschlag(
                funktion,
                "CS003",
                format!("condition {} is not a boolean local", o.text()),
            ),
        },
        ExprArt::Binaer(op, a, b) => {
            let leaned: Option<(&'static str, bool)> = match op {
                BinOp::Kleiner => Some(("lt", false)),
                BinOp::KleinerGleich => Some(("le", false)),
                BinOp::Gleich => Some(("eq", false)),
                BinOp::Ungleich => Some(("eq", true)),
                BinOp::Groesser => Some(("lt", false)),
                BinOp::GroesserGleich => Some(("le", false)),
                BinOp::Und => return drucke_verknuepfung(funktion, "und", a, b, ctx, info),
                BinOp::Oder => {
                    return drucke_verknuepfung(funktion, "oder", a, b, ctx, info)
                }
                _ => None,
            };
            let (name, negiert, links, rechts) = match leaned {
                Some((n, neg)) => match op {
                    BinOp::Groesser | BinOp::GroesserGleich => (n, neg, b, a),
                    _ => (n, neg, a, b),
                },
                None => {
                    return fehlschlag(
                        funktion,
                        "CS002",
                        format!("{} has no CertCond shape", expr_name(e)),
                    )
                }
            };
            let (ta, _, _) = drucke_expr(funktion, links, ctx, info)?;
            let (tb, _, _) = drucke_expr(funktion, rechts, ctx, info)?;
            let inner = format!("(.{name} {ta} {tb})");
            Ok(if negiert {
                format!("(.nicht {inner})")
            } else {
                inner
            })
        }
        ExprArt::Unaer(UnOp::Nicht, x) => {
            let t = drucke_bedingung(funktion, x, ctx, info)?;
            Ok(format!("(.nicht {t})"))
        }
        _ => fehlschlag(
            funktion,
            "CS002",
            format!("{} has no CertCond shape", expr_name(e)),
        ),
    }
}

fn drucke_verknuepfung(
    funktion: &str,
    name: &str,
    a: &Expr,
    b: &Expr,
    ctx: &Ctx,
    info: &DeclInfo,
) -> Result<String, Refusal> {
    let ta = drucke_bedingung(funktion, a, ctx, info)?;
    let tb = drucke_bedingung(funktion, b, ctx, info)?;
    Ok(format!("(.{name} {ta} {tb})"))
}

/// The short name of a statement form, for refusals.
fn stmt_name(s: &Stmt) -> String {
    match &s.art {
        StmtArt::Let(_) => "let".to_string(),
        StmtArt::LetSonst(_) => "let-else".to_string(),
        StmtArt::Zuweisung(z) => format!("assignment to {}", z.ziel.text()),
        StmtArt::Wenn(_) => "if".to_string(),
        StmtArt::Match(_) => "match".to_string(),
        StmtArt::Schleife(_) => "loop".to_string(),
        StmtArt::Bricht(_) => "breaking".to_string(),
        StmtArt::Narrow(_) => "narrow".to_string(),
        StmtArt::Sperrt(_) => "locks".to_string(),
        StmtArt::Observiert(_) => "observes".to_string(),
        StmtArt::Leave(_) => "leave".to_string(),
        StmtArt::Next(_) => "next".to_string(),
        StmtArt::Publish(_) => "publish".to_string(),
        StmtArt::AwaitLoad(_) => "awaits".to_string(),
        StmtArt::Exchange(_) => "exchange".to_string(),
        StmtArt::Return(_) => "return".to_string(),
        StmtArt::Ruf(r) => format!("call {}", r.ziel.text()),
        StmtArt::LibraryCall(_) => "library call".to_string(),
        StmtArt::Alloc(_) => "alloc".to_string(),
        StmtArt::ResetArena(_) => "reset arena".to_string(),
        // **Lane 257:** the commit request, named for refusals.
        StmtArt::Grow(_) => "grow".to_string(),
        // **Lane O-1:** the clone-child path, named for refusals.
        StmtArt::Child(_) => "child".to_string(),
        // **Lane 253:** the hosted thread-start statement, named for refusals.
        StmtArt::Start(_) => "start".to_string(),
    }
}

/// One falling step of a `CertSeq`: a `let` binding or a statement.
enum SeqSchritt {
    Binde { term: String, lo: i128, hi: i128 },
    Schritt { term: String },
}

/// Print a falling block as `CertSeq` (for `if` branches).
fn drucke_seq(
    funktion: &str,
    block: &Block,
    ctx: &mut Ctx,
    info: &DeclInfo,
) -> Result<String, Refusal> {
    let mut schritte: Vec<SeqSchritt> = Vec::new();
    for s in &block.anweisungen {
        match &s.art {
            StmtArt::Let(l) => {
                let (lo, hi) = claimed_range(funktion, l, info)?;
                let (t, r, _) = drucke_expr(funktion, &l.wert, ctx, info)?;
                let t = verenge(
                    funktion,
                    &format!("let {}", l.name.text),
                    t,
                    r,
                    (lo, hi),
                )?;
                // The bound local's storage is the annotation's, not the
                // value's: `let y : u8 = x` complements in eight bits.
                let repr = l.typ.as_ref().and_then(|t| wort_repr(t, info));
                ctx.eintraege
                    .push(CtxEintrag::Ganz(l.name.text.clone(), lo, hi, repr));
                schritte.push(SeqSchritt::Binde { term: t, lo, hi });
            }
            StmtArt::Zuweisung(z) => {
                match drucke_zuweisung(funktion, z, ctx, info)? {
                    StmtTerm::Alt(term) => schritte.push(SeqSchritt::Schritt { term }),
                    StmtTerm::Neu2(_) => {
                        return fehlschlag(
                            funktion,
                            "CS001",
                            format!(
                                "assignment to {} falls through nowhere printable",
                                z.ziel.text()
                            ),
                        )
                    }
                }
            }
            StmtArt::Wenn(w) => {
                schritte.push(SeqSchritt::Schritt {
                    term: drucke_wenn_seq(funktion, w, ctx, info)?,
                });
            }
            _ => {
                return fehlschlag(
                    funktion,
                    "CS001",
                    format!("{} falls through nowhere printable", stmt_name(s)),
                )
            }
        }
    }
    let mut aus = ".nil".to_string();
    for schritt in schritte.into_iter().rev() {
        aus = match schritt {
            SeqSchritt::Binde { term, lo, hi } => {
                format!("(.bind {term} {lo} {hi} {aus})")
            }
            SeqSchritt::Schritt { term } => format!("(.cons {term} [] {aus})"),
        };
    }
    Ok(aus)
}

/// The claimed range of a `let`: its annotation, never inferred. An
/// `index into T` annotation claims `(0, count - 1)`.
fn claimed_range(
    funktion: &str,
    l: &LetStmt,
    info: &DeclInfo,
) -> Result<(i128, i128), Refusal> {
    match &l.typ {
        Some(TypExpr::Index { tabelle, optional, .. }) => {
            if *optional {
                return Err(refuse(
                    "CS005",
                    format!(
                        "function {funktion}: let {} has no range annotation",
                        l.name.text
                    ),
                ));
            }
            tabelle_text(tabelle, info).map(|(_, count)| (0, count - 1)).ok_or_else(|| {
                refuse(
                    "CS005",
                    format!(
                        "function {funktion}: let {} has no range annotation",
                        l.name.text
                    ),
                )
            })
        }
        Some(t) => bereich_von_typ(t, info).ok_or_else(|| {
            refuse(
                "CS005",
                format!(
                    "function {funktion}: let {} has no range annotation",
                    l.name.text
                ),
            )
        }),
        None => Err(refuse(
            "CS005",
            format!(
                "function {funktion}: let {} has no range annotation",
                l.name.text
            ),
        )),
    }
}

/// One printed assignment: a `CertStmt` term (old layer) or a `CertStmt2`
/// term (a write through a pointer, `assignDurch`).
enum StmtTerm {
    Alt(String),
    Neu2(String),
}

/// Print an assignment as a `CertStmt`/`CertStmt2` without its resource flow.
/// A direct write prints `assignSlot`; a write through a pointer parameter
/// (`k.slots[i].f`, the `slots` path) prints `assignDurch` with the table
/// number in declaration order (the pointer proof is rebuilt from `tabNr`
/// on the Lean side, so only an `rw` pointer writes).
fn drucke_zuweisung(
    funktion: &str,
    z: &Zuweisung,
    ctx: &Ctx,
    info: &DeclInfo,
) -> Result<StmtTerm, Refusal> {
    if z.op != ZuwOp::Setzt {
        let op = match z.op {
            ZuwOp::Setzt => "=",
            ZuwOp::Plus => "+=",
            ZuwOp::Minus => "-=",
            ZuwOp::Und => "&=",
            ZuwOp::Oder => "|=",
        };
        return Err(refuse(
            "CS001",
            format!("assignment {op} to {} has no CertStmt shape", z.ziel.text()),
        ));
    }
    let o = &z.ziel;
    if o.suffixe.is_empty() {
        let (k, lo, hi) = match ctx.index_von(&o.basis.text) {
            Some((k, CtxEintrag::Ganz(_, lo, hi, _))) => (k, *lo, *hi),
            _ => {
                return Err(refuse(
                    "CS003",
                    format!("assignment to {} is not an integer local", o.text()),
                ))
            }
        };
        let (t, r, _) = drucke_expr(funktion, &z.wert, ctx, info)?;
        let t = verenge(
            funktion,
            &format!("assignment to {}", o.text()),
            t,
            r,
            (lo, hi),
        )?;
        return Ok(StmtTerm::Alt(format!("(.assignVar {k} {lo} {hi} {t})")));
    }
    if let [OrtSuffix::Feld(slots), OrtSuffix::Index(idx), OrtSuffix::Feld(feld)] =
        o.suffixe.as_slice()
    {
        if slots.text != "slots" {
            return Err(refuse(
                "CS002",
                format!("assignment to {} has no CertStmt shape", o.text()),
            ));
        }
        if let Some(tab) = tabelle(info, &o.basis.text) {
            let count = tab.count.ok_or_else(|| {
                refuse(
                    "CS005",
                    format!("count of table {} is not a literal", tab.name),
                )
            })?;
            let iterm = drucke_index(
                funktion,
                &format!("index of {}", o.text()),
                idx,
                ctx,
                info,
                count,
            )?;
            let (fr, _) = tab
                .felder
                .iter()
                .find(|(n, _, _)| *n == feld.text)
                .and_then(|(_, r, rp)| r.map(|rr| (rr, *rp)))
                .ok_or_else(|| {
                    refuse("CS005", format!("field {} has no integer range", o.text()))
                })?;
            let (t, r, _) = drucke_expr(funktion, &z.wert, ctx, info)?;
            let t = verenge(
                funktion,
                &format!("value of {}", o.text()),
                t,
                r,
                fr,
            )?;
            return Ok(StmtTerm::Alt(format!(
                "(.assignSlot {} {} {iterm} {t})",
                tab.name, feld.text,
            )));
        }
        let (ti, rw) = match ctx.index_von(&o.basis.text) {
            Some((_, CtxEintrag::Zeiger(_, ti, rw))) => (*ti, *rw),
            Some(_) => {
                return Err(refuse(
                    "CS002",
                    format!("pointer write {} has no CertStmt shape", o.text()),
                ))
            }
            None => {
                return Err(refuse(
                    "CS005",
                    format!("unknown table {} in {funktion}", o.basis.text),
                ))
            }
        };
        if !rw {
            return Err(refuse(
                "CS002",
                format!(
                    "write through read-only pointer {} has no CertStmt shape",
                    o.text()
                ),
            ));
        }
        let tab = &info.tabellen[ti];
        let count = tab.count.ok_or_else(|| {
            refuse(
                "CS005",
                format!("count of table {} is not a literal", tab.name),
            )
        })?;
        let iterm = drucke_index(
            funktion,
            &format!("index of {}", o.text()),
            idx,
            ctx,
            info,
            count,
        )?;
        let (fr, _) = tab
            .felder
            .iter()
            .find(|(n, _, _)| *n == feld.text)
            .and_then(|(_, r, rp)| r.map(|rr| (rr, *rp)))
            .ok_or_else(|| {
                refuse("CS005", format!("field {} has no integer range", o.text()))
            })?;
        let (t, r, _) = drucke_expr(funktion, &z.wert, ctx, info)?;
        let t = verenge(
            funktion,
            &format!("value of {}", o.text()),
            t,
            r,
            fr,
        )?;
        return Ok(StmtTerm::Neu2(format!(
            "(.assignDurch {} {} {ti} true {iterm} {t})",
            tab.name, feld.text,
        )));
    }
    Err(refuse(
        "CS002",
        format!("assignment to {} has no CertStmt shape", o.text()),
    ))
}

/// Print an `if` with falling branches as a `CertStmt` without its flow.
fn drucke_wenn_seq(
    funktion: &str,
    w: &WennStmt,
    ctx: &mut Ctx,
    info: &DeclInfo,
) -> Result<String, Refusal> {
    if w.zweige.len() != 1 {
        return fehlschlag(
            funktion,
            "CS001",
            format!("if with {} branches has no CertStmt shape", w.zweige.len()),
        );
    }
    let (bed, dann) = &w.zweige[0];
    let c = drucke_bedingung(funktion, bed, ctx, info)?;
    let vor = ctx.eintraege.len();
    let t = drucke_seq(funktion, dann, ctx, info)?;
    ctx.eintraege.truncate(vor);
    let e = match &w.sonst {
        Some(s) => {
            let s = drucke_seq(funktion, s, ctx, info)?;
            ctx.eintraege.truncate(vor);
            s
        }
        None => ".nil".to_string(),
    };
    Ok(format!("(.ite {c} {t} {e})"))
}

/// Print a function body as a `CertEnd` (wrapped in `liftE` by the caller).
fn drucke_ende(
    funktion: &str,
    stmts: &[Stmt],
    ctx: &mut Ctx,
    info: &DeclInfo,
    ergebnis: &Option<TypExpr>,
) -> Result<String, Refusal> {
    let Some((s, rest)) = stmts.split_first() else {
        match ergebnis {
            None => return Ok(".ret".to_string()),
            Some(_) => {
                return fehlschlag(
                    funktion,
                    "CS005",
                    "body falls off the end with a result type".to_string(),
                )
            }
        }
    };
    match &s.art {
        StmtArt::Return(r) => {
            if !rest.is_empty() {
                return fehlschlag(
                    funktion,
                    "CS001",
                    "statements after return have no CertEnd shape".to_string(),
                );
            }
            match r {
                None => match ergebnis {
                    None => Ok(".ret".to_string()),
                    Some(_) => fehlschlag(
                        funktion,
                        "CS005",
                        "bare return with a result type".to_string(),
                    ),
                },
                Some(e) => {
                    let (lo, hi) = ergebnis
                        .as_ref()
                        .and_then(|t| bereich_von_typ(t, info))
                        .ok_or_else(|| {
                            refuse(
                                "CS005",
                                format!(
                                    "function {funktion}: result type has no integer range"
                                ),
                            )
                        })?;
                    let (t, r, _) = drucke_expr(funktion, e, ctx, info)?;
                    let t = verenge(funktion, "return", t, r, (lo, hi))?;
                    Ok(format!("(.retWert {t} {lo} {hi})"))
                }
            }
        }
        StmtArt::Let(l) => {
            let (lo, hi) = claimed_range(funktion, l, info)?;
            if !matches!(
                &l.typ,
                Some(TypExpr::Int(_)) | Some(TypExpr::Pfad(_)) | Some(TypExpr::Index { .. })
            ) {
                return Err(refuse(
                    "CS001",
                    format!(
                        "function {funktion}: let {} binds no integer",
                        l.name.text
                    ),
                ));
            }
            let (t, r, _) = drucke_expr(funktion, &l.wert, ctx, info)?;
            let t = verenge(
                funktion,
                &format!("let {}", l.name.text),
                t,
                r,
                (lo, hi),
            )?;
            let repr = l.typ.as_ref().and_then(|t| wort_repr(t, info));
            ctx.eintraege
                .push(CtxEintrag::Ganz(l.name.text.clone(), lo, hi, repr));
            let weiter = drucke_ende(funktion, rest, ctx, info, ergebnis)?;
            Ok(format!("(.bind {t} {lo} {hi} {weiter})"))
        }
        StmtArt::Zuweisung(z) => {
            let StmtTerm::Alt(t) = drucke_zuweisung(funktion, z, ctx, info)? else {
                return fehlschlag(
                    funktion,
                    "CS001",
                    format!(
                        "assignment to {} falls through nowhere printable",
                        z.ziel.text()
                    ),
                );
            };
            let weiter = drucke_ende(funktion, rest, ctx, info, ergebnis)?;
            Ok(format!("(.cons {t} [] {weiter})"))
        }
        StmtArt::Wenn(w) => {
            let t = drucke_wenn_seq(funktion, w, ctx, info)?;
            let weiter = drucke_ende(funktion, rest, ctx, info, ergebnis)?;
            Ok(format!("(.cons {t} [] {weiter})"))
        }
        StmtArt::Ruf(r) => match &r.ziel {
            CallTarget::Path(p) if r.argumente.is_empty() => Err(refuse(
                "CS004",
                format!(
                    "function {funktion}: call {} needs RufPasst as proof",
                    p.text()
                ),
            )),
            _ => Err(refuse(
                "CS001",
                format!(
                    "function {funktion}: {} has no printable CertStmt shape",
                    stmt_name(s)
                ),
            )),
        },
        _ => Err(refuse(
            "CS001",
            format!(
                "function {funktion}: {} has no printable CertStmt shape",
                stmt_name(s)
            ),
        )),
    }
}

/// Whether a body needs the `CertEnd104` layer: a call with arguments, a
/// write through a pointer parameter, or a return through one. Anything
/// inside an `if` branch stays on the old layer (and refuses there).
fn benutzt_neu(f: &FnDecl, info: &DeclInfo) -> bool {
    let FnRumpf::Block(b) = &f.rumpf else {
        return false;
    };
    let ptrs: Vec<String> = f
        .parameter
        .iter()
        .filter(|p| {
            matches!(
                param_eintrag(&p.name.text, &p.typ, info),
                CtxEintrag::Zeiger(..)
            )
        })
        .map(|p| p.name.text.clone())
        .collect();
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Ruf(r) => {
                if matches!(&r.ziel, CallTarget::Path(_)) && !r.argumente.is_empty() {
                    return true;
                }
            }
            StmtArt::Zuweisung(z) => {
                if ptrs.contains(&z.ziel.basis.text) && z.ziel.suffixe.len() == 3 {
                    return true;
                }
            }
            StmtArt::Return(e) => {
                if let Some(x) = e {
                    let mut inner = x;
                    while let ExprArt::Klammer(y) = &inner.art {
                        inner = y;
                    }
                    if let ExprArt::Ort(o) = &inner.art {
                        if ptrs.contains(&o.basis.text) && !o.suffixe.is_empty() {
                            return true;
                        }
                    }
                }
                break;
            }
            _ => {}
        }
    }
    false
}

/// A call with arguments as `consCall` data: the callee name and count.
/// Every argument must name a bare parameter place (checked here); the
/// elaborated `Args` travel as proof, filled at paste beside `?hp`.
fn drucke_ruf_mit_args(
    funktion: &str,
    r: &Ruf,
    ctx: &Ctx,
    info: &DeclInfo,
) -> Result<(String, usize), Refusal> {
    match &r.ziel {
        CallTarget::Place(o) => Err(refuse(
            "CS001",
            format!("indirect call {} has no printable CertStmt shape", o.text()),
        )),
        CallTarget::Path(p) => {
            let (name, nargs) = callee_nargs(info, &r.ziel).ok_or_else(|| {
                refuse(
                    "CS005",
                    format!("function {funktion}: callee {} is unknown", p.text()),
                )
            })?;
            if r.argumente.len() != nargs {
                return Err(refuse(
                    "CS005",
                    format!(
                        "function {funktion}: call {name} takes {} arguments, not {}",
                        nargs,
                        r.argumente.len()
                    ),
                ));
            }
            for a in &r.argumente {
                match &a.art {
                    ExprArt::Ort(o)
                        if o.suffixe.is_empty()
                            && ctx.index_von(&o.basis.text).is_some() => {}
                    _ => {
                        return Err(refuse(
                            "CS002",
                            format!(
                                "call argument {} has no printed shape",
                                expr_name(a)
                            ),
                        ))
                    }
                }
            }
            Ok((name, nargs))
        }
    }
}

/// A `return` through a pointer parameter as `retDurch` data: the table,
/// field, table number and index term. The pointer proof is rebuilt from
/// the parameter at paste; the field-type equation recomputes in Lean.
/// Returns `None` when the base names a table (a direct read, which the
/// `retWert` path prints).
fn drucke_rueck_durch(
    funktion: &str,
    o: &Ort,
    ctx: &Ctx,
    info: &DeclInfo,
    ergebnis: &Option<TypExpr>,
) -> Result<Option<String>, Refusal> {
    if tabelle(info, &o.basis.text).is_some() {
        return Ok(None);
    }
    if ergebnis.is_none() {
        return Err(refuse(
            "CS005",
            format!(
                "function {funktion}: return {} has no result type",
                o.text()
            ),
        ));
    }
    let [OrtSuffix::Feld(slots), OrtSuffix::Index(idx), OrtSuffix::Feld(feld)] =
        o.suffixe.as_slice()
    else {
        return Err(refuse(
            "CS002",
            format!("place {} has no CertExpr shape", o.text()),
        ));
    };
    if slots.text != "slots" {
        return Err(refuse(
            "CS002",
            format!("place {} has no CertExpr shape", o.text()),
        ));
    }
    let ti = match ctx.index_von(&o.basis.text) {
        Some((_, CtxEintrag::Zeiger(_, ti, _))) => *ti,
        Some(_) => {
            return Err(refuse(
                "CS002",
                format!("place {} has no CertExpr shape", o.text()),
            ))
        }
        None => {
            return Err(refuse(
                "CS005",
                format!("unknown name {} in {funktion}", o.basis.text),
            ))
        }
    };
    let tab = &info.tabellen[ti];
    if !tab.felder.iter().any(|(n, _, _)| *n == feld.text) {
        return Err(refuse(
            "CS005",
            format!("unknown field {} in {funktion}", o.text()),
        ));
    }
    let count = tab.count.ok_or_else(|| {
        refuse(
            "CS005",
            format!("count of table {} is not a literal", tab.name),
        )
    })?;
    let iterm = drucke_index(
        funktion,
        &format!("index of {}", o.text()),
        idx,
        ctx,
        info,
        count,
    )?;
    Ok(Some(format!(
        "(.retDurch {} {} {ti} {iterm})",
        tab.name, feld.text,
    )))
}

/// Print a function body as a `CertEnd104`: the old shapes travel through
/// `cons1`/`bind104`/terminals, pointer writes through `cons2`
/// (`assignDurch`), calls with arguments through `consCall` (the `RufPasst`
/// prints as `?hp`, filled at paste), and a return through a pointer as
/// `retDurch`.
fn drucke_ende104(
    funktion: &str,
    stmts: &[Stmt],
    ctx: &mut Ctx,
    info: &DeclInfo,
    ergebnis: &Option<TypExpr>,
) -> Result<String, Refusal> {
    let Some((s, rest)) = stmts.split_first() else {
        match ergebnis {
            None => return Ok(".ret".to_string()),
            Some(_) => {
                return fehlschlag(
                    funktion,
                    "CS005",
                    "body falls off the end with a result type".to_string(),
                )
            }
        }
    };
    match &s.art {
        StmtArt::Return(r) => {
            if !rest.is_empty() {
                return fehlschlag(
                    funktion,
                    "CS001",
                    "statements after return have no CertEnd shape".to_string(),
                );
            }
            match r {
                None => match ergebnis {
                    None => Ok(".ret".to_string()),
                    Some(_) => fehlschlag(
                        funktion,
                        "CS005",
                        "bare return with a result type".to_string(),
                    ),
                },
                Some(e) => {
                    let mut inner = e;
                    while let ExprArt::Klammer(y) = &inner.art {
                        inner = y;
                    }
                    if let ExprArt::Ort(o) = &inner.art {
                        if let Some(t) =
                            drucke_rueck_durch(funktion, o, ctx, info, ergebnis)?
                        {
                            return Ok(t);
                        }
                    }
                    let (lo, hi) = ergebnis
                        .as_ref()
                        .and_then(|t| bereich_von_typ(t, info))
                        .ok_or_else(|| {
                            refuse(
                                "CS005",
                                format!(
                                    "function {funktion}: result type has no integer range"
                                ),
                            )
                        })?;
                    let (t, rr, _) = drucke_expr(funktion, e, ctx, info)?;
                    let t = verenge(funktion, "return", t, rr, (lo, hi))?;
                    Ok(format!("(.retWert {t} {lo} {hi})"))
                }
            }
        }
        StmtArt::Let(l) => {
            let (lo, hi) = claimed_range(funktion, l, info)?;
            if !matches!(
                &l.typ,
                Some(TypExpr::Int(_)) | Some(TypExpr::Pfad(_)) | Some(TypExpr::Index { .. })
            ) {
                return Err(refuse(
                    "CS001",
                    format!(
                        "function {funktion}: let {} binds no integer",
                        l.name.text
                    ),
                ));
            }
            let (t, rr, _) = drucke_expr(funktion, &l.wert, ctx, info)?;
            let t = verenge(
                funktion,
                &format!("let {}", l.name.text),
                t,
                rr,
                (lo, hi),
            )?;
            let repr = l.typ.as_ref().and_then(|t| wort_repr(t, info));
            ctx.eintraege
                .push(CtxEintrag::Ganz(l.name.text.clone(), lo, hi, repr));
            let weiter = drucke_ende104(funktion, rest, ctx, info, ergebnis)?;
            Ok(format!("(.bind {t} {lo} {hi} {weiter})"))
        }
        StmtArt::Zuweisung(z) => {
            match drucke_zuweisung(funktion, z, ctx, info)? {
                StmtTerm::Alt(t) => {
                    let weiter = drucke_ende104(funktion, rest, ctx, info, ergebnis)?;
                    Ok(format!("(.cons1 {t} [] {weiter})"))
                }
                StmtTerm::Neu2(t) => {
                    let weiter = drucke_ende104(funktion, rest, ctx, info, ergebnis)?;
                    Ok(format!("(.cons2 {t} [] {weiter})"))
                }
            }
        }
        StmtArt::Wenn(w) => {
            let t = drucke_wenn_seq(funktion, w, ctx, info)?;
            let weiter = drucke_ende104(funktion, rest, ctx, info, ergebnis)?;
            Ok(format!("(.cons1 {t} [] {weiter})"))
        }
        StmtArt::Ruf(r) => match &r.ziel {
            CallTarget::Path(p) if r.argumente.is_empty() => Err(refuse(
                "CS004",
                format!(
                    "function {funktion}: call {} needs RufPasst as proof",
                    p.text()
                ),
            )),
            _ => {
                let (name, nargs) = drucke_ruf_mit_args(funktion, r, ctx, info)?;
                let weiter = drucke_ende104(funktion, rest, ctx, info, ergebnis)?;
                Ok(format!("(.consCall {name} {nargs} [] ?hp {weiter})"))
            }
        },
        _ => Err(refuse(
            "CS001",
            format!(
                "function {funktion}: {} has no printable CertStmt shape",
                stmt_name(s)
            ),
        )),
    }
}

/// Print the statement certificate for one checked function body.
pub fn zeige_rumpf(f: &FnDecl, info: &DeclInfo) -> BodyCert {
    let funktion = f.name.text.clone();
    let FnRumpf::Block(b) = &f.rumpf else {
        return BodyCert::Abgewiesen {
            weigerung: refuse(
                "CS001",
                format!("function {funktion} has no block body"),
            ),
        };
    };
    let mut ctx = Ctx {
        eintraege: Vec::new(),
    };
    // Head-first: the FIRST parameter is de Bruijn 0 (the `gCtx` convention
    // of `lean-g`), so parameters push in reverse.
    for p in f.parameter.iter().rev() {
        ctx.eintraege
            .push(param_eintrag(&p.name.text, &p.typ, info));
    }
    if benutzt_neu(f, info) {
        // A call with arguments, a write through a pointer, or a return
        // through one: the `CertEnd104` layer.
        match drucke_ende104(&funktion, &b.anweisungen, &mut ctx, info, &f.ergebnis) {
            Ok(lean) => BodyCert::Gedruckt { lean, neu: true },
            Err(weigerung) => BodyCert::Abgewiesen { weigerung },
        }
    } else {
        match drucke_ende(&funktion, &b.anweisungen, &mut ctx, info, &f.ergebnis) {
            Ok(ende) => BodyCert::Gedruckt {
                lean: format!("(.liftE {ende})"),
                neu: false,
            },
            Err(weigerung) => BodyCert::Abgewiesen { weigerung },
        }
    }
}

/// Print the statement certificate of one named function: the same entry
/// the command uses, queryable per function (and from the test crate).
pub fn zeuge_funktion(baum: &Programm, name: &str) -> Option<BodyCert> {
    let info = sammle(baum);
    let mut gef = None;
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Funktion(f) = &item.art {
            if f.name.text == name && gef.is_none() {
                gef = Some(zeige_rumpf(f, &info));
            }
        }
    });
    gef
}

/// The per-function section of `gabbro certificate`: one `CertEnd2` (or
/// `CertEnd104`) term per block body, or a named refusal for every body
/// outside the fragment.
pub fn zeige(baum: &Programm) -> String {
    let info = sammle(baum);
    let mut aus = String::new();
    aus.push_str("\nS  STATEMENT CERTIFICATES (transfer printer)\n");
    let mut n = 0;
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Funktion(f) = &item.art {
            if !matches!(f.rumpf, FnRumpf::Block(_)) {
                return;
            }
            n += 1;
            match zeige_rumpf(f, &info) {
                BodyCert::Gedruckt { lean, neu } => {
                    let schicht = if neu { "CertEnd104" } else { "CertEnd2" };
                    aus.push_str(&format!(
                        "   function {}: {schicht} term:\n     {lean}\n",
                        f.name.text
                    ));
                }
                BodyCert::Abgewiesen { weigerung } => {
                    aus.push_str(&format!(
                        "   function {}: REFUSED {}: {}\n",
                        f.name.text, weigerung.code, weigerung.grund
                    ));
                }
            }
        }
    });
    if n == 0 {
        aus.push_str("   no block bodies.\n");
    }
    aus
}

#[cfg(test)]
mod tests {
    use super::*;

    fn programm(quelle: &str) -> Programm {
        let (baum, absagen) = gabbro_syntax::lies("probe.gab", quelle);
        assert_eq!(
            absagen.fehler_zahl(),
            0,
            "the probe does not parse: {}",
            absagen.zeige(quelle)
        );
        baum
    }

    fn funktion(baum: &Programm) -> (FnDecl, DeclInfo) {
        let info = sammle(baum);
        let mut gef = None;
        crate::fuer_jedes_item(baum, &mut |item| {
            if let ItemArt::Funktion(f) = &item.art {
                if gef.is_none() {
                    gef = Some(f.clone());
                }
            }
        });
        (gef.expect("one function"), info)
    }

    #[test]
    fn bare_return_prints_ret() {
        let baum = programm(
            "module m { impl fn f() effects { pure } costs <= 1 ops { return; } }",
        );
        let (f, info) = funktion(&baum);
        let BodyCert::Gedruckt { lean, .. } = zeige_rumpf(&f, &info) else {
            panic!("a bare return prints");
        };
        assert_eq!(lean, "(.liftE .ret)");
    }
}
