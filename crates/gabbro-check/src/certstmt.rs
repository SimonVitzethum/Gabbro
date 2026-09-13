//! Statement certificates from Rust (T1 transfer printer, lane 153).
//!
//! The Lean side holds statement/block certificates with decidable validity
//! (`ZeugnisStmt.lean`: `CertStmt`/`CertSeq`/`CertEnd`, `ZeugnisStmt2.lean`:
//! `CertStmt2`/`CertSeq2`/`CertEnd2`). The Rust side printed only expression
//! certificates (`certemit.rs`). This module prints, per function body, a Lean
//! term of the `CertEnd`/`CertEnd2` shape for the forms both Lean files cover,
//! and REFUSES by name every body with a form outside them.
//!
//! ## Fragment boundary (measured, not hoped)
//!
//! Printable today: `return;`, `return <int-expr>;`, `let x : <range> = ...;`,
//! direct table writes with literal indices, integer locals, `if` with a
//! printable condition and falling branches. Everything else is a named
//! refusal, never a truncation:
//!
//! * `CS001` statement form with no printed `CertStmt`/`CertStmt2` shape
//!   (calls with arguments, indirect calls, matches, loops, `let-else`,
//!   `leave`/`next` outside loops, register/mark/float/global steps, ...)
//! * `CS002` expression with no `CertExpr` shape (pointer reads, bitwise and
//!   shift operators, division, calls, quantifiers, ...)
//! * `CS003` index or variable with no recomputable range (non-literal slot
//!   indices, reads of non-integer locals)
//! * `CS004` nullary direct call: the `CertStmt.call` shape exists but its
//!   `RufPasst` travels as proof (R-3), which plain data cannot carry
//! * `CS005` unresolvable name, count, rank or range for the claim (unknown
//!   table, non-literal `count`, result type with no integer range, ...)
//!
//! ## Conventions of the printed term
//!
//! Table, field and function names print as written in surface syntax; every
//! resource list prints as `[]` (the Lean side recomputes validity over it,
//! so a wrong flow fails `decide` loudly instead of passing silently).
//! Counts, field ranges and alias ranges resolve from literal declarations
//! only; anything else is `CS005`. Values print under `wide` exactly where
//! the checker elaborates `weiter` (a contained range narrows to the claim,
//! an exact one prints bare); an uncontained value is refused, since the
//! checker would reject it as a type error. The printed term is linked to
//! the checked body by construction of this printer only; term identity
//! (`print (elab x) = x`) is proved nowhere yet (the `ZeugnisStmt2.lean`
//! CUTS booking).

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
    Gedruckt { lean: String },
    /// The body has a form outside the covered fragment.
    Abgewiesen { weigerung: Refusal },
}

/// One table as the printer sees it: literal `count`, literal field ranges.
struct TableInfo {
    name: String,
    count: Option<i128>,
    felder: Vec<(String, Option<(i128, i128)>)>,
}

/// What the printer resolves from the declarations: tables and int aliases.
struct DeclInfo {
    tabellen: Vec<TableInfo>,
    alias: Vec<(String, (i128, i128))>,
}

/// One context entry: an integer or boolean local, or something else.
enum CtxEintrag {
    Ganz(String, i128, i128),
    Wahr(String),
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
            CtxEintrag::Ganz(n, _, _) | CtxEintrag::Wahr(n) | CtxEintrag::Sonst(n) => {
                n == name
            }
        })?;
        Some((self.eintraege.len() - 1 - pos, &self.eintraege[pos]))
    }
}

/// A literal integer value of an expression, or `None` where it is not one.
fn als_zahl(e: &Expr) -> Option<u128> {
    match &e.art {
        ExprArt::Zahl(n) => Some(*n),
        ExprArt::Klammer(x) => als_zahl(x),
        _ => None,
    }
}

/// An integer range spelled in a type: a literal `in lo .. hi` or an alias.
fn bereich_von_typ(t: &TypExpr, info: &DeclInfo) -> Option<(i128, i128)> {
    match t {
        TypExpr::Int(i) => {
            let b = i.bereich.as_ref()?;
            let lo = als_zahl(&b.von).and_then(|n| i128::try_from(n).ok())?;
            let hi = als_zahl(&b.bis).and_then(|n| i128::try_from(n).ok())?;
            Some((lo, if b.exklusiv { hi - 1 } else { hi }))
        }
        TypExpr::Pfad(p) => {
            let name = p.teile.last()?.text.clone();
            info.alias.iter().find(|(n, _)| *n == name).map(|(_, r)| *r)
        }
        _ => None,
    }
}

/// Collect tables (literal counts and field ranges) and int aliases.
fn sammle(baum: &Programm) -> DeclInfo {
    let mut info = DeclInfo {
        tabellen: Vec::new(),
        alias: Vec::new(),
    };
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Typ(t) => {
            if let Some(rumpf) = &t.rumpf {
                if let Some(r) = bereich_von_typ(rumpf, &info) {
                    info.alias.push((t.name.text.clone(), r));
                }
            }
        }
        ItemArt::Tabelle(t) => {
            let count = t
                .kapazitaet
                .as_ref()
                .and_then(als_zahl)
                .and_then(|n| i128::try_from(n).ok());
            let mut felder = Vec::new();
            if let Some(slot) = &t.slot {
                for f in &slot.felder {
                    let r = match &f.typ {
                        SlotTyp::Typ(te) => bereich_von_typ(te, &info),
                        SlotTyp::Wrapping(_) => None,
                    };
                    felder.push((f.name.text.clone(), r));
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

fn tabelle<'a>(info: &'a DeclInfo, name: &str) -> Option<&'a TableInfo> {
    info.tabellen.iter().find(|t| t.name == name)
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

/// Print an integer expression as `CertExpr` with its recomputed range.
///
/// The range mirrors `certRange` (`Zeugnis.lean`): unbounded `Int`
/// arithmetic would lie on overflow, so checked `i128` answers `CS005`.
fn drucke_expr(
    funktion: &str,
    e: &Expr,
    ctx: &Ctx,
    info: &DeclInfo,
) -> Result<(String, (i128, i128)), Refusal> {
    match &e.art {
        ExprArt::Zahl(n) => {
            let v = i128::try_from(*n).map_err(|_| {
                refuse("CS005", format!("function {funktion}: literal {n} too large"))
            })?;
            Ok((format!("(.lit {v})"), (v, v)))
        }
        ExprArt::Klammer(x) => drucke_expr(funktion, x, ctx, info),
        ExprArt::Binaer(op, a, b) => {
            let (ta, (l1, h1)) = drucke_expr(funktion, a, ctx, info)?;
            let (tb, (l2, h2)) = drucke_expr(funktion, b, ctx, info)?;
            // The bound mirrors `certRange` (`Zeugnis.lean`); `None` is
            // overflow (or an uncovered operator), never a guess.
            let ecken: Option<((i128, i128), &'static str)> = match op {
                BinOp::Plus => l1
                    .checked_add(l2)
                    .and_then(|lo| h1.checked_add(h2).map(|hi| (lo, hi)))
                    .map(|r| (r, "add")),
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
                    .map(|s| (s, (0, 0)));
                }
            };
            let ((lo, hi), name) = ecken.ok_or_else(|| {
                refuse(
                    "CS005",
                    format!("function {funktion}: {} overflows", expr_name(e)),
                )
            })?;
            Ok((format!("(.{name} {ta} {tb})"), (lo, hi)))
        }
        ExprArt::Unaer(UnOp::Negativ, x) => {
            let (t, (l1, h1)) = drucke_expr(funktion, x, ctx, info)?;
            let (lo, hi) = (h1.checked_neg().and_then(|a| l1.checked_neg().map(|b| (a, b))))
                .ok_or_else(|| {
                    refuse(
                        "CS005",
                        format!("function {funktion}: {} overflows", expr_name(e)),
                    )
                })?;
            Ok((format!("(.neg {t})"), (lo, hi)))
        }
        ExprArt::Ort(o) => drucke_ort_wert(funktion, o, ctx, info),
        _ => fehlschlag(
            funktion,
            "CS002",
            format!("{} has no CertExpr shape", expr_name(e)),
        )
        .map(|s| (s, (0, 0))),
    }
}

/// Print a place in value position: an integer local or a direct slot read
/// with a literal index. Pointer steps (`->`) have no `CertExpr` shape.
fn drucke_ort_wert(
    funktion: &str,
    o: &Ort,
    ctx: &Ctx,
    info: &DeclInfo,
) -> Result<(String, (i128, i128)), Refusal> {
    if o.suffixe.is_empty() {
        match ctx.index_von(&o.basis.text) {
            Some((k, CtxEintrag::Ganz(_, lo, hi))) => {
                Ok((format!("(.var {k})"), (*lo, *hi)))
            }
            Some(_) => fehlschlag(
                funktion,
                "CS003",
                format!("place {} has no integer range", o.text()),
            )
            .map(|s| (s, (0, 0))),
            None => fehlschlag(
                funktion,
                "CS005",
                format!("unknown name {} in {funktion}", o.basis.text),
            )
            .map(|s| (s, (0, 0))),
        }
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
        let k = als_zahl(idx).ok_or_else(|| {
            refuse(
                "CS003",
                format!("index of {} is not a literal", o.text()),
            )
        })?;
        let kv = i128::try_from(k).map_err(|_| {
            refuse(
                "CS005",
                format!("function {funktion}: index {k} too large"),
            )
        })?;
        if kv < 0 || kv >= count {
            return Err(refuse(
                "CS005",
                format!("index {kv} of {} is outside count {count}", o.text()),
            ));
        }
        let (_, fr) = tab
            .felder
            .iter()
            .find(|(n, _)| *n == feld.text)
            .and_then(|(n, r)| r.map(|rr| (n.clone(), rr)))
            .ok_or_else(|| {
                refuse(
                    "CS005",
                    format!("field {} has no integer range", o.text()),
                )
            })?;
        Ok((
            format!(
                "(.slot {} {} (.wide 0 {} (.lit {kv})))",
                tab.name,
                feld.text,
                count - 1
            ),
            fr,
        ))
    } else {
        fehlschlag(
            funktion,
            "CS002",
            format!("place {} has no CertExpr shape", o.text()),
        )
        .map(|s| (s, (0, 0)))
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
            let (ta, _) = drucke_expr(funktion, links, ctx, info)?;
            let (tb, _) = drucke_expr(funktion, rechts, ctx, info)?;
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
                let (t, r) = drucke_expr(funktion, &l.wert, ctx, info)?;
                let t = verenge(
                    funktion,
                    &format!("let {}", l.name.text),
                    t,
                    r,
                    (lo, hi),
                )?;
                ctx.eintraege.push(CtxEintrag::Ganz(l.name.text.clone(), lo, hi));
                schritte.push(SeqSchritt::Binde { term: t, lo, hi });
            }
            StmtArt::Zuweisung(z) => {
                schritte.push(SeqSchritt::Schritt {
                    term: drucke_zuweisung(funktion, z, ctx, info)?,
                });
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

/// The claimed range of a `let`: its annotation, never inferred.
fn claimed_range(
    funktion: &str,
    l: &LetStmt,
    info: &DeclInfo,
) -> Result<(i128, i128), Refusal> {
    match &l.typ {
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

/// Print an assignment as a `CertStmt` without its resource flow.
fn drucke_zuweisung(
    funktion: &str,
    z: &Zuweisung,
    ctx: &Ctx,
    info: &DeclInfo,
) -> Result<String, Refusal> {
    if z.op != ZuwOp::Setzt {
        let op = match z.op {
            ZuwOp::Setzt => "=",
            ZuwOp::Plus => "+=",
            ZuwOp::Minus => "-=",
            ZuwOp::Und => "&=",
            ZuwOp::Oder => "|=",
        };
        return fehlschlag(
            funktion,
            "CS001",
            format!("assignment {op} to {} has no CertStmt shape", z.ziel.text()),
        );
    }
    let o = &z.ziel;
    if o.suffixe.is_empty() {
        let (k, lo, hi) = match ctx.index_von(&o.basis.text) {
            Some((k, CtxEintrag::Ganz(_, lo, hi))) => (k, *lo, *hi),
            _ => {
                return fehlschlag(
                    funktion,
                    "CS003",
                    format!("assignment to {} is not an integer local", o.text()),
                )
            }
        };
        let (t, r) = drucke_expr(funktion, &z.wert, ctx, info)?;
        let t = verenge(
            funktion,
            &format!("assignment to {}", o.text()),
            t,
            r,
            (lo, hi),
        )?;
        return Ok(format!("(.assignVar {k} {lo} {hi} {t})"));
    }
    if let [OrtSuffix::Feld(_), OrtSuffix::Index(idx), OrtSuffix::Feld(feld)] =
        o.suffixe.as_slice()
    {
        let tab = tabelle(info, &o.basis.text).ok_or_else(|| {
            if ctx.index_von(&o.basis.text).is_some() {
                refuse(
                    "CS002",
                    format!("pointer write {} has no CertStmt shape", o.text()),
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
        let k = als_zahl(idx).ok_or_else(|| {
            refuse(
                "CS003",
                format!("index of {} is not a literal", o.text()),
            )
        })?;
        let kv = i128::try_from(k).map_err(|_| {
            refuse("CS005", format!("function {funktion}: index {k} too large"))
        })?;
        if kv < 0 || kv >= count {
            return Err(refuse(
                "CS005",
                format!("index {kv} of {} is outside count {count}", o.text()),
            ));
        }
        let fr = tab
            .felder
            .iter()
            .find(|(n, _)| *n == feld.text)
            .and_then(|(_, r)| *r)
            .ok_or_else(|| {
                refuse("CS005", format!("field {} has no integer range", o.text()))
            })?;
        let (t, r) = drucke_expr(funktion, &z.wert, ctx, info)?;
        let t = verenge(
            funktion,
            &format!("value of {}", o.text()),
            t,
            r,
            fr,
        )?;
        return Ok(format!(
            "(.assignSlot {} {} (.wide 0 {} (.lit {kv})) {t})",
            tab.name,
            feld.text,
            count - 1
        ));
    }
    fehlschlag(
        funktion,
        "CS002",
        format!("assignment to {} has no CertStmt shape", o.text()),
    )
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
                    let (t, r) = drucke_expr(funktion, e, ctx, info)?;
                    let t = verenge(funktion, "return", t, r, (lo, hi))?;
                    Ok(format!("(.retWert {t} {lo} {hi})"))
                }
            }
        }
        StmtArt::Let(l) => {
            let (lo, hi) = match &l.typ {
                Some(t) => bereich_von_typ(t, info).ok_or_else(|| {
                    refuse(
                        "CS005",
                        format!(
                            "function {funktion}: let {} has no range annotation",
                            l.name.text
                        ),
                    )
                })?,
                None => {
                    return Err(refuse(
                        "CS005",
                        format!(
                            "function {funktion}: let {} has no range annotation",
                            l.name.text
                        ),
                    ))
                }
            };
            if !matches!(
                &l.typ,
                Some(TypExpr::Int(_)) | Some(TypExpr::Pfad(_))
            ) {
                return Err(refuse(
                    "CS001",
                    format!(
                        "function {funktion}: let {} binds no integer",
                        l.name.text
                    ),
                ));
            }
            let (t, r) = drucke_expr(funktion, &l.wert, ctx, info)?;
            let t = verenge(
                funktion,
                &format!("let {}", l.name.text),
                t,
                r,
                (lo, hi),
            )?;
            ctx.eintraege
                .push(CtxEintrag::Ganz(l.name.text.clone(), lo, hi));
            let weiter = drucke_ende(funktion, rest, ctx, info, ergebnis)?;
            Ok(format!("(.bind {t} {lo} {hi} {weiter})"))
        }
        StmtArt::Zuweisung(z) => {
            let t = drucke_zuweisung(funktion, z, ctx, info)?;
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
    for p in &f.parameter {
        if let Some((lo, hi)) = bereich_von_typ(&p.typ, info) {
            // An integer parameter reads through `ctxTyp`.
            ctx.eintraege
                .push(CtxEintrag::Ganz(p.name.text.clone(), lo, hi));
        } else if matches!(p.typ, TypExpr::Bool(_)) {
            ctx.eintraege.push(CtxEintrag::Wahr(p.name.text.clone()));
        } else {
            ctx.eintraege.push(CtxEintrag::Sonst(p.name.text.clone()));
        }
    }
    match drucke_ende(&funktion, &b.anweisungen, &mut ctx, info, &f.ergebnis) {
        Ok(ende) => BodyCert::Gedruckt {
            lean: format!("(.liftE {ende})"),
        },
        Err(weigerung) => BodyCert::Abgewiesen { weigerung },
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

/// The per-function section of `gabbro certificate`: one `CertEnd2` term
/// per block body, or a named refusal for every body outside the fragment.
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
                BodyCert::Gedruckt { lean } => {
                    aus.push_str(&format!(
                        "   function {}: CertEnd2 term:\n     {lean}\n",
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
        let BodyCert::Gedruckt { lean } = zeige_rumpf(&f, &info) else {
            panic!("a bare return prints");
        };
        assert_eq!(lean, "(.liftE .ret)");
    }
}
