//! **Counterexamples for handed-over obligations (PLAN-ZIELSATZ.md §9).**
//!
//! When a user's `ensures` does not hold, the project says "unproved"; a
//! solver would say "for these inputs it breaks". This module is the
//! model-search half: `gabbro counterexample|gegenbeispiel <file.gab> [fn]`
//! searches inputs (parameters within their declared ranges, table slots
//! within field ranges) that satisfy `requires` but violate `ensures`, and
//! prints a Lean file that runs every candidate through the EXPORTED
//! program's Lean semantics (`rufAt`/`execEnd` on `gP`) via `#eval`, with a
//! kernel-checked CONFIRMATION theorem per hit.
//!
//! ## Why a CLI subcommand and not an instrument script
//!
//! The search needs exactly what `lean-g` knows and nothing else: the
//! parameter ranges (with constants inlined and aliases resolved), the
//! field ranges, and the per-conjunct `ensures` terms. A Python script
//! would re-derive all three by scraping the export text -- a second
//! register over the same facts, drifting at the first exporter change.
//! In-crate code reuses `Model`, `CheckedFn` and `tr_ensures` directly, and
//! succeeds exactly where `lean-g` succeeds (same `LG` refusals, no new
//! codes). The tool is outside the trusted base the same way either
//! spelling would be: every verdict it prints is re-checked by the kernel.
//!
//! ## What the searcher is, and what buys the reliability
//!
//! The searcher is a small interpreter over the checked surface AST,
//! mirroring `Semantik.lean`'s `eval`/`execStmt`/`execEnd`/`rufAt`
//! (unbounded integers, truncated shifts, `Nat` bit operations on
//! nonnegative operands, the `traverse` invariant checked every round with
//! `.logik .schleife` on failure, `old()` read at frame entry). It is
//! deliberately dumb: exhaustive enumeration while the input space is
//! small, deterministic random sampling otherwise. It may be incomplete --
//! a form it cannot model skips its function LOUDLY (a comment in the
//! output, counted in the summary), never silently.
//!
//! The CONFIRMATION buys the reliability, not the search: for every
//! candidate the file `#eval`s the Lean-computed verdict, and for every
//! predicted hit it states `example : hit = true := by decide` over
//! `rufAt` -- plus `requires = true` and the per-conjunct outcomes. A
//! searcher false positive fails the file LOUDLY (red, not wrong): the
//! kernel re-executes the exported program on the concrete input. A
//! searcher miss stays what the tool says it is: "none found", never
//! "proved".
//!
//! ## Known boundaries (measured, not assumed)
//!
//! * `lean-g` carries `requires` (lane 198: the value clauses travel as
//!   `gReq` arms, `.wahr` where none stands): the searcher enumerates
//!   inputs freely, and the file kernel-checks `requires = true` per
//!   candidate rather than hiding it. A hit whose `requires` fails fails
//!   the file LOUDLY (red, not wrong).
//! * Lock invariants travel as the separate family `gS`; the export sets
//!   `invs := []`, so `rufAt` never reports `.invariante`. Only `ensures`
//!   violations are searched.
//! * Division and the `%`-family never reach the searcher: `tr_binaer`
//!   refuses them (`LG003`), so no candidate can divide by zero.
//! * The searcher and the Lean confirmation share one fuel constant: the
//!   file runs `rufAt` at the same depth the searcher interprets. A deeper
//!   call chain reads `abstieg` on both sides, never a disagreement.

use gabbro_syntax::ast::*;

use crate::lean_g::{
    analysiere, ensures_konjunkte, export_ns, namespace_of, CheckedFn, Model, ParamTy,
    Refusal, Scope, VTy,
};

/// Search options. Defaults are set for kernel-checkable files, not for
/// coverage records: every candidate costs one compiled `#eval`, every hit
/// costs kernel `decide`s.
pub struct Suche {
    /// Exhaustive enumeration while the input space fits this many
    /// candidates; random sampling above it.
    pub erschoepfend_grenze: u128,
    /// Random candidates per function when exhaustive does not apply.
    pub max_zufaellig: usize,
    /// Deterministic seed for the sampling (printed, so a run repeats).
    pub saat: u64,
    /// Call-depth fuel of the searcher; the file runs `rufAt` at the same
    /// depth (see the module docs: one constant, both sides).
    pub treibstoff: u64,
    /// Hits per function with the full witness (result, end state, every
    /// conjunct). Every further hit still gets its `= true` confirmation.
    pub treffer_grenze: usize,
    /// Lean fuel printed into the file (kept equal to `treibstoff`).
    pub lean_treibstoff: u64,
}

impl Default for Suche {
    fn default() -> Self {
        Suche {
            erschoepfend_grenze: 2048,
            max_zufaellig: 512,
            saat: 0x9E3779B97F4A7C15,
            treibstoff: 64,
            treffer_grenze: 8,
            lean_treibstoff: 64,
        }
    }
}

/// Export the checked unit plus the counterexample search over `nur`
/// (`None`: every function with an `ensures`), or refuse by name exactly
/// where `lean-g` refuses.
pub fn export(
    source_name: &str,
    tree: &Programm,
    nur: Option<&str>,
    opt: &Suche,
) -> Result<String, Refusal> {
    let analyse = analysiere(source_name, tree)?;
    let ns = namespace_of(source_name);
    let text = export_ns(source_name, tree, &ns)?;
    let schluss = format!("end {ns}\n\nend Gabbro.Grammatik\n");
    let rumpf = text
        .strip_suffix(schluss.as_str())
        .expect("lean-g export ends its namespaces")
        .to_string();
    let mut out = rumpf;
    out.push_str(&abschnitt(source_name, &analyse.model, &analyse.fns, &analyse.scope, nur, opt)?);
    out.push_str(&schluss);
    Ok(out)
}

fn refuse(code: &'static str, message: String) -> Refusal {
    Refusal { code, message }
}

// ---------------------------------------------------------------------------------------
// 1. The searcher: values, memory, environments
// ---------------------------------------------------------------------------------------

/// A searcher value: an integer, a boolean, a pointer (carries no data --
/// `Val .ptr = Unit`, so every pointer is the same value), or a reason
/// (`Fin`, only bound by `let … else`).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum SWert {
    Zahl(i128),
    Wahr(bool),
    Zeiger,
    Grund(u64),
}

/// One memory cell schema: table, slot index, field, and the value domain.
#[derive(Clone, Debug)]
enum ZellSchema {
    Zahl { t: usize, idx: i128, fi: usize, lo: i128, hi: i128 },
    Wahr { t: usize, idx: i128, fi: usize },
}

/// One parameter schema: the value domain behind the parameter.
#[derive(Clone, Debug)]
enum ParSchema {
    Zahl { lo: i128, hi: i128 },
    Wahr,
    Zeiger,
}

/// A logic outcome the searcher propagates (mirroring `Logik D`).
#[derive(Clone, Debug, PartialEq, Eq)]
#[allow(dead_code)]
enum LogikArt {
    Vorbedingung(String),
    Nachbedingung(String),
    Schleife,
    Abstieg,
    Vorzustand,
}

/// What running a block leaves behind.
enum BlockAus {
    Weiter,
    Zurueck(Option<SWert>),
    /// A reason return (`return R::F`): only a reason-channel callee
    /// produces one, and only `let … else` catches it.
    #[allow(dead_code)]
    Grund(u64),
    Logik(LogikArt),
    /// The searcher cannot model this step: loud skip, never a verdict.
    Unbekannt(String),
}

/// A confirmed-by-search hit: the violated function, the input that breaks
/// it (parameters and whole entry memory), the computed result, and the
/// per-conjunct outcomes. (The end state is re-computed by the Lean
/// witness, not stored: every stored claim would be a second register.)
#[derive(Clone)]
struct Treffer {
    ziel: String,
    params: Vec<SWert>,
    zellen: Vec<SWert>,
    ergebnis: Option<SWert>,
    klauseln: Vec<bool>,
}

/// The interpreter state for one run.
struct Lauf<'a> {
    modell: &'a Model,
    fns: &'a [CheckedFn],
    scope: &'a Scope,
    /// Entry memory per call frame (for `old()`).
    eintritte: Vec<Vec<SWert>>,
    /// Function index per call frame (for error attribution).
    rahmen: Vec<usize>,
    treffer: Vec<Treffer>,
    /// Skipped candidates/steps, counted and reported.
    spruenge: usize,
}

fn zell_schemata(modell: &Model) -> Result<Vec<ZellSchema>, String> {
    let mut acc = Vec::new();
    for (ti, t) in modell.tables.iter().enumerate() {
        if t.count < 0 || t.count > 1024 {
            return Err(format!("table {} has count {}", t.name, t.count));
        }
        for idx in 0..t.count {
            for (fi, f) in t.fields.iter().enumerate() {
                match &f.ty {
                    VTy::Int { lo, hi, .. } => acc.push(ZellSchema::Zahl { t: ti, idx, fi, lo: *lo, hi: *hi }),
                    VTy::Bool => acc.push(ZellSchema::Wahr { t: ti, idx, fi }),
                    _ => return Err(format!("field {}.{} has no searchable form", t.name, f.name)),
                }
            }
        }
    }
    Ok(acc)
}

fn par_schemata(cf: &CheckedFn, modell: &Model) -> Result<Vec<ParSchema>, String> {
    let mut acc = Vec::new();
    for (_, p) in &cf.params {
        match p {
            ParamTy::Bool => acc.push(ParSchema::Wahr),
            ParamTy::Ptr { .. } => acc.push(ParSchema::Zeiger),
            // Integers and indices alike: the declared range (an index
            // spans its table, as `VTy::range` spells it).
            t => match t.vty(modell).range(modell) {
                Some((lo, hi)) => acc.push(ParSchema::Zahl { lo, hi }),
                None => return Err(format!("parameter with no searchable range")),
            },
        }
    }
    Ok(acc)
}

// ---------------------------------------------------------------------------------------
// 2. The searcher: expression evaluation (mirrors `eval` in `Semantik.lean`)
// ---------------------------------------------------------------------------------------

/// The value and the G type of an expression, exactly as `tr_typed` pairs
/// them (the type carries the storage width `~` and the bit operations
/// read).
#[derive(Clone, Debug)]
struct Getypt {
    wert: SWert,
    typ: VTy,
}

fn als_zahl(w: &SWert) -> Option<i128> {
    match w {
        SWert::Zahl(n) => Some(*n),
        _ => None,
    }
}

fn als_wahr(w: &SWert) -> Option<bool> {
    match w {
        SWert::Wahr(b) => Some(*b),
        _ => None,
    }
}

impl<'a> Lauf<'a> {
    fn bereich(&self, ty: &VTy) -> Option<(i128, i128)> {
        ty.range(self.modell)
    }

    fn bindeg(&self, umg: &[(String, Getypt)], name: &str) -> Option<Getypt> {
        umg.iter().rev().find(|(n, _)| n == name).map(|(_, g)| g.clone())
    }

    /// A bare name: limit word, sugared limit, inlined constant, or binding.
    fn name_wert(&self, o: &Ort, umg: &[(String, Getypt)]) -> Option<Getypt> {
        if o.suffixe.len() == 1 {
            if let Some((_, _, wert)) = crate::umgebung::grenzwort(o) {
                return Some(Getypt { wert: SWert::Zahl(wert), typ: VTy::Int { lo: wert, hi: wert, bits: None } });
            }
            if let OrtSuffix::Feld(f) = &o.suffixe[0] {
                if f.text == "max" || f.text == "min" {
                    if let Some((lo, hi)) = gabbro_syntax::zucker_bereich(&o.basis.text) {
                        let v = if f.text == "max" { hi } else { lo };
                        return Some(Getypt { wert: SWert::Zahl(v), typ: VTy::Int { lo: v, hi: v, bits: None } });
                    }
                }
            }
        }
        if o.suffixe.is_empty() {
            if let Some(v) = self.scope.consts.get(&o.basis.text) {
                return Some(Getypt { wert: SWert::Zahl(*v), typ: VTy::Int { lo: *v, hi: *v, bits: None } });
            }
            return self.bindeg(umg, &o.basis.text);
        }
        None
    }

    /// A slot read `p.slots[i].f` / `T.slots[i].f` (mirrors `slot_access`).
    /// `quelle` is the memory read: the current one, or the frame entry
    /// snapshot for `old()`.
    fn schlitz(
        &self,
        o: &Ort,
        umg: &[(String, Getypt)],
        zellen: &[ZellSchema],
        quelle: &[SWert],
    ) -> Option<Getypt> {
        let [OrtSuffix::Feld(slots), OrtSuffix::Index(idx_e), OrtSuffix::Feld(f)] = o.suffixe.as_slice() else {
            return None;
        };
        if slots.text != "slots" {
            return None;
        }
        let t = if let Some(ti) = self.modell.tables.iter().position(|t| t.name == o.basis.text) {
            ti
        } else {
            let g = self.bindeg(umg, &o.basis.text)?;
            match (&g.wert, &g.typ) {
                (SWert::Zeiger, VTy::Ptr { table, .. }) => *table,
                _ => return None,
            }
        };
        let fi = self.modell.tables[t].fields.iter().position(|fd| fd.name == f.text)?;
        // The index is a literal or an index-typed name (as `tr_index`).
        let idx = match &idx_e.art {
            ExprArt::Zahl(n) => i128::try_from(*n).ok()?,
            ExprArt::Ort(io) if io.suffixe.is_empty() => {
                let g = self.bindeg(umg, &io.basis.text)?;
                match (&g.wert, &g.typ) {
                    (SWert::Zahl(n), VTy::Index { table }) if *table == t => *n,
                    _ => return None,
                }
            }
            _ => return None,
        };
        let pos = zellen.iter().position(|z| match z {
            ZellSchema::Zahl { t: zt, idx: zi, fi: zf, .. } | ZellSchema::Wahr { t: zt, idx: zi, fi: zf } => {
                *zt == t && *zi == idx && *zf == fi
            }
        })?;
        let ty = self.modell.tables[t].fields[fi].ty.clone();
        Some(Getypt { wert: quelle[pos].clone(), typ: ty })
    }

    /// A conversion `uN(x)`: the value travels unchanged (`Expr.weiter`).
    fn umwandlung(&self, r: &Ruf, umg: &[(String, Getypt)], speicher: &[SWert], zellen: &[ZellSchema], quelle: &[SWert], ergebnis: &Option<SWert>) -> Option<Getypt> {
        if !r.marken.is_empty() || r.argumente.len() != 1 {
            return None;
        }
        let path = r.path()?;
        if path.teile.len() != 1 {
            return None;
        }
        let word = path.teile[0].text.clone();
        if self.fns.iter().any(|f| f.name == word) {
            return None;
        }
        let ziel = if let Some((lo, hi, bits)) = self.scope_aliase(&word) {
            VTy::Int { lo, hi, bits }
        } else if let Some(kw) = gabbro_syntax::kw::Kw::suche(&word) {
            if !kw.ist_intty() {
                return None;
            }
            let (breite, vz) = crate::umgebung::breite_von(kw)?;
            let (lo, hi) = crate::typen::grenzen(breite, vz);
            VTy::Int { lo, hi, bits: Some(breite as u32) }
        } else if let Some((lo, hi)) = gabbro_syntax::zucker_bereich(&word) {
            VTy::Int { lo, hi, bits: None }
        } else {
            return None;
        };
        let g = self.werte(&r.argumente[0], umg, speicher, zellen, quelle, ergebnis)?;
        match &g.wert {
            SWert::Zahl(_) => Some(Getypt { wert: g.wert, typ: ziel }),
            _ => None,
        }
    }

    fn scope_aliase(&self, word: &str) -> Option<(i128, i128, Option<u32>)> {
        self.scope.aliases_get(word)
    }

    fn bitop(&self, op: BinOp, a: i128, b: i128) -> Option<i128> {
        if a < 0 || b < 0 {
            return None;
        }
        let (au, bu) = (a as u128, b as u128);
        match op {
            BinOp::BitUnd => Some((au & bu) as i128),
            BinOp::BitOder => Some((au | bu) as i128),
            BinOp::BitXor => Some((au ^ bu) as i128),
            BinOp::SchiebLinks => {
                if b > 127 {
                    return None;
                }
                au.checked_mul(1u128 << (b as u32)).and_then(|v| i128::try_from(v).ok())
            }
            BinOp::SchiebRechts => {
                if b > 127 {
                    return None;
                }
                Some((au / (1u128 << (b as u32))) as i128)
            }
            _ => None,
        }
    }

    fn binaer(&self, op: BinOp, l: Getypt, r: Getypt) -> Option<Getypt> {
        match op {
            BinOp::Plus | BinOp::Minus | BinOp::Mal => {
                let (a, b) = (als_zahl(&l.wert)?, als_zahl(&r.wert)?);
                let (l1, h1) = self.bereich(&l.typ)?;
                let (l2, h2) = self.bereich(&r.typ)?;
                let (v, lo, hi) = match op {
                    BinOp::Plus => (a.checked_add(b)?, l1.checked_add(l2)?, h1.checked_add(h2)?),
                    BinOp::Minus => (a.checked_sub(b)?, l1.checked_sub(h2)?, h1.checked_sub(l2)?),
                    _ => {
                        let ecken = [l1.checked_mul(l2)?, l1.checked_mul(h2)?, h1.checked_mul(l2)?, h1.checked_mul(h2)?];
                        let (lo, hi) = (ecken.iter().min().copied()?, ecken.iter().max().copied()?);
                        (a.checked_mul(b)?, lo, hi)
                    }
                };
                Some(Getypt { wert: SWert::Zahl(v), typ: VTy::Int { lo, hi, bits: None } })
            }
            BinOp::BitUnd | BinOp::BitOder | BinOp::BitXor | BinOp::SchiebLinks | BinOp::SchiebRechts => {
                let (a, b) = (als_zahl(&l.wert)?, als_zahl(&r.wert)?);
                let (l1, _) = self.bereich(&l.typ)?;
                let (l2, _) = self.bereich(&r.typ)?;
                if l1 < 0 || l2 < 0 {
                    return None;
                }
                let VTy::Int { bits: Some(w), .. } = &l.typ else {
                    return None;
                };
                if *w > 64 {
                    return None;
                }
                let v = self.bitop(op, a, b)?;
                // The result type mirrors `tr_bitop` (the proofs were
                // decided at translation; the values agree by construction).
                let top: i128 = 1i128 << w;
                let typ = match op {
                    BinOp::BitUnd => {
                        let (_, h1) = self.bereich(&l.typ)?;
                        VTy::Int { lo: 0, hi: h1, bits: None }
                    }
                    BinOp::SchiebLinks | BinOp::SchiebRechts => {
                        let (_, h1) = self.bereich(&l.typ)?;
                        let (_, h2) = self.bereich(&r.typ)?;
                        let hi = if op == BinOp::SchiebLinks { h1.checked_mul(1i128 << (h2 as u32))? } else { h1 };
                        VTy::Int { lo: 0, hi, bits: None }
                    }
                    _ => VTy::Int { lo: 0, hi: top - 1, bits: Some(*w) },
                };
                Some(Getypt { wert: SWert::Zahl(v), typ })
            }
            BinOp::Und | BinOp::Oder => {
                let (a, b) = (als_wahr(&l.wert)?, als_wahr(&r.wert)?);
                let v = if op == BinOp::Und { a && b } else { a || b };
                Some(Getypt { wert: SWert::Wahr(v), typ: VTy::Bool })
            }
            BinOp::Gleich | BinOp::Ungleich | BinOp::Kleiner | BinOp::KleinerGleich | BinOp::Groesser | BinOp::GroesserGleich => {
                if self.bereich(&l.typ).is_none() || self.bereich(&r.typ).is_none() {
                    return None;
                }
                let (a, b) = (als_zahl(&l.wert)?, als_zahl(&r.wert)?);
                let v = match op {
                    BinOp::Gleich => a == b,
                    BinOp::Ungleich => a != b,
                    BinOp::Kleiner => a < b,
                    BinOp::KleinerGleich => a <= b,
                    BinOp::Groesser => a > b,
                    _ => a >= b,
                };
                Some(Getypt { wert: SWert::Wahr(v), typ: VTy::Bool })
            }
            _ => None,
        }
    }

    fn werte(
        &self,
        e: &Expr,
        umg: &[(String, Getypt)],
        speicher: &[SWert],
        zellen: &[ZellSchema],
        quelle: &[SWert],
        ergebnis: &Option<SWert>,
    ) -> Option<Getypt> {
        match &e.art {
            ExprArt::Zahl(n) => {
                let n = i128::try_from(*n).ok()?;
                Some(Getypt { wert: SWert::Zahl(n), typ: VTy::Int { lo: n, hi: n, bits: None } })
            }
            ExprArt::Wahr => Some(Getypt { wert: SWert::Wahr(true), typ: VTy::Bool }),
            ExprArt::Falsch => Some(Getypt { wert: SWert::Wahr(false), typ: VTy::Bool }),
            ExprArt::Ort(o) if o.suffixe.is_empty() => self.name_wert(o, umg),
            ExprArt::Ort(o) => {
                if let Some(g) = self.name_wert(o, umg) {
                    return Some(g);
                }
                self.schlitz(o, umg, zellen, speicher)
            }
            ExprArt::Ergebnis => {
                let v = ergebnis.clone()?;
                let ty = self.fns[self.rahmen.last().copied()?].result.clone()?;
                Some(Getypt { wert: v, typ: ty })
            }
            ExprArt::Alt(o) => {
                // `old()` reads the frame entry snapshot (as `eval` threads
                // `σ₀` from the call site through `rufAt`).
                let eintritt = self.eintritte.last()?;
                let g = self.schlitz(o, umg, zellen, eintritt)?;
                match &g.typ {
                    VTy::Int { .. } => Some(g),
                    _ => None,
                }
            }
            ExprArt::Klammer(x) => self.werte(x, umg, speicher, zellen, quelle, ergebnis),
            ExprArt::Binaer(op, a, b) => {
                let l = self.werte(a, umg, speicher, zellen, quelle, ergebnis)?;
                let r = self.werte(b, umg, speicher, zellen, quelle, ergebnis)?;
                self.binaer(*op, l, r)
            }
            ExprArt::Unaer(op, x) => {
                let g = self.werte(x, umg, speicher, zellen, quelle, ergebnis)?;
                match op {
                    UnOp::Nicht => Some(Getypt { wert: SWert::Wahr(!als_wahr(&g.wert)?), typ: VTy::Bool }),
                    UnOp::Negativ => {
                        let (lo, hi) = self.bereich(&g.typ)?;
                        Some(Getypt {
                            wert: SWert::Zahl(als_zahl(&g.wert)?.checked_neg()?),
                            typ: VTy::Int { lo: -hi, hi: -lo, bits: None },
                        })
                    }
                    UnOp::BitNicht => {
                        let (l1, h1) = self.bereich(&g.typ)?;
                        let VTy::Int { bits: Some(w), .. } = &g.typ else {
                            return None;
                        };
                        if *w > 64 || l1 < 0 || h1 >= (1i128 << w) {
                            return None;
                        }
                        let mask = (1i128 << w) - 1;
                        let v = als_zahl(&g.wert)? ^ mask;
                        Some(Getypt { wert: SWert::Zahl(v), typ: VTy::Int { lo: 0, hi: mask, bits: Some(*w) } })
                    }
                }
            }
            ExprArt::Ruf(r) => self.umwandlung(r, umg, speicher, zellen, quelle, ergebnis),
            _ => None,
        }
    }

    /// A boolean expression: comparisons, `&&`/`||`/`!`, literals and bool
    /// places (the `tr_bool` fragment).
    fn wahr(
        &self,
        e: &Expr,
        umg: &[(String, Getypt)],
        speicher: &[SWert],
        zellen: &[ZellSchema],
        quelle: &[SWert],
        ergebnis: &Option<SWert>,
    ) -> Option<bool> {
        let g = self.werte(e, umg, speicher, zellen, quelle, ergebnis)?;
        als_wahr(&g.wert)
    }

    /// An `ensures` predicate (the `tr_ensures` fragment).
    fn klausel(
        &self,
        p: &Pred,
        umg: &[(String, Getypt)],
        speicher: &[SWert],
        zellen: &[ZellSchema],
        quelle: &[SWert],
        ergebnis: &Option<SWert>,
    ) -> Option<bool> {
        match &p.art {
            PredArt::Vergleich(e) => match &e.art {
                ExprArt::Binaer(op, l, r) if op.ist_vergleich() => {
                    let a = self.werte(l, umg, speicher, zellen, quelle, ergebnis)?;
                    let b = self.werte(r, umg, speicher, zellen, quelle, ergebnis)?;
                    if self.bereich(&a.typ).is_none() || self.bereich(&b.typ).is_none() {
                        return None;
                    }
                    let (x, y) = (als_zahl(&a.wert)?, als_zahl(&b.wert)?);
                    Some(match op {
                        BinOp::Gleich => x == y,
                        BinOp::Ungleich => x != y,
                        BinOp::Kleiner => x < y,
                        BinOp::KleinerGleich => x <= y,
                        BinOp::Groesser => x > y,
                        _ => x >= y,
                    })
                }
                ExprArt::Wahr => Some(true),
                ExprArt::Falsch => Some(false),
                _ => None,
            },
            PredArt::Klammer(q) => self.klausel(q, umg, speicher, zellen, quelle, ergebnis),
            PredArt::Und(a, b) => Some(self.klausel(a, umg, speicher, zellen, quelle, ergebnis)? && self.klausel(b, umg, speicher, zellen, quelle, ergebnis)?),
            PredArt::Oder(a, b) => Some(self.klausel(a, umg, speicher, zellen, quelle, ergebnis)? || self.klausel(b, umg, speicher, zellen, quelle, ergebnis)?),
            PredArt::Nicht(q) => Some(!self.klausel(q, umg, speicher, zellen, quelle, ergebnis)?),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------------------
// 3. The searcher: statements (mirrors `execStmt`/`execBlock`/`rufAt`)
// ---------------------------------------------------------------------------------------

impl<'a> Lauf<'a> {
    fn ruf_args(
        &self,
        r: &Ruf,
        callee: &CheckedFn,
        umg: &[(String, Getypt)],
        speicher: &[SWert],
        zellen: &[ZellSchema],
        quelle: &[SWert],
    ) -> Option<Vec<SWert>> {
        if !r.marken.is_empty() || r.path().is_none() {
            return None;
        }
        if r.argumente.len() != callee.params.len() {
            return None;
        }
        let mut acc = Vec::new();
        for (a, (_, pty)) in r.argumente.iter().zip(callee.params.iter()) {
            let g = self.werte(a, umg, speicher, zellen, quelle, &None)?;
            match (pty, &g.wert) {
                (ParamTy::Ptr { .. }, SWert::Zeiger) => {}
                (ParamTy::Index { .. }, SWert::Zahl(_)) => {}
                (ParamTy::Int { .. }, SWert::Zahl(_)) => {}
                (ParamTy::Bool, SWert::Wahr(_)) => {}
                _ => return None,
            }
            acc.push(g.wert);
        }
        Some(acc)
    }

    fn callee_von(&self, r: &Ruf) -> Option<usize> {
        let path = r.path()?;
        let last = path.teile.last()?;
        if path.teile.len() != 1 {
            return None;
        }
        self.fns.iter().position(|f| f.name == last.text)
    }

    /// Run a function on concrete arguments and memory (mirrors `rufAt`
    /// at fixed fuel: the body runs, then the `ensures` clauses run, and a
    /// failed clause is BOTH a recorded hit against the run function AND a
    /// `.logik .nachbedingung` outcome for the caller -- exactly as `rufAt`
    /// reports the violation to the call site while the violated contract
    /// stays the callee's).
    fn laufe(
        &mut self,
        fi: usize,
        args: Vec<SWert>,
        speicher: &mut Vec<SWert>,
        zellen: &[ZellSchema],
        treibstoff: u64,
    ) -> BlockAus {
        if treibstoff == 0 {
            return BlockAus::Logik(LogikArt::Abstieg);
        }
        let cf = self.fns[fi].clone();
        if cf.params.len() != args.len() {
            return BlockAus::Unbekannt("argument count mismatch".to_string());
        }
        let mut umg: Vec<(String, Getypt)> = Vec::new();
        for ((name, pty), v) in cf.params.iter().zip(args.iter()) {
            umg.push((name.clone(), Getypt { wert: v.clone(), typ: pty.vty(self.modell) }));
        }
        self.eintritte.push(speicher.clone());
        self.rahmen.push(fi);
        let aus = self.block(&cf.body.anweisungen, &mut umg, speicher, zellen, true, treibstoff);
        let ende = speicher.clone();
        // A value function ends in `return` (checked); a void one may fall
        // off (as `Endblock` ends in `.ret .keine`).
        let aus = match aus {
            BlockAus::Weiter => {
                if cf.result.is_none() {
                    BlockAus::Zurueck(None)
                } else {
                    BlockAus::Unbekannt(format!("function {} falls off with a result", cf.name))
                }
            }
            a => a,
        };
        // The entry snapshot is still on the stack: `old()` inside the
        // clauses reads it, as `eval` threads `σ₀` from the call site.
        let aus = match aus {
            BlockAus::Zurueck(ergebnis) => match self.pruefe_ensures(fi, &args, &ende, zellen, &ergebnis) {
                Some(klauseln) => {
                    if klauseln.iter().any(|b| !b) {
                        let eintritt = self.eintritte.last().cloned().unwrap_or_default();
                        self.treffer.push(Treffer {
                            ziel: cf.name.clone(),
                            params: args,
                            zellen: eintritt,
                            ergebnis: ergebnis.clone(),
                            klauseln,
                        });
                        BlockAus::Logik(LogikArt::Nachbedingung(cf.name.clone()))
                    } else {
                        BlockAus::Zurueck(ergebnis)
                    }
                }
                None => {
                    self.spruenge += 1;
                    BlockAus::Unbekannt("ensures have no search form".to_string())
                }
            },
            a => a,
        };
        self.rahmen.pop();
        self.eintritte.pop();
        aus
    }

    fn schreibe(
        &self,
        z: &Zuweisung,
        umg: &[(String, Getypt)],
        speicher: &mut Vec<SWert>,
        zellen: &[ZellSchema],
    ) -> Option<()> {
        if z.op != ZuwOp::Setzt {
            return None;
        }
        let [OrtSuffix::Feld(slots), OrtSuffix::Index(idx_e), OrtSuffix::Feld(f)] = z.ziel.suffixe.as_slice() else {
            return None;
        };
        if slots.text != "slots" {
            return None;
        }
        let (t, schreibbar) = if let Some(ti) = self.modell.tables.iter().position(|t| t.name == z.ziel.basis.text) {
            (ti, true)
        } else {
            let g = self.bindeg(umg, &z.ziel.basis.text)?;
            match (&g.wert, &g.typ) {
                (SWert::Zeiger, VTy::Ptr { table, write }) => (*table, *write),
                _ => return None,
            }
        };
        if !schreibbar {
            return None;
        }
        let fi = self.modell.tables[t].fields.iter().position(|fd| fd.name == f.text)?;
        let idx = match &idx_e.art {
            ExprArt::Zahl(n) => i128::try_from(*n).ok()?,
            ExprArt::Ort(io) if io.suffixe.is_empty() => {
                let g = self.bindeg(umg, &io.basis.text)?;
                match (&g.wert, &g.typ) {
                    (SWert::Zahl(n), VTy::Index { table }) if *table == t => *n,
                    _ => return None,
                }
            }
            _ => return None,
        };
        let pos = zellen.iter().position(|zc| match zc {
            ZellSchema::Zahl { t: zt, idx: zi, fi: zf, .. } | ZellSchema::Wahr { t: zt, idx: zi, fi: zf } => {
                *zt == t && *zi == idx && *zf == fi
            }
        })?;
        let g = self.werte(&z.wert, umg, speicher, zellen, speicher, &None)?;
        match (&self.modell.tables[t].fields[fi].ty, &g.wert) {
            (VTy::Int { .. }, SWert::Zahl(_)) => {}
            (VTy::Bool, SWert::Wahr(_)) => {}
            _ => return None,
        }
        speicher[pos] = g.wert;
        Some(())
    }

    /// A direct call in statement position (mirrors `Stmt.call`: the result
    /// is discarded, a `grund` is impossible at `gruende = 0`).
    fn ruf_stmt(&mut self, r: &Ruf, umg: &[(String, Getypt)], speicher: &mut Vec<SWert>, zellen: &[ZellSchema], treibstoff: u64) -> BlockAus {
        let Some(ci) = self.callee_von(r) else {
            return BlockAus::Unbekannt("indirect or unknown call".to_string());
        };
        if self.fns[ci].gruende > 0 {
            return BlockAus::Unbekannt(format!("call of {} carries a reason", self.fns[ci].name));
        }
        let Some(args) = self.ruf_args(r, &self.fns[ci].clone(), umg, speicher, zellen, speicher) else {
            return BlockAus::Unbekannt("call arguments have no form".to_string());
        };
        // Fuel strictly descends per call (as `rufAt` recurses on `n`):
        // at zero the callee reads `abstieg`, never a verdict.
        match self.laufe(ci, args, speicher, zellen, treibstoff.saturating_sub(1)) {
            BlockAus::Zurueck(_) => BlockAus::Weiter,
            BlockAus::Grund(_) => BlockAus::Unbekannt("grund from a reason-free call".to_string()),
            BlockAus::Logik(e) => BlockAus::Logik(e),
            BlockAus::Unbekannt(m) => BlockAus::Unbekannt(m),
            BlockAus::Weiter => BlockAus::Unbekannt("call fell off with a result".to_string()),
        }
    }

    /// A `let x = f()` in a block (mirrors `Block.bindCall`).
    fn ruf_let(
        &mut self,
        name: &str,
        r: &Ruf,
        umg: &mut Vec<(String, Getypt)>,
        speicher: &mut Vec<SWert>,
        zellen: &[ZellSchema],
        treibstoff: u64,
    ) -> BlockAus {
        let Some(ci) = self.callee_von(r) else {
            return BlockAus::Unbekannt("indirect or unknown call".to_string());
        };
        if self.fns[ci].gruende > 0 {
            return BlockAus::Unbekannt(format!("call of {} carries a reason", self.fns[ci].name));
        }
        let snapshot: Vec<(String, Getypt)> = umg.clone();
        let callee = self.fns[ci].clone();
        let result_ty = callee.result.clone();
        let Some(args) = self.ruf_args(r, &callee, &snapshot, speicher, zellen, speicher) else {
            return BlockAus::Unbekannt("call arguments have no form".to_string());
        };
        match self.laufe(ci, args, speicher, zellen, treibstoff.saturating_sub(1)) {
            BlockAus::Zurueck(v) => {
                let ty = result_ty.unwrap_or(VTy::Bool);
                let wert = v.unwrap_or(SWert::Wahr(false));
                umg.push((name.to_string(), Getypt { wert, typ: ty }));
                BlockAus::Weiter
            }
            BlockAus::Grund(_) => BlockAus::Unbekannt("grund from a reason-free call".to_string()),
            BlockAus::Logik(e) => BlockAus::Logik(e),
            BlockAus::Unbekannt(m) => BlockAus::Unbekannt(m),
            BlockAus::Weiter => BlockAus::Unbekannt("call fell off with a result".to_string()),
        }
    }

    /// A `let x = f() else (e) { … }` (mirrors `Block.bindCallElse`): the
    /// `else` branch ends in `return`, so its outcome is the outcome.
    fn ruf_sonst(
        &mut self,
        l: &LetSonst,
        umg: &mut Vec<(String, Getypt)>,
        speicher: &mut Vec<SWert>,
        zellen: &[ZellSchema],
        treibstoff: u64,
    ) -> BlockAus {
        let LetQuelle::Ruf(r) = &l.quelle else {
            return BlockAus::Unbekannt("`let … else` over a place".to_string());
        };
        let Some(ci) = self.callee_von(r) else {
            return BlockAus::Unbekannt("indirect or unknown call".to_string());
        };
        let callee = self.fns[ci].clone();
        if callee.gruende == 0 || callee.result.is_none() {
            return BlockAus::Unbekannt(format!("`let … else` of {} binds no reason and value", callee.name));
        }
        let snapshot: Vec<(String, Getypt)> = umg.clone();
        let result_ty = callee.result.clone().expect("checked");
        let n_gruende = callee.gruende;
        let Some(args) = self.ruf_args(r, &callee, &snapshot, speicher, zellen, speicher) else {
            return BlockAus::Unbekannt("call arguments have no form".to_string());
        };
        match self.laufe(ci, args, speicher, zellen, treibstoff.saturating_sub(1)) {
            BlockAus::Zurueck(v) => {
                let wert = v.unwrap_or(SWert::Wahr(false));
                umg.push((l.name.text.clone(), Getypt { wert, typ: result_ty }));
                BlockAus::Weiter
            }
            BlockAus::Grund(fall) => {
                let mut sonst_umg = snapshot;
                sonst_umg.push((
                    l.fehlername.text.clone(),
                    Getypt { wert: SWert::Grund(fall), typ: VTy::Grund { n: n_gruende } },
                ));
                self.block(&l.sonst.anweisungen, &mut sonst_umg, speicher, zellen, true, treibstoff)
            }
            BlockAus::Logik(e) => BlockAus::Logik(e),
            BlockAus::Unbekannt(m) => BlockAus::Unbekannt(m),
            BlockAus::Weiter => BlockAus::Unbekannt("call fell off with a result".to_string()),
        }
    }

    /// A `traverse i over slots of T` loop (mirrors `traverseLauf`: the
    /// invariant runs before every round and after the last one, and a
    /// failed invariant is `.logik .schleife`).
    fn traverse(
        &mut self,
        t: &Traverse,
        umg: &mut Vec<(String, Getypt)>,
        speicher: &mut Vec<SWert>,
        zellen: &[ZellSchema],
        treibstoff: u64,
    ) -> BlockAus {
        if t.gegenstand.is_some() {
            return BlockAus::Unbekannt("`traverse … of …`".to_string());
        }
        let Domaene::SlotsVon(o) = &t.domaene else {
            return BlockAus::Unbekannt("non-slot traverse domain".to_string());
        };
        if !o.suffixe.is_empty() {
            return BlockAus::Unbekannt("traverse domain with suffixes".to_string());
        }
        let Some(ti) = self.modell.tables.iter().position(|tb| tb.name == o.basis.text) else {
            return BlockAus::Unbekannt("traverse over unknown table".to_string());
        };
        let count = self.modell.tables[ti].count;
        // The enclosing bindings, owned: the invariant reads them (the
        // loop binder is not in scope, as in `tr_traverse`).
        let snapshot: Vec<(String, Getypt)> = umg.clone();
        for k in 0..count {
            // The invariant is over the enclosing context (the binder is
            // not in scope, as in `tr_traverse`).
            match self.invariante(&t.invariante, &snapshot, speicher, zellen) {
                Some(true) => {}
                Some(false) => return BlockAus::Logik(LogikArt::Schleife),
                None => return BlockAus::Unbekannt("loop invariant has no form".to_string()),
            }
            let mut rund: Vec<(String, Getypt)> = snapshot.clone();
            rund.push((
                t.variable.text.clone(),
                Getypt { wert: SWert::Zahl(k), typ: VTy::Index { table: ti } },
            ));
            match self.block(&t.rumpf.anweisungen, &mut rund, speicher, zellen, false, treibstoff) {
                BlockAus::Weiter => {}
                a @ (BlockAus::Zurueck(_) | BlockAus::Grund(_) | BlockAus::Logik(_) | BlockAus::Unbekannt(_)) => {
                    return a;
                }
            }
        }
        match self.invariante(&t.invariante, &snapshot, speicher, zellen) {
            Some(true) => BlockAus::Weiter,
            Some(false) => BlockAus::Logik(LogikArt::Schleife),
            None => BlockAus::Unbekannt("loop invariant has no form".to_string()),
        }
    }

    /// A loop invariant over the enclosing bindings and memory (the binder
    /// is not in scope). A separate method -- not a closure -- so the
    /// borrow on the memory ends before the round's body runs.
    fn invariante(
        &self,
        inv: &Option<Pred>,
        umg: &[(String, Getypt)],
        speicher: &[SWert],
        zellen: &[ZellSchema],
    ) -> Option<bool> {
        match inv {
            None => Some(true),
            Some(p) => self.klausel(p, umg, speicher, zellen, speicher, &None),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn stmt(
        &mut self,
        s: &Stmt,
        umg: &mut Vec<(String, Getypt)>,
        speicher: &mut Vec<SWert>,
        zellen: &[ZellSchema],
        endblock: bool,
        treibstoff: u64,
    ) -> Option<BlockAus> {
        match &s.art {
            StmtArt::Zuweisung(z) => {
                self.schreibe(z, umg, speicher, zellen)?;
                Some(BlockAus::Weiter)
            }
            StmtArt::Ruf(r) => Some(self.ruf_stmt(r, umg, speicher, zellen, treibstoff)),
            StmtArt::Wenn(w) => {
                let snapshot: Vec<(String, Getypt)> = umg.clone();
                // `else if` chains run front to back (as the nested `ite`s).
                let mut zweig: Option<&Block> = None;
                for (cnd, b) in &w.zweige {
                    if self.wahr(cnd, &snapshot, speicher, zellen, speicher, &None)? {
                        zweig = Some(b);
                        break;
                    }
                }
                match zweig.or(w.sonst.as_ref()) {
                    Some(b) => {
                        let mut innen = snapshot;
                        Some(self.block(&b.anweisungen, &mut innen, speicher, zellen, false, treibstoff))
                    }
                    None => Some(BlockAus::Weiter),
                }
            }
            StmtArt::Sperrt(sp) => {
                if sp.geteilt || !sp.sperre.suffixe.is_empty() {
                    return None;
                }
                if self.modell.locks.iter().all(|l| l.name != sp.sperre.basis.text) {
                    return None;
                }
                // Locks are unobservable to `ensures` (no lock state is
                // readable by an expression): run the body as a block.
                let snapshot: Vec<(String, Getypt)> = umg.clone();
                let mut innen = snapshot;
                Some(self.block(&sp.rumpf.anweisungen, &mut innen, speicher, zellen, false, treibstoff))
            }
            StmtArt::Schleife(sl) => match &**sl {
                Schleife::Traverse(t) => Some(self.traverse(t, umg, speicher, zellen, treibstoff)),
                Schleife::Retry(_) | Schleife::Forever(_) => None,
            },
            StmtArt::Let(l) => {
                if let ExprArt::Ruf(r) = &l.wert.art {
                    if self.callee_von(r).is_some() {
                        return Some(self.ruf_let(&l.name.text, r, umg, speicher, zellen, treibstoff));
                    }
                }
                let g = self.werte(&l.wert, umg, speicher, zellen, speicher, &None)?;
                umg.push((l.name.text.clone(), g));
                Some(BlockAus::Weiter)
            }
            StmtArt::LetSonst(l) => {
                if endblock {
                    return None;
                }
                Some(self.ruf_sonst(l, umg, speicher, zellen, treibstoff))
            }
            StmtArt::Return(e) => {
                let v = match e {
                    None => None,
                    Some(x) => Some(self.werte(x, umg, speicher, zellen, speicher, &None)?.wert),
                };
                Some(BlockAus::Zurueck(v))
            }
            _ => None,
        }
    }

    fn block(
        &mut self,
        stmts: &[Stmt],
        umg: &mut Vec<(String, Getypt)>,
        speicher: &mut Vec<SWert>,
        zellen: &[ZellSchema],
        endblock: bool,
        treibstoff: u64,
    ) -> BlockAus {
        for s in stmts {
            match self.stmt(s, umg, speicher, zellen, endblock, treibstoff) {
                None => {
                    return BlockAus::Unbekannt("statement has no search form".to_string());
                }
                Some(BlockAus::Weiter) => {}
                Some(a) => return a,
            }
        }
        BlockAus::Weiter
    }

    /// Check the `ensures` clauses of `fi` after a run. The entry
    /// snapshot is the frame top on the stack (the caller pops after).
    fn pruefe_ensures(
        &self,
        fi: usize,
        args: &[SWert],
        speicher: &[SWert],
        zellen: &[ZellSchema],
        ergebnis: &Option<SWert>,
    ) -> Option<Vec<bool>> {
        let cf = self.fns[fi].clone();
        let mut umg: Vec<(String, Getypt)> = Vec::new();
        for ((name, pty), v) in cf.params.iter().zip(args.iter()) {
            umg.push((name.clone(), Getypt { wert: v.clone(), typ: pty.vty(self.modell) }));
        }
        let mut klauseln = Vec::new();
        for p in &cf.ensures {
            klauseln.push(self.klausel(p, &umg, speicher, zellen, speicher, ergebnis)?);
        }
        Some(klauseln)
    }
}

// ---------------------------------------------------------------------------------------
// 4. Candidate enumeration: exhaustive while small, sampled otherwise
// ---------------------------------------------------------------------------------------

#[derive(Clone)]
struct Kandidat {
    params: Vec<SWert>,
    zellen: Vec<SWert>,
}

fn raum_volumen(par: &[ParSchema], zellen: &[ZellSchema], grenze: u128) -> Option<u128> {
    let mut vol: u128 = 1;
    let breite = |lo: i128, hi: i128| -> Option<u128> {
        if hi < lo {
            return Some(1);
        }
        Some((hi as u128).wrapping_sub(lo as u128).wrapping_add(1))
    };
    for p in par {
        let w = match p {
            ParSchema::Zahl { lo, hi } => breite(*lo, *hi)?,
            ParSchema::Wahr => 2,
            ParSchema::Zeiger => 1,
        };
        vol = vol.checked_mul(w)?;
        if vol > grenze {
            return None;
        }
    }
    for z in zellen {
        let w = match z {
            ZellSchema::Zahl { lo, hi, .. } => breite(*lo, *hi)?,
            ZellSchema::Wahr { .. } => 2,
        };
        vol = vol.checked_mul(w)?;
        if vol > grenze {
            return None;
        }
    }
    Some(vol)
}

fn zufall(saat: &mut u64) -> u64 {
    let mut x = *saat | 1;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *saat = x;
    x
}

fn ziehe(saat: &mut u64, lo: i128, hi: i128) -> i128 {
    if hi <= lo {
        return lo;
    }
    let w = (hi as u128).wrapping_sub(lo as u128).wrapping_add(1);
    lo.wrapping_add((zufall(saat) as u128 % w) as i128)
}

fn kandidat_aus_index(
    mut n: u128,
    par: &[ParSchema],
    zellen: &[ZellSchema],
) -> Kandidat {
    let mut params = Vec::new();
    for p in par {
        match p {
            ParSchema::Zahl { lo, hi } => {
                let w = (*hi as u128).wrapping_sub(*lo as u128).wrapping_add(1);
                params.push(SWert::Zahl(lo.wrapping_add((n % w) as i128)));
                n /= w;
            }
            ParSchema::Wahr => {
                params.push(SWert::Wahr(n % 2 == 1));
                n /= 2;
            }
            ParSchema::Zeiger => params.push(SWert::Zeiger),
        }
    }
    let mut zs = Vec::new();
    for z in zellen {
        match z {
            ZellSchema::Zahl { lo, hi, .. } => {
                let w = (*hi as u128).wrapping_sub(*lo as u128).wrapping_add(1);
                zs.push(SWert::Zahl(lo.wrapping_add((n % w) as i128)));
                n /= w;
            }
            ZellSchema::Wahr { .. } => {
                zs.push(SWert::Wahr(n % 2 == 1));
                n /= 2;
            }
        }
    }
    Kandidat { params, zellen: zs }
}

fn kandidat_zufaellig(saat: &mut u64, par: &[ParSchema], zellen: &[ZellSchema]) -> Kandidat {
    let mut params = Vec::new();
    for p in par {
        match p {
            ParSchema::Zahl { lo, hi } => params.push(SWert::Zahl(ziehe(saat, *lo, *hi))),
            ParSchema::Wahr => params.push(SWert::Wahr(zufall(saat) % 2 == 1)),
            ParSchema::Zeiger => params.push(SWert::Zeiger),
        }
    }
    let mut zs = Vec::new();
    for z in zellen {
        match z {
            ZellSchema::Zahl { lo, hi, .. } => zs.push(SWert::Zahl(ziehe(saat, *lo, *hi))),
            ZellSchema::Wahr { .. } => zs.push(SWert::Wahr(zufall(saat) % 2 == 1)),
        }
    }
    Kandidat { params, zellen: zs }
}

// ---------------------------------------------------------------------------------------
// 5. The run: search every function, collect hits
// ---------------------------------------------------------------------------------------

struct FnBericht {
    kandidaten: usize,
    erschoepfend: bool,
    raum: Option<u128>,
    urteile: Vec<(Kandidat, Urteil)>,
    spruenge: usize,
    uebersprungen: Option<String>,
}

/// The searcher's verdict per candidate (a comment in the file; the
/// `#eval` beside it is the Lean verdict, the `example` the proof).
#[derive(Clone)]
enum Urteil {
    Treffer(Treffer),
    Ok,
    Grund,
    Logik(String),
    Sprung,
}

fn suche_fn(
    lauf: &mut Lauf,
    fi: usize,
    par: &[ParSchema],
    zellen: &[ZellSchema],
    opt: &Suche,
) -> FnBericht {
    let name = lauf.fns[fi].name.clone();
    let raum = raum_volumen(par, zellen, opt.erschoepfend_grenze);
    let (kandidaten, erschoepfend) = match raum {
        Some(v) => (v as usize, true),
        None => (opt.max_zufaellig, false),
    };
    let start_spruenge = lauf.spruenge;
    let mut saat = opt.saat ^ (fi as u64).wrapping_mul(0x9E3779B97F4A7C15);
    let mut urteile = Vec::new();
    for n in 0..kandidaten {
        let k = if erschoepfend {
            kandidat_aus_index(n as u128, par, zellen)
        } else {
            kandidat_zufaellig(&mut saat, par, zellen)
        };
        let vor = lauf.treffer.len();
        let mut speicher = k.zellen.clone();
        let treibstoff = opt.treibstoff;
        // The contract check runs inside `laufe` (as in `rufAt`): a hit
        // against this function -- or against a callee -- is recorded
        // there. Anything but a clean return is no verdict for this input.
        let aus = lauf.laufe(fi, k.params.clone(), &mut speicher, zellen, treibstoff);
        // The run's own hit, if any: same target, same entry input.
        let hit = lauf.treffer[vor..]
            .iter()
            .find(|t| t.ziel == name && t.params == k.params && t.zellen == k.zellen)
            .cloned();
        let u = match (aus, hit) {
            (_, Some(t)) => Urteil::Treffer(t),
            (BlockAus::Zurueck(_), None) => Urteil::Ok,
            (BlockAus::Grund(_), None) => Urteil::Grund,
            (BlockAus::Logik(e), None) => Urteil::Logik(format!("{e:?}")),
            (BlockAus::Unbekannt(_), None) | (BlockAus::Weiter, None) => {
                lauf.spruenge += 1;
                Urteil::Sprung
            }
        };
        urteile.push((k, u));
    }
    FnBericht {
        kandidaten,
        erschoepfend,
        raum,
        urteile,
        spruenge: lauf.spruenge - start_spruenge,
        uebersprungen: None,
    }
}
// ---------------------------------------------------------------------------------------
// 6. Lean code generation: every candidate through `rufAt`/`execEnd`, every
//    hit kernel-confirmed. The EXECUTION the report rests on is Lean's; the
//    searcher's verdict travels as a comment beside each `#eval`.
// ---------------------------------------------------------------------------------------

/// An integer as Lean parses it after the dot (as in `lean_g`).
fn lean_zahl(n: i128) -> String {
    if n < 0 { format!("({n})") } else { format!("{n}") }
}

/// A searcher value as a Lean term (against the expected `Wert` type: the
/// anonymous constructor's proofs decide over the unfolded declaration).
fn wert_term(w: &SWert) -> String {
    match w {
        SWert::Zahl(n) => format!("⟨{}, by decide, by decide⟩", lean_zahl(*n)),
        SWert::Wahr(true) => "true".to_string(),
        SWert::Wahr(false) => "false".to_string(),
        SWert::Zeiger => "()".to_string(),
        SWert::Grund(r) => format!("⟨{r}, by decide⟩"),
    }
}

fn env_term(params: &[SWert]) -> String {
    // Dot notation with the expected type from the `def` ascription (as
    // in `Bibliothek.lean`): the declaration never appears by name here.
    let mut acc = ".nil".to_string();
    for w in params.iter().rev() {
        acc = format!("(.cons {} {acc})", wert_term(w));
    }
    acc
}

/// The initial world: every slot a concrete value, as one `slots` function
/// with an if-chain per (table, field) over the indices.
fn welt_term(modell: &Model, zellen: &[ZellSchema], werte: &[SWert]) -> String {
    let mut arme = Vec::new();
    // Group cell positions per (table, field), in index order.
    let mut pro_feld: Vec<(usize, usize, Vec<(i128, SWert)>)> = Vec::new();
    for (pos, z) in zellen.iter().enumerate() {
        let (t, idx, fi) = match z {
            ZellSchema::Zahl { t, idx, fi, .. } | ZellSchema::Wahr { t, idx, fi, .. } => (*t, *idx, *fi),
        };
        match pro_feld.iter_mut().find(|(pt, pfi, _)| *pt == t && *pfi == fi) {
            Some((_, _, v)) => v.push((idx, werte[pos].clone())),
            None => pro_feld.push((t, fi, vec![(idx, werte[pos].clone())])),
        }
    }
    for (t, fi, mut vs) in pro_feld {
        vs.sort_by_key(|(i, _)| *i);
        let tname = &modell.tables[t].name;
        let fname = &modell.tables[t].fields[fi].name;
        // The else-branch carries the last index's value (reads outside
        // `count` cannot arise from well-typed terms).
        let mut kette = wert_term(&vs.last().expect("nonempty").1);
        for (i, w) in vs.iter().rev().skip(1) {
            kette = format!("if n = {} then {} else {kette}", lean_zahl(*i), wert_term(w));
        }
        arme.push(format!("| GTab.{tname}, n, G{tname}Feld.{fname} => {kette}"));
    }
    let slots = if arme.is_empty() {
        "(fun t => nomatch t)".to_string()
    } else {
        format!("(fun {} )", arme.join(" "))
    };
    // The `fun` bodies stay parenthesized: an unparenthesized `fun`
    // inside a `{ … }` structure instance swallows the following comma
    // into its own body (measured: "unexpected token ':='").
    format!("{{ slots := {slots}, globs := (fun e => nomatch e), spur := [] }}")
}

fn wert_text(w: &SWert) -> String {
    match w {
        SWert::Zahl(n) => format!("{n}"),
        SWert::Wahr(b) => format!("{b}"),
        SWert::Zeiger => "ptr".to_string(),
        SWert::Grund(r) => format!("grund{r}"),
    }
}

fn eingabe_text(cf: &CheckedFn, k: &Kandidat) -> String {
    let mut teile = Vec::new();
    for ((name, _), w) in cf.params.iter().zip(k.params.iter()) {
        teile.push(format!("{name}={}", wert_text(w)));
    }
    teile.join(" ")
}

fn zellen_text(modell: &Model, zellen: &[ZellSchema], werte: &[SWert]) -> String {
    let mut teile = Vec::new();
    for (pos, z) in zellen.iter().enumerate() {
        let (t, idx, fi) = match z {
            ZellSchema::Zahl { t, idx, fi, .. } | ZellSchema::Wahr { t, idx, fi, .. } => (*t, *idx, *fi),
        };
        teile.push(format!(
            "{}.slots[{idx}].{}={}",
            modell.tables[t].name,
            modell.tables[t].fields[fi].name,
            wert_text(&werte[pos])
        ));
    }
    teile.join(" ")
}

/// The result display inside the witness: per result type, so `v.n`
/// resolves against the unfolded `ErgVal`. Returns the display term and
/// whether it binds the result value (a void result binds nothing, so no
/// unused-name warning).
fn erg_anzeige(cf: &CheckedFn) -> (String, bool) {
    match &cf.result {
        None => ("\"()\"".to_string(), false),
        Some(VTy::Int { .. }) | Some(VTy::Index { .. }) => ("toString v.n".to_string(), true),
        Some(VTy::Bool) => ("toString v".to_string(), true),
        _ => ("\"(Ergebnis ohne Anzeige)\"".to_string(), false),
    }
}

/// One candidate: input defs, the Lean verdicts (`#eval`), and -- for hits
/// -- the kernel-checked confirmations.
#[allow(clippy::too_many_arguments)]
fn kandidat_emit(
    out: &mut String,
    g: &str,
    cf: &CheckedFn,
    modell: &Model,
    zellen: &[ZellSchema],
    konjunkte: &[String],
    nr: usize,
    k: &Kandidat,
    u: &Urteil,
    fuel: u64,
    voller_zeuge: bool,
) {
    let sucher: String = match u {
        Urteil::Treffer(t) => {
            let falsch: Vec<String> = t
                .klauseln
                .iter()
                .enumerate()
                .filter(|(_, b)| !**b)
                .map(|(j, _)| format!("{j}"))
                .collect();
            let ergebnis = match &t.ergebnis {
                None => "()".to_string(),
                Some(w) => wert_text(w),
            };
            format!("searcher: HIT (ensures violated; result {ergebnis}; failing conjuncts [{}])", falsch.join(","))
        }
        Urteil::Ok => "searcher: clean".to_string(),
        Urteil::Grund => "searcher: reason return (no ensures verdict)".to_string(),
        Urteil::Logik(e) => format!("searcher: logic outcome {e} (no ensures verdict)"),
        Urteil::Sprung => "searcher: SKIPPED (no search form -- Lean still decides below)".to_string(),
    };
    out.push_str(&format!(
        "-- candidate {nr}: {} ; {} {{{}}}\n",
        eingabe_text(cf, k),
        sucher,
        zellen_text(modell, zellen, &k.zellen)
    ));
    out.push_str(&format!("def gx_{g}_s{nr} : World gD := {}\n", welt_term(modell, zellen, &k.zellen)));
    out.push_str(&format!("def gx_{g}_r{nr} : Env gD gCtx_{g} := {}\n", env_term(&k.params)));
    // The CONTRACT verdict: `rufAt` on the exported program (a violated
    // `requires` reads `vorbedingung` here -- the file still checks
    // `requires = true` below). Only the function's OWN
    // `nachbedingung` counts: a caller that dies in a callee's violated
    // contract reads false here (its own `ensures` never ran -- the
    // comment above says where the run died, and the callee's own
    // section carries that hit with its confirmation).
    out.push_str(&format!(
        "def gx_{g}_o{nr} := rufAt gP gO 0 {fuel} g_{g} gx_{g}_s{nr} gx_{g}_r{nr}\n"
    ));
    out.push_str(&format!(
        "def gx_{g}_t{nr} : Bool := match gx_{g}_o{nr} with | .logik (.nachbedingung f) => f == g_{g} | _ => false\n"
    ));
    out.push_str(&format!("#eval gx_{g}_t{nr}\n"));
    out.push_str(&format!(
        "def gx_{g}_q{nr} : Bool := wahr? (eval gx_{g}_s{nr} (gP.requires g_{g}) gx_{g}_s{nr} gx_{g}_r{nr})\n"
    ));
    out.push_str(&format!("#eval gx_{g}_q{nr}\n"));
    let hit = matches!(u, Urteil::Treffer(_));
    if hit && voller_zeuge {
        // The WITNESS: the body run directly (`execEnd`), so the computed
        // result and end state stay observable (`rufAt` discards them on a
        // violation). `gP.rumpf g_` is the exported program's body.
        out.push_str(&format!(
            "def gx_{g}_e{nr} := execEnd (V := vertragVon gD g_{g}) (l := false) (Γ := gCtx_{g}) (Λ := gL_{g}) gO 0 (rufAt gP gO 0 {fuel}) (gP.rumpf g_{g}) gx_{g}_s{nr} gx_{g}_r{nr}\n"
        ));
        let (erg_term, bindet) = erg_anzeige(cf);
        let erg_arm = if bindet { ".zurueck _ v" } else { ".zurueck _ _" };
        out.push_str(&format!(
            "def gx_{g}_erg{nr} : String := match gx_{g}_e{nr} with | {erg_arm} => \"Ergebnis: \" ++ {erg_term} | .grund _ r => \"grund \" ++ toString r.val | .logik _ => \"logik\" | .hardware _ => \"hardware\" | .leave _ _ _ => \"leave\" | .next _ _ _ => \"next\"\n",
        ));
        out.push_str(&format!("#eval gx_{g}_erg{nr}\n"));
        // The end state: every cell read back (truncated past 256 cells;
        // the confirmation never depends on this display).
        let chose: Vec<(String, bool)> = zellen
            .iter()
            .map(|z| match z {
                ZellSchema::Zahl { t, idx, fi, .. } => (
                    format!("(σ.slots GTab.{} {} G{}Feld.{})", modell.tables[*t].name, lean_zahl(*idx), modell.tables[*t].name, modell.tables[*t].fields[*fi].name),
                    true,
                ),
                ZellSchema::Wahr { t, idx, fi } => (
                    format!("(σ.slots GTab.{} {} G{}Feld.{})", modell.tables[*t].name, lean_zahl(*idx), modell.tables[*t].name, modell.tables[*t].fields[*fi].name),
                    false,
                ),
            })
            .collect();
        if chose.len() > 256 {
            out.push_str(&format!(
                "def gx_{g}_zu{nr} : String := match gx_{g}_e{nr} with | .zurueck _ _ => \"(Endzustand: mehr als 256 Zellen, gekuerzt)\" | _ => \"kein Zurueck\"\n"
            ));
        } else if chose.is_empty() {
            out.push_str(&format!(
                "def gx_{g}_zu{nr} : String := match gx_{g}_e{nr} with | .zurueck _ _ => \"(keine Tabellen)\" | _ => \"kein Zurueck\"\n"
            ));
        } else {
            let mut teile = Vec::new();
            for (zelle, ist_zahl) in &chose {
                if *ist_zahl {
                    teile.push(format!("toString {zelle}.n"));
                } else {
                    teile.push(format!("toString {zelle}"));
                }
            }
            out.push_str(&format!(
                "def gx_{g}_zu{nr} : String := match gx_{g}_e{nr} with | .zurueck σ _ => \"Endzustand: \" ++ {} | _ => \"kein Zurueck\"\n",
                teile.join(" ++ \", \" ++ ")
            ));
        }
        out.push_str(&format!("#eval gx_{g}_zu{nr}\n"));
        // Every `ensures` conjunct on the computed result and end state --
        // the failing one names itself (a human sees at a glance whether
        // the code or the promise is wrong).
        for (j, konj) in konjunkte.iter().enumerate() {
            out.push_str(&format!(
                "def gx_{g}_c{nr}_{j} : Bool := match gx_{g}_e{nr} with | .zurueck σ v => wahr? (eval gx_{g}_s{nr} ({konj} : Expr gD (ErgCtx (gD.params g_{g}) (gD.erg g_{g})) (vertragVon gD g_{g}).ende .bool) σ (ergEnv (gD.erg g_{g}) v gx_{g}_r{nr})) | _ => false\n"
            ));
            out.push_str(&format!("#eval gx_{g}_c{nr}_{j}\n"));
        }
    }
    if hit {
        // The CONFIRMATION: kernel-checked, over the Lean semantics. A
        // searcher false positive fails the file here -- loudly, never as
        // a wrong report.
        out.push_str(&format!("example : gx_{g}_t{nr} = true := by decide\n"));
        out.push_str(&format!("example : gx_{g}_q{nr} = true := by decide\n"));
        if voller_zeuge {
            if let Urteil::Treffer(t) = u {
                for (j, wahr) in t.klauseln.iter().enumerate() {
                    out.push_str(&format!("example : gx_{g}_c{nr}_{j} = {wahr} := by decide\n"));
                }
            }
        }
    }
    out.push('\n');
}

fn fn_abschnitt(
    out: &mut String,
    cf: &CheckedFn,
    modell: &Model,
    zellen: &[ZellSchema],
    konjunkte: &[String],
    bericht: &FnBericht,
    extra: &[Treffer],
    opt: &Suche,
) {
    let g = cf.name.clone();
    out.push_str(&format!(
        "-- FUNCTION {g}: {} ensures clause(s), {} conjunct(s); {} candidate(s) {} (seed {}).\n",
        cf.ensures.len(),
        konjunkte.len(),
        bericht.kandidaten,
        if bericht.erschoepfend { "exhaustive" } else { "sampled" },
        opt.saat
    ));
    if let Some(raum) = bericht.raum {
        out.push_str(&format!("-- input space: {raum} (exhaustive)\n"));
    } else {
        out.push_str("-- input space: larger than the exhaustive bound (sampled)\n");
    }
    let mut nr = 0;
    let mut zeugen = 0;
    for (k, u) in &bericht.urteile {
        let voller_zeuge = match u {
            Urteil::Treffer(_) => {
                zeugen += 1;
                zeugen <= opt.treffer_grenze
            }
            _ => false,
        };
        // Full witness displays only for hits (misses carry the Lean
        // verdict via `#eval`, which is execution, just uncertified --
        // and "none found" claims nothing).
        kandidat_emit(out, &g, cf, modell, zellen, konjunkte, nr, k, u, opt.lean_treibstoff, voller_zeuge);
        nr += 1;
    }
    // Derived hits from callers' searches: inputs no enumeration covered.
    for t in extra {
        let schon = bericht
            .urteile
            .iter()
            .any(|(k, _)| k.params == t.params && k.zellen == t.zellen);
        if schon {
            continue;
        }
        zeugen += 1;
        let k = Kandidat { params: t.params.clone(), zellen: t.zellen.clone() };
        let u = Urteil::Treffer(t.clone());
        out.push_str(&format!("-- (derived: found while searching a caller)\n"));
        kandidat_emit(out, &g, cf, modell, zellen, konjunkte, nr, &k, &u, opt.lean_treibstoff, zeugen <= opt.treffer_grenze);
        nr += 1;
    }
    let hits: usize = bericht
        .urteile
        .iter()
        .filter(|(_, u)| matches!(u, Urteil::Treffer(_)))
        .count()
        + extra.len();
    if hits == 0 {
        out.push_str(&format!(
            "-- {g}: NONE FOUND among {} candidate(s) -- this is NOT a proof (the search is incomplete by design).\n",
            bericht.kandidaten
        ));
    } else {
        out.push_str(&format!("-- {g}: {hits} confirmed counterexample(s) above (kernel-checked).\n"));
    }
    if bericht.spruenge > 0 {
        out.push_str(&format!(
            "-- {g}: {} candidate(s) SKIPPED (no search form) -- incompleteness, counted here.\n",
            bericht.spruenge
        ));
    }
    out.push('\n');
}

fn abschnitt(
    source_name: &str,
    modell: &Model,
    fns: &[CheckedFn],
    scope: &Scope,
    nur: Option<&str>,
    opt: &Suche,
) -> Result<String, Refusal> {
    if let Some(name) = nur {
        if !fns.iter().any(|f| f.name == name) {
            return Err(refuse("LG005", format!("unknown function {name} in {source_name}")));
        }
    }
    let zellen = zell_schemata(modell)
        .map_err(|m| refuse("LG002", format!("search space of {source_name}: {m}")))?;
    let mut lauf = Lauf { modell, fns, scope, eintritte: Vec::new(), rahmen: Vec::new(), treffer: Vec::new(), spruenge: 0 };
    // Search every selected function with an `ensures` first; derived
    // callee hits land in the global list and join their own section.
    struct Einsatz {
        fi: usize,
        konjunkte: Vec<String>,
        bericht: FnBericht,
    }
    let mut einsaetze = Vec::new();
    for (fi, cf) in fns.iter().enumerate() {
        if let Some(name) = nur {
            if cf.name != name {
                continue;
            }
        }
        if cf.ensures.is_empty() {
            einsaetze.push(Einsatz {
                fi,
                konjunkte: Vec::new(),
                bericht: FnBericht {
                    kandidaten: 0,
                    erschoepfend: true,
                    raum: Some(1),
                    urteile: Vec::new(),
                    spruenge: 0,
                    uebersprungen: Some("no ensures -- nothing to violate".to_string()),
                },
            });
            continue;
        }
        let par = match par_schemata(cf, modell) {
            Ok(p) => p,
            Err(m) => {
                einsaetze.push(Einsatz {
                    fi,
                    konjunkte: Vec::new(),
                    bericht: FnBericht {
                        kandidaten: 0,
                        erschoepfend: true,
                        raum: None,
                        urteile: Vec::new(),
                        spruenge: 0,
                        uebersprungen: Some(m),
                    },
                });
                continue;
            }
        };
        let konjunkte = ensures_konjunkte(cf, modell, scope)
            .map_err(|w| refuse(w.code, w.message))?;
        let bericht = suche_fn(&mut lauf, fi, &par, &zellen, opt);
        einsaetze.push(Einsatz { fi, konjunkte, bericht });
    }
    // Deduplicate hits globally (the same input may surface from several
    // callers): same target, same parameters, same entry memory.
    let mut gesehen = std::collections::HashSet::new();
    let mut treffer: Vec<Treffer> = Vec::new();
    for t in lauf.treffer {
        let schluessel = (t.ziel.clone(), t.params.clone(), t.zellen.clone());
        if gesehen.insert(schluessel) {
            treffer.push(t);
        }
    }
    let mut out = String::new();
    out.push_str("-- COUNTEREXAMPLE SEARCH over the exported program above.\n");
    out.push_str(&format!(
        "-- GENERATED by `gabbro counterexample {source_name}`{} -- do not edit.\n",
        nur.map(|n| format!(" {n}")).unwrap_or_default()
    ));
    out.push_str("--\n");
    out.push_str("-- For every candidate the file evaluates the EXPORTED program's\n");
    out.push_str("-- Lean semantics (`rufAt` for the contract verdict, `execEnd` for\n");
    out.push_str("-- the witness) via `#eval`, and for every hit it states a\n");
    out.push_str("-- kernel-checked `example ... := by decide`. A searcher false\n");
    out.push_str("-- positive fails the file LOUDLY; \"none found\" is NEVER a proof.\n");
    out.push_str("--\n");
    out.push_str("-- Boundaries, measured: `requires` travels (`gReq` arms, `.wahr`\n");
    out.push_str("-- where none stands) and is kernel-checked per hit; lock\n");
    out.push_str("-- invariants are the separate family `gS` (`invs := []`), so only\n");
    out.push_str("-- `ensures` violations are searched. Searcher and file share one\n");
    out.push_str(&format!(
        "-- fuel ({}): a deeper call chain reads `abstieg` on both sides.\n",
        opt.treibstoff
    ));
    out.push_str(&format!("-- Options: exhaustive bound {}, samples {}, seed {}.\n--\n", opt.erschoepfend_grenze, opt.max_zufaellig, opt.saat));
    out.push_str(&format!(
        "def gO : Orakel gD where\n  wirkt := fun a _ _ => nomatch a\n  regLies := fun r _ => nomatch r\n  regSchreib := fun r _ => nomatch r\n  sichtbar := fun g _ => nomatch g\n\n"
    ));
    let mut gesamt_kandidaten = 0;
    let mut gesamt_treffer = 0;
    for e in &einsaetze {
        let cf = &fns[e.fi];
        match &e.bericht.uebersprungen {
            Some(grund) => {
                out.push_str(&format!("-- FUNCTION {}: SKIPPED ({grund}).\n\n", cf.name));
            }
            None => {
                let extra: Vec<Treffer> = treffer.iter().filter(|t| t.ziel == cf.name).cloned().collect();
                // Hits already shown among the enumerated verdicts are not
                // extra; count only derived ones for the summary.
                let extra_neu: Vec<Treffer> = extra
                    .into_iter()
                    .filter(|t| {
                        !e.bericht
                            .urteile
                            .iter()
                            .any(|(k, _)| k.params == t.params && k.zellen == t.zellen)
                    })
                    .collect();
                let eigene: usize = e.bericht.urteile.iter().filter(|(_, u)| matches!(u, Urteil::Treffer(_))).count();
                gesamt_kandidaten += e.bericht.kandidaten + extra_neu.len();
                gesamt_treffer += eigene + extra_neu.len();
                fn_abschnitt(&mut out, cf, modell, &zellen, &e.konjunkte, &e.bericht, &extra_neu, opt);
            }
        }
    }
    out.push_str(&format!(
        "-- SUMMARY: {gesamt_kandidaten} candidate(s), {gesamt_treffer} confirmed counterexample(s).\n"
    ));
    out.push_str("-- Where the count above reads 0 confirmed, that is \"none found within this search\" --\n");
    out.push_str("-- never \"proved\".\n");
    Ok(out)
}
