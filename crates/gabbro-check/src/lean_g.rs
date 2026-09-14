//! **Export `.gab` to a G program term (Lean 4).**
//!
//! The only certified corpus program today is a HAND translation (`r4P`/`r4D`
//! in `grammatik/Grammatik/Referenz104.lean`). This module is the mechanical
//! path: it reads a checked `.gab` unit and prints a Lean file defining the
//! declaration `gD`, the program `gP : Programm gD` (the G program syntax of
//! `RufMaschineG.lean`, which is `Programm` of `Syntax.lean`), the function
//! list `gFs`, and the decidable checks `programmImFragmentG` and -- where it
//! applies -- `fussOrtGB` as `example ... := by decide`.
//!
//! ## What has a G counterpart, and what is refused
//!
//! Every surface form without a counterpart is REFUSED with an `LG` code --
//! never silently truncated. A refusal names the spelling that was typed.
//! The forms with a counterpart:
//!
//! * `table T count N { slot { f : <int range>, ... } }` -- `Tab`/`Feld`/`typ`/`count`
//!   (a bare word travels as its full range, the numbers the checker uses).
//!   A `bool` field travels as `Ty.bool`; `option`, record, `tagged`,
//!   float and wrapping fields have no form (LG002). A unit without tables
//!   travels with `Tab := Empty` (pure computation over parameters).
//! * `lock L protects { ... } rank N` -- `Lock`/`rang`/`braucht` (the `held`
//!   budget, the pointer address spaces and the `reads` effects
//!   have NO FORM and are ignored, each named in the printed header)
//! * `lock L ... invariant <pred>` -- the `SperrInv` family `gS` (lane 156):
//!   `orte` is the `protects` set, `inv` the predicate over the memory
//!   snapshot (table-slot reads with literal indices, named constants,
//!   integer arithmetic and comparisons). The guard half of `SperrInvOk`
//!   travels as `List.elem … = true` by `decide`, per lock and protected
//!   carrier in both directions; the read half and the release duty are the
//!   user's, booked beside the `ensures` duties.
//! * `impl fn` with pointer/index/range/`bool` parameters, `requires Held(L)`,
//!   `ensures` over comparisons of slot reads, `old`, `result` and literals,
//!   `effects { reads/writes/locks }`, an optional `or R` reason channel, and
//!   a body of slot writes, direct calls, `locks` blocks, `if`/`else`,
//!   `traverse ... over slots of T`, `let` bindings and a trailing `return`
//! * `-> T or R` -- the reason channel: `gruende` is the number of cases of
//!   the named `reason` declaration. A bare call of such a function has no
//!   form (its `hr` needs `gruende = 0`); only `let x = f() else (e) { … }`
//!   travels (`Block.bindCallElse`).
//! * `const NAME = N` (inlined at every use) and `type NAME = u32 in lo..hi`
//!   (resolved at every use); the module wrapper is transparent
//!
//! ## The lock floor (`boden`, lane 174)
//!
//! `RufPasst.hh` is the SUBSET (`∀ L, L ∈ S.haelt → Res.held L ∈ Λ`,
//! relaxed 2026-09-13): a caller may hold more than the callee requires.
//! Every extra lock must rank below the callee's floor (`RufPasst.hx`), and
//! the caller's own floor must not exceed the callee's (`RufPasst.hb`).
//! The floor is computed, not written: `boden` of a function is the minimum
//! rank its own body takes in `locks` blocks, or `none` where it takes none
//! (`Stmt.ueberBoden`, `StufenOk`). A call the floor cannot type -- an extra
//! lock at or above the callee's floor, a floored caller into a floorless
//! callee -- is refused by name (LG004 `RufPasst.hx`/`hb`), never weakened.
//! The `hx` proof has the shape of the hand witness `HelferZeuge.lean`
//! (`cases L`, one branch per lock: the floor, or absurdity from `hn`/`hL`).
//!
//! ## Refusal codes (`LG`)
//!
//! * `LG001` item with no G form (globals, devices, axioms, entries, ...)
//! * `LG002` type with no `Ty` form (floats, records, pointers outside `normal`, ...)
//! * `LG003` contract or value expression with no `Expr` form
//! * `LG004` body statement with no `Stmt`/`Endblock` form (this covers the
//!   `RufPasst` proof failures `hh`/`hx`/`hb`/`hw`, which are named in the
//!   message -- the checker accepts the call, the model cannot type it)
//! * `LG005` unresolvable name, count, rank or range (unknown table, lock,
//!   function, constant or type alias)
//! * `LG006` loop with no export form (`retry`, `forever`, a `traverse` that
//!   is not `traverse i over slots of T` with a translatable invariant)
//! * `LG007` reason-channel form with no export form (`let … else` over a
//!   place, a falling-off `else` branch, a valueless reason function in
//!   `let … else`)
//!
//! ## NO FORM in G (accepted and dropped, each named in the header)
//!
//! The module wrapper; named constants (inlined); bare carrier widths;
//! pointer address spaces; lock hold budgets; the `reads` effects; `costs`;
//! the `by unvisited`/`by consuming` run form, the `decreases` witness and
//! the `touches` clause of a `traverse` (static annotations, like `costs`);
//! `by ops` on a field (a writer discipline the checker holds);
//! `mut` on a `let` (reassignments still refuse by name); `concurrent` (all
//! functions travel in `gFs`; which of them start threads is not a G notion).

use gabbro_syntax::ast::*;
use gabbro_syntax::kw::Kw;

/// A refused export: the code and the message naming what was typed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Refusal {
    pub code: &'static str,
    pub message: String,
}

impl std::fmt::Display for Refusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}] {}", self.code, self.message)
    }
}

fn refuse(code: &'static str, message: String) -> Refusal {
    Refusal { code, message }
}

/// An integer bound as Lean parses it: a negative numeral cannot stand
/// bare after the dot (`.int -3 5` misparses as field notation on `-3`).
fn int_num(n: i128) -> String {
    if n < 0 {
        format!("({n})")
    } else {
        format!("{n}")
    }
}

/// A literal with its exact type: bare `.lit` needs the expected type to
/// resolve the dot, which implicit-only positions (a `bor` operand, a
/// comparison side) do not give it. A negative numeral stands parenthesized
/// (`.lit -5` misparses as field notation on `-5`, like `.int`).
fn lit_term(n: i128, ctx: &Ctx) -> String {
    let lit = if n < 0 { format!("(.lit ({n}))") } else { format!("(.lit {n})") };
    format!("(({lit}) : Expr gD {} {} {})", ctx.gamma, ctx.lambda, int_ty_str(n, n))
}

/// An integer range as G spells it.
fn int_ty_str(lo: i128, hi: i128) -> String {
    format!("(.int {} {})", int_num(lo), int_num(hi))
}

/// A value type as G spells it: an integer range (with the storage width
/// where the spelling names one), `bool`, a pointer, an index, or a reason
/// (`Fin n`, only ever bound by `let … else`, never computed with).
#[derive(Debug, Clone)]
pub(crate) enum VTy {
    Int { lo: i128, hi: i128, bits: Option<u32> },
    Bool,
    Ptr { table: usize, write: bool },
    Index { table: usize },
    Grund { n: usize },
}

impl VTy {
    /// The `Ty` term. An index travels through the declaration's `count`,
    /// exactly as the model's `traverse` binds it (`Ty.index` unfolds to
    /// `.int 0 (n-1)`).
    pub(crate) fn term(&self, model: &Model) -> String {
        match self {
            VTy::Int { lo, hi, .. } => int_ty_str(*lo, *hi),
            VTy::Bool => ".bool".to_string(),
            VTy::Ptr { table, write } => format!(".ptr {table} {write}"),
            VTy::Index { table } => {
                format!("(.index (gD.count {}))", tab_ctor(model, *table))
            }
            VTy::Grund { n } => format!("(.grund {n})"),
        }
    }

    /// The numeric range where there is one (an index spans its table).
    pub(crate) fn range(&self, model: &Model) -> Option<(i128, i128)> {
        match self {
            VTy::Int { lo, hi, .. } => Some((*lo, *hi)),
            VTy::Index { table } => Some((0, model.tables[*table].count - 1)),
            _ => None,
        }
    }

    fn bits(&self) -> Option<u32> {
        match self {
            VTy::Int { bits, .. } => *bits,
            _ => None,
        }
    }
}

/// The exportable fragment of a unit: tables, locks, functions, threads,
/// and the reason declarations behind the `or R` channels.
pub(crate) struct Model {
    pub(crate) tables: Vec<TableModel>,
    pub(crate) locks: Vec<LockModel>,
    pub(crate) fns: Vec<FnModel>,
    #[allow(dead_code)]
    concurrent: Vec<String>,
    reasons: std::collections::HashMap<String, usize>,
}

/// One slot field: its G type and, for integers, the storage width the
/// spelling names (for the `~` complement, which M1 reads over the storage
/// width -- `beispiele/61`, `hohes_nibble` is `u8 in 240 .. 255`).
pub(crate) struct FieldModel {
    pub(crate) name: String,
    pub(crate) ty: VTy,
}

pub(crate) struct TableModel {
    pub(crate) name: String,
    pub(crate) count: i128,
    pub(crate) fields: Vec<FieldModel>,
}

pub(crate) struct LockModel {
    pub(crate) name: String,
    pub(crate) rank: i128,
    pub(crate) guards: Vec<usize>,
    /// `invariant <pred>` -- `None` where the lock carries none (its `inv`
    /// arm is `fun _ => true`, the empty-family shape over its carriers).
    pub(crate) invariant: Option<Pred>,
}

pub(crate) struct FnModel {
    name: String,
    decl: FnDecl,
}

/// A file-local scope: named constants (inlined) and integer type aliases
/// (resolved, with the storage width where the spelling names one). Both
/// are NO FORM in G -- the value travels, the name does not.
#[derive(Default)]
pub(crate) struct Scope {
    pub(crate) consts: std::collections::HashMap<String, i128>,
    aliases: std::collections::HashMap<String, (i128, i128, Option<u32>)>,
}

impl Scope {
    /// A named integer range (for the counterexample search's conversions).
    pub(crate) fn aliases_get(&self, word: &str) -> Option<(i128, i128, Option<u32>)> {
        self.aliases.get(word).copied()
    }
}

/// A numeral where a declaration needs one: a literal (signed or not),
/// or a named constant.
fn numeral(e: &Expr, scope: &Scope) -> Option<i128> {
    match &e.art {
        ExprArt::Zahl(n) => i128::try_from(*n).ok(),
        // The negated literal the desugar rule writes for signed ranges.
        ExprArt::Unaer(UnOp::Negativ, x) => numeral(x, scope).and_then(|n| n.checked_neg()),
        ExprArt::Ort(o) if o.suffixe.is_empty() => scope.consts.get(&o.basis.text).copied(),
        _ => None,
    }
}

/// The storage width in bits a bare integer word names (`u8` is 8), or
/// `None` where the word names none.
fn word_bits(wort: Kw) -> Option<u32> {
    crate::umgebung::breite_von(wort).map(|(b, _)| b as u32)
}

/// A sugared limit word (`u13::max`): the bound off the desugar rule
/// itself (`zucker_bereich`), so the constant and the type never disagree.
fn zucker_grenzwort(o: &Ort) -> Option<i128> {
    if o.suffixe.len() != 1 {
        return None;
    }
    let OrtSuffix::Feld(f) = &o.suffixe[0] else {
        return None;
    };
    let (lo, hi) = gabbro_syntax::zucker_bereich(&o.basis.text)?;
    match f.text.as_str() {
        "max" => Some(hi),
        "min" => Some(lo),
        _ => None,
    }
}

/// An integer range where G needs a `Ty`: `u32 in lo..hi`, or an alias for
/// one. A bare word (`u32`) travels as its full range -- the same numbers
/// the checker computes with (`breite_von`/`grenzen`), spelled by the word.
/// An exclusive bound (`..<`) has no form here (LG002).
fn int_ty(t: &TypExpr, scope: &Scope) -> Option<VTy> {
    match t {
        TypExpr::Int(i) => {
            if let Some(b) = &i.bereich {
                if b.exklusiv {
                    return None;
                }
                let lo = numeral(&b.von, scope)?;
                let hi = numeral(&b.bis, scope)?;
                Some(VTy::Int { lo, hi, bits: word_bits(i.wort) })
            } else {
                let (breite, vz) = crate::umgebung::breite_von(i.wort)?;
                let (lo, hi) = crate::typen::grenzen(breite, vz);
                Some(VTy::Int { lo, hi, bits: Some(breite as u32) })
            }
        }
        TypExpr::Pfad(p) => {
            let name = p.einfach()?;
            let (lo, hi, bits) = scope.aliases.get(&name.text).copied()?;
            Some(VTy::Int { lo, hi, bits })
        }
        TypExpr::Bool(_) => Some(VTy::Bool),
        _ => None,
    }
}

/// Every item of the unit, through modules. Anything without a G form is
/// refused here, so nothing below ever sees it.
fn collect(source_name: &str, tree: &Programm) -> Result<Model, Refusal> {
    let mut model = Model { tables: vec![], locks: vec![], fns: vec![], concurrent: vec![], reasons: std::collections::HashMap::new() };
    let mut scope = Scope::default();
    // Pass one: constants and type aliases, so `count` and field types resolve.
    fn pass_one(scope: &mut Scope, items: &[Item]) -> Result<(), Refusal> {
        for item in items {
            match &item.art {
                ItemArt::Modul(m) => pass_one(scope, &m.items)?,
                ItemArt::Konst(k) => {
                    let Some(v) = numeral(&k.wert, scope) else {
                        return Err(refuse("LG005", format!("const {} is not a numeral", k.name.text)));
                    };
                    scope.consts.insert(k.name.text.clone(), v);
                }
                ItemArt::Typ(t) => {
                    if t.opaque || t.linear || t.ghost || t.tagged || t.ordnung.is_some()
                        || t.parameter.is_some()
                    {
                        return Err(refuse("LG001", format!("type {} has no G form", t.name.text)));
                    }
                    let Some(r) = t.rumpf.as_ref() else {
                        return Err(refuse("LG001", format!("type {} has no G form", t.name.text)));
                    };
                    let Some(VTy::Int { lo, hi, bits }) = int_ty(r, scope) else {
                        return Err(refuse("LG002", format!("type {} is not an integer range", t.name.text)));
                    };
                    scope.aliases.insert(t.name.text.clone(), (lo, hi, bits));
                }
                _ => {}
            }
        }
        Ok(())
    }
    pass_one(&mut scope, &tree.items)?;
    // Pass two: tables, locks, functions, concurrency.
    fn walk(model: &mut Model, scope: &Scope, items: &[Item]) -> Result<(), Refusal> {
        for item in items {
            if item.when.is_some() {
                return Err(refuse("LG001", "`when` on an item has no G form".to_string()));
            }
            match &item.art {
                ItemArt::Modul(m) => walk(model, scope, &m.items)?,
                ItemArt::Typ(_) | ItemArt::Konst(_) => {}
                ItemArt::Tabelle(t) => model.tables.push(read_table(t, scope)?),
                ItemArt::Lock(l) => model.locks.push(read_lock(l, model)?),
                // A `reason` declaration is pure declaration data: its case
                // count is the `gruende` of every `-> T or R` naming it.
                ItemArt::Reason(r) => {
                    model.reasons.insert(r.name.text.clone(), r.faelle.len());
                }
                ItemArt::Funktion(f) => {
                    model.fns.push(FnModel { name: f.name.text.clone(), decl: f.clone() });
                }
                ItemArt::Concurrent(c) => {
                    for p in &c.koerper {
                        let Some(last) = p.teile.last() else {
                            return Err(refuse("LG005", "empty path in `concurrent`".to_string()));
                        };
                        model.concurrent.push(last.text.clone());
                    }
                }
                other => {
                    return Err(refuse("LG001", format!("{} has no G form", other.benennung())));
                }
            }
        }
        Ok(())
    }
    walk(&mut model, &scope, &tree.items)?;
    // A unit without tables travels with `Tab := Empty` (pure computation
    // over parameters); a unit without functions has no program at all.
    if model.fns.is_empty() {
        if model.tables.is_empty() {
            return Err(refuse("LG001", "a G declaration needs at least one table".to_string()));
        }
        return Err(refuse("LG001", "a G program needs at least one function".to_string()));
    }
    for name in &model.concurrent {
        if !model.fns.iter().any(|f| &f.name == name) {
            return Err(refuse("LG005", format!("`concurrent` names unknown function {name}")));
        }
    }
    let _ = source_name;
    Ok(model)
}

/// A function with everything G needs resolved: parameter types, held locks,
/// written tables, contracts, the reason count, the lock floor and the body.
#[derive(Clone)]
pub(crate) struct CheckedFn {
    pub(crate) name: String,
    pub(crate) params: Vec<(String, ParamTy)>,
    pub(crate) result: Option<VTy>,
    held: Vec<usize>,
    writes: Vec<usize>,
    pub(crate) ensures: Vec<Pred>,
    pub(crate) body: Block,
    /// `-> T or R`: the case count of the named `reason`, 0 without one.
    pub(crate) gruende: usize,
    /// The lock floor: the minimum rank the body takes, or `none`
    /// (`Signatur.boden`, `StufenOk`).
    boden: Option<i128>,
    /// The functions the body may call (for the footprint mirror).
    calls: Vec<String>,
}

/// A parameter as G sees it: a pointer to a table, an index into one, an
/// integer range, or a `bool`. Named address spaces other than `normal`
/// have no G form. An `own` pointer travels as read-write: ownership
/// carries both rights (`beispiele/15`).
#[derive(Debug, Clone)]
pub(crate) enum ParamTy {
    Ptr { table: usize, write: bool },
    Index { table: usize },
    Int { lo: i128, hi: i128, bits: Option<u32> },
    Bool,
}

impl ParamTy {
    pub(crate) fn vty(&self, _model: &Model) -> VTy {
        match self {
            ParamTy::Ptr { table, write } => VTy::Ptr { table: *table, write: *write },
            ParamTy::Index { table } => VTy::Index { table: *table },
            ParamTy::Int { lo, hi, bits } => VTy::Int { lo: *lo, hi: *hi, bits: *bits },
            ParamTy::Bool => VTy::Bool,
        }
    }
}

/// What the surface body needs before checking: the locks it takes and the
/// functions it may call. Lenient (names only) -- translation resolves
/// strictly and refuses by name.
#[derive(Default)]
struct Scan {
    taken: Vec<String>,
    calls: Vec<String>,
}

fn scan_expr(e: &Expr, acc: &mut Scan) {
    match &e.art {
        ExprArt::Binaer(_, a, b) => {
            scan_expr(a, acc);
            scan_expr(b, acc);
        }
        ExprArt::Unaer(_, x) | ExprArt::Klammer(x) => scan_expr(x, acc),
        ExprArt::Ruf(r) => scan_ruf(r, acc),
        ExprArt::Eingebaut(_) => {}
        _ => {}
    }
}

fn scan_pred(p: &Pred, acc: &mut Scan) {
    match &p.art {
        PredArt::Vergleich(e) => scan_expr(e, acc),
        PredArt::Klammer(q) | PredArt::Nicht(q) => scan_pred(q, acc),
        PredArt::Und(a, b) | PredArt::Oder(a, b) | PredArt::Folgt(a, b) => {
            scan_pred(a, acc);
            scan_pred(b, acc);
        }
        PredArt::Quantor(q) => scan_pred(&q.rumpf, acc),
        _ => {}
    }
}

fn scan_ruf(r: &Ruf, acc: &mut Scan) {
    if let Some(path) = r.path() {
        if let Some(last) = path.teile.last() {
            acc.calls.push(last.text.clone());
        }
    }
    for a in &r.argumente {
        scan_expr(a, acc);
    }
}

fn scan_block(b: &Block, acc: &mut Scan) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Zuweisung(z) => scan_expr(&z.wert, acc),
            StmtArt::Ruf(r) => scan_ruf(r, acc),
            StmtArt::Return(e) => {
                if let Some(e) = e {
                    scan_expr(e, acc);
                }
            }
            StmtArt::Let(l) => scan_expr(&l.wert, acc),
            StmtArt::LetSonst(l) => {
                match &l.quelle {
                    LetQuelle::Ruf(r) => scan_ruf(r, acc),
                    LetQuelle::Ort(_) => {}
                }
                scan_block(&l.sonst, acc);
            }
            StmtArt::Wenn(w) => {
                for (c, b) in &w.zweige {
                    scan_expr(c, acc);
                    scan_block(b, acc);
                }
                if let Some(s) = &w.sonst {
                    scan_block(s, acc);
                }
            }
            StmtArt::Match(m) => {
                scan_expr(&m.gegenstand, acc);
                for z in &m.zweige {
                    scan_block(&z.rumpf, acc);
                }
            }
            StmtArt::Schleife(sl) => match &**sl {
                Schleife::Traverse(t) => {
                    if let Some(g) = &t.gegenstand {
                        scan_expr(g, acc);
                    }
                    if let Some(m) = &t.mass {
                        scan_expr(m, acc);
                    }
                    if let Some(p) = &t.invariante {
                        scan_pred(p, acc);
                    }
                    scan_block(&t.rumpf, acc);
                }
                Schleife::Retry(r) => {
                    scan_block(&r.rumpf, acc);
                }
                Schleife::Forever(f) => {
                    scan_block(&f.rumpf, acc);
                }
            },
            StmtArt::Sperrt(sp) => {
                acc.taken.push(sp.sperre.basis.text.clone());
                scan_block(&sp.rumpf, acc);
            }
            StmtArt::Bricht(b) => scan_block(&b.rumpf, acc),
            StmtArt::Narrow(_) => {}
            _ => {}
        }
    }
}

/// **Lane 191: the derived clause, read back through the real parser.**
///
/// An omitted `effects` is derived from the body, and the export treats it
/// exactly like a written one. The derived set travels as STRINGS
/// (`writes c.slots`) while the checks below match on `WirkungArt` — so the
/// line is rebuilt on a synthetic function and read back. `None` where an
/// entry has no written form; every entry the derivation produces
/// round-trips through the clause grammar.
fn synth_effects(gesetzt: &std::collections::BTreeSet<String>) -> Option<Wirkungen> {
    let mut eintraege: Vec<String> =
        gesetzt.iter().filter(|w| w.as_str() != "pure").cloned().collect();
    if eintraege.is_empty() {
        eintraege.push("pure".to_string());
    }
    let quelle = format!("impl fn f() effects {{ {} }} {{ }}", eintraege.join(", "));
    let (baum, absagen) = gabbro_syntax::lies("synth.gab", &quelle);
    if absagen.fehler_zahl() > 0 {
        return None;
    }
    for item in &baum.items {
        if let ItemArt::Funktion(f) = &item.art {
            if f.name.text == "f" {
                return f.effects.clone();
            }
        }
    }
    None
}

/// **Lane 191: derived sets by short name, unambiguous only.**
///
/// The model keys functions by short name; the derivation by qualified key.
/// Where two modules declare one short name, guessing would wed the export
/// to the wrong body — both stay refused (`LG001`, as before). Incomplete
/// derivations (a lower bound, R16) never stand in for a line either.
fn abgeleitete_nach_kurz(
    ab: &crate::ableitung::Ableitung,
) -> std::collections::BTreeMap<String, std::collections::BTreeSet<String>> {
    let mut anzahl: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    for key in ab.je.keys() {
        let kurz = key.rsplit("::").next().unwrap_or(key).to_string();
        *anzahl.entry(kurz).or_insert(0) += 1;
    }
    let mut aus: std::collections::BTreeMap<String, std::collections::BTreeSet<String>> =
        std::collections::BTreeMap::new();
    for (key, a) in &ab.je {
        if a.unvollstaendig.is_some() {
            continue;
        }
        let kurz = key.rsplit("::").next().unwrap_or(key).to_string();
        if anzahl.get(&kurz).copied().unwrap_or(0) != 1 {
            continue;
        }
        aus.insert(kurz, a.wirkungen.clone());
    }
    aus
}

fn check_fn(
    f: &FnModel,
    model: &Model,
    scope: &Scope,
    abgeleitet: &std::collections::BTreeMap<String, std::collections::BTreeSet<String>>,
) -> Result<CheckedFn, Refusal> {
    let d = &f.decl;
    if d.klasse != Some(FnKlasse::Impl) {
        return Err(refuse("LG001", format!("function {} is not `impl`", f.name)));
    }
    if d.verfeinert.is_some() || !d.maintains.is_empty()
        || d.deadline.is_some() || d.decreases.is_some() || !d.by.is_empty()
        || d.arch.is_some() || d.when.is_some() || d.advances.is_some() || d.retires.is_some()
    {
        return Err(refuse("LG001", format!("function {} carries a form with no G counterpart", f.name)));
    }
    // `-> T or R`: the case count of the named `reason` is the `gruende`.
    let gruende = match &d.fehler {
        None => 0,
        Some(r) => *model.reasons.get(&r.text).ok_or_else(|| {
            refuse("LG005", format!("function {} names unknown reason {}", f.name, r.text))
        })?,
    };
    let mut params = Vec::new();
    for p in &d.parameter {
        params.push((p.name.text.clone(), param_ty(&p.typ, model, scope, &f.name)?));
    }
    let result = match &d.ergebnis {
        None => None,
        Some(t) => Some(int_ty(t, scope).ok_or_else(|| {
            refuse("LG002", format!("result of {} has no integer-range or bool form", f.name))
        })?),
    };
    // `requires Held(L)` names exactly the signature-held locks.
    let mut held = Vec::new();
    for r in &d.requires {
        match &r.art {
            PredArt::Held { sperre, geteilt, .. } => {
                if *geteilt {
                    return Err(refuse("LG001", format!("shared `Held` in {} has no G form", f.name)));
                }
                let Some(li) = model.locks.iter().position(|l| l.name == sperre.text) else {
                    return Err(refuse("LG005", format!("{} requires unknown lock {}", f.name, sperre.text)));
                };
                if !held.contains(&li) {
                    held.push(li);
                }
            }
            _ => return Err(refuse("LG003", format!("requires-clause in {} has no G form", f.name))),
        }
    }
    // Effects: `locks L` must say what `requires Held(L)` says; `writes`
    // names the written tables; `reads` and `costs` are NO FORM (ignored).
    // **Lane 191:** an omitted clause is derived, and the export reads it
    // like a written one (`synth_effects` above). What stays refused is the
    // omission nothing settles — an ambiguous name, a lower bound, or an
    // entry with no written form.
    let synth: Option<Wirkungen>;
    let effects = match &d.effects {
        Some(w) => w,
        None => {
            synth = abgeleitet.get(&f.name).and_then(synth_effects);
            synth.as_ref().ok_or_else(|| {
                refuse("LG001", format!("function {} has no `effects`", f.name))
            })?
        }
    };
    let mut effect_locks = Vec::new();
    let mut writes = Vec::new();
    for w in &effects.liste {
        match &w.art {
            // `reads` is the computed footprint (NO FORM); `writes` is read
            // by the second loop below.
            WirkungArt::Liest(_) | WirkungArt::Schreibt(_) | WirkungArt::Rein | WirkungArt::Divergiert => {}
            WirkungArt::Sperrt(o) => {
                if !o.suffixe.is_empty() {
                    return Err(refuse("LG005", format!("locks-clause in {} names {}", f.name, o.text())));
                }
                let Some(li) = model.locks.iter().position(|l| l.name == o.basis.text) else {
                    return Err(refuse("LG005", format!("{} locks unknown {}", f.name, o.basis.text)));
                };
                if !effect_locks.contains(&li) {
                    effect_locks.push(li);
                }
            }
            _ => return Err(refuse("LG001", format!("effect in {} has no G form", f.name))),
        }
    }
    for w in &effects.liste {
        if let WirkungArt::Schreibt(o) = &w.art {
            writes.push(write_table(o, &params, model, &f.name)?);
        }
    }
    // Deduplicate writes while keeping order.
    let mut seen = Vec::new();
    for t in writes {
        if !seen.contains(&t) {
            seen.push(t);
        }
    }
    let writes = seen;
    let FnRumpf::Block(body) = &d.rumpf else {
        return Err(refuse("LG004", format!("function {} has no block body", f.name)));
    };
    // What the body takes and calls (names only; translation refuses strictly).
    let mut scan = Scan::default();
    scan_block(body, &mut scan);
    let mut taken = Vec::new();
    for name in &scan.taken {
        let Some(li) = model.locks.iter().position(|l| &l.name == name) else {
            return Err(refuse("LG005", format!("function {} takes unknown lock {name}", f.name)));
        };
        if !taken.contains(&li) {
            taken.push(li);
        }
    }
    // `requires Held(L)` names the signature-held set; an effect `locks L`
    // beyond it travels through the `locks` statement taking it (119), and
    // an effect below it (108: readers holding by signature without
    // redeeming an effect) is that statement's absence.
    for l in &effect_locks {
        if !held.contains(l) && !taken.contains(l) {
            return Err(refuse(
                "LG001",
                format!("function {}: `locks {}` is neither held by signature nor taken in the body",
                    f.name, model.locks[*l].name),
            ));
        }
    }
    // The lock floor: the minimum rank the body takes, or `none`.
    let boden = taken.iter().map(|li| model.locks[*li].rank).min();
    Ok(CheckedFn { name: f.name.clone(), params, result, held, writes, ensures: d.ensures.clone(), body: body.clone(), gruende, boden, calls: scan.calls })
}

/// The table a `writes` place names: `writes k.slots` through a pointer
/// parameter, or `writes T.slots` at a table.
fn write_table(o: &Ort, params: &[(String, ParamTy)], model: &Model, fname: &str) -> Result<usize, Refusal> {
    let [OrtSuffix::Feld(slots)] = o.suffixe.as_slice() else {
        return Err(refuse("LG001", format!("writes-clause in {fname} names {}", o.text())));
    };
    if slots.text != "slots" {
        return Err(refuse("LG001", format!("writes-clause in {fname} names {}", o.text())));
    }
    if let Some(ti) = model.tables.iter().position(|t| t.name == o.basis.text) {
        return Ok(ti);
    }
    for (pname, pty) in params {
        if pname == &o.basis.text {
            match pty {
                ParamTy::Ptr { table, .. } => return Ok(*table),
                _ => {
                    return Err(refuse("LG001", format!("writes-clause in {fname} names {}", o.text())));
                }
            }
        }
    }
    Err(refuse("LG005", format!("writes-clause in {fname} names unknown {}", o.text())))
}

fn param_ty(t: &TypExpr, model: &Model, scope: &Scope, fname: &str) -> Result<ParamTy, Refusal> {
    match t {
        TypExpr::Zeiger(p) => {
            if !matches!(p.raum, Raum::Normal) {
                return Err(refuse("LG002", format!("address space in {fname} has no G form")));
            }
            // `own` travels as read-write: ownership carries both rights.
            let write = p.rechte.iter().any(|r| matches!(r, Recht::LesenSchreiben | Recht::Schreiben | Recht::Eigen(_)));
            if !p.rechte.iter().any(|r| matches!(r, Recht::Lesen | Recht::Schreiben | Recht::LesenSchreiben | Recht::Eigen(_))) {
                return Err(refuse("LG002", format!("pointer right in {fname} has no G form")));
            }
            let TypExpr::Pfad(path) = &p.ziel else {
                return Err(refuse("LG002", format!("pointer target in {fname} has no G form")));
            };
            let Some(name) = path.einfach() else {
                return Err(refuse("LG002", format!("pointer target in {fname} has no G form")));
            };
            let Some(ti) = model.tables.iter().position(|t| t.name == name.text) else {
                return Err(refuse("LG005", format!("pointer in {fname} names unknown table {}", name.text)));
            };
            Ok(ParamTy::Ptr { table: ti, write })
        }
        TypExpr::Index { tabelle, optional, .. } => {
            if *optional {
                return Err(refuse("LG002", format!("optional index in {fname} has no G form")));
            }
            let Some(ti) = model.tables.iter().position(|t| t.name == tabelle.text) else {
                return Err(refuse("LG005", format!("index in {fname} names unknown table {}", tabelle.text)));
            };
            Ok(ParamTy::Index { table: ti })
        }
        t => match int_ty(t, scope) {
            Some(VTy::Int { lo, hi, bits }) => Ok(ParamTy::Int { lo, hi, bits }),
            Some(VTy::Bool) => Ok(ParamTy::Bool),
            _ => Err(refuse("LG002", format!("parameter type in {fname} has no G form"))),
        },
    }
}

/// A `let` annotation as a G type: an integer range, `bool`, or an index.
fn annot_ty(t: &TypExpr, model: &Model, scope: &Scope, fname: &str) -> Result<VTy, Refusal> {
    if let Some(ty) = int_ty(t, scope) {
        return Ok(ty);
    }
    if let TypExpr::Index { tabelle, optional, .. } = t {
        if !optional {
            if let Some(ti) = model.tables.iter().position(|t| t.name == tabelle.text) {
                return Ok(VTy::Index { table: ti });
            }
        }
    }
    Err(refuse("LG002", format!("`let` annotation in {fname} has no G form")))
}

/// One table: `count` and one integer range per slot field. Table invariants,
/// generated `ops`, tree edges and the occupancy mark have no G form.
fn read_table(t: &Tabelle, scope: &Scope) -> Result<TableModel, Refusal> {
    if !t.invarianten.is_empty() || !t.ops.is_empty() || t.baum.is_some() || t.belegt.is_some() {
        return Err(refuse("LG001", format!("table {} carries a form with no G counterpart", t.name.text)));
    }
    // An `owner` mark would travel in `braucht` beside the locks; the export
    // writes `eigner := fun _ => []`, so accepting one would silently drop it.
    if t.eigner.is_some() {
        return Err(refuse("LG001", format!("table {} has an `owner` mark with no G form", t.name.text)));
    }
    // A `backed` mark and table-level constants have no carrier in G either.
    if t.hinterlegt.is_some() {
        return Err(refuse("LG001", format!("table {} has a `backed` mark with no G form", t.name.text)));
    }
    if !t.konstanten.is_empty() {
        return Err(refuse("LG001", format!("table {} carries constants with no G form", t.name.text)));
    }
    let Some(cap) = t.kapazitaet.as_ref() else {
        return Err(refuse("LG005", format!("table {} has no `count`", t.name.text)));
    };
    let Some(count) = numeral(cap, scope) else {
        return Err(refuse("LG005", format!("table {} has no numeric `count`", t.name.text)));
    };
    let Some(slot) = t.slot.as_ref() else {
        return Err(refuse("LG001", format!("table {} has no slot", t.name.text)));
    };
    let mut fields = Vec::new();
    for f in &slot.felder {
        // `by ops` is a writer discipline the checker holds; the export
        // translates the accesses as written, so it is NO FORM here.
        match &f.typ {
            SlotTyp::Typ(ty) => {
                let Some(ty) = int_ty(ty, scope) else {
                    return Err(refuse("LG002", format!("field {} has no integer-range or bool form", f.name.text)));
                };
                fields.push(FieldModel { name: f.name.text.clone(), ty });
            }
            SlotTyp::Wrapping(_) => {
                return Err(refuse("LG002", format!("field {} is wrapping", f.name.text)));
            }
        }
    }
    if fields.is_empty() {
        return Err(refuse("LG001", format!("table {} has no fields", t.name.text)));
    }
    Ok(TableModel { name: t.name.text.clone(), count, fields })
}

/// One lock: its rank and the tables its `protects` names (by table or by
/// field). Masking and the shared branch have no G form.
fn read_lock(l: &LockDecl, model: &Model) -> Result<LockModel, Refusal> {
    if l.maskiert.is_some() || l.geteilte_haltezeit.is_some() {
        return Err(refuse("LG001", format!("lock {} carries a form with no G counterpart", l.name.text)));
    }
    let ExprArt::Zahl(rank) = &l.rang.art else {
        return Err(refuse("LG005", format!("lock {} has no numeric rank", l.name.text)));
    };
    let rank = i128::try_from(*rank).map_err(|_| refuse("LG005", format!("lock {} rank too large", l.name.text)))?;
    let mut guards = Vec::new();
    for o in &l.schuetzt {
        if !o.suffixe.is_empty() {
            return Err(refuse("LG005", format!("lock {} protects {}", l.name.text, o.text())));
        }
        let mut found = None;
        for (ti, t) in model.tables.iter().enumerate() {
            if t.name == o.basis.text || t.fields.iter().any(|f| f.name == o.basis.text) {
                found = Some(ti);
                break;
            }
        }
        let Some(ti) = found else {
            return Err(refuse("LG005", format!("lock {} protects unknown {}", l.name.text, o.text())));
        };
        if !guards.contains(&ti) {
            guards.push(ti);
        }
    }
    Ok(LockModel { name: l.name.text.clone(), rank, guards, invariant: l.invariante.clone() })
}

/// Export the checked unit as a Lean file, or refuse it by name.
pub fn export(source_name: &str, tree: &Programm) -> Result<String, Refusal> {
    export_ns(source_name, tree, &namespace_of(source_name))
}

/// Export under an explicit namespace (lane 176: the obligation export states
/// duties over the same program under `<base>_oblig`, so the two exports of
/// one file never declare the same names even when both are imported).
pub fn export_ns(source_name: &str, tree: &Programm, namespace: &str) -> Result<String, Refusal> {
    let model = collect(source_name, tree)?;
    let scope = rescope(tree)?;
    // **Lane 191:** one derivation for the whole unit; every omitted clause
    // with a settled set reads like a written one in `check_fn`.
    let abgeleitet = abgeleitete_nach_kurz(&crate::ableitung::leite_ab(tree, true));
    let mut checked = Vec::new();
    for f in &model.fns {
        checked.push(check_fn(f, &model, &scope, &abgeleitet)?);
    }
    let mut out = Out::default();
    for c in &checked {
        check_contracts(c, &model, &scope, &mut out)?;
        check_body(c, &model)?;
    }
    check_locks(&model, &scope)?;
    Ok(emit(source_name, namespace, &model, &checked, &scope, &mut out)?)
}

/// The function names of the export, in declaration order (the `g_<fn>`
/// constants an obligation export states duties over). Runs the same
/// collection as `export`, so it succeeds exactly where the export succeeds
/// and names exactly the functions the export defines.
pub fn function_names(source_name: &str, tree: &Programm) -> Result<Vec<String>, Refusal> {
    let model = collect(source_name, tree)?;
    Ok(model.fns.iter().map(|f| f.name.clone()).collect())
}

/// The checked unit behind an export: the model, every function checked,
/// and the constant/alias scope. Runs exactly the collection and checks
/// `export` runs, so it succeeds exactly where the export succeeds -- the
/// counterexample search never sees a program `lean-g` refuses.
pub(crate) struct Analyse {
    pub(crate) model: Model,
    pub(crate) fns: Vec<CheckedFn>,
    pub(crate) scope: Scope,
}

pub(crate) fn analysiere(source_name: &str, tree: &Programm) -> Result<Analyse, Refusal> {
    let model = collect(source_name, tree)?;
    let scope = rescope(tree)?;
    // The same derived `effects` the export uses (lane 191), so the analysis and the
    // export check every function against one and the same contract.
    let abgeleitet = abgeleitete_nach_kurz(&crate::ableitung::leite_ab(tree, true));
    let mut checked = Vec::new();
    for f in &model.fns {
        checked.push(check_fn(f, &model, &scope, &abgeleitet)?);
    }
    let mut out = Out::default();
    for c in &checked {
        check_contracts(c, &model, &scope, &mut out)?;
        check_body(c, &model)?;
    }
    check_locks(&model, &scope)?;
    Ok(Analyse { model, fns: checked, scope })
}

/// One `ensures` clause as a flat list of conjunct leaves: `Und` chains
/// (across and inside clauses) split apart, everything else travels as one
/// leaf through `tr_ensures`. The caller ascribes each leaf with the
/// `ensures` expression type, exactly as `tr_contract` does for the whole
/// conjunction -- so per-conjunct `#eval` reads the same term the program's
/// `gEns_` conjoins.
pub(crate) fn ensures_konjunkte(
    cf: &CheckedFn,
    model: &Model,
    scope: &Scope,
) -> Result<Vec<String>, Refusal> {
    fn flach(
        p: &Pred,
        ctx: &Ctx,
        model: &Model,
        scope: &Scope,
        fname: &str,
        out: &mut Out,
        acc: &mut Vec<String>,
    ) -> Result<(), Refusal> {
        match &p.art {
            PredArt::Und(a, b) => {
                flach(a, ctx, model, scope, fname, out, acc)?;
                flach(b, ctx, model, scope, fname, out, acc)?;
            }
            PredArt::Klammer(q) => flach(q, ctx, model, scope, fname, out, acc)?,
            _ => acc.push(tr_ensures(p, ctx, model, scope, fname, out)?),
        }
        Ok(())
    }
    let ctx = ensures_ctx(cf, model);
    let mut out = Out::default();
    let mut acc = Vec::new();
    for p in &cf.ensures {
        flach(p, &ctx, model, scope, &cf.name, &mut out, &mut acc)?;
    }
    Ok(acc)
}

/// Rebuild the constant/alias scope (pass one of `collect`, rerun for the
/// checked phase so `export` stays a straight line).
fn rescope(tree: &Programm) -> Result<Scope, Refusal> {
    let mut scope = Scope::default();
    fn go(scope: &mut Scope, items: &[Item]) -> Result<(), Refusal> {
        for item in items {
            match &item.art {
                ItemArt::Modul(m) => go(scope, &m.items)?,
                ItemArt::Konst(k) => {
                    let Some(v) = numeral(&k.wert, scope) else {
                        return Err(refuse("LG005", format!("const {} is not a numeral", k.name.text)));
                    };
                    scope.consts.insert(k.name.text.clone(), v);
                }
                ItemArt::Typ(t) => {
                    let r = t.rumpf.as_ref().expect("checked in collect");
                    // Checked in `collect`: an alias is an integer range.
                    if let Some(VTy::Int { lo, hi, bits }) = int_ty(r, scope) {
                        scope.aliases.insert(t.name.text.clone(), (lo, hi, bits));
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }
    go(&mut scope, &tree.items)?;
    Ok(scope)
}

/// What translation collects for the emission: the call sites (caller,
/// held-context tag, callee, with the floor facts their proofs need) and
/// the guard facts (function, tag, table) each use site names.
#[derive(Default)]
struct Out {
    hps: Vec<HpNeeded>,
    darf: Vec<(String, String, usize)>,
}

#[derive(Clone, PartialEq, Eq)]
struct HpNeeded {
    caller: String,
    tag: String,
    callee: String,
    /// The callee's floor, where the call holds extras (`hx`).
    extra_floor: Option<i128>,
    /// The caller/callee floors, where the caller is floored (`hb`).
    hb: Option<(i128, i128)>,
}

impl Out {
    fn hp(&mut self, need: HpNeeded) {
        if !self.hps.contains(&need) {
            self.hps.push(need);
        }
    }

    fn braucht(&mut self, fname: &str, tag: &str, t: usize) {
        let key = (fname.to_string(), tag.to_string(), t);
        if !self.darf.contains(&key) {
            self.darf.push(key);
        }
    }
}

/// How a bound name travels: a parameter, a `let` binding, or a `traverse`
/// binder over a table (whose type is exactly the model's loop index).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NameKind {
    Param,
    Let,
    Loop,
}

/// Translation context: the value environment (head-first: the innermost
/// binding is position 0), the held locks, and the exact `Γ`/`Λ` terms.
/// Bodies see the parameters; `ensures` sees the result first (`ErgCtx`,
/// via `with_result`). `gamma`/`lambda` are the exact terms for type
/// ascriptions: every emitted tactic proof is ascribed a fully concrete
/// type, because elaboration order must never decide whether `D` is pinned
/// when a `by decide` runs. `locks_open` tracks whether a `locks` block is
/// enclosing (then `Λ` is not the signature end, and no `ret` fits it).
#[derive(Clone)]
struct Ctx<'a> {
    cf: &'a CheckedFn,
    model: &'a Model,
    names: Vec<(String, VTy, NameKind)>,
    held: Vec<usize>,
    tag: String,
    locks_open: bool,
    in_body: bool,
    with_result: bool,
    gamma: String,
    lambda: String,
}

fn body_ctx<'a>(cf: &'a CheckedFn, model: &'a Model) -> Ctx<'a> {
    let g = lean_fn(&cf.name);
    let names = cf.params.iter().map(|(n, p)| (n.clone(), p.vty(model), NameKind::Param)).collect();
    Ctx {
        cf,
        model,
        names,
        held: cf.held.clone(),
        tag: String::new(),
        locks_open: false,
        in_body: true,
        with_result: false,
        gamma: format!("gCtx_{g}"),
        lambda: format!("gL_{g}"),
    }
}

fn ensures_ctx<'a>(cf: &'a CheckedFn, model: &'a Model) -> Ctx<'a> {
    let g = lean_fn(&cf.name);
    let names = cf.params.iter().map(|(n, p)| (n.clone(), p.vty(model), NameKind::Param)).collect();
    Ctx {
        cf,
        model,
        names,
        held: cf.held.clone(),
        tag: String::new(),
        locks_open: false,
        in_body: false,
        with_result: cf.result.is_some(),
        gamma: format!("(ErgCtx (gD.params g_{g}) (gD.erg g_{g}))"),
        lambda: format!("gL_{g}"),
    }
}

impl<'a> Ctx<'a> {
    /// The de Bruijn variable at stack position `j`.
    fn var(&self, j: usize) -> String {
        let depth = if self.with_result { j + 1 } else { j };
        let mut s = ".hier".to_string();
        for _ in 0..depth {
            s = format!("(.dort {s})");
        }
        format!("(.var {s})")
    }

    fn lookup(&self, name: &str) -> Option<(usize, VTy, NameKind)> {
        self.names.iter().enumerate().find(|(_, (n, _, _))| n == name)
            .map(|(j, (_, ty, kind))| (j, ty.clone(), *kind))
    }

    /// The full `Expr` type of an index into table `t` in this context. Used
    /// as an ascription on literal indices: without it the declaration `D`
    /// is still a metavariable when the `weiter` proofs elaborate, and they
    /// fail instead of postponing.
    fn index_ty(&self, model: &Model, t: usize) -> String {
        format!("Expr gD {} {} (.index (gD.count {}))", self.gamma, self.lambda, tab_ctor(model, t))
    }

    /// Push a binding to the head (`bind` and the `traverse` binder extend
    /// `Γ` on the left).
    fn push(&self, name: String, ty: VTy, kind: NameKind) -> Ctx<'a> {
        let mut names = vec![(name, ty.clone(), kind)];
        names.extend(self.names.iter().cloned());
        Ctx {
            names,
            gamma: format!("({} :: {})", ty.term(self.model), self.gamma),
            ..self.clone()
        }
    }

    /// Enter a `locks L` body: one more witness in hand, under a longer name.
    fn locked(&self, li: usize, lock: &str) -> Ctx<'a> {
        let mut held = self.held.clone();
        held.push(li);
        Ctx {
            held,
            tag: format!("{}_in_{}", self.tag, lock),
            locks_open: true,
            lambda: format!("gL_{}{}_in_{}", lean_fn(&self.cf.name), self.tag, lock),
            ..self.clone()
        }
    }

    /// Enter a `traverse` body: the loop binder in scope.
    fn looping(&self, name: String, table: usize) -> Ctx<'a> {
        self.push(name, VTy::Index { table }, NameKind::Loop)
    }
}

/// The named guard fact for function `fname` and table `t`: proved
/// top-level with a fully concrete type (`unfold` on the access predicate +
/// `decide`), because inline the declaration stays a metavariable when the
/// proof elaborates. Only pairs whose guards the function holds get a
/// theorem; `slot_access` refuses the rest, so a reference never dangles.
fn darf_name(fname: &str, tag: &str, model: &Model, t: usize) -> String {
    format!("gDarf_{}{}_{}", lean_fn(fname), tag, model.tables[t].name)
}

/// Every table `t`'s guards must be among `held`: the generation-time half
/// of the guard proof (the Lean half is the `gDarf` theorem the use site names).
fn holds_guards(held: &[usize], model: &Model, t: usize) -> bool {
    model.locks.iter().enumerate()
        .filter(|(_, l)| l.guards.contains(&t))
        .map(|(li, _)| li)
        .all(|li| held.contains(&li))
}

/// Some guard of `t` is signature-held: the footprint half of `fussOrtGB`
/// (`waechterVon`, decided Lean-side; this mirrors it for the print decision).
fn guard_held(held: &[usize], model: &Model, t: usize) -> bool {
    model.locks.iter().enumerate()
        .filter(|(_, l)| l.guards.contains(&t))
        .map(|(li, _)| li)
        .any(|li| held.contains(&li))
}
/// The constructor names: tables, locks and fields travel as named
/// constructors of small inductives (never `Fin` literals), so every match
/// is exhaustive by constructors and every proof is `cases` + `decide`.
fn tab_ctor(model: &Model, t: usize) -> String {
    format!("GTab.{}", model.tables[t].name)
}

fn lock_ctor(model: &Model, l: usize) -> String {
    format!("GLock.{}", model.locks[l].name)
}

fn feld_type(model: &Model, t: usize) -> String {
    format!("G{}Feld", model.tables[t].name)
}

fn feld_ctor(model: &Model, t: usize, fi: usize) -> String {
    format!("{}.{}", feld_type(model, t), model.tables[t].fields[fi].name)
}

/// A parameter `Ty` as G spells it. Signatures precede the declaration,
/// so an index travels as its literal count here (as before); inside
/// bodies (`VTy::term`) it goes through `gD.count`.
fn ty_of(pty: &ParamTy, model: &Model) -> String {
    match pty {
        ParamTy::Ptr { table, write } => format!(".ptr {table} {write}"),
        ParamTy::Index { table } => format!(".index {}", model.tables[*table].count),
        ParamTy::Int { lo, hi, .. } => int_ty_str(*lo, *hi),
        ParamTy::Bool => ".bool".to_string(),
    }
}

/// Coerce `base` of type `actual` to `expected`: direct where equal, a
/// widening where the computed range fits, refused otherwise (a Lean
/// failure is not a named refusal, so the fit is decided here, in Rust).
/// The widening is ascribed with the expected type: under an
/// implicit-only position (a `bor` operand) its range would stay ambiguous.
fn fit(base: String, actual: &VTy, expected: &VTy, ctx: &Ctx, model: &Model, fname: &str) -> Result<String, Refusal> {
    match (actual, expected) {
        (VTy::Bool, VTy::Bool) => Ok(base),
        _ => {
            let Some((alo, ahi)) = actual.range(model) else {
                return Err(refuse("LG004", format!("type in {fname} has no coercion to {}", expected.term(model))));
            };
            let Some((elo, ehi)) = expected.range(model) else {
                return Err(refuse("LG004", format!("type in {fname} has no coercion to {}", expected.term(model))));
            };
            if alo == elo && ahi == ehi {
                Ok(base)
            } else if elo <= alo && ahi <= ehi {
                Ok(format!("((.weiter (by decide) (by decide) {base}) : Expr gD {} {} {})",
                    ctx.gamma, ctx.lambda, expected.term(model)))
            } else {
                Err(refuse("LG004", format!("range {alo}..{ahi} in {fname} fits no {}", expected.term(model))))
            }
        }
    }
}

/// The index expression for slot `idx` of table `t`: a literal in range,
/// an index parameter for this table, or the enclosing `traverse` binder.
fn tr_index(e: &Expr, t: usize, ctx: &Ctx, model: &Model, fname: &str) -> Result<String, Refusal> {
    let count = model.tables[t].count;
    match &e.art {
        ExprArt::Zahl(n) => {
            let n = i128::try_from(*n).map_err(|_| refuse("LG003", format!("index in {fname} too large")))?;
            if n < 0 || n >= count {
                return Err(refuse("LG003", format!("index {n} in {fname} is outside `count {count}`")));
            }
            Ok(format!("((.weiter (by decide) (by decide) (.lit {n}) : {}))", ctx.index_ty(model, t)))
        }
        ExprArt::Ort(o) if o.suffixe.is_empty() => {
            let Some((j, ty, _)) = ctx.lookup(&o.basis.text) else {
                return Err(refuse("LG005", format!("unknown name {} in {fname}", o.basis.text)));
            };
            match &ty {
                VTy::Index { table } if *table == t => Ok(ctx.var(j)),
                _ => Err(refuse("LG004", format!("index {} in {fname} has no G form", o.text()))),
            }
        }
        _ => Err(refuse("LG003", format!("index in {fname} has no G form"))),
    }
}

/// A slot read `p.slots[i].f` / `T.slots[i].f`: table, field, index term,
/// the pointer parameter it goes through (`None` at a table name), and the
/// field type. Guards are read against the enclosing held set (a `locks`
/// body holds one more), and the guard proof is the theorem of that context.
fn slot_access(o: &Ort, ctx: &Ctx, model: &Model, fname: &str) -> Result<(usize, usize, String, Option<usize>, VTy), Refusal> {
    let [OrtSuffix::Feld(slots), OrtSuffix::Index(idx), OrtSuffix::Feld(f)] = o.suffixe.as_slice() else {
        return Err(refuse("LG003", format!("place {} in {fname} has no G form", o.text())));
    };
    if slots.text != "slots" {
        return Err(refuse("LG003", format!("place {} in {fname} has no G form", o.text())));
    }
    let (t, through) = if let Some(ti) = model.tables.iter().position(|t| t.name == o.basis.text) {
        (ti, None)
    } else if let Some((j, ty, _)) = ctx.lookup(&o.basis.text) {
        match &ty {
            VTy::Ptr { table, .. } => (*table, Some(j)),
            _ => return Err(refuse("LG003", format!("place {} in {fname} has no G form", o.text()))),
        }
    } else {
        return Err(refuse("LG005", format!("unknown name {} in {fname}", o.basis.text)));
    };
    let Some(fi) = model.tables[t].fields.iter().position(|fd| fd.name == f.text) else {
        return Err(refuse("LG005", format!("unknown field {} in {fname}", o.text())));
    };
    if !holds_guards(&ctx.held, model, t) {
        return Err(refuse("LG004", format!("access to {} in {fname} holds no guard (no proof)", o.text())));
    }
    let index = tr_index(idx, t, ctx, model, fname)?;
    let ty = model.tables[t].fields[fi].ty.clone();
    Ok((t, fi, index, through, ty))
}

/// The guard proof a slot access names: the theorem of its held context.
fn darf_at(ctx: &Ctx, model: &Model, fname: &str, t: usize, out: &mut Out) -> String {
    out.braucht(fname, &ctx.tag, t);
    darf_name(fname, &ctx.tag, model, t)
}

/// A value expression with its G type: literals, places, parameters and
/// `let` bindings, arithmetic (`+`/`-`/`*`/negation), bit operations with a
/// named width, integer conversions, limit words, comparisons and boolean
/// combinations. A call in value position has no `Expr` form (LG003); a
/// reason value (`R::F`) has none here either.
fn tr_typed(e: &Expr, ctx: &Ctx, model: &Model, scope: &Scope, fname: &str, out: &mut Out) -> Result<(String, VTy), Refusal> {
    match &e.art {
        // A literal travels bare: the `weiter` to its use type is
        // printed by `fit`, where the expected type is concrete (an
        // unascribed inner `weiter` leaves its range ambiguous and its
        // `by decide` without a goal).
        ExprArt::Zahl(n) => {
            let n = i128::try_from(*n).map_err(|_| refuse("LG003", format!("literal in {fname} too large")))?;
            Ok((lit_term(n, ctx), VTy::Int { lo: n, hi: n, bits: None }))
        }
        ExprArt::Wahr => Ok((".wahr".to_string(), VTy::Bool)),
        ExprArt::Falsch => Ok((".falsch".to_string(), VTy::Bool)),
        ExprArt::Ort(o) if o.suffixe.is_empty() => {
            // A limit word (`u32::max`) travels as its number.
            if let Some((_, _, wert)) = crate::umgebung::grenzwort(o) {
                return Ok((lit_term(wert, ctx), VTy::Int { lo: wert, hi: wert, bits: None }));
            }
            let Some((j, ty, _)) = ctx.lookup(&o.basis.text) else {
                return Err(refuse("LG005", format!("unknown name {} in {fname}", o.basis.text)));
            };
            Ok((ctx.var(j), ty))
        }
        ExprArt::Ort(o) => {
            // A limit word (`u32::max`) or sugared one (`u13::max`) travels
            // as its number.
            if let Some((_, _, wert)) = crate::umgebung::grenzwort(o) {
                return Ok((lit_term(wert, ctx), VTy::Int { lo: wert, hi: wert, bits: None }));
            }
            if let Some(wert) = zucker_grenzwort(o) {
                return Ok((lit_term(wert, ctx), VTy::Int { lo: wert, hi: wert, bits: None }));
            }
            let (t, fi, index, through, ty) = slot_access(o, ctx, model, fname)?;
            let proof = darf_at(ctx, model, fname, t, out);
            let base = if let Some(j) = through {
                format!("(Expr.durch (D := gD) {} {} rfl {} ({index}) {proof})", ctx.var(j), tab_ctor(model, t), feld_ctor(model, t, fi))
            } else {
                format!("(Expr.slot (D := gD) {} {} ({index}) {proof})", tab_ctor(model, t), feld_ctor(model, t, fi))
            };
            Ok((base, ty))
        }
        ExprArt::Ergebnis => {
            if ctx.in_body {
                return Err(refuse("LG003", format!("`result` in {fname} has no G form here")));
            }
            let Some(ty) = ctx.cf.result.clone() else {
                return Err(refuse("LG003", format!("`result` in {fname} has no G form here")));
            };
            Ok(("(.var .hier)".to_string(), ty))
        }
        ExprArt::Klammer(x) => tr_typed(x, ctx, model, scope, fname, out),
        ExprArt::Binaer(op, a, b) => tr_binaer(*op, a, b, ctx, model, scope, fname, out),
        ExprArt::Unaer(op, x) => tr_unaer(*op, x, ctx, model, scope, fname, out),
        ExprArt::Ruf(r) => tr_conversion(r, ctx, model, scope, fname, out),
        _ => Err(refuse("LG003", format!("expression in {fname} has no G form"))),
    }
}

/// A boolean expression: comparisons, `&&`/`||`/`!`, literals and bool
/// places. Anything else (including `==` over bools, for which G has no
/// constructor) is refused by name.
fn tr_bool(e: &Expr, ctx: &Ctx, model: &Model, scope: &Scope, fname: &str, out: &mut Out) -> Result<String, Refusal> {
    let (term, ty) = tr_typed(e, ctx, model, scope, fname, out)?;
    match ty {
        VTy::Bool => Ok(term),
        _ => Err(refuse("LG003", format!("condition in {fname} has no bool form"))),
    }
}

/// A value against the expected `Ty`: computed, then fitted.
fn tr_value(e: &Expr, expected: &VTy, ctx: &Ctx, model: &Model, scope: &Scope, fname: &str, out: &mut Out) -> Result<String, Refusal> {
    let (term, ty) = tr_typed(e, ctx, model, scope, fname, out)?;
    fit(term, &ty, expected, ctx, model, fname)
}

/// A binary operator with both sides computed.
fn tr_binaer(op: BinOp, a: &Expr, b: &Expr, ctx: &Ctx, model: &Model, scope: &Scope, fname: &str, out: &mut Out) -> Result<(String, VTy), Refusal> {
    match op {
        BinOp::Plus | BinOp::Minus | BinOp::Mal => {
            let (la, ta) = tr_typed(a, ctx, model, scope, fname, out)?;
            let (lb, tb) = tr_typed(b, ctx, model, scope, fname, out)?;
            let Some((l1, h1)) = ta.range(model) else {
                return Err(refuse("LG003", format!("arithmetic in {fname} has no G form")));
            };
            let Some((l2, h2)) = tb.range(model) else {
                return Err(refuse("LG003", format!("arithmetic in {fname} has no G form")));
            };
            let (lo, hi, ctor) = match op {
                BinOp::Plus => (l1.checked_add(l2), h1.checked_add(h2), "add"),
                BinOp::Minus => (l1.checked_sub(h2), h1.checked_sub(l2), "sub"),
                _ => {
                    let lows = [l1.checked_mul(l2), l1.checked_mul(h2), h1.checked_mul(l2), h1.checked_mul(h2)];
                    let (mut lo, mut hi) = (None, None);
                    for v in lows.into_iter().flatten() {
                        lo = Some(lo.map_or(v, |m: i128| m.min(v)));
                        hi = Some(hi.map_or(v, |m: i128| m.max(v)));
                    }
                    (lo, hi, "mul")
                }
            };
            let (Some(lo), Some(hi)) = (lo, hi) else {
                return Err(refuse("LG003", format!("arithmetic in {fname} leaves the checked range")));
            };
            Ok((format!("(.{ctor} {la} {lb})"), VTy::Int { lo, hi, bits: None }))
        }
        BinOp::BitUnd | BinOp::BitOder | BinOp::BitXor | BinOp::SchiebLinks | BinOp::SchiebRechts => {
            tr_bitop(op, a, b, ctx, model, scope, fname, out)
        }
        BinOp::Und | BinOp::Oder => {
            let la = tr_bool(a, ctx, model, scope, fname, out)?;
            let lb = tr_bool(b, ctx, model, scope, fname, out)?;
            let ctor = if op == BinOp::Und { "und" } else { "oder" };
            Ok((format!("(.{ctor} {la} {lb})"), VTy::Bool))
        }
        BinOp::Gleich | BinOp::Ungleich | BinOp::Kleiner | BinOp::KleinerGleich | BinOp::Groesser | BinOp::GroesserGleich => {
            let (la, ta) = tr_typed(a, ctx, model, scope, fname, out)?;
            let (lb, tb) = tr_typed(b, ctx, model, scope, fname, out)?;
            if ta.range(model).is_none() || tb.range(model).is_none() {
                return Err(refuse("LG003", format!("comparison in {fname} has no G form")));
            }
            let term = match op {
                BinOp::Gleich => format!("(.eq {la} {lb})"),
                BinOp::Ungleich => format!("(.nicht (.eq {la} {lb}))"),
                BinOp::Kleiner => format!("(.lt {la} {lb})"),
                BinOp::KleinerGleich => format!("(.le {la} {lb})"),
                BinOp::Groesser => format!("(.lt {lb} {la})"),
                _ => format!("(.le {lb} {la})"),
            };
            Ok((term, VTy::Bool))
        }
        _ => Err(refuse("LG003", format!("operator in {fname} has no G form"))),
    }
}

/// A unary operator.
fn tr_unaer(op: UnOp, x: &Expr, ctx: &Ctx, model: &Model, scope: &Scope, fname: &str, out: &mut Out) -> Result<(String, VTy), Refusal> {
    match op {
        UnOp::Nicht => {
            let e = tr_bool(x, ctx, model, scope, fname, out)?;
            Ok((format!("(.nicht {e})"), VTy::Bool))
        }
        UnOp::Negativ => {
            let (e, ty) = tr_typed(x, ctx, model, scope, fname, out)?;
            let Some((lo, hi)) = ty.range(model) else {
                return Err(refuse("LG003", format!("negation in {fname} has no G form")));
            };
            Ok((format!("(.neg {e})"), VTy::Int { lo: -hi, hi: -lo, bits: None }))
        }
        UnOp::BitNicht => {
            // `~x` is `x ^ (2^w - 1)` over the storage width, the exact
            // range M1 reads (`beispiele/61`).
            let (e, ty) = tr_typed(x, ctx, model, scope, fname, out)?;
            let Some((l1, h1)) = ty.range(model) else {
                return Err(refuse("LG003", format!("complement in {fname} has no G form")));
            };
            let Some(w) = ty.bits() else {
                return Err(refuse("LG003", format!("complement in {fname} names no width")));
            };
            if w > 64 {
                return Err(refuse("LG003", format!("complement in {fname} names no width")));
            }
            if l1 < 0 || h1 >= (1i128 << w) {
                return Err(refuse("LG003", format!("complement in {fname} leaves its width")));
            }
            let mask = (1i128 << w) - 1;
            let m = lit_term(mask, ctx);
            Ok((format!("(.bxor {w} (by decide) (by decide) (by decide) (by decide) {e} {m})"), VTy::Int { lo: 0, hi: mask, bits: Some(w) }))
        }
    }
}

/// A bit operation (`&`/`|`/`^`/`<<`/`>>`) with the width off the left
/// operand's storage. Every proof is decided here, in Rust, before it is
/// printed as `by decide`.
fn tr_bitop(op: BinOp, a: &Expr, b: &Expr, ctx: &Ctx, model: &Model, scope: &Scope, fname: &str, out: &mut Out) -> Result<(String, VTy), Refusal> {
    let (la, ta) = tr_typed(a, ctx, model, scope, fname, out)?;
    let (lb, tb) = tr_typed(b, ctx, model, scope, fname, out)?;
    let Some((l1, h1)) = ta.range(model) else {
        return Err(refuse("LG003", format!("bit operation in {fname} has no G form")));
    };
    let Some((l2, h2)) = tb.range(model) else {
        return Err(refuse("LG003", format!("bit operation in {fname} has no G form")));
    };
    if l1 < 0 || l2 < 0 {
        return Err(refuse("LG003", format!("bit operation in {fname} over a negative range has no G form")));
    }
    let Some(w) = ta.bits() else {
        return Err(refuse("LG003", format!("bit operation in {fname} names no width")));
    };
    if w > 64 {
        return Err(refuse("LG003", format!("bit operation in {fname} names no width")));
    }
    let top: i128 = 1i128 << w;
    match op {
        BinOp::BitUnd => Ok((format!("(.band (by decide) (by decide) {la} {lb})"), VTy::Int { lo: 0, hi: h1, bits: None })),
        BinOp::BitOder | BinOp::BitXor => {
            if h1 >= top || h2 >= top {
                return Err(refuse("LG003", format!("bit operation in {fname} leaves its width")));
            }
            let ctor = if op == BinOp::BitOder { "bor" } else { "bxor" };
            Ok((format!("(.{ctor} {w} (by decide) (by decide) (by decide) (by decide) {la} {lb})"), VTy::Int { lo: 0, hi: top - 1, bits: Some(w) }))
        }
        BinOp::SchiebLinks | BinOp::SchiebRechts => {
            if h1 >= top || h2 >= w as i128 {
                return Err(refuse("LG003", format!("shift in {fname} leaves its width")));
            }
            let ctor = if op == BinOp::SchiebLinks { "shl" } else { "shr" };
            let hi = if op == BinOp::SchiebLinks {
                let Some(hi) = h1.checked_mul(1i128 << (h2 as u32)) else {
                    return Err(refuse("LG003", format!("shift in {fname} leaves the checked range")));
                };
                hi
            } else {
                h1
            };
            Ok((format!("(.{ctor} {w} (by decide) (by decide) (by decide) (by decide) {la} {lb})"), VTy::Int { lo: 0, hi, bits: None }))
        }
        _ => Err(refuse("LG003", format!("operator in {fname} has no G form"))),
    }
}

/// An integer conversion `u64(x)`: a call whose path names a type is the
/// widening the checker reads (`SYNTAX.md` G9) -- exactly `Expr.weiter`.
fn tr_conversion(r: &Ruf, ctx: &Ctx, model: &Model, scope: &Scope, fname: &str, out: &mut Out) -> Result<(String, VTy), Refusal> {
    if !r.marken.is_empty() {
        return Err(refuse("LG003", format!("call in {fname} has no G form here")));
    }
    let Some(path) = r.path() else {
        return Err(refuse("LG003", format!("indirect call in {fname} has no G form here")));
    };
    if path.teile.len() != 1 || r.argumente.len() != 1 {
        // A one-segment call to a declared function in value position has
        // no `Expr` form (`Endblock` binds no calls); anything else names
        // nothing.
        if path.teile.len() == 1 {
            if let Some(last) = path.teile.last() {
                if model.fns.iter().any(|f| f.name == last.text) {
                    return Err(refuse("LG003", format!("call in {fname} has no G form here")));
                }
            }
        }
        return Err(refuse("LG005", format!("call in {fname} names unknown {}", path.text())));
    }
    let word = path.teile[0].text.clone();
    // The target range: an alias, a sugared width, a bare integer word --
    // or, by name, nothing else.
    let target = if let Some((lo, hi, bits)) = scope.aliases.get(&word).copied() {
        VTy::Int { lo, hi, bits }
    } else if let Some(kw) = Kw::suche(&word) {
        if !kw.ist_intty() {
            return Err(refuse("LG005", format!("call in {fname} names unknown {word}")));
        }
        let Some((breite, vz)) = crate::umgebung::breite_von(kw) else {
            return Err(refuse("LG005", format!("call in {fname} names unknown {word}")));
        };
        let (lo, hi) = crate::typen::grenzen(breite, vz);
        VTy::Int { lo, hi, bits: Some(breite as u32) }
    } else if let Some((lo, hi)) = gabbro_syntax::zucker_bereich(&word) {
        // A sugared width (`u13`): the exact range from the desugar rule
        // itself, so the constant and the type can never disagree. No
        // storage width travels (bit operations on it refuse by name).
        VTy::Int { lo, hi, bits: None }
    } else if model.fns.iter().any(|f| f.name == word) {
        return Err(refuse("LG003", format!("call in {fname} has no G form here")));
    } else {
        return Err(refuse("LG005", format!("call in {fname} names unknown {word}")));
    };
    // The checker gives the conversion the FULL target range; the argument
    // fits it exactly where M1 accepted the program (decided both here, in
    // Rust, and Lean-side by the printed `weiter`).
    let (arg, aty) = tr_typed(&r.argumente[0], ctx, model, scope, fname, out)?;
    Ok((fit(arg, &aty, &target, ctx, model, fname)?, target))
}

/// `old(p.slots[i].f)` / `old(T.slots[i].f)` in an `ensures`: the entry value
/// of the table slot (a pointer's `old` is the table's `old` -- the hand
/// translation reads it the same way). Integer slots only: the snapshot
/// arithmetic is conserved sums.
fn tr_old(o: &Ort, ctx: &Ctx, model: &Model, fname: &str, out: &mut Out) -> Result<(String, VTy), Refusal> {
    let (t, fi, index, _, ty) = slot_access(o, ctx, model, fname)?;
    if !matches!(ty, VTy::Int { .. }) {
        return Err(refuse("LG003", format!("`old` of {} in {fname} has no G form", o.text())));
    }
    let proof = darf_at(ctx, model, fname, t, out);
    Ok((format!("(Expr.altSlot (D := gD) {} {} ({index}) {proof})", tab_ctor(model, t), feld_ctor(model, t, fi)), ty))
}

/// One side of an `ensures` comparison: the term and its type.
fn tr_side(e: &Expr, ctx: &Ctx, model: &Model, scope: &Scope, fname: &str, out: &mut Out) -> Result<(String, VTy), Refusal> {
    match &e.art {
        ExprArt::Zahl(n) => {
            let n = i128::try_from(*n).map_err(|_| refuse("LG003", format!("literal in {fname} too large")))?;
            Ok((lit_term(n, ctx), VTy::Int { lo: n, hi: n, bits: None }))
        }
        ExprArt::Ort(o) if o.suffixe.is_empty() => {
            if let Some((_, _, wert)) = crate::umgebung::grenzwort(o) {
                return Ok((lit_term(wert, ctx), VTy::Int { lo: wert, hi: wert, bits: None }));
            }
            let Some((j, ty, _)) = ctx.lookup(&o.basis.text) else {
                return Err(refuse("LG005", format!("unknown name {} in {fname}", o.basis.text)));
            };
            Ok((ctx.var(j), ty))
        }
        ExprArt::Ort(o) => {
            let (t, fi, index, through, ty) = slot_access(o, ctx, model, fname)?;
            let proof = darf_at(ctx, model, fname, t, out);
            let base = if let Some(j) = through {
                format!("(Expr.durch (D := gD) {} {} rfl {} ({index}) {proof})", ctx.var(j), tab_ctor(model, t), feld_ctor(model, t, fi))
            } else {
                format!("(Expr.slot (D := gD) {} {} ({index}) {proof})", tab_ctor(model, t), feld_ctor(model, t, fi))
            };
            Ok((base, ty))
        }
        ExprArt::Ergebnis => {
            let Some(ty) = ctx.cf.result.clone() else {
                return Err(refuse("LG003", format!("`result` in {fname} has no G form here")));
            };
            Ok(("(.var .hier)".to_string(), ty))
        }
        ExprArt::Alt(o) => tr_old(o, ctx, model, fname, out),
        ExprArt::Klammer(x) => tr_side(x, ctx, model, scope, fname, out),
        _ => Err(refuse("LG003", format!("comparison in {fname} has no G form"))),
    }
}

/// One `ensures` comparison. G has `lt`/`le`/`eq` over integers only; the
/// rest are folded, and anything else is refused by name.
fn tr_cmp(op: &BinOp, l: &Expr, r: &Expr, ctx: &Ctx, model: &Model, scope: &Scope, fname: &str, out: &mut Out) -> Result<String, Refusal> {
    let (ls, lt) = tr_side(l, ctx, model, scope, fname, out)?;
    let (rs, rt) = tr_side(r, ctx, model, scope, fname, out)?;
    if lt.range(model).is_none() || rt.range(model).is_none() {
        return Err(refuse("LG003", format!("comparison in {fname} has no G form")));
    }
    // Limit words and literals carry their own range into the comparison:
    // `.eq`/`.lt`/`.le` read both sides as they stand.
    match op {
        BinOp::Gleich => Ok(format!("(.eq {ls} {rs})")),
        BinOp::Ungleich => Ok(format!("(.nicht (.eq {ls} {rs}))")),
        BinOp::Kleiner => Ok(format!("(.lt {ls} {rs})")),
        BinOp::KleinerGleich => Ok(format!("(.le {ls} {rs})")),
        BinOp::Groesser => Ok(format!("(.lt {rs} {ls})")),
        BinOp::GroesserGleich => Ok(format!("(.le {rs} {ls})")),
        _ => Err(refuse("LG003", format!("operator in {fname} has no G form"))),
    }
}

/// A lock invariant as a `Speicher gD → Bool` body (lane 156): the `inv`
/// arm of the `SperrInv` family `gS`. Only the checker-pure fragment over
/// TABLE slots travels -- globals have no G form at all (`Glob := Empty`),
/// a pointer basis names no parameter at lock scope, and indices are
/// literals (a lock invariant binds no index). Anything else is refused here
/// with the same codes the contract channel uses (`LG003`/`LG005`).
fn tr_sinv_pred(p: &Pred, model: &Model, scope: &Scope, lock: &str) -> Result<String, Refusal> {
    match &p.art {
        PredArt::Vergleich(e) => match &e.art {
            ExprArt::Binaer(op, l, r) if op.ist_vergleich() => tr_sinv_cmp(op, l, r, model, scope, lock),
            ExprArt::Wahr => Ok("true".to_string()),
            ExprArt::Falsch => Ok("false".to_string()),
            _ => Err(refuse("LG003", format!("lock invariant of {lock} has no G form"))),
        },
        PredArt::Klammer(q) => tr_sinv_pred(q, model, scope, lock),
        PredArt::Und(a, b) => Ok(format!(
            "({} && {})",
            tr_sinv_pred(a, model, scope, lock)?,
            tr_sinv_pred(b, model, scope, lock)?
        )),
        PredArt::Oder(a, b) => Ok(format!(
            "({} || {})",
            tr_sinv_pred(a, model, scope, lock)?,
            tr_sinv_pred(b, model, scope, lock)?
        )),
        PredArt::Nicht(q) => Ok(format!("(!{})", tr_sinv_pred(q, model, scope, lock)?)),
        _ => Err(refuse("LG003", format!("lock invariant of {lock} has no G form"))),
    }
}

/// One invariant comparison. `==`/`!=` are `Bool` already; `<`/`≤` over `Int`
/// are `Prop`, so they travel under `decide`.
fn tr_sinv_cmp(
    op: &BinOp,
    l: &Expr,
    r: &Expr,
    model: &Model,
    scope: &Scope,
    lock: &str,
) -> Result<String, Refusal> {
    let ls = tr_sinv_val(l, model, scope, lock)?;
    let rs = tr_sinv_val(r, model, scope, lock)?;
    match op {
        BinOp::Gleich => Ok(format!("({ls} == {rs})")),
        BinOp::Ungleich => Ok(format!("({ls} != {rs})")),
        BinOp::Kleiner => Ok(format!("(decide ({ls} < {rs}))")),
        BinOp::KleinerGleich => Ok(format!("(decide ({ls} ≤ {rs}))")),
        BinOp::Groesser => Ok(format!("(decide ({rs} < {ls}))")),
        BinOp::GroesserGleich => Ok(format!("(decide ({rs} ≤ {ls}))")),
        _ => Err(refuse("LG003", format!("operator in the lock invariant of {lock} has no G form"))),
    }
}

/// One invariant value as an `Int` term: literals (inlined constants
/// included), table-slot reads with literal indices, and `+`/`-`/`*` over
/// them. Division, remainders and bit operations have no `Int` form here --
/// the snapshot arithmetic the invariant needs is conserved sums, and a wider
/// fragment would move the goal from `decide`-closed guards to unproved
/// arithmetic.
fn tr_sinv_val(e: &Expr, model: &Model, scope: &Scope, lock: &str) -> Result<String, Refusal> {
    match &e.art {
        ExprArt::Zahl(n) => {
            let n = i128::try_from(*n)
                .map_err(|_| refuse("LG003", format!("literal in the lock invariant of {lock} too large")))?;
            Ok(format!("({n} : Int)"))
        }
        ExprArt::Ort(o) if o.suffixe.is_empty() => {
            let Some(v) = scope.consts.get(&o.basis.text) else {
                return Err(refuse(
                    "LG005",
                    format!("lock invariant of {lock} names unknown {}", o.basis.text),
                ));
            };
            Ok(format!("({v} : Int)"))
        }
        ExprArt::Ort(o) => {
            let [OrtSuffix::Feld(slots), OrtSuffix::Index(idx), OrtSuffix::Feld(f)] =
                o.suffixe.as_slice()
            else {
                return Err(refuse(
                    "LG003",
                    format!("place {} in the lock invariant of {lock} has no G form", o.text()),
                ));
            };
            if slots.text != "slots" {
                return Err(refuse(
                    "LG003",
                    format!("place {} in the lock invariant of {lock} has no G form", o.text()),
                ));
            }
            let Some(t) = model.tables.iter().position(|t| t.name == o.basis.text) else {
                return Err(refuse(
                    "LG005",
                    format!("lock invariant of {lock} names unknown {}", o.basis.text),
                ));
            };
            let Some(fi) = model.tables[t].fields.iter().position(|fd| fd.name == f.text) else {
                return Err(refuse(
                    "LG005",
                    format!("unknown field {} in the lock invariant of {lock}", o.text()),
                ));
            };
            if !matches!(model.tables[t].fields[fi].ty, VTy::Int { .. }) {
                return Err(refuse(
                    "LG003",
                    format!("place {} in the lock invariant of {lock} has no G form", o.text()),
                ));
            }
            let ExprArt::Zahl(n) = &idx.art else {
                return Err(refuse(
                    "LG003",
                    format!("non-literal index in the lock invariant of {lock} has no G form"),
                ));
            };
            let n = i128::try_from(*n).map_err(|_| {
                refuse("LG003", format!("index in the lock invariant of {lock} too large"))
            })?;
            if n < 0 || n >= model.tables[t].count {
                return Err(refuse(
                    "LG003",
                    format!("index {n} in the lock invariant of {lock} is outside its `count`"),
                ));
            }
            let _ = fi;
            Ok(format!("((s.slots {} {n} {}).n)", tab_ctor(model, t), feld_ctor(model, t, fi)))
        }
        ExprArt::Klammer(x) => tr_sinv_val(x, model, scope, lock),
        ExprArt::Unaer(UnOp::Negativ, x) => Ok(format!("(-{})", tr_sinv_val(x, model, scope, lock)?)),
        ExprArt::Binaer(op, a, b) => {
            let l = tr_sinv_val(a, model, scope, lock)?;
            let r = tr_sinv_val(b, model, scope, lock)?;
            match op {
                BinOp::Plus => Ok(format!("({l} + {r})")),
                BinOp::Minus => Ok(format!("({l} - {r})")),
                BinOp::Mal => Ok(format!("({l} * {r})")),
                _ => Err(refuse(
                    "LG003",
                    format!("operator in the lock invariant of {lock} has no G form"),
                )),
            }
        }
        _ => Err(refuse("LG003", format!("expression in the lock invariant of {lock} has no G form"))),
    }
}

/// One `ensures` predicate.
fn tr_ensures(p: &Pred, ctx: &Ctx, model: &Model, scope: &Scope, fname: &str, out: &mut Out) -> Result<String, Refusal> {
    match &p.art {
        PredArt::Vergleich(e) => match &e.art {
            ExprArt::Binaer(op, l, r) if op.ist_vergleich() => tr_cmp(op, l, r, ctx, model, scope, fname, out),
            ExprArt::Wahr => Ok(".wahr".to_string()),
            ExprArt::Falsch => Ok(".falsch".to_string()),
            _ => Err(refuse("LG003", format!("ensures-clause in {fname} has no G form"))),
        },
        PredArt::Klammer(q) => tr_ensures(q, ctx, model, scope, fname, out),
        PredArt::Und(a, b) => Ok(format!("(.und {} {})", tr_ensures(a, ctx, model, scope, fname, out)?, tr_ensures(b, ctx, model, scope, fname, out)?)),
        PredArt::Oder(a, b) => Ok(format!("(.oder {} {})", tr_ensures(a, ctx, model, scope, fname, out)?, tr_ensures(b, ctx, model, scope, fname, out)?)),
        PredArt::Nicht(q) => Ok(format!("(.nicht {})", tr_ensures(q, ctx, model, scope, fname, out)?)),
        _ => Err(refuse("LG003", format!("ensures-clause in {fname} has no G form"))),
    }
}

/// Every lock invariant must translate (the `inv` arm is the predicate).
fn check_locks(model: &Model, scope: &Scope) -> Result<(), Refusal> {
    for l in &model.locks {
        if let Some(p) = &l.invariant {
            tr_sinv_pred(p, model, scope, &l.name)?;
        }
    }
    Ok(())
}

/// Every `ensures` clause must translate (the conjunction is the contract).
fn check_contracts(cf: &CheckedFn, model: &Model, scope: &Scope, out: &mut Out) -> Result<(), Refusal> {
    // `ErgCtx` prepends the result only where there is one.
    let ctx = ensures_ctx(cf, model);
    for p in &cf.ensures {
        tr_ensures(p, &ctx, model, scope, &cf.name, out)?;
    }
    Ok(())
}

/// One call argument against the callee's parameter type. A `rw` pointer
/// passed where an `r` is declared has no coercion form -- like the hand
/// translation, the exporter passes a fresh pointer to the same table.
fn tr_arg(a: &Expr, pty: &ParamTy, ctx: &Ctx, model: &Model, scope: &Scope, fname: &str, out: &mut Out) -> Result<String, Refusal> {
    let expected = pty.vty(model);
    match (pty, &a.art) {
        (ParamTy::Ptr { table, write }, ExprArt::Ort(o)) if o.suffixe.is_empty() => {
            let Some((j, ty, _)) = ctx.lookup(&o.basis.text) else {
                return Err(refuse("LG005", format!("unknown name {} in {fname}", o.basis.text)));
            };
            match &ty {
                VTy::Ptr { table: t2, write: w2 } if t2 == table => {
                    if w2 == write {
                        Ok(ctx.var(j))
                    } else {
                        Ok(format!("(.ptrOf {} {table} rfl {write})", tab_ctor(model, *table)))
                    }
                }
                _ => Err(refuse("LG004", format!("argument {} in {fname} has no G form", o.text()))),
            }
        }
        (ParamTy::Index { table }, _) => {
            let idx = tr_index(a, *table, ctx, model, fname)?;
            Ok(idx)
        }
        (ParamTy::Int { .. }, _) | (ParamTy::Bool, _) => tr_value(a, &expected, ctx, model, scope, fname, out),
        (ParamTy::Ptr { .. }, _) => Err(refuse("LG004", format!("pointer argument in {fname} has no G form"))),
    }
}

/// One direct call: the argument tuple and the `RufPasst` proof the call
/// site names. The subset (`hh`), the floor (`hx`, after the hand witness
/// `HelferZeuge.lean`) and the floor order (`hb`) are decided here, in Rust;
/// what they cannot type is refused by name.
fn tr_call_args(r: &Ruf, ctx: &Ctx, model: &Model, scope: &Scope, fns: &[CheckedFn], fname: &str, out: &mut Out) -> Result<(String, String), Refusal> {
    if !r.marken.is_empty() {
        return Err(refuse("LG004", format!("call in {fname} has no G form")));
    }
    let Some(path) = r.path() else {
        return Err(refuse("LG004", format!("indirect call in {fname} has no G form")));
    };
    let Some(last) = path.teile.last() else {
        return Err(refuse("LG004", format!("call in {fname} has no G form")));
    };
    let Some(callee) = fns.iter().find(|f| f.name == last.text) else {
        return Err(refuse("LG005", format!("call in {fname} names unknown function {}", last.text)));
    };
    // `RufPasst.hw`: the callee writes no carrier the caller does not.
    for t in &callee.writes {
        if !ctx.cf.writes.contains(t) {
            return Err(refuse("LG004", format!("call of {} in {fname} writes beyond its caller (`RufPasst.hw`)", callee.name)));
        }
    }
    // `RufPasst.hh`: the callee's held set is a SUBSET of the caller's.
    let caller_holds: std::collections::BTreeSet<usize> = ctx.held.iter().copied().collect();
    let callee_holds: std::collections::BTreeSet<usize> = callee.held.iter().copied().collect();
    if !callee_holds.is_subset(&caller_holds) {
        return Err(refuse("LG004", format!("call of {} in {fname} requires a lock its caller does not hold (`RufPasst.hh`)", callee.name)));
    }
    // `RufPasst.hx`: every extra lock ranks below the callee's floor. The
    // printed proof argues per lock (`cases L`): the floor witness where
    // the lock ranks below it, absurdity from `hn` where the callee
    // requires it, absurdity from `hL` where it is not held at all --
    // and what takes none of the three branches is refused here. The
    // model's own default tactic does not close even the exact case
    // (measured), so `hx` is always printed, never defaulted.
    let extras: Vec<usize> = caller_holds.difference(&callee_holds).copied().collect();
    let extra_floor = if extras.is_empty() {
        None
    } else {
        let Some(c) = callee.boden else {
            return Err(refuse("LG004", format!("call of {} in {fname} holds locks beyond a floorless callee (`RufPasst.hx`)", callee.name)));
        };
        Some(c)
    };
    for li in 0..model.locks.len() {
        let witness = extra_floor.is_some_and(|c| model.locks[li].rank < c);
        if witness || callee.held.contains(&li) || !caller_holds.contains(&li) {
            continue;
        }
        return Err(refuse("LG004", format!("call of {} in {fname} holds {} at or above its floor (`RufPasst.hx`)", callee.name, model.locks[li].name)));
    }
    // `RufPasst.hb`: the caller's floor is at most the callee's.
    let hb = match (ctx.cf.boden, callee.boden) {
        (Some(c0), Some(c1)) => {
            if c0 > c1 {
                return Err(refuse("LG004", format!("call of {} in {fname} runs a higher floor into a lower one (`RufPasst.hb`)", callee.name)));
            }
            Some((c0, c1))
        }
        (Some(_), None) => {
            return Err(refuse("LG004", format!("call of {} in {fname} runs a floored caller into a floorless callee (`RufPasst.hb`)", callee.name)));
        }
        _ => None,
    };
    if r.argumente.len() != callee.params.len() {
        return Err(refuse("LG004", format!("call of {} in {fname} has the wrong arity", callee.name)));
    }
    let mut term = ".nil".to_string();
    for (a, (_, pty)) in r.argumente.iter().zip(callee.params.iter()).rev() {
        let ta = tr_arg(a, pty, ctx, model, scope, fname, out)?;
        term = format!("(.cons {ta} {term})");
    }
    let hp = format!("gHp_{}{}_{}", lean_fn(fname), ctx.tag, lean_fn(&callee.name));
    out.hp(HpNeeded { caller: fname.to_string(), tag: ctx.tag.clone(), callee: callee.name.clone(), extra_floor, hb });
    Ok((term, hp))
}

/// Whether a block can fall off: anywhere a `return` stands under it.
fn contains_return(b: &Block) -> bool {
    b.anweisungen.iter().any(|s| match &s.art {
        StmtArt::Return(_) | StmtArt::Leave(_) | StmtArt::Next(_) => true,
        StmtArt::Wenn(w) => {
            w.zweige.iter().any(|(_, b)| contains_return(b))
                || w.sonst.as_ref().is_some_and(contains_return)
        }
        StmtArt::Sperrt(sp) => contains_return(&sp.rumpf),
        StmtArt::Schleife(sl) => match &**sl {
            Schleife::Traverse(t) => contains_return(&t.rumpf),
            Schleife::Retry(r) => contains_return(&r.rumpf),
            Schleife::Forever(f) => contains_return(&f.rumpf),
        },
        StmtArt::LetSonst(l) => contains_return(&l.sonst),
        StmtArt::Match(m) => m.zweige.iter().any(|z| contains_return(&z.rumpf)),
        StmtArt::Bricht(b) => contains_return(&b.rumpf),
        _ => false,
    })
}

/// A trailing `return` as an `Endblock.ret`: only where `Λ` is the
/// signature end, so the `Perm.refl` fits it.
fn tr_ret_end(e: &Option<Expr>, ctx: &Ctx, model: &Model, scope: &Scope, fname: &str, out: &mut Out) -> Result<String, Refusal> {
    if ctx.locks_open {
        return Err(refuse("LG004", format!("`return` under `locks` in {fname} has no G form")));
    }
    match (&ctx.cf.result, e) {
        (None, None) => Ok("(.ret .keine (List.Perm.refl _))".to_string()),
        (Some(ty), Some(v)) => {
            let val = tr_value(v, ty, ctx, model, scope, fname, out)?;
            Ok(format!("(.ret (.wert {val}) (List.Perm.refl _))"))
        }
        _ => Err(refuse("LG004", format!("`return` in {fname} disagrees with its result"))),
    }
}

/// A `return` as a mid-block statement (`Stmt.ret`): only where `Λ` is the
/// signature end, so the `Perm.refl` fits it.
fn tr_ret_stmt(e: &Option<Expr>, ctx: &Ctx, model: &Model, scope: &Scope, fname: &str, out: &mut Out) -> Result<String, Refusal> {
    if ctx.locks_open {
        return Err(refuse("LG004", format!("`return` under `locks` in {fname} has no G form")));
    }
    match (&ctx.cf.result, e) {
        (None, None) => Ok("(.ret .keine (List.Perm.refl _))".to_string()),
        (Some(ty), Some(v)) => {
            let val = tr_value(v, ty, ctx, model, scope, fname, out)?;
            Ok(format!("(.ret (.wert {val}) (List.Perm.refl _))"))
        }
        _ => Err(refuse("LG004", format!("`return` in {fname} disagrees with its result"))),
    }
}

/// An `if`/`else if`/`else` chain as nested `Stmt.ite`. In tail position of
/// an `Endblock` the branches must be return-free (their continuation is
/// the peeled tail); anywhere else a branch may return through `Stmt.ret`.
fn tr_ite(w: &WennStmt, rest_empty_tail: bool, ctx: &Ctx, model: &Model, scope: &Scope, fns: &[CheckedFn], fname: &str, out: &mut Out) -> Result<String, Refusal> {
    let else_term = match &w.sonst {
        Some(b) => {
            if rest_empty_tail && contains_return(b) {
                return Err(refuse("LG004", format!("`return` inside `if` in {fname} has no G form")));
            }
            tr_block(&b.anweisungen, ctx, model, scope, fns, fname, out)?
        }
        None => ".nil".to_string(),
    };
    let mut acc = else_term;
    for (c, b) in w.zweige.iter().rev() {
        if rest_empty_tail && contains_return(b) {
            return Err(refuse("LG004", format!("`return` inside `if` in {fname} has no G form")));
        }
        let cond = tr_bool(c, ctx, model, scope, fname, out)?;
        let then = tr_block(&b.anweisungen, ctx, model, scope, fns, fname, out)?;
        acc = format!("(.ite {cond} {then} {acc})");
    }
    Ok(acc)
}

/// A `locks L { … }` block: the rank must exceed everything held (`H006`,
/// decided here), and the body runs with one more witness in hand.
fn tr_locks(sp: &SperrtStmt, ctx: &Ctx, model: &Model, scope: &Scope, fns: &[CheckedFn], fname: &str, out: &mut Out) -> Result<String, Refusal> {
    if sp.geteilt {
        return Err(refuse("LG004", format!("shared `locks` in {fname} has no G form")));
    }
    if !sp.sperre.suffixe.is_empty() {
        return Err(refuse("LG005", format!("locks-clause in {fname} names {}", sp.sperre.text())));
    }
    let Some(li) = model.locks.iter().position(|l| l.name == sp.sperre.basis.text) else {
        return Err(refuse("LG005", format!("locks-clause in {fname} names unknown {}", sp.sperre.basis.text)));
    };
    for h in &ctx.held {
        if model.locks[*h].rank >= model.locks[li].rank {
            return Err(refuse("LG004", format!("`locks {}` in {fname} takes no rank above everything held", model.locks[li].name)));
        }
    }
    let inner = ctx.locked(li, &model.locks[li].name);
    let body = tr_block(&sp.rumpf.anweisungen, &inner, model, scope, fns, fname, out)?;
    Ok(format!("(.locks {} (fun M => by cases M <;> decide) {body})", lock_ctor(model, li)))
}

/// A `traverse i over slots of T` loop. The mode, the `decreases` witness
/// and `touches` are static annotations (NO FORM, like `costs`); the
/// invariant travels where it translates, and `.wahr` where none stands
/// (like the default `requires` of `gP`).
fn tr_traverse(t: &Traverse, ctx: &Ctx, model: &Model, scope: &Scope, fns: &[CheckedFn], fname: &str, out: &mut Out) -> Result<String, Refusal> {
    if t.gegenstand.is_some() {
        return Err(refuse("LG006", format!("`traverse … of …` in {fname} has no G form")));
    }
    let Domaene::SlotsVon(o) = &t.domaene else {
        return Err(refuse("LG006", format!("`traverse` domain in {fname} has no G form")));
    };
    if !o.suffixe.is_empty() {
        return Err(refuse("LG006", format!("`traverse` domain in {fname} has no G form")));
    }
    let Some(ti) = model.tables.iter().position(|t| t.name == o.basis.text) else {
        return Err(refuse("LG006", format!("`traverse` domain in {fname} is not a table")));
    };
    // The invariant is over the outer context (the binder is not in scope).
    let inv = match &t.invariante {
        None => ".wahr".to_string(),
        Some(p) => tr_inv_bool(p, ctx, model, scope, fname, out)?,
    };
    let inner = ctx.looping(t.variable.text.clone(), ti);
    let body = tr_block(&t.rumpf.anweisungen, &inner, model, scope, fns, fname, out)?;
    Ok(format!("(.traverse {} {inv} {body})", tab_ctor(model, ti)))
}

/// A loop invariant as a boolean expression over the enclosing context.
fn tr_inv_bool(p: &Pred, ctx: &Ctx, model: &Model, scope: &Scope, fname: &str, out: &mut Out) -> Result<String, Refusal> {
    match &p.art {
        PredArt::Vergleich(e) => match &e.art {
            ExprArt::Binaer(op, l, r) if op.ist_vergleich() => {
                let (term, _) = tr_cmp_bool(op, l, r, ctx, model, scope, fname, out)?;
                Ok(term)
            }
            ExprArt::Wahr => Ok(".wahr".to_string()),
            ExprArt::Falsch => Ok(".falsch".to_string()),
            _ => Err(refuse("LG006", format!("loop invariant in {fname} has no G form"))),
        },
        PredArt::Klammer(q) => tr_inv_bool(q, ctx, model, scope, fname, out),
        PredArt::Und(a, b) => Ok(format!("(.und {} {})", tr_inv_bool(a, ctx, model, scope, fname, out)?, tr_inv_bool(b, ctx, model, scope, fname, out)?)),
        PredArt::Oder(a, b) => Ok(format!("(.oder {} {})", tr_inv_bool(a, ctx, model, scope, fname, out)?, tr_inv_bool(b, ctx, model, scope, fname, out)?)),
        PredArt::Nicht(q) => Ok(format!("(.nicht {})", tr_inv_bool(q, ctx, model, scope, fname, out)?)),
        _ => Err(refuse("LG006", format!("loop invariant in {fname} has no G form"))),
    }
}

/// A comparison over integer sides, for loop invariants.
fn tr_cmp_bool(op: &BinOp, l: &Expr, r: &Expr, ctx: &Ctx, model: &Model, scope: &Scope, fname: &str, out: &mut Out) -> Result<(String, VTy), Refusal> {
    let (la, ta) = tr_typed(l, ctx, model, scope, fname, out)?;
    let (lb, tb) = tr_typed(r, ctx, model, scope, fname, out)?;
    if ta.range(model).is_none() || tb.range(model).is_none() {
        return Err(refuse("LG006", format!("loop invariant in {fname} has no G form")));
    }
    let term = match op {
        BinOp::Gleich => format!("(.eq {la} {lb})"),
        BinOp::Ungleich => format!("(.nicht (.eq {la} {lb}))"),
        BinOp::Kleiner => format!("(.lt {la} {lb})"),
        BinOp::KleinerGleich => format!("(.le {la} {lb})"),
        BinOp::Groesser => format!("(.lt {lb} {la})"),
        BinOp::GroesserGleich => format!("(.le {lb} {la})"),
        _ => return Err(refuse("LG006", format!("loop invariant in {fname} has no G form"))),
    };
    Ok((term, VTy::Bool))
}

/// One statement sequence: `Block` (`nil`-terminated) or `Endblock` tail
/// (`endblock`, ending in the peeled `return`). `let` binds through
/// `bind`; a call-valued `let` binds through `bindCall`, which only blocks
/// have -- at the top level it is refused by name.
fn tr_rest(stmts: &[Stmt], ctx: &mut Ctx, model: &Model, scope: &Scope, fns: &[CheckedFn], fname: &str, out: &mut Out, cont: String, endblock: bool) -> Result<String, Refusal> {
    let Some((first, rest)) = stmts.split_first() else {
        return Ok(cont);
    };
    match &first.art {
        StmtArt::Zuweisung(z) => {
            if z.op != ZuwOp::Setzt {
                return Err(refuse("LG004", format!("compound assignment in {fname} has no G form")));
            }
            let (t, fi, index, through, ty) = slot_access(&z.ziel, ctx, model, fname)?;
            // The value fits the field: an integer range, or `bool`.
            let val = match &ty {
                VTy::Int { lo, hi, .. } => tr_value(&z.wert, &VTy::Int { lo: *lo, hi: *hi, bits: None }, ctx, model, scope, fname, out)?,
                VTy::Bool => tr_bool(&z.wert, ctx, model, scope, fname, out)?,
                _ => return Err(refuse("LG004", format!("assignment to {} in {fname} has no G form", z.ziel.text()))),
            };
            let proof = darf_at(ctx, model, fname, t, out);
            let base = if let Some(j) = through {
                match &ctx.names[j].1 {
                    VTy::Ptr { write: true, .. } => {},
                    _ => return Err(refuse("LG004", format!("write through a read-only pointer in {fname}"))),
                }
                format!("(.assignDurch {} {} rfl {} ({index}) {val} (by decide) {proof})",
                    ctx.var(j), tab_ctor(model, t), feld_ctor(model, t, fi))
            } else {
                format!("(.assignSlot {} {} ({index}) {val} (by decide) {proof})",
                    tab_ctor(model, t), feld_ctor(model, t, fi))
            };
            Ok(format!("(.cons {base} {})", tr_rest(rest, ctx, model, scope, fns, fname, out, cont, endblock)?))
        }
        StmtArt::Ruf(r) => {
            let Some(path) = r.path() else {
                return Err(refuse("LG004", format!("indirect call in {fname} has no G form")));
            };
            let Some(last) = path.teile.last() else {
                return Err(refuse("LG004", format!("call in {fname} has no G form")));
            };
            let Some(callee) = fns.iter().find(|f| f.name == last.text) else {
                return Err(refuse("LG005", format!("call in {fname} names unknown function {}", last.text)));
            };
            if callee.gruende > 0 {
                return Err(refuse("LG004", format!("call of {} in {fname} carries a reason -- `let … else` has the form", callee.name)));
            }
            let (args, hp) = tr_call_args(r, ctx, model, scope, fns, fname, out)?;
            let call = format!("(.call g_{} {args} {hp} rfl)", lean_fn(&callee.name));
            Ok(format!("(.cons {call} {})", tr_rest(rest, ctx, model, scope, fns, fname, out, cont, endblock)?))
        }
        StmtArt::Wenn(w) => {
            let tail = rest.is_empty() && endblock;
            let ite = tr_ite(w, tail, ctx, model, scope, fns, fname, out)?;
            Ok(format!("(.cons {ite} {})", tr_rest(rest, ctx, model, scope, fns, fname, out, cont, endblock)?))
        }
        StmtArt::Sperrt(sp) => {
            let locks = tr_locks(sp, ctx, model, scope, fns, fname, out)?;
            Ok(format!("(.cons {locks} {})", tr_rest(rest, ctx, model, scope, fns, fname, out, cont, endblock)?))
        }
        StmtArt::Schleife(sl) => match &**sl {
            Schleife::Traverse(t) => {
                let trav = tr_traverse(t, ctx, model, scope, fns, fname, out)?;
                Ok(format!("(.cons {trav} {})", tr_rest(rest, ctx, model, scope, fns, fname, out, cont, endblock)?))
            }
            Schleife::Retry(_) => Err(refuse("LG006", format!("`retry` in {fname} has no G form in this fragment"))),
            Schleife::Forever(_) => Err(refuse("LG006", format!("`forever` in {fname} has no G form in this fragment"))),
        },
        StmtArt::Let(l) => {
            // A call-valued `let` binds through `bindCall`, which only
            // blocks have; conversions are pure and bind anywhere.
            if let ExprArt::Ruf(r) = &l.wert.art {
                if is_value_call(r, model) {
                    if endblock {
                        return Err(refuse("LG004", format!("`let` of a call in {fname} has no G form at the top level")));
                    }
                    return tr_let_call(l, r, ctx, model, scope, fns, fname, out, rest, cont);
                }
            }
            let (eterm, vty) = tr_typed(&l.wert, ctx, model, scope, fname, out)?;
            if let Some(ann) = &l.typ {
                let aty = annot_ty(ann, model, scope, fname)?;
                check_annotation(&vty, &aty, model, fname, &l.name.text)?;
            }
            // Ascribed with the computed type: unlike every other value
            // position, `bind` gives the value no expected type, so an
            // unascribed `weiter` would leave its range ambiguous and its
            // `by decide` without a goal.
            let ascribed = format!("({eterm} : Expr gD {} {} {})", ctx.gamma, ctx.lambda, vty.term(model));
            *ctx = ctx.push(l.name.text.clone(), vty, NameKind::Let);
            Ok(format!("(.bind {ascribed} {})", tr_rest(rest, ctx, model, scope, fns, fname, out, cont, endblock)?))
        }
        StmtArt::LetSonst(l) => {
            if endblock {
                return Err(refuse("LG004", format!("`let … else` in {fname} has no G form at the top level")));
            }
            tr_let_else(l, ctx, model, scope, fns, fname, out, rest, cont)
        }
        StmtArt::Return(e) => {
            // A `return` ends its sequence (a mid-sequence one has no form);
            // it translates with the context as it stands, so `let` bindings
            // above it are in scope.
            if !rest.is_empty() {
                return Err(refuse("LG004", format!("`return` in the middle of {fname} has no G form")));
            }
            if endblock {
                tr_ret_end(e, ctx, model, scope, fname, out)
            } else {
                // A branch return: a `Stmt.ret` consed onto the block end.
                let ret = tr_ret_stmt(e, ctx, model, scope, fname, out)?;
                Ok(format!("(.cons {ret} {cont})"))
            }
        }
        StmtArt::Match(_) => Err(refuse("LG004", format!("`match` in {fname} has no G form in this fragment"))),
        StmtArt::Publish(_) => Err(refuse("LG004", format!("`publishes` in {fname} has no G form in this fragment"))),
        StmtArt::AwaitLoad(_) => Err(refuse("LG004", format!("`awaits` in {fname} has no G form in this fragment"))),
        StmtArt::Exchange(_) => Err(refuse("LG004", format!("`exchange` in {fname} has no G form in this fragment"))),
        StmtArt::LibraryCall(_) => Err(refuse("LG004", format!("library call in {fname} has no G form in this fragment"))),
        StmtArt::Alloc(_) => Err(refuse("LG004", format!("`alloc` in {fname} has no G form in this fragment"))),
        StmtArt::ResetArena(_) => Err(refuse("LG004", format!("`reset` in {fname} has no G form in this fragment"))),
        StmtArt::Bricht(_) => Err(refuse("LG004", format!("`breaking` in {fname} has no G form in this fragment"))),
        StmtArt::Narrow(_) => Err(refuse("LG004", format!("`narrow` in {fname} has no G form in this fragment"))),
        StmtArt::Observiert(_) => Err(refuse("LG004", format!("`observes` in {fname} has no G form in this fragment"))),
        StmtArt::Leave(_) | StmtArt::Next(_) => Err(refuse("LG004", format!("`leave`/`next` in {fname} has no G form in this fragment"))),
    }
}

/// Whether a call in value position goes to a declared function (a
/// conversion -- a call naming a type -- is pure and binds anywhere).
fn is_value_call(r: &Ruf, model: &Model) -> bool {
    if !r.marken.is_empty() {
        return false;
    }
    let Some(path) = r.path() else {
        return false;
    };
    if path.teile.len() != 1 {
        return false;
    }
    model.fns.iter().any(|f| f.name == path.teile[0].text)
}

/// The computed type against a `let` annotation: the annotation stands
/// where M1 already held it, so the computed range must fit inside it
/// (binding happens at the computed type; every use fits from there).
fn check_annotation(computed: &VTy, annotated: &VTy, model: &Model, fname: &str, name: &str) -> Result<(), Refusal> {
    match (computed, annotated) {
        (VTy::Bool, VTy::Bool) => Ok(()),
        _ => {
            let (Some((clo, chi)), Some((alo, ahi))) = (computed.range(model), annotated.range(model)) else {
                return Err(refuse("LG004", format!("`let {name}` in {fname} has no G form")));
            };
            if alo <= clo && chi <= ahi {
                Ok(())
            } else {
                Err(refuse("LG004", format!("`let {name}` in {fname} exceeds its annotation")))
            }
        }
    }
}

/// A block-valued `let x = f()`: `Block.bindCall`. Only blocks have it.
fn tr_let_call(l: &LetStmt, r: &Ruf, ctx: &mut Ctx, model: &Model, scope: &Scope, fns: &[CheckedFn], fname: &str, out: &mut Out, rest: &[Stmt], cont: String) -> Result<String, Refusal> {
    let Some(path) = r.path() else {
        return Err(refuse("LG004", format!("indirect call in {fname} has no G form")));
    };
    let last = path.teile.last().expect("single segment");
    let Some(callee) = fns.iter().find(|f| f.name == last.text) else {
        return Err(refuse("LG005", format!("call in {fname} names unknown function {}", last.text)));
    };
    if callee.gruende > 0 {
        return Err(refuse("LG004", format!("call of {} in {fname} carries a reason -- `let … else` has the form", callee.name)));
    }
    let Some(rt) = callee.result.clone() else {
        return Err(refuse("LG004", format!("call of {} in {fname} returns nothing to bind", callee.name)));
    };
    let (args, hp) = tr_call_args(r, ctx, model, scope, fns, fname, out)?;
    // `he`: the callee's result is what binds (uses fit from there).
    *ctx = ctx.push(l.name.text.clone(), rt, NameKind::Let);
    Ok(format!("(.bindCall g_{} {args} rfl {hp} (by decide) {})",
        lean_fn(&callee.name), tr_rest(rest, ctx, model, scope, fns, fname, out, cont, false)?))
}

/// A `let x = f() else (e) { … }`: `Block.bindCallElse`. The `else` branch
/// must end in a `return` (an `Endblock`); a falling-off branch would
/// continue after the `let`, for which no constructor exists.
fn tr_let_else(l: &LetSonst, ctx: &mut Ctx, model: &Model, scope: &Scope, fns: &[CheckedFn], fname: &str, out: &mut Out, rest: &[Stmt], cont: String) -> Result<String, Refusal> {
    let r = match &l.quelle {
        LetQuelle::Ruf(r) => r,
        LetQuelle::Ort(o) => {
            return Err(refuse("LG007", format!("`let … else` over {} in {fname} has no G form", o.text())));
        }
    };
    let Some(path) = r.path() else {
        return Err(refuse("LG004", format!("indirect call in {fname} has no G form")));
    };
    let last = path.teile.last().expect("call has a name");
    let Some(callee) = fns.iter().find(|f| f.name == last.text) else {
        return Err(refuse("LG005", format!("call in {fname} names unknown function {}", last.text)));
    };
    if callee.gruende == 0 {
        return Err(refuse("LG007", format!("`let … else` of {} in {fname} binds no reason", callee.name)));
    }
    let Some(rt) = callee.result.clone() else {
        return Err(refuse("LG007", format!("`let … else` of {} in {fname} binds no value", callee.name)));
    };
    let (args, hp) = tr_call_args(r, ctx, model, scope, fns, fname, out)?;
    // The `else` branch: the reason binds, and the branch ends in `return`.
    // The `else` branch must end in a `return`: a falling-off branch
    // would continue after the `let`, for which no constructor exists.
    let Some((err_last, _)) = l.sonst.anweisungen.split_last() else {
        return Err(refuse("LG007", format!("empty `else` in {fname} has no G form")));
    };
    let StmtArt::Return(_) = &err_last.art else {
        return Err(refuse("LG007", format!("falling-off `else` in {fname} has no G form")));
    };
    if ctx.locks_open {
        return Err(refuse("LG007", format!("`let … else` under `locks` in {fname} has no G form")));
    }
    // The `else` branch translates as an end block (its tail `return`
    // with the reason in scope); bindings never leak out of it.
    let mut err_ctx = ctx.push(l.fehlername.text.clone(), VTy::Grund { n: callee.gruende }, NameKind::Let);
    let err = tr_rest(&l.sonst.anweisungen, &mut err_ctx, model, scope, fns, fname, out, String::new(), true)?;
    *ctx = ctx.push(l.name.text.clone(), rt, NameKind::Let);
    Ok(format!("(.bindCallElse g_{} {args} rfl {hp} (by decide) {err} {})",
        lean_fn(&callee.name), tr_rest(rest, ctx, model, scope, fns, fname, out, cont, false)?))
}

/// One block as a `Block` term: the statements consed onto `nil`.
/// Bindings never leak out of a block, so the context is a copy.
fn tr_block(stmts: &[Stmt], ctx: &Ctx, model: &Model, scope: &Scope, fns: &[CheckedFn], fname: &str, out: &mut Out) -> Result<String, Refusal> {
    let mut inner = ctx.clone();
    tr_rest(stmts, &mut inner, model, scope, fns, fname, out, ".nil".to_string(), false)
}

/// The whole body must translate; `return` handling and the fall-off rule
/// live here so `emit` only prints.
fn check_body(cf: &CheckedFn, _model: &Model) -> Result<(), Refusal> {
    // Cheap structural pass here; the real translation runs in `emit`
    // (which needs the full function table). This pass refuses bodies no
    // translation could serve: a result that falls off, or none that returns.
    let last = cf.body.anweisungen.last();
    match (&cf.result, last.map(|s| &s.art)) {
        (Some(_), Some(StmtArt::Return(Some(_)))) => Ok(()),
        (Some(_), _) => Err(refuse("LG004", format!("function {} falls off with a result", cf.name))),
        (None, Some(StmtArt::Return(None))) => Ok(()),
        (None, _) => Ok(()),
    }
}

/// One body as an `Endblock` term: the sequence translates with the
/// context threaded through it, so the trailing `return` sees every `let`
/// above it (`check_body` guards the fall-off shape beforehand).
fn tr_endblock(cf: &CheckedFn, model: &Model, scope: &Scope, fns: &[CheckedFn], out: &mut Out) -> Result<String, Refusal> {
    let mut ctx = body_ctx(cf, model);
    tr_rest(&cf.body.anweisungen, &mut ctx, model, scope, fns, &cf.name, out,
        "(.ret .keine (List.Perm.refl _))".to_string(), true)
}

/// One `ensures` contract as an `Expr` term (`.wahr` where there is none).
fn tr_contract(cf: &CheckedFn, model: &Model, scope: &Scope, out: &mut Out) -> Result<Option<String>, Refusal> {
    if cf.ensures.is_empty() {
        return Ok(None);
    }
    let ctx = ensures_ctx(cf, model);
    let mut it = cf.ensures.iter();
    let first = tr_ensures(it.next().expect("nonempty"), &ctx, model, scope, &cf.name, out)?;
    let mut acc = first;
    for p in it {
        let t = tr_ensures(p, &ctx, model, scope, &cf.name, out)?;
        acc = format!("(.und {acc} {t})");
    }
    Ok(Some(acc))
}

/// The carrier a place names: a table name, or a pointer parameter (which
/// names its table). Lenient -- translation refuses strictly.
fn foot_carrier(o: &Ort, model: &Model, params: &[(String, ParamTy)]) -> Option<usize> {
    if let Some(ti) = model.tables.iter().position(|t| t.name == o.basis.text) {
        return Some(ti);
    }
    for (n, pty) in params {
        if n == &o.basis.text {
            if let ParamTy::Ptr { table, .. } = pty {
                return Some(*table);
            }
        }
    }
    None
}

fn foot_push(acc: &mut Vec<usize>, ti: usize) {
    if !acc.contains(&ti) {
        acc.push(ti);
    }
}

/// The tables a surface block reads or writes: the footprint mirror for
/// the `fussOrtGB` print decision.
fn foot_block(b: &Block, model: &Model, params: &[(String, ParamTy)], acc: &mut Vec<usize>) {
    fn foot_expr(e: &Expr, model: &Model, params: &[(String, ParamTy)], acc: &mut Vec<usize>) {
        match &e.art {
            ExprArt::Ort(o) => {
                if o.suffixe.len() == 3 {
                    if let Some(ti) = foot_carrier(o, model, params) {
                        foot_push(acc, ti);
                    }
                }
                for s in &o.suffixe {
                    if let OrtSuffix::Index(x) = s {
                        foot_expr(x, model, params, acc);
                    }
                }
            }
            ExprArt::Alt(o) => {
                if let Some(ti) = foot_carrier(o, model, params) {
                    foot_push(acc, ti);
                }
            }
            ExprArt::Binaer(_, a, b) => {
                foot_expr(a, model, params, acc);
                foot_expr(b, model, params, acc);
            }
            ExprArt::Unaer(_, x) | ExprArt::Klammer(x) => foot_expr(x, model, params, acc),
            ExprArt::Ruf(r) => {
                for a in &r.argumente {
                    foot_expr(a, model, params, acc);
                }
            }
            _ => {}
        }
    }
    fn foot_pred(p: &Pred, model: &Model, params: &[(String, ParamTy)], acc: &mut Vec<usize>) {
        match &p.art {
            PredArt::Vergleich(e) => foot_expr(e, model, params, acc),
            PredArt::Klammer(q) | PredArt::Nicht(q) => foot_pred(q, model, params, acc),
            PredArt::Und(a, b) | PredArt::Oder(a, b) | PredArt::Folgt(a, b) => {
                foot_pred(a, model, params, acc);
                foot_pred(b, model, params, acc);
            }
            PredArt::Quantor(q) => foot_pred(&q.rumpf, model, params, acc),
            _ => {}
        }
    }
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Zuweisung(z) => {
                if z.ziel.suffixe.len() == 3 {
                    if let Some(ti) = foot_carrier(&z.ziel, model, params) {
                        foot_push(acc, ti);
                    }
                }
                foot_expr(&z.wert, model, params, acc);
            }
            StmtArt::Ruf(r) => {
                for a in &r.argumente {
                    foot_expr(a, model, params, acc);
                }
            }
            StmtArt::Return(e) => {
                if let Some(e) = e {
                    foot_expr(e, model, params, acc);
                }
            }
            StmtArt::Let(l) => foot_expr(&l.wert, model, params, acc),
            StmtArt::LetSonst(l) => {
                if let LetQuelle::Ruf(r) = &l.quelle {
                    for a in &r.argumente {
                        foot_expr(a, model, params, acc);
                    }
                }
                foot_block(&l.sonst, model, params, acc);
            }
            StmtArt::Wenn(w) => {
                for (c, b) in &w.zweige {
                    foot_expr(c, model, params, acc);
                    foot_block(b, model, params, acc);
                }
                if let Some(s) = &w.sonst {
                    foot_block(s, model, params, acc);
                }
            }
            StmtArt::Sperrt(sp) => foot_block(&sp.rumpf, model, params, acc),
            StmtArt::Schleife(sl) => match &**sl {
                Schleife::Traverse(t) => {
                    if let Some(p) = &t.invariante {
                        foot_pred(p, model, params, acc);
                    }
                    foot_block(&t.rumpf, model, params, acc);
                }
                Schleife::Retry(r) => foot_block(&r.rumpf, model, params, acc),
                Schleife::Forever(f) => foot_block(&f.rumpf, model, params, acc),
            },
            StmtArt::Match(m) => {
                foot_expr(&m.gegenstand, model, params, acc);
                for z in &m.zweige {
                    foot_block(&z.rumpf, model, params, acc);
                }
            }
            _ => {}
        }
    }
}

/// The footprint mirror of a function: its `ensures` carriers, its body
/// carriers, and its direct callees' `ensures` carriers (`fussOrte`, one
/// level; `requires` prints `.wahr`, invariants are not admitted).
fn foot_fn(cf: &CheckedFn, model: &Model, fns: &[CheckedFn]) -> Vec<usize> {
    fn foot_pred(p: &Pred, model: &Model, params: &[(String, ParamTy)], acc: &mut Vec<usize>) {
        match &p.art {
            PredArt::Vergleich(e) => foot_expr(e, model, params, acc),
            PredArt::Klammer(q) | PredArt::Nicht(q) => foot_pred(q, model, params, acc),
            PredArt::Und(a, b) | PredArt::Oder(a, b) | PredArt::Folgt(a, b) => {
                foot_pred(a, model, params, acc);
                foot_pred(b, model, params, acc);
            }
            _ => {}
        }
    }
    fn foot_expr(e: &Expr, model: &Model, params: &[(String, ParamTy)], acc: &mut Vec<usize>) {
        match &e.art {
            ExprArt::Ort(o) => {
                if o.suffixe.len() == 3 {
                    if let Some(ti) = foot_carrier(o, model, params) {
                        foot_push(acc, ti);
                    }
                }
            }
            ExprArt::Alt(o) => {
                if let Some(ti) = foot_carrier(o, model, params) {
                    foot_push(acc, ti);
                }
            }
            ExprArt::Binaer(_, a, b) => {
                foot_expr(a, model, params, acc);
                foot_expr(b, model, params, acc);
            }
            ExprArt::Unaer(_, x) | ExprArt::Klammer(x) => foot_expr(x, model, params, acc),
            _ => {}
        }
    }
    let mut acc = Vec::new();
    for p in &cf.ensures {
        foot_pred(p, model, &cf.params, &mut acc);
    }
    foot_block(&cf.body, model, &cf.params, &mut acc);
    for name in &cf.calls {
        if let Some(g) = fns.iter().find(|f| &f.name == name) {
            for p in &g.ensures {
                foot_pred(p, model, &g.params, &mut acc);
            }
        }
    }
    acc
}

/// Whether the old footprint check holds: every accessed carrier is
/// guarded by a signature-held lock, or written by no function
/// (`fussOrtGB`, decided Lean-side; this mirrors it for the print decision
/// and never guesses).
fn fuss_holds(model: &Model, fns: &[CheckedFn]) -> bool {
    for f in fns {
        for t in foot_fn(f, model, fns) {
            if guard_held(&f.held, model, t) {
                continue;
            }
            if fns.iter().all(|g| !g.writes.contains(&t)) {
                continue;
            }
            return false;
        }
    }
    true
}

/// The namespace segment for a source file: sanitized stem (`104-referenz`
/// becomes `G104_referenz`), so two exports never declare the same names.
/// Public for the obligation export, which derives its own namespace from it.
pub fn namespace_of(source_name: &str) -> String {
    let stem = source_name.rsplit('/').next().unwrap_or(source_name);
    let stem = stem.rsplit('.').nth(1).unwrap_or(stem);
    let mut s: String = stem.chars().map(|c| if c.is_alphanumeric() || c == '_' { c } else { '_' }).collect();
    if s.is_empty() || !s.chars().next().is_some_and(|c| c.is_alphabetic()) {
        s = format!("G{s}");
    }
    s
}

/// The printed Lean file.
fn emit(source_name: &str, ns: &str, model: &Model, fns: &[CheckedFn], scope: &Scope, collected: &mut Out) -> Result<String, Refusal> {
    let nt = model.tables.len();
    let mut out = String::new();
    // Header: generated marker, source, and the NO-FORM ledger.
    out.push_str(&format!("-- GENERATED by `gabbro lean-g {source_name}` -- do not edit.\n"));
    out.push_str("-- A mechanical export of the checked unit as a G program term\n");
    out.push_str("-- (`Programm gD`, the syntax `RufMaschineG.lean` runs).\n--\n");
    out.push_str("-- NO FORM in G (accepted and dropped, each named): the module\n");
    out.push_str("-- wrapper; named constants (inlined at every use); bare carrier\n");
    out.push_str("-- widths (a bare word travels as its full range); pointer address\n");
    out.push_str("-- spaces; lock hold budgets;\n");
    out.push_str("-- the `reads` effects; `costs`; the `by unvisited`/`by consuming`\n");
    out.push_str("-- run form, the `decreases` witness and the `touches` clause of a\n");
    out.push_str("-- `traverse` (static annotations, like `costs`); `by ops` on a field\n");
    out.push_str("-- (a writer discipline the checker holds); `mut` on a `let`;\n");
    out.push_str("-- `concurrent` (all functions travel\n");
    out.push_str("-- in `gFs`; which of them start threads is not a G notion).\n--\n");
    for (ti, t) in model.tables.iter().enumerate() {
        out.push_str(&format!("-- table {ti}: {} (count {})", t.name, t.count));
        for f in &t.fields {
            match &f.ty {
                VTy::Int { lo, hi, .. } => out.push_str(&format!(", {} : {lo}..{hi}", f.name)),
                VTy::Bool => out.push_str(&format!(", {} : bool", f.name)),
                _ => out.push_str(&format!(", {} : ?", f.name)),
            }
        }
        out.push('\n');
    }
    for (li, l) in model.locks.iter().enumerate() {
        out.push_str(&format!("-- lock {li}: {} (rank {}) guards", l.name, l.rank));
        for g in &l.guards {
            out.push_str(&format!(" {}", model.tables[*g].name));
        }
        out.push('\n');
    }
    for f in fns {
        out.push_str(&format!("-- fn {} (holds", f.name));
        for h in &f.held {
            out.push_str(&format!(" {}", model.locks[*h].name));
        }
        out.push_str("; writes");
        for w in &f.writes {
            out.push_str(&format!(" {}", model.tables[*w].name));
        }
        out.push_str(")\n");
    }
    out.push_str("import Grammatik.ZielOrtGeraetSem\nimport Grammatik.SperreSem\n\nnamespace Gabbro.Grammatik\n\nnamespace ");
    out.push_str(ns);
    out.push_str("\n\n");
    // The carrier inductives: one constructor per table, lock and field.
    // An empty carrier is core `Empty` (never a fresh empty inductive, so
    // no deriver ever runs over zero constructors).
    if model.tables.is_empty() {
        out.push_str("abbrev GTab := Empty\n\n");
    } else {
        out.push_str("inductive GTab where\n");
        for t in &model.tables {
            out.push_str(&format!("  | {}\n", t.name));
        }
        out.push_str("  deriving DecidableEq\n\n");
    }
    if model.locks.is_empty() {
        out.push_str("abbrev GLock := Empty\n\n");
    } else {
        out.push_str("inductive GLock where\n");
        for l in &model.locks {
            out.push_str(&format!("  | {}\n", l.name));
        }
        out.push_str("  deriving DecidableEq\n\n");
    }
    for (ti, t) in model.tables.iter().enumerate() {
        out.push_str(&format!("inductive {} where\n", feld_type(model, ti)));
        for f in &t.fields {
            out.push_str(&format!("  | {}\n", f.name));
        }
        out.push_str("  deriving DecidableEq\n\n");
    }
    // The function type.
    out.push_str("inductive GFn where\n");
    for f in fns {
        out.push_str(&format!("  | {}\n", lean_fn(&f.name)));
    }
    out.push_str("  deriving DecidableEq\n\n");
    // One signature per function.
    for f in fns {
        let mut params = Vec::new();
        for (_, pty) in &f.params {
            params.push(ty_of(pty, model));
        }
        let erg = match &f.result {
            None => "none".to_string(),
            Some(ty) => format!("some ({})", ty.term(model)),
        };
        let mut held = String::new();
        for h in &f.held {
            held.push_str(&format!("{}{}", if held.is_empty() { "" } else { ", " }, lock_ctor(model, *h)));
        }
        let boden = match f.boden {
            None => "none".to_string(),
            Some(c) => format!("some {c}"),
        };
        let schreibt = if f.writes.is_empty() {
            "fun _ => false".to_string()
        } else if f.writes.len() == nt {
            "fun _ => true".to_string()
        } else {
            let mut sarms = Vec::new();
            for w in &f.writes {
                sarms.push(format!("| .{} => true", model.tables[*w].name));
            }
            sarms.push("| _ => false".to_string());
            format!("fun {}", sarms.join(" "))
        };
        out.push_str(&format!("def gSig_{} : Signatur GTab Empty GLock Empty where\n", lean_fn(&f.name)));
        out.push_str(&format!("  params := [{}]\n", params.join(", ")));
        out.push_str(&format!("  erg := {erg}\n"));
        out.push_str(&format!("  gruende := {}\n", f.gruende));
        out.push_str(&format!("  haelt := [{held}]\n"));
        out.push_str(&format!("  boden := {boden}\n"));
        out.push_str(&format!("  schreibt := {schreibt}\n"));
        out.push_str("  gschreibt := fun e => nomatch e\n");
        out.push_str("  konsumiert := []\n");
        out.push_str("  produziert := []\n\n");
    }
    // The declaration as a reducible abbreviation: proofs by `decide`
    // synthesize `Decidable` instances over `gD.Tab`/`gD.Lock`, and instance
    // search only unfolds reducible definitions to see the `GTab`/`GLock`
    // inductives behind the projections.
    out.push_str("abbrev gD : Deklaration where\n");
    out.push_str("  Tab := GTab\n");
    out.push_str("  decTab := inferInstance\n");
    if model.tables.is_empty() {
        out.push_str("  count := fun t => nomatch t\n");
        out.push_str("  Feld := fun t => nomatch t\n");
        out.push_str("  decFeld := fun t => nomatch t\n");
        out.push_str("  typ := fun t => nomatch t\n");
    } else {
        let arms: Vec<String> = model.tables.iter()
            .map(|t| format!("| .{} => {}", t.name, t.count)).collect();
        out.push_str(&format!("  count := fun {}\n", arms.join(" ")));
        let farms: Vec<String> = model.tables.iter()
            .map(|t| format!("| .{} => G{}Feld", t.name, t.name)).collect();
        out.push_str(&format!("  Feld := fun {}\n", farms.join(" ")));
        let darms: Vec<String> = model.tables.iter()
            .map(|t| format!("| .{} => inferInstance", t.name)).collect();
        out.push_str(&format!("  decFeld := fun {}\n", darms.join(" ")));
        let mut tarms = Vec::new();
        for t in &model.tables {
            for f in &t.fields {
                tarms.push(format!("| .{}, .{} => ({})", t.name, f.name, f.ty.term(model)));
            }
        }
        out.push_str(&format!("  typ := fun {}\n", tarms.join(" ")));
    }
    out.push_str("  erlaubt := fun _ _ _ _ => false\n");
    if model.tables.is_empty() {
        out.push_str("  tabNr := fun _ => none\n");
    } else {
        let narms: Vec<String> = model.tables.iter().enumerate()
            .map(|(ti, t)| format!("| {ti} => some GTab.{}", t.name)).collect();
        out.push_str(&format!("  tabNr := fun {} | _ => none\n", narms.join(" ")));
    }
    out.push_str("  Glob := Empty\n");
    out.push_str("  decGlob := inferInstance\n");
    out.push_str("  gtyp := fun e => nomatch e\n");
    out.push_str("  nutzlast := fun e => nomatch e\n");
    out.push_str("  atomar := fun e => nomatch e\n");
    if model.tables.is_empty() {
        out.push_str("  geteilt := fun t => nomatch t\n");
    } else {
        let garms: Vec<String> = model.tables.iter().enumerate().map(|(ti, _)| {
            let guarded = model.locks.iter().any(|l| l.guards.contains(&ti));
            format!("| .{} => {guarded}", model.tables[ti].name)
        }).collect();
        out.push_str(&format!("  geteilt := fun {}\n", garms.join(" ")));
    }
    out.push_str("  ggeteilt := fun e => nomatch e\n");
    out.push_str("  Lock := GLock\n");
    out.push_str("  decLock := inferInstance\n");
    if model.locks.is_empty() {
        out.push_str("  rang := fun L => nomatch L\n");
    } else {
        let rarms: Vec<String> = model.locks.iter()
            .map(|l| format!("| .{} => {}", l.name, l.rank)).collect();
        out.push_str(&format!("  rang := fun {}\n", rarms.join(" ")));
    }
    out.push_str("  maskiert := fun _ => false\n");
    out.push_str("  Marke := Empty\n");
    out.push_str("  decMarke := inferInstance\n");
    out.push_str("  stufen := fun e => nomatch e\n");
    if model.tables.is_empty() {
        out.push_str("  braucht := fun t => nomatch t\n");
    } else {
        let barms: Vec<String> = model.tables.iter().enumerate().map(|(ti, t)| {
            let mut guards = String::new();
            for g in model.locks.iter().enumerate().filter(|(_, l)| l.guards.contains(&ti)).map(|(li, _)| li) {
                guards.push_str(&format!("{}.inl GLock.{}", if guards.is_empty() { "" } else { ", " }, model.locks[g].name));
            }
            format!("| .{} => [{guards}]", t.name)
        }).collect();
        out.push_str(&format!("  braucht := fun {}\n", barms.join(" ")));
    }
    out.push_str("  gbraucht := fun e => nomatch e\n");
    out.push_str("  eigner := fun _ => []\n");
    out.push_str("  Fn := GFn\n");
    let sarms: Vec<String> = fns.iter().enumerate()
        .map(|(i, f)| format!("| .{} => {i}", lean_fn(&f.name))).collect();
    out.push_str(&format!("  sig := fun {}\n", sarms.join(" ")));
    let narms2: Vec<String> = fns.iter().enumerate()
        .map(|(i, f)| format!("| {i} => gSig_{}", lean_fn(&f.name))).collect();
    out.push_str(&format!("  sigNr := fun {} | _ => gSig_{}\n", narms2.join(" "),
        lean_fn(&fns.last().expect("nonempty").name)));
    out.push_str("  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h\n");
    out.push_str("  Inv := Empty\n");
    out.push_str("  traeger := fun e => nomatch e\n");
    out.push_str("  invs := []\n");
    out.push_str("  Ax := Empty\n");
    out.push_str("  aparams := fun e => nomatch e\n");
    out.push_str("  aerg := fun e => nomatch e\n");
    out.push_str("  aschreibt := fun e => nomatch e\n");
    out.push_str("  agschreibt := fun e => nomatch e\n");
    out.push_str("  Reg := Empty\n");
    out.push_str("  rtyp := fun e => nomatch e\n");
    out.push_str("  rklasse := fun e => nomatch e\n");
    out.push_str("  spiegel := fun e => nomatch e\n");
    out.push_str("  rzusage := fun e => nomatch e\n");
    out.push_str("  Annahme := Unit\n");
    out.push_str("  a10 := ()\n");
    out.push_str("  geteilt_bewacht := fun t => by cases t <;> decide\n");
    out.push_str("  invarianten_gehalten := fun _ i => nomatch i\n");
    out.push_str("  ggeteilt_bewacht := fun e => nomatch e\n\n");
    // Translate contracts and bodies first (registering every guard fact
    // and call site), then print the abbreviations and theorems they need.
    let mut contracts = Vec::new();
    for f in fns {
        contracts.push((f.name.clone(), tr_contract(f, model, scope, collected)?));
    }
    let mut bodies = Vec::new();
    for f in fns {
        bodies.push((f.name.clone(), tr_endblock(f, model, scope, fns, collected)?));
    }
    // Context and held-list abbreviations, function constants.
    for f in fns {
        let mut params = Vec::new();
        for (_, pty) in &f.params {
            params.push(ty_of(pty, model));
        }
        out.push_str(&format!("abbrev gCtx_{} : Ctx := [{}]\n", lean_fn(&f.name), params.join(", ")));
        out.push_str(&format!("def g_{} : gD.Fn := GFn.{}\n", lean_fn(&f.name), lean_fn(&f.name)));
    }
    out.push('\n');
    // Every held context the translation used: the signature list and one
    // per enclosing `locks` path.
    let mut tags: Vec<(String, String)> = Vec::new();
    for f in fns {
        tags.push((f.name.clone(), String::new()));
    }
    for (fname, tag, _) in collected.darf.clone() {
        if !tags.contains(&(fname.clone(), tag.clone())) {
            tags.push((fname, tag));
        }
    }
    for hp in collected.hps.clone() {
        if !tags.contains(&(hp.caller.clone(), hp.tag.clone())) {
            tags.push((hp.caller, hp.tag));
        }
    }
    for (fname, tag) in &tags {
        let f = fns.iter().find(|f| &f.name == fname).expect("known function");
        let mut held = f.held.clone();
        if !tag.is_empty() {
            // The tag records the taken locks in order (`_in_L[_in_M]`).
            for part in tag.split("_in_").skip(1) {
                if let Some(li) = model.locks.iter().position(|l| l.name == part) {
                    held.push(li);
                }
            }
        }
        let mut hs = String::new();
        for h in &held {
            hs.push_str(&format!("{}Res.held (D := gD) {}",
                if hs.is_empty() { "" } else { ", " }, lock_ctor(model, *h)));
        }
        out.push_str(&format!("abbrev gL_{}{} : List (Res gD) := [{}]\n", lean_fn(fname), tag, hs));
    }
    out.push('\n');
    // The guard facts each use site names: one per (context, table). Pairs
    // whose guards the context does not hold get no theorem (it would be
    // false), and `slot_access` refuses them, so no use site dangles.
    let mut darfs = collected.darf.clone();
    darfs.sort();
    darfs.dedup();
    for (fname, tag, ti) in &darfs {
        out.push_str(&format!("theorem {} : darf gD {} gL_{}{} := by unfold darf; decide\n",
            darf_name(fname, tag, model, *ti), tab_ctor(model, *ti), lean_fn(fname), tag));
    }
    out.push('\n');
    for hp in collected.hps.clone() {
        out.push_str(&format!("theorem gHp_{}{}_{} : RufPasst gD (vertragVon gD g_{}) (gD.signatur g_{}) gL_{}{} where\n",
            lean_fn(&hp.caller), hp.tag, lean_fn(&hp.callee),
            lean_fn(&hp.caller), lean_fn(&hp.callee), lean_fn(&hp.caller), hp.tag));
        // `decide` ranges over closed goals after `cases` splits the small
        // carrier inductives; `fin_cases` would need mathlib, which
        // `grammatik/` does not have.
        out.push_str("  hw := fun t => by cases t <;> decide\n");
        out.push_str("  hg := fun g => nomatch g\n");
        out.push_str("  hk := ⟨[], List.Perm.refl [], by simp⟩\n");
        out.push_str("  hh := fun L => by cases L <;> decide\n");
        // `hx` after the hand witness `HelferZeuge.lean`: one branch per
        // lock -- the floor where it ranks below it, absurdity from `hn`
        // where the callee requires it, absurdity from `hL` where it is
        // not held at all (each decided here, in Rust, first). Always
        // printed: the field default does not close (measured).
        match hp.extra_floor {
            Some(c) => out.push_str(&format!("  hx := fun L hL hn => by cases L <;> (first | exact ⟨{c}, rfl, by decide⟩ | exact absurd (by decide) hn | exact absurd hL (by decide))\n")),
            None => out.push_str("  hx := fun L hL hn => by cases L <;> (first | exact absurd (by decide) hn | exact absurd hL (by decide))\n"),
        }
        // `hb`: the caller's floor is the callee's floor or below it --
        // or there is no caller floor, and the hypothesis contradicts the
        // signature. Always printed, like `hx`.
        match hp.hb {
            Some((c0, c1)) => out.push_str(&format!("  hb := fun c h => by have hV : (vertragVon gD g_{}).boden = some {c0} := rfl; rw [hV] at h; cases h; exact ⟨{c1}, rfl, by decide⟩\n",
                lean_fn(&hp.caller))),
            None => out.push_str(&format!("  hb := fun c h => by have hV : (vertragVon gD g_{}).boden = none := rfl; rw [hV] at h; cases h\n",
                lean_fn(&hp.caller))),
        }
        out.push('\n');
    }
    // Contracts and bodies.
    for (name, term) in &contracts {
        if let Some(term) = term {
            out.push_str(&format!("def gEns_{name} : Expr gD (ErgCtx (gD.params g_{name}) (gD.erg g_{name})) (vertragVon gD g_{name}).ende .bool :=\n  {term}\n\n"));
        }
    }
    for (name, term) in &bodies {
        out.push_str(&format!("def gBody_{name} : Endblock gD (vertragVon gD g_{name}) false gCtx_{name} gL_{name} :=\n  {term}\n\n", name = lean_fn(name)));
    }
    // The program, the member list, and the decidable checks.
    out.push_str("def gP : Programm gD where\n");
    out.push_str("  invariante := fun i => nomatch i\n");
    out.push_str("  requires := fun _ => .wahr\n");
    out.push_str("  ensures\n");
    for f in fns {
        let rhs = if f.ensures.is_empty() { ".wahr".to_string() } else { format!("gEns_{}", lean_fn(&f.name)) };
        out.push_str(&format!("    | .{} => {rhs}\n", lean_fn(&f.name)));
    }
    out.push_str("  rumpf\n");
    for f in fns {
        out.push_str(&format!("    | .{} => gBody_{}\n", lean_fn(&f.name), lean_fn(&f.name)));
    }
    out.push_str(&format!("\ndef gFs : List gD.Fn := [{}]\n\n",
        fns.iter().map(|f| format!("g_{}", lean_fn(&f.name))).collect::<Vec<_>>().join(", ")));
    // The fragment check holds structurally (no registers, no indirect
    // calls); the footprint check holds exactly where every accessed
    // carrier is signature-guarded or written by none -- never guessed.
    out.push_str("example : programmImFragmentG gP gFs = true := by decide\n\n");
    if fuss_holds(model, fns) {
        out.push_str("example : fussOrtGB gP gFs = true := by decide\n\n");
    } else {
        out.push_str("-- No `fussOrtGB` check: some accessed carrier is taken in a\n");
        out.push_str("-- `locks` block (or written elsewhere unguarded), so the old\n");
        out.push_str("-- signature-held footprint does not apply. The applicable check\n");
        out.push_str("-- is the flagship's `FussS`/`fussSperreB`, which has no Rust rule.\n\n");
    }
    // The lock invariant family `gS` (lane 156): `orte` is the `protects`
    // set, `inv` the predicate over the memory snapshot (`fun _ => true`
    // where the lock carries none). The guard half of `SperrInvOk` travels
    // as `List.elem … = true` by `decide`, per lock and protected carrier in
    // both directions (the carrier in `orte`, the guard in `braucht`) -- the
    // universal over all carriers is not decidable (memories are functions),
    // so the decidable content is stated carrier by carrier; the read half
    // and the release duty are the user's, booked beside the `ensures` duties.
    out.push_str("-- The lock invariant family `gS` (`SperrInv`, `SperreSem.lean`):\n");
    for l in &model.locks {
        match &l.invariant {
            None => out.push_str(&format!("-- lock {}: no invariant (arm `fun _ => true`)\n", l.name)),
            Some(_) => out.push_str(&format!("-- lock {}: invariant below\n", l.name)),
        }
    }
    let mut orte_arms = Vec::new();
    let mut inv_arms = Vec::new();
    for l in &model.locks {
        let mut cs = String::new();
        for g in &l.guards {
            cs.push_str(&format!(
                "{}.inl {}",
                if cs.is_empty() { "" } else { ", " },
                tab_ctor(model, *g)
            ));
        }
        orte_arms.push(format!("| .{} => [{}]", l.name, cs));
        let body = match &l.invariant {
            None => "fun _ => true".to_string(),
            Some(p) => format!("fun s => {}", tr_sinv_pred(p, model, scope, &l.name)?),
        };
        inv_arms.push(format!("| .{} => {}", l.name, body));
    }
    out.push_str("def gS : SperrInv gD where\n");
    if model.locks.is_empty() {
        // The empty family (`SperrInv.leer`): no carriers, invariant `true`.
        out.push_str("  orte := fun _ => []\n");
        out.push_str("  inv := fun _ _ => true\n\n");
    } else {
        out.push_str(&format!("  orte := fun {}\n", orte_arms.join(" ")));
        out.push_str(&format!("  inv := fun {}\n\n", inv_arms.join(" ")));
    }
    for l in &model.locks {
        for g in &l.guards {
            let li = model.locks.iter().position(|x| x.name == l.name).expect("lock present");
            // Membership `∈` does not decide over sum carriers in this
            // toolchain (`Decidable (x ∈ l)` fails where `x : T ⊕ Empty`,
            // measured 2026-09-13); `List.elem … = true` is the same
            // computation and decides.
            out.push_str(&format!(
                "example : ((gS.orte {}).elem (.inl {}) = true) := by decide\n",
                lock_ctor(model, li),
                tab_ctor(model, *g)
            ));
            out.push_str(&format!(
                "example : ((gD.braucht {}).elem (Sum.inl {}) = true) := by decide\n",
                tab_ctor(model, *g),
                lock_ctor(model, li)
            ));
        }
    }
    out.push('\n');
    out.push_str(&format!("end {ns}\n\nend Gabbro.Grammatik\n"));
    Ok(out)
}

/// A Gabbro function name as a Lean name: verbatim (names travel, they are
/// not pretty-printed).
fn lean_fn(name: &str) -> String {
    name.to_string()
}
