//! **Export `.gab` to a G program term (Lean 4).**
//!
//! The only certified corpus program today is a HAND translation (`r4P`/`r4D`
//! in `grammatik/Grammatik/Referenz104.lean`). This module is the mechanical
//! path: it reads a checked `.gab` unit and prints a Lean file defining the
//! declaration `gD`, the program `gP : Programm gD` (the G program syntax of
//! `RufMaschineG.lean`, which is `Programm` of `Syntax.lean`), the function
//! list `gFs`, and the two decidable checks `programmImFragmentG` and
//! `fussOrtGB` as `example ... := by decide`.
//!
//! ## What has a G counterpart, and what is refused
//!
//! Every surface form without a counterpart is REFUSED with an `LG` code --
//! never silently truncated. A refusal names the spelling that was typed.
//! The forms with a counterpart:
//!
//! * `table T count N { slot { f : <int range>, ... } }` -- `Tab`/`Feld`/`typ`/`count`
//!   (a bare word travels as its full range, the numbers the checker uses)
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
//! * `impl fn` with pointer/index/range parameters, `requires Held(L)`,
//!   `ensures` over comparisons of slot reads, `old`, `result` and literals,
//!   `effects { reads/writes/locks }`, and a straight-line body of slot
//!   writes through a pointer, direct calls and a trailing `return`
//! * `const NAME = N` (inlined at every use) and `type NAME = u32 in lo..hi`
//!   (resolved at every use); the module wrapper is transparent
//!
//! ## Refusal codes (`LG`)
//!
//! * `LG001` item with no G form (globals, devices, axioms, entries, ...)
//! * `LG002` type with no `Ty` form (floats, records, pointers outside `normal`, ...)
//! * `LG003` contract clause with no `Expr` form
//! * `LG004` body statement with no `Stmt`/`Endblock` form
//! * `LG005` unresolvable name, count, rank or range (unknown table, lock,
//!   function, constant or type alias)

use gabbro_syntax::ast::*;

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

/// The exportable fragment of a unit: tables, locks, functions, threads.
struct Model {
    tables: Vec<TableModel>,
    locks: Vec<LockModel>,
    fns: Vec<FnModel>,
    #[allow(dead_code)]
    concurrent: Vec<String>,
}

struct TableModel {
    name: String,
    count: i128,
    fields: Vec<(String, i128, i128)>,
}

struct LockModel {
    name: String,
    rank: i128,
    guards: Vec<usize>,
    /// `invariant <pred>` -- `None` where the lock carries none (its `inv`
    /// arm is `fun _ => true`, the empty-family shape over its carriers).
    invariant: Option<Pred>,
}

struct FnModel {
    name: String,
    decl: FnDecl,
}

/// A file-local scope: named constants (inlined) and integer type aliases
/// (resolved). Both are NO FORM in G -- the value travels, the name does not.
#[derive(Default)]
struct Scope {
    consts: std::collections::HashMap<String, i128>,
    aliases: std::collections::HashMap<String, (i128, i128)>,
}

/// A numeral where a declaration needs one: a literal, or a named constant.
fn numeral(e: &Expr, scope: &Scope) -> Option<i128> {
    match &e.art {
        ExprArt::Zahl(n) => i128::try_from(*n).ok(),
        ExprArt::Ort(o) if o.suffixe.is_empty() => scope.consts.get(&o.basis.text).copied(),
        _ => None,
    }
}

/// An integer range where G needs a `Ty`: `u32 in lo..hi`, or an alias for
/// one. A bare word (`u32`) travels as its full range -- the same numbers
/// the checker computes with (`breite_von`/`grenzen`), spelled by the word.
fn int_range(t: &TypExpr, scope: &Scope) -> Option<(i128, i128)> {
    match t {
        TypExpr::Int(i) => {
            if let Some(b) = &i.bereich {
                if b.exklusiv {
                    return None;
                }
                let lo = numeral(&b.von, scope)?;
                let hi = numeral(&b.bis, scope)?;
                Some((lo, hi))
            } else {
                let (breite, vz) = crate::umgebung::breite_von(i.wort)?;
                Some(crate::typen::grenzen(breite, vz))
            }
        }
        TypExpr::Pfad(p) => {
            let name = p.einfach()?;
            scope.aliases.get(&name.text).copied()
        }
        _ => None,
    }
}

/// Every item of the unit, through modules. Anything without a G form is
/// refused here, so nothing below ever sees it.
fn collect(source_name: &str, tree: &Programm) -> Result<Model, Refusal> {
    let mut model = Model { tables: vec![], locks: vec![], fns: vec![], concurrent: vec![] };
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
                    let Some(range) = int_range(r, scope) else {
                        return Err(refuse("LG002", format!("type {} is not an integer range", t.name.text)));
                    };
                    scope.aliases.insert(t.name.text.clone(), range);
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
    if model.tables.is_empty() {
        return Err(refuse("LG001", "a G declaration needs at least one table".to_string()));
    }
    if model.fns.is_empty() {
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
/// written tables, contracts and the body.
struct CheckedFn {
    name: String,
    params: Vec<(String, ParamTy)>,
    result: Option<(i128, i128)>,
    held: Vec<usize>,
    writes: Vec<usize>,
    ensures: Vec<Pred>,
    body: Block,
}

/// A parameter as G sees it: a pointer to a table, an index into one, or an
/// integer range. Named address spaces other than `normal` have no G form.
enum ParamTy {
    Ptr { table: usize, write: bool },
    Index { table: usize },
    Int(i128, i128),
}

fn check_fn(f: &FnModel, model: &Model, scope: &Scope) -> Result<CheckedFn, Refusal> {
    let d = &f.decl;
    if d.klasse != Some(FnKlasse::Impl) {
        return Err(refuse("LG001", format!("function {} is not `impl`", f.name)));
    }
    if d.fehler.is_some() || d.verfeinert.is_some() || !d.maintains.is_empty()
        || d.deadline.is_some() || d.decreases.is_some() || !d.by.is_empty()
        || d.arch.is_some() || d.when.is_some() || d.advances.is_some() || d.retires.is_some()
    {
        return Err(refuse("LG001", format!("function {} carries a form with no G counterpart", f.name)));
    }
    let mut params = Vec::new();
    for p in &d.parameter {
        params.push((p.name.text.clone(), param_ty(&p.typ, model, scope, &f.name)?));
    }
    let result = match &d.ergebnis {
        None => None,
        Some(t) => Some(int_range(t, scope).ok_or_else(|| {
            refuse("LG002", format!("result of {} has no integer-range form", f.name))
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
    let effects = d.effects.as_ref().ok_or_else(|| {
        refuse("LG001", format!("function {} has no `effects`", f.name))
    })?;
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
    if held != effect_locks {
        // `requires Held(L)` names the signature-held set (`RufPasst.hh`:
        // exactly the witnesses the caller holds). An effect `locks L`
        // beyond it would need the `locks` statement, which has no form
        // here; an effect below it (108: readers holding by signature
        // without redeeming an effect) is that statement's absence.
        for l in &effect_locks {
            if !held.contains(l) {
                return Err(refuse(
                    "LG001",
                    format!("function {}: `locks {}` without `requires Held` has no G form in this fragment",
                        f.name, model.locks[*l].name),
                ));
            }
        }
    }
    let FnRumpf::Block(body) = &d.rumpf else {
        return Err(refuse("LG004", format!("function {} has no block body", f.name)));
    };
    Ok(CheckedFn { name: f.name.clone(), params, result, held, writes, ensures: d.ensures.clone(), body: body.clone() })
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
            let write = p.rechte.iter().any(|r| matches!(r, Recht::LesenSchreiben | Recht::Schreiben));
            if !p.rechte.iter().any(|r| matches!(r, Recht::Lesen | Recht::Schreiben | Recht::LesenSchreiben)) {
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
        t => int_range(t, scope)
            .map(|(lo, hi)| ParamTy::Int(lo, hi))
            .ok_or_else(|| refuse("LG002", format!("parameter type in {fname} has no G form"))),
    }
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
        match &f.typ {
            SlotTyp::Typ(ty) => {
                let Some((lo, hi)) = int_range(ty, scope) else {
                    return Err(refuse("LG002", format!("field {} has no integer-range form", f.name.text)));
                };
                fields.push((f.name.text.clone(), lo, hi));
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
            if t.name == o.basis.text || t.fields.iter().any(|(f, _, _)| f == &o.basis.text) {
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
    let model = collect(source_name, tree)?;
    let scope = rescope(tree)?;
    let mut checked = Vec::new();
    for f in &model.fns {
        checked.push(check_fn(f, &model, &scope)?);
    }
    for c in &checked {
        check_contracts(c, &model)?;
        check_body(c, &model)?;
    }
    check_locks(&model, &scope)?;
    Ok(emit(source_name, &model, &checked, &scope)?)
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
                    let (lo, hi) = int_range(r, scope).expect("checked in collect");
                    scope.aliases.insert(t.name.text.clone(), (lo, hi));
                }
                _ => {}
            }
        }
        Ok(())
    }
    go(&mut scope, &tree.items)?;
    Ok(scope)
}

/// Translation context: the value environment. Bodies see the parameters;
/// `ensures` sees the result first (`ErgCtx`). `gamma`/`lambda` are the exact
/// `Γ`/`Λ` terms for type ascriptions: every emitted tactic proof is ascribed
/// a fully concrete type, because elaboration order must never decide whether
/// `D` is pinned when a `by decide` runs.
struct Ctx<'a> {
    cf: &'a CheckedFn,
    with_result: bool,
    gamma: String,
    lambda: String,
}

fn body_ctx(cf: &CheckedFn) -> Ctx<'_> {
    let g = lean_fn(&cf.name);
    Ctx { cf, with_result: false, gamma: format!("gCtx_{g}"), lambda: format!("gL_{g}") }
}

fn ensures_ctx(cf: &CheckedFn) -> Ctx<'_> {
    let g = lean_fn(&cf.name);
    Ctx {
        cf,
        with_result: cf.result.is_some(),
        gamma: format!("(ErgCtx (gD.params g_{g}) (gD.erg g_{g}))"),
        lambda: format!("gL_{g}"),
    }
}

impl Ctx<'_> {
    /// The de Bruijn variable for parameter `j`.
    fn var(&self, j: usize) -> String {
        let depth = if self.with_result { j + 1 } else { j };
        let mut s = ".hier".to_string();
        for _ in 0..depth {
            s = format!("(.dort {s})");
        }
        format!("(.var {s})")
    }

    fn param_index(&self, name: &str) -> Option<usize> {
        self.cf.params.iter().position(|(n, _)| n == name)
    }

    /// The full `Expr` type of an index into table `t` in this context. Used
    /// as an ascription on literal indices: without it the declaration `D`
    /// is still a metavariable when the `weiter` proofs elaborate, and they
    /// fail instead of postponing. (`Expr` takes `Γ Λ τ`; dropping `Λ` puts
    /// `.index` in the `List (Res D)` position and it resolves to
    /// `List.index`.)
    fn index_ty(&self, model: &Model, t: usize) -> String {
        format!("Expr gD {} {} (.index (gD.count {}))", self.gamma, self.lambda, tab_ctor(model, t))
    }
}

/// The named guard fact for function `fname` and table `t`: proved
/// top-level with a fully concrete type (`unfold` on the access predicate +
/// `decide`), because inline the declaration stays a metavariable when the
/// proof elaborates. Only pairs whose guards the function holds get a
/// theorem; `slot_access` refuses the rest, so a reference never dangles.
fn darf_name(fname: &str, model: &Model, t: usize) -> String {
    format!("gDarf_{}_{}", lean_fn(fname), model.tables[t].name)
}

/// Every table `t`'s guards must be among `held`: the generation-time half
/// of the guard proof (the Lean half is the `gDarf` theorem the use site names).
fn holds_guards(held: &[usize], model: &Model, t: usize) -> bool {
    model.locks.iter().enumerate()
        .filter(|(_, l)| l.guards.contains(&t))
        .map(|(li, _)| li)
        .all(|li| held.contains(&li))
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
    format!("{}.{}", feld_type(model, t), model.tables[t].fields[fi].0)
}

/// A `Ty` as G spells it.
fn ty_of(pty: &ParamTy, model: &Model) -> String {
    match pty {
        ParamTy::Ptr { table, write } => format!(".ptr {table} {write}"),
        ParamTy::Index { table } => format!(".index {}", model.tables[*table].count),
        ParamTy::Int(lo, hi) => format!(".int {lo} {hi}"),
    }
}

fn is_numeric(ty: &str) -> bool {
    ty.starts_with(".int") || ty.starts_with(".index")
}

/// Coerce `base` of type `actual` to `expected`: direct where equal, a
/// widening where both are numeric, refused otherwise (Lean would fail there,
/// and a Lean failure is not a named refusal).
fn fit(base: String, actual: &str, expected: &str, fname: &str) -> Result<String, Refusal> {
    if actual == expected {
        Ok(base)
    } else if is_numeric(actual) && is_numeric(expected) {
        Ok(format!("(.weiter (by decide) (by decide) {base})"))
    } else {
        Err(refuse("LG004", format!("type {actual} in {fname} has no coercion to {expected}")))
    }
}

/// The index expression for slot `idx` of table `t`.
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
            let Some(j) = ctx.param_index(&o.basis.text) else {
                return Err(refuse("LG005", format!("unknown name {} in {fname}", o.basis.text)));
            };
            match &ctx.cf.params[j].1 {
                ParamTy::Index { table } if *table == t => Ok(ctx.var(j)),
                _ => Err(refuse("LG004", format!("index {} in {fname} has no G form", o.text()))),
            }
        }
        _ => Err(refuse("LG003", format!("index in {fname} has no G form"))),
    }
}

/// A slot read `p.slots[i].f` / `T.slots[i].f`: table, field, index term, and
/// the pointer parameter it goes through (`None` at a table name).
fn slot_access(o: &Ort, ctx: &Ctx, model: &Model, fname: &str) -> Result<(usize, usize, String, Option<usize>), Refusal> {
    let [OrtSuffix::Feld(slots), OrtSuffix::Index(idx), OrtSuffix::Feld(f)] = o.suffixe.as_slice() else {
        return Err(refuse("LG003", format!("place {} in {fname} has no G form", o.text())));
    };
    if slots.text != "slots" {
        return Err(refuse("LG003", format!("place {} in {fname} has no G form", o.text())));
    }
    let (t, through) = if let Some(ti) = model.tables.iter().position(|t| t.name == o.basis.text) {
        (ti, None)
    } else if let Some(j) = ctx.param_index(&o.basis.text) {
        match &ctx.cf.params[j].1 {
            ParamTy::Ptr { table, .. } => (*table, Some(j)),
            _ => return Err(refuse("LG003", format!("place {} in {fname} has no G form", o.text()))),
        }
    } else {
        return Err(refuse("LG005", format!("unknown name {} in {fname}", o.basis.text)));
    };
    let Some(fi) = model.tables[t].fields.iter().position(|(n, _, _)| n == &f.text) else {
        return Err(refuse("LG005", format!("unknown field {} in {fname}", o.text())));
    };
    if !holds_guards(&ctx.cf.held, model, t) {
        return Err(refuse("LG004", format!("access to {} in {fname} holds no guard (no proof)", o.text())));
    }
    let index = tr_index(idx, t, ctx, model, fname)?;
    Ok((t, fi, index, through))
}

/// A value expression against the expected `Ty`: literals widen, places must
/// fit, everything else is refused.
fn tr_value(e: &Expr, expected: &str, ctx: &Ctx, model: &Model, fname: &str, in_ensures: bool) -> Result<String, Refusal> {
    match &e.art {
        ExprArt::Zahl(n) => {
            let n = i128::try_from(*n).map_err(|_| refuse("LG003", format!("literal in {fname} too large")))?;
            if n < 0 {
                return Err(refuse("LG003", format!("negative literal in {fname} has no G form")));
            }
            if !is_numeric(expected) {
                return Err(refuse("LG003", format!("literal in {fname} has no G form here")));
            }
            Ok(format!("(.weiter (by decide) (by decide) (.lit {n}))"))
        }
        ExprArt::Ort(o) if o.suffixe.is_empty() => {
            let Some(j) = ctx.param_index(&o.basis.text) else {
                return Err(refuse("LG005", format!("unknown name {} in {fname}", o.basis.text)));
            };
            let actual = ty_of(&ctx.cf.params[j].1, model);
            fit(ctx.var(j), &actual, expected, fname)
        }
        ExprArt::Ort(o) => {
            let (t, fi, index, through) = slot_access(o, ctx, model, fname)?;
            let (_, lo, hi) = &model.tables[t].fields[fi];
            let (lo, hi) = (*lo, *hi);
            let base = if let Some(j) = through {
                format!("(Expr.durch (D := gD) {} {} rfl {} ({index}) {proof})", ctx.var(j), tab_ctor(model, t), feld_ctor(model, t, fi), proof = darf_name(fname, model, t))
            } else {
                format!("(Expr.slot (D := gD) {} {} ({index}) {proof})", tab_ctor(model, t), feld_ctor(model, t, fi), proof = darf_name(fname, model, t))
            };
            fit(base, &format!(".int {lo} {hi}"), expected, fname)
        }
        ExprArt::Ergebnis => {
            if !in_ensures || ctx.cf.result.is_none() {
                return Err(refuse("LG003", format!("`result` in {fname} has no G form here")));
            }
            let (lo, hi) = ctx.cf.result.expect("checked above");
            fit("(.var .hier)".to_string(), &format!(".int {lo} {hi}"), expected, fname)
        }
        _ => Err(refuse("LG003", format!("expression in {fname} has no G form"))),
    }
}

/// `old(p.slots[i].f)` / `old(T.slots[i].f)` in an `ensures`: the entry value
/// of the table slot (a pointer's `old` is the table's `old` -- the hand
/// translation reads it the same way).
fn tr_old(o: &Ort, ctx: &Ctx, model: &Model, fname: &str) -> Result<String, Refusal> {
    let (t, fi, index, _) = slot_access(o, ctx, model, fname)?;
    Ok(format!("(Expr.altSlot (D := gD) {} {} ({index}) {proof})", tab_ctor(model, t), feld_ctor(model, t, fi), proof = darf_name(fname, model, t)))
}

/// One side of an `ensures` comparison: the term and its range.
fn tr_side(e: &Expr, ctx: &Ctx, model: &Model, fname: &str) -> Result<(String, String), Refusal> {
    match &e.art {
        ExprArt::Zahl(n) => {
            let n = i128::try_from(*n).map_err(|_| refuse("LG003", format!("literal in {fname} too large")))?;
            if n < 0 {
                return Err(refuse("LG003", format!("negative literal in {fname} has no G form")));
            }
            Ok((format!("(.weiter (by decide) (by decide) (.lit {n}))"), format!(".int {n} {n}")))
        }
        ExprArt::Ort(o) if o.suffixe.is_empty() => {
            let Some(j) = ctx.param_index(&o.basis.text) else {
                return Err(refuse("LG005", format!("unknown name {} in {fname}", o.basis.text)));
            };
            let ty = ty_of(&ctx.cf.params[j].1, model);
            if !is_numeric(&ty) {
                return Err(refuse("LG003", format!("comparison in {fname} has no G form")));
            }
            Ok((ctx.var(j), ty))
        }
        ExprArt::Ort(o) => {
            let (t, fi, index, through) = slot_access(o, ctx, model, fname)?;
            let (_, lo, hi) = &model.tables[t].fields[fi];
            let (lo, hi) = (*lo, *hi);
            let base = if let Some(j) = through {
                format!("(Expr.durch (D := gD) {} {} rfl {} ({index}) {proof})", ctx.var(j), tab_ctor(model, t), feld_ctor(model, t, fi), proof = darf_name(fname, model, t))
            } else {
                format!("(Expr.slot (D := gD) {} {} ({index}) {proof})", tab_ctor(model, t), feld_ctor(model, t, fi), proof = darf_name(fname, model, t))
            };
            Ok((base, format!(".int {lo} {hi}")))
        }
        ExprArt::Ergebnis => {
            let Some((lo, hi)) = ctx.cf.result else {
                return Err(refuse("LG003", format!("`result` in {fname} has no G form here")));
            };
            Ok(("(.var .hier)".to_string(), format!(".int {lo} {hi}")))
        }
        ExprArt::Alt(o) => {
            let (t, fi, _, _) = slot_access(o, ctx, model, fname)?;
            let (_, lo, hi) = &model.tables[t].fields[fi];
            let (lo, hi) = (*lo, *hi);
            Ok((tr_old(o, ctx, model, fname)?, format!(".int {lo} {hi}")))
        }
        _ => Err(refuse("LG003", format!("comparison in {fname} has no G form"))),
    }
}

/// One `ensures` comparison. G has `lt`/`le`/`eq` only; the rest are folded.
fn tr_cmp(op: &BinOp, l: &Expr, r: &Expr, ctx: &Ctx, model: &Model, fname: &str) -> Result<String, Refusal> {
    let (ls, _) = tr_side(l, ctx, model, fname)?;
    let (rs, _) = tr_side(r, ctx, model, fname)?;
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
            let Some(fi) = model.tables[t].fields.iter().position(|(n, _, _)| n == &f.text) else {
                return Err(refuse(
                    "LG005",
                    format!("unknown field {} in the lock invariant of {lock}", o.text()),
                ));
            };
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
fn tr_ensures(p: &Pred, ctx: &Ctx, model: &Model, fname: &str) -> Result<String, Refusal> {
    match &p.art {
        PredArt::Vergleich(e) => match &e.art {
            ExprArt::Binaer(op, l, r) if op.ist_vergleich() => tr_cmp(op, l, r, ctx, model, fname),
            ExprArt::Wahr => Ok(".wahr".to_string()),
            ExprArt::Falsch => Ok(".falsch".to_string()),
            _ => Err(refuse("LG003", format!("ensures-clause in {fname} has no G form"))),
        },
        PredArt::Klammer(q) => tr_ensures(q, ctx, model, fname),
        PredArt::Und(a, b) => Ok(format!("(.und {} {})", tr_ensures(a, ctx, model, fname)?, tr_ensures(b, ctx, model, fname)?)),
        PredArt::Oder(a, b) => Ok(format!("(.oder {} {})", tr_ensures(a, ctx, model, fname)?, tr_ensures(b, ctx, model, fname)?)),
        PredArt::Nicht(q) => Ok(format!("(.nicht {})", tr_ensures(q, ctx, model, fname)?)),
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
fn check_contracts(cf: &CheckedFn, model: &Model) -> Result<(), Refusal> {
    // `ErgCtx` prepends the result only where there is one.
    let ctx = ensures_ctx(cf);
    for p in &cf.ensures {
        tr_ensures(p, &ctx, model, &cf.name)?;
    }
    Ok(())
}

/// One call argument against the callee's parameter type. A `rw` pointer
/// passed where an `r` is declared has no coercion form -- like the hand
/// translation, the exporter passes a fresh pointer to the same table.
fn tr_arg(a: &Expr, pty: &ParamTy, ctx: &Ctx, model: &Model, fname: &str) -> Result<String, Refusal> {
    let expected = ty_of(pty, model);
    match (pty, &a.art) {
        (ParamTy::Ptr { table, write }, ExprArt::Ort(o)) if o.suffixe.is_empty() => {
            let Some(j) = ctx.param_index(&o.basis.text) else {
                return Err(refuse("LG005", format!("unknown name {} in {fname}", o.basis.text)));
            };
            match &ctx.cf.params[j].1 {
                ParamTy::Ptr { table: t2, write: w2 } if t2 == table => {
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
        (ParamTy::Int(..), _) => tr_value(a, &expected, ctx, model, fname, false),
        (ParamTy::Ptr { .. }, _) => Err(refuse("LG004", format!("pointer argument in {fname} has no G form"))),
    }
}

/// One body statement: an assignment or a call. `return` is peeled by the
/// body emitter, never translated here. Returns the term and, for a call,
/// the callee (so the emitter prints the `RufPasst` proof beside it).
fn tr_stmt(s: &Stmt, ctx: &Ctx, model: &Model, fns: &[CheckedFn]) -> Result<(String, Option<String>), Refusal> {
    let fname = ctx.cf.name.clone();
    match &s.art {
        StmtArt::Zuweisung(z) => {
            if z.op != ZuwOp::Setzt {
                return Err(refuse("LG004", format!("compound assignment in {fname} has no G form")));
            }
            let (t, fi, index, through) = slot_access(&z.ziel, ctx, model, &fname)?;
            let (_, lo, hi) = &model.tables[t].fields[fi];
            let (lo, hi) = (*lo, *hi);
            let val = tr_value(&z.wert, &format!(".int {lo} {hi}"), ctx, model, &fname, false)?;
            let base = if let Some(j) = through {
                match &ctx.cf.params[j].1 {
                    ParamTy::Ptr { write: true, .. } => {},
                    _ => return Err(refuse("LG004", format!("write through a read-only pointer in {fname}"))),
                }
                format!("(.assignDurch {} {} rfl {} ({index}) {val} (by decide) {proof})",
                    ctx.var(j), tab_ctor(model, t), feld_ctor(model, t, fi), proof = darf_name(&fname, model, t))
            } else {
                format!("(.assignSlot {} {} ({index}) {val} (by decide) {proof})",
                    tab_ctor(model, t), feld_ctor(model, t, fi), proof = darf_name(&fname, model, t))
            };
            Ok((base, None))
        }
        StmtArt::Ruf(r) => {
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
            // `RufPasst.hh`: the callee's `requires Held` names EXACTLY the
            // witnesses the caller holds. A call across different held sets
            // (a helper called with and without a lock) has no `RufPasst`
            // term -- the checker accepts it, the model cannot type it.
            let caller_holds: std::collections::BTreeSet<usize> = ctx.cf.held.iter().copied().collect();
            let callee_holds: std::collections::BTreeSet<usize> = callee.held.iter().copied().collect();
            if caller_holds != callee_holds {
                return Err(refuse("LG004", format!("call of {} in {fname} holds a different lock set (`RufPasst.hh`)", callee.name)));
            }
            if r.argumente.len() != callee.params.len() {
                return Err(refuse("LG004", format!("call of {} in {fname} has the wrong arity", callee.name)));
            }
            let mut term = ".nil".to_string();
            for (a, (_, pty)) in r.argumente.iter().zip(callee.params.iter()).rev() {
                let ta = tr_arg(a, pty, ctx, model, &fname)?;
                term = format!("(.cons {ta} {term})");
            }
            let hp = format!("gHp_{}_{}", lean_fn(&fname), lean_fn(&callee.name));
            let call = format!("(.call g_{} {term} {hp} rfl)", lean_fn(&callee.name));
            Ok((call, Some(callee.name.clone())))
        }
        StmtArt::Return(_) => Err(refuse("LG004", format!("`return` in the middle of {fname} has no G form"))),
        _ => Err(refuse("LG004", format!("statement in {fname} has no G form"))),
    }
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

/// One body as an `Endblock` term: the statements consed onto the trailing
/// `return` (explicit, or the fall-off rule for result-free functions).
fn tr_body(cf: &CheckedFn, model: &Model, fns: &[CheckedFn]) -> Result<(String, Vec<(String, String)>), Refusal> {
    let ctx = body_ctx(cf);
    let mut stmts = cf.body.anweisungen.as_slice();
    // Peel the trailing `return` (checked by `check_body`).
    let mut ret = "(.ret .keine (List.Perm.refl _))".to_string();
    if let Some(last) = stmts.last() {
        if let StmtArt::Return(e) = &last.art {
            match (&cf.result, e) {
                (None, None) => { stmts = &stmts[..stmts.len() - 1]; }
                (Some((lo, hi)), Some(v)) => {
                    let val = tr_value(v, &format!(".int {lo} {hi}"), &ctx, model, &cf.name, false)?;
                    ret = format!("(.ret (.wert {val}) (List.Perm.refl _))");
                    stmts = &stmts[..stmts.len() - 1];
                }
                _ => return Err(refuse("LG004", format!("`return` in {} disagrees with its result", cf.name))),
            }
        }
    }
    let mut hps = Vec::new();
    let mut term = ret;
    for s in stmts.iter().rev() {
        let (st, callee) = tr_stmt(s, &ctx, model, fns)?;
        if let Some(g) = callee {
            hps.push((cf.name.clone(), g));
        }
        term = format!("(.cons {st} {term})");
    }
    Ok((term, hps))
}

/// One `ensures` contract as an `Expr` term (`.wahr` where there is none).
fn tr_contract(cf: &CheckedFn, model: &Model) -> Result<Option<String>, Refusal> {
    if cf.ensures.is_empty() {
        return Ok(None);
    }
    let ctx = ensures_ctx(cf);
    let mut it = cf.ensures.iter();
    let first = tr_ensures(it.next().expect("nonempty"), &ctx, model, &cf.name)?;
    let mut acc = first;
    for p in it {
        let t = tr_ensures(p, &ctx, model, &cf.name)?;
        acc = format!("(.und {acc} {t})");
    }
    Ok(Some(acc))
}

/// The namespace segment for a source file: sanitized stem (`104-referenz`
/// becomes `G104_referenz`), so two exports never declare the same names.
fn namespace_of(source_name: &str) -> String {
    let stem = source_name.rsplit('/').next().unwrap_or(source_name);
    let stem = stem.rsplit('.').nth(1).unwrap_or(stem);
    let mut s: String = stem.chars().map(|c| if c.is_alphanumeric() || c == '_' { c } else { '_' }).collect();
    if s.is_empty() || !s.chars().next().is_some_and(|c| c.is_alphabetic()) {
        s = format!("G{s}");
    }
    s
}

/// The printed Lean file.
fn emit(source_name: &str, model: &Model, fns: &[CheckedFn], scope: &Scope) -> Result<String, Refusal> {
    let nt = model.tables.len();
    let nl = model.locks.len();
    let mut out = String::new();
    // Header: generated marker, source, and the NO-FORM ledger.
    out.push_str(&format!("-- GENERATED by `gabbro lean-g {source_name}` -- do not edit.\n"));
    out.push_str("-- A mechanical export of the checked unit as a G program term\n");
    out.push_str("-- (`Programm gD`, the syntax `RufMaschineG.lean` runs).\n--\n");
    out.push_str("-- NO FORM in G (accepted and dropped, each named): the module\n");
    out.push_str("-- wrapper; named constants (inlined at every use); bare carrier\n");
    out.push_str("-- widths (a bare word travels as its full range); pointer address\n");
    out.push_str("-- spaces; lock hold budgets;\n");
    out.push_str("-- the `reads` effects; `costs`; `concurrent` (all functions travel\n");
    out.push_str("-- in `gFs`; which of them start threads is not a G notion).\n--\n");
    for (ti, t) in model.tables.iter().enumerate() {
        out.push_str(&format!("-- table {ti}: {} (count {})", t.name, t.count));
        for (f, lo, hi) in &t.fields {
            out.push_str(&format!(", {f} : {lo}..{hi}"));
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
    let ns = namespace_of(source_name);
    out.push_str(&ns);
    out.push_str("\n\n");
    // The carrier inductives: one constructor per table, lock and field.
    out.push_str("inductive GTab where\n");
    for t in &model.tables {
        out.push_str(&format!("  | {}\n", t.name));
    }
    out.push_str("  deriving DecidableEq\n\n");
    out.push_str("inductive GLock where\n");
    for l in &model.locks {
        out.push_str(&format!("  | {}\n", l.name));
    }
    out.push_str("  deriving DecidableEq\n\n");
    for (ti, t) in model.tables.iter().enumerate() {
        out.push_str(&format!("inductive {} where\n", feld_type(model, ti)));
        for (f, _, _) in &t.fields {
            out.push_str(&format!("  | {f}\n"));
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
        let erg = match f.result {
            None => "none".to_string(),
            Some((lo, hi)) => format!("some (.int {lo} {hi})"),
        };
        let mut held = String::new();
        for h in &f.held {
            held.push_str(&format!("{}{}", if held.is_empty() { "" } else { ", " }, lock_ctor(model, *h)));
        }
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
        out.push_str("  gruende := 0\n");
        out.push_str(&format!("  haelt := [{held}]\n"));
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
        for (f, lo, hi) in &t.fields {
            tarms.push(format!("| .{}, .{f} => .int {lo} {hi}", t.name));
        }
    }
    out.push_str(&format!("  typ := fun {}\n", tarms.join(" ")));
    out.push_str("  erlaubt := fun _ _ _ _ => false\n");
    let narms: Vec<String> = model.tables.iter().enumerate()
        .map(|(ti, t)| format!("| {ti} => some GTab.{}", t.name)).collect();
    out.push_str(&format!("  tabNr := fun {} | _ => none\n", narms.join(" ")));
    out.push_str("  Glob := Empty\n");
    out.push_str("  decGlob := inferInstance\n");
    out.push_str("  gtyp := fun e => nomatch e\n");
    out.push_str("  nutzlast := fun e => nomatch e\n");
    out.push_str("  atomar := fun e => nomatch e\n");
    let garms: Vec<String> = model.tables.iter().enumerate().map(|(ti, _)| {
        let guarded = model.locks.iter().any(|l| l.guards.contains(&ti));
        format!("| .{} => {guarded}", model.tables[ti].name)
    }).collect();
    out.push_str(&format!("  geteilt := fun {}\n", garms.join(" ")));
    out.push_str("  ggeteilt := fun e => nomatch e\n");
    out.push_str("  Lock := GLock\n");
    out.push_str("  decLock := inferInstance\n");
    let rarms: Vec<String> = model.locks.iter()
        .map(|l| format!("| .{} => {}", l.name, l.rank)).collect();
    out.push_str(&format!("  rang := fun {}\n", rarms.join(" ")));
    out.push_str("  maskiert := fun _ => false\n");
    out.push_str("  Marke := Empty\n");
    out.push_str("  decMarke := inferInstance\n");
    out.push_str("  stufen := fun e => nomatch e\n");
    let barms: Vec<String> = model.tables.iter().enumerate().map(|(ti, t)| {
        let mut guards = String::new();
        for g in model.locks.iter().enumerate().filter(|(_, l)| l.guards.contains(&ti)).map(|(li, _)| li) {
            guards.push_str(&format!("{}.inl GLock.{}", if guards.is_empty() { "" } else { ", " }, model.locks[g].name));
        }
        format!("| .{} => [{guards}]", t.name)
    }).collect();
    out.push_str(&format!("  braucht := fun {}\n", barms.join(" ")));
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
    // Context and held-list abbreviations, function constants.
    for f in fns {
        let mut params = Vec::new();
        for (_, pty) in &f.params {
            params.push(ty_of(pty, model));
        }
        out.push_str(&format!("abbrev gCtx_{} : Ctx := [{}]\n", lean_fn(&f.name), params.join(", ")));
        let mut held = String::new();
        for h in &f.held {
            held.push_str(&format!("{}Res.held (D := gD) {}",
                if held.is_empty() { "" } else { ", " }, lock_ctor(model, *h)));
        }
        out.push_str(&format!("abbrev gL_{} : List (Res gD) := [{}]\n", lean_fn(&f.name), held));
        out.push_str(&format!("def g_{} : gD.Fn := GFn.{}\n", lean_fn(&f.name), lean_fn(&f.name)));
        // The guard facts this function can use: one per table whose guards
        // it holds. Pairs it does not hold get no theorem (it would be
        // false), and `slot_access` refuses them, so no use site dangles.
        for (ti, t) in model.tables.iter().enumerate() {
            if holds_guards(&f.held, model, ti) {
                out.push_str(&format!("theorem {} : darf gD {} gL_{} := by unfold darf; decide\n",
                    darf_name(&f.name, model, ti), tab_ctor(model, ti), lean_fn(&f.name)));
            }
        }
        out.push('\n');
    }
    // Bodies (collecting the call sites for the `RufPasst` proofs).
    let mut bodies = Vec::new();
    let mut hps = Vec::new();
    for f in fns {
        let (term, calls) = tr_body(f, model, fns)?;
        for (caller, callee) in calls {
            if !hps.contains(&(caller.clone(), callee.clone())) {
                hps.push((caller, callee));
            }
        }
        bodies.push((f.name.clone(), term));
    }
    for (caller, callee) in &hps {
        out.push_str(&format!("theorem gHp_{caller}_{callee} : RufPasst gD (vertragVon gD g_{caller}) (gD.signatur g_{callee}) gL_{caller} where\n"));
        // `decide` ranges over closed goals after `cases` splits the small
        // carrier inductives; `fin_cases` would need mathlib, which
        // `grammatik/` does not have. (`decide` proves the closed `↔`
        // directly; splitting it first with `Iff.intro` leaves the two
        // halves to metavariables the synthesis cannot see.)
        out.push_str("  hw := fun t => by cases t <;> decide\n");
        out.push_str("  hg := fun g => nomatch g\n");
        out.push_str("  hk := ⟨[], List.Perm.refl [], by simp⟩\n");
        out.push_str("  hh := fun L => by cases L <;> decide\n\n");
    }
    // Contracts and bodies.
    for f in fns {
        if let Some(term) = tr_contract(f, model)? {
            out.push_str(&format!("def gEns_{} : Expr gD (ErgCtx (gD.params g_{}) (gD.erg g_{})) (vertragVon gD g_{}).ende .bool :=\n  {term}\n\n",
                lean_fn(&f.name), lean_fn(&f.name), lean_fn(&f.name), lean_fn(&f.name)));
        }
    }
    for (name, term) in &bodies {
        out.push_str(&format!("def gBody_{name} : Endblock gD (vertragVon gD g_{name}) false gCtx_{name} gL_{name} :=\n  {term}\n\n"));
    }
    // The program, the member list, and the two decidable checks.
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
    out.push_str("example : programmImFragmentG gP gFs = true := by decide\n\n");
    out.push_str("example : fussOrtGB gP gFs = true := by decide\n\n");
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
    out.push_str(&format!("  orte := fun {}\n", orte_arms.join(" ")));
    out.push_str(&format!("  inv := fun {}\n\n", inv_arms.join(" ")));
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
