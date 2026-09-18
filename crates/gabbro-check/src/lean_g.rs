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
//!   A `bool` field travels as `Ty.bool` and a `tagged` field as `Ty.sum`
//!   (see below); `option`, record, float and wrapping fields have no form
//!   (LG002). A unit without tables travels with `Tab := Empty` (pure
//!   computation over parameters).
//! * `tagged type N = { Leer, Kurz(u32 in 0 .. 100) };` -- **`Ty.sum`**,
//!   closed 2026-09-15. The cases are the `List (Option (Int × Int))` the
//!   type is indexed by, in DECLARATION order, and a case is its POSITION:
//!   `Kurz(x)` is `Expr.fall cs ⟨i, _⟩ (.zahl x)`, the payload-free `Leer` is
//!   `.keine`, and `match m { … }` is `Stmt.onTag` with an `Arms` list of ONE
//!   block per case, in that same order (`ArmCtx` pushes the payload of a
//!   case that has one). A tagged value travels as a parameter, a result, a
//!   slot field, a global and a `static` initialiser (`gSp0` at the case the
//!   `static` names; a slot starts at case 0, payload zero, for the same
//!   reason every integer slot starts at zero).
//!   **Refused BY NAME:** a case payload that is not ONE integer range
//!   (`Nutzlast` is `Option (Int × Int)`, so a `bool`, a pointer, a record, a
//!   float or a nested tagged payload has none -- LG002); a tagged type with
//!   NO case (`Val (.sum [])` is `Σ i : Fin 0, …` and holds no value at all,
//!   so nothing of that type can exist -- LG002); a case name two tagged
//!   types share (the exporter translates bottom-up and has no expected type
//!   to pick the `Ty.sum` with -- LG005); a `match` over an `option` or a
//!   reason, whose forms are `Stmt.onOption` and `Stmt.onGrund` and are not
//!   built here (LG004). A `tagged` type is NEVER also `linear`/`ghost`:
//!   a `Ty.sum` is a VALUE and a `D.Marke` is a RESOURCE, and no
//!   `Deklaration` field carries both.
//! * `static mut X : <int range|bool> = <literal>;` -- `Glob`/`gtyp`, with
//!   the declared initialiser as the `gSp0` entry (`Syntax.lean` §1: "ein
//!   `static` ein `Glob`"). A read is `Expr.glob`, an `old(X)` is
//!   `Expr.altGlob`, a write is `Stmt.assignGlob` and the write right is
//!   `Signatur.gschreibt` off `effects { writes X }`. A `lock L protects
//!   { X }` puts `L` in `gbraucht X`, and a global is `ggeteilt` exactly
//!   where a lock guards it -- the same rule the tables travel under.
//!   **An ARRAY static has NO form** (`[u8; K]`): a `Glob` carries ONE
//!   `Wert`, not a row, and that is refused by name (LG002), as are a
//!   pointer, a record and a float static, and a `section` at a `static`
//!   (a PLACEMENT, LG001).
//! * `type Zelle = { wert : u32, fertig : bool };` -- **a record is a `Tab`
//!   with `count 1`**, closed 2026-09-15, and `Syntax.lean` §1/§9 says it in
//!   as many words ("ein `format` und ein Verbund sind Tabellen mit
//!   `count 1`"). The record name is the table name, each record field a slot
//!   field, and the one slot is index `0`: `p->f` is `Expr.durch` there,
//!   `p->f = e` is `Stmt.assignDurch`, and a bare `writes p` is the table's
//!   write right (a TABLE pointer still has to name `p.slots` -- a table has
//!   more than one slot).
//!   **A record as a VALUE is CLASS (ii) and stays refused by name.**
//!   `Typen.lean` §1 lists every `Ty` there is -- `int`, `bool`, `opt`,
//!   `sum`, `grund`, `never`, `fl`, `fnptr`, `ptr` -- and **there is no
//!   product**. So `-> Completion`, `let c = fertig(k, 7);` and
//!   `Completion(id: k, len: n)` name no type the specification can carry,
//!   and no exporter work makes them one: closing it is a `Ty` constructor,
//!   a change to the specification reviewed as a diff of `Spec.lean`.
//!   A record field that is no `Ty` (an array, a nested record, a float, a
//!   function pointer) is refused naming the FIELD and its record (LG002).
//! * `arena A capacity lo .. hi of T` -- **O14**, closed 2026-09-15: the
//!   PAIR `Grammatik/ArenaZucker.lean` names, synthesised here. A table `A`
//!   of `count = hi` with one field `wert : T`, a global `A_used : int 0 hi`
//!   starting at zero, and `def gArena_A : ArenaForm gD` beside them.
//!   `reset A;` is `Stmt.arenaReset`, `let i = alloc A (v) else { … };` is
//!   `Block.arenaAlloc`, and `A[i]` is the slot read of the one field.
//!   **The reservation `lo` does NOT travel** -- it is the checker's static
//!   count (`N212`), whose model-side consequence is already proved
//!   (`arenaAlloc_unter_schranke`).
//!   **An `alloc` WITHOUT `else` is refused by name** (LG004), and that is a
//!   decision: `Block.arenaAlloc` always carries a full-arena branch, the
//!   emitted C carries none, and what makes the branch dead is `N212`, which
//!   does not travel into the term. Inventing a `return` the user did not
//!   write would put a guard into the exported term that neither the source
//!   nor the C has. An `alloc` at the TOP LEVEL of a body is refused for the
//!   reason every `narrow`/`bindCall` is: a body is an `Endblock`, and those
//!   are `Block` formers.
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
//! * `impl fn` with pointer/index/range/`bool` parameters, `requires Held(L)`
//!   plus value clauses (lane 198: a `Held`-only clause names the
//!   signature-held set, every other clause travels as an `Expr` like the
//!   `ensures`, refusing by name what has no `Expr` form),
//!   `ensures` over comparisons of slot reads, `old`, `result` and literals,
//!   `effects { reads/writes/locks }`, an optional `or R` reason channel, and
//!   a body of slot writes, direct calls, `locks` blocks, `if`/`else`,
//!   `traverse ... over slots of T` (or of a pointer-typed name for `T`,
//!   lane 207), `let` bindings and a trailing `return`
//! * `-> T or R` -- the reason channel: `gruende` is the number of cases of
//!   the named `reason` declaration. A bare call of such a function has no
//!   form (its `hr` needs `gruende = 0`); only `let x = f() else (e) { … }`
//!   travels (`Block.bindCallElse`).
//! * `const NAME = N` (inlined at every use) and `type NAME = u32 in lo..hi`
//!   / `lo..<hi` (resolved at every use, the exclusive bound as `lo..hi-1`);
//!   an `opaque` alias travels as its range -- `opaque` is a rule about a
//!   UNIT BOUNDARY, like `pub`, and `Deklaration` has no boundary; the module
//!   wrapper is transparent
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
//! ## The linear family -- class (i) in the specification, built nowhere
//!
//! `linear type M;`, `linear ghost type M order { … };` and `type Duty(check)`
//! are **not** `Ty`s: a mark is a RESOURCE, held in `Λ` as `Res.marke m s`.
//! `D.Marke`, `D.stufen`, `Signatur.konsumiert`/`produziert`, `D.eigner`,
//! `braucht … .inr (m, s)`, `Stmt.advances` and `Stmt.retires` are all in the
//! specification, so the family is class (i) -- and none of it is built here:
//! the export writes `Marke := Empty` and `konsumiert := []`. Every shape is
//! refused BY NAME with the field it would travel in (`refuse_linear`).
//!
//! > **Measured 2026-09-15, and it is why the family is written down rather
//! > than built:** all TEN corpus programs whose FIRST refusal is a linear
//! > type stop at a SECOND wall from a different group -- a `walk`, a
//! > `backed` table, a device, a foreign body (`extern fn`), an
//! > `option index into Self` field, an `assume`. *Closing the whole family
//! > would move sieve (b) by ZERO.* A first-refusal count is not a count of
//! > programs a lane would gain, and the export census must be read that way.
//!
//! ## Refusal codes (`LG`)
//!
//! * `LG001` item with no G form (devices, axioms, `entrust`, ...; a
//!   `static` LEFT this list on 2026-09-15, see above); since lane 198 also a declared start with parameters
//!   (no `Env` argument form) -- `entry`/`boot` items themselves travel
//!   only as their dispatch root (see below)
//! * `LG002` type with no `Ty` form (floats, records, pointers outside
//!   `normal`, ...; a `tagged` type LEFT this list on 2026-09-15, see above,
//!   but its payload and case-count rules joined it)
//! * `LG003` contract or value expression with no `Expr` form -- since lane
//!   198 also a `requires` value clause with none, and an integer field
//!   whose range holds no zero (no `sp0` value)
//! * `LG004` body statement with no `Stmt`/`Endblock` form (this covers the
//!   `RufPasst` proof failures `hh`/`hx`/`hb`/`hw`, which are named in the
//!   message -- the checker accepts the call, the model cannot type it)
//! * `LG005` unresolvable name, count, rank or range (unknown table, lock,
//!   function, constant or type alias) -- since lane 198 also a start
//!   (`concurrent` member, `entry`/`boot` dispatch) naming nothing
//!   exported, or naming two functions at once
//! * `LG006` loop with no export form (`retry`, `forever`, a `traverse` that
//!   is not `traverse i over slots of T` -- or of a pointer-typed name for
//!   `T`, lane 207 -- with a translatable invariant)
//! * `LG007` reason-channel form with no export form (`let … else` over a
//!   place, a falling-off `else` branch, a valueless reason function in
//!   `let … else`)
//!
//! ## The program as one declaration (lane 198)
//!
//! Beside the program `gP` the export assembles what `GabbroZiel`
//! (`Zielsatz/Spec.lean`) quantifies over: the lock-invariant family `gS`
//! (lane 156), the member lists `gFs`/`gLs`/`gCs` (`gCs` carries the
//! globals as `.inr` since 2026-09-15), the declared initial
//! memory `gSp0` (every slot at zero, `false` for `bool`, the FIRST case with
//! payload zero for a `tagged` field -- no surface form names a slot
//! initialiser; every global at the initialiser its `static` DOES name)
//! and the declared starts `gE.starts` (the `concurrent` members, then the
//! `entry`/`boot` dispatch roots; every start is parameterless, its
//! argument list `.nil`), as `def gE : Einheit gD` (no axiom exists, so
//! `Q` is `fun _ _ _ => true`).
//!
//! ## NO FORM in G (accepted and dropped, each named in the header)
//!
//! The module wrapper; named constants (inlined); bare carrier widths;
//! pointer address spaces; lock hold budgets; the `reads` effects; `costs`;
//! the `by unvisited`/`by consuming` run form, the `decreases` witness and
//! the `touches` clause of a `traverse` (static annotations, like `costs`);
//! `by ops` on a field (a writer discipline the checker holds);
//! `mut` on a `let` (reassignments still refuse by name); **`pub`** and
//! **`opaque`** (both are rules about a UNIT BOUNDARY, and `Deklaration` has
//! no boundary -- `opaque` joined on 2026-09-15, when its alias started to
//! travel as its range); the
//! `entry`/`boot` hardware around a dispatch (the vector, the registers, the
//! steps -- only the dispatch root travels, as a declared start where
//! exportable).
//!
//! > **`concurrent` LEFT this list on 2026-09-15 (lane 198).** It used to read
//! > "which functions start threads is not a G notion"; since the unit carries
//! > `gE.starts`, its members travel as the declared starts, each with the
//! > argument list `.nil`. *A ledger entry that has become false is worse than
//! > a missing one.*
//! > **`pub` joined this list on 2026-09-15, and it had been dropped for longer
//! > than that.** Measured with a differential over `gabbro lean-g`: a unit with
//! > `pub const Q` and one with `const Q` export a BYTE-IDENTICAL term. The drop
//! > was right; naming it is what this ledger is for, and the omission is the
//! > same class as an `UNCOVERED` grammar form -- *it looked carried on both
//! > sides.* `section` at a function was the second such cell and is refused by
//! > name instead (`N320`, `namen.rs`); `section` at a `static` never reaches
//! > here, because a `static` is `LG001`.

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
    /// `tagged type T = { A, B(u32 in lo..hi), … }` -- `Ty.sum`, whose cases
    /// are `List (Option (Int × Int))`: a case carries NO payload or ONE
    /// integer range (`Nutzlast`, `Typen.lean`). **The case NAMES do not
    /// travel** -- a case is its POSITION in the list, and `Expr.fall` names
    /// it as a `Fin`. They are carried here so a refusal can spell them, and
    /// so two tagged types with the same shape stay two types.
    Sum { name: String, cases: Vec<(String, Option<(i128, i128)>)> },
}

/// The `List (Option (Int × Int))` a `Ty.sum` is indexed by, as Lean spells
/// it. Written once, here: the constructor (`Expr.fall`) repeats it, and two
/// spellings of one list would be two types.
fn sum_list(cases: &[(String, Option<(i128, i128)>)]) -> String {
    let cs: Vec<String> = cases
        .iter()
        .map(|(_, p)| match p {
            None => "none".to_string(),
            Some((lo, hi)) => format!("some ({}, {})", int_num(*lo), int_num(*hi)),
        })
        .collect();
    format!("[{}]", cs.join(", "))
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
            VTy::Sum { cases, .. } => format!("(.sum {})", sum_list(cases)),
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

/// The exportable fragment of a unit: tables, globals, locks, functions,
/// threads, and the reason declarations behind the `or R` channels.
pub(crate) struct Model {
    pub(crate) tables: Vec<TableModel>,
    /// `static mut X : <int range|bool> = <literal>;` -- the `Glob` half of
    /// the declaration. An ARRAY static has no single `Wert` and is refused
    /// by name (a `Glob` is one value, not a row).
    pub(crate) globs: Vec<GlobModel>,
    /// `arena A capacity lo .. hi of T` -- **O14**: the specification carries
    /// `alloc`/`reset` as SUGAR over a table of `count = hi` slots beside a
    /// `used` global (`Grammatik/ArenaZucker.lean`), and this is the pair the
    /// exporter synthesises. The reservation `lo` does NOT travel: it is the
    /// checker's static count (`N212`).
    pub(crate) arenas: Vec<ArenaModel>,
    pub(crate) locks: Vec<LockModel>,
    pub(crate) fns: Vec<FnModel>,
    #[allow(dead_code)]
    concurrent: Vec<String>,
    /// `entry`/`boot` dispatch roots (lane 198): the hardware around them
    /// (vectors, registers, steps) has no G form, but the dispatched
    /// function is a declared start like a `concurrent` member.
    wurzeln: Vec<Pfad>,
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
    /// **This table is a RECORD** (`type Zelle = { wert : u32 };`), lowered
    /// as the sentence of `Syntax.lean` §1/§9 quoted in the module header
    /// says. It differs from a declared `table` only in how it is SPELLED at
    /// a use: `p->f` instead of `T.slots[i].f`, and a bare `writes p`
    /// instead of `writes T.slots`.
    pub(crate) record: bool,
}

/// The declared initial value of a global: the `sp0` entry the loader
/// establishes (`Laufzeit.lader`). A slot starts at zero because no surface
/// form names a slot initialiser; a `static` names one, and it travels.
#[derive(Debug, Clone, Copy)]
pub(crate) enum GInit {
    Int(i128),
    Bool(bool),
    /// `static X : T = Kurz(5);` at a `tagged` type -- the case POSITION and
    /// its payload, which is what `Val (.sum cs)` is: `⟨i, nutzlast⟩`.
    Sum { case: usize, payload: Option<i128> },
}

pub(crate) struct GlobModel {
    pub(crate) name: String,
    pub(crate) ty: VTy,
    pub(crate) init: GInit,
}

/// The `ArenaForm` of one `arena` declaration: which synthesised table holds
/// the slots and which synthesised global holds the `used` counter.
pub(crate) struct ArenaModel {
    pub(crate) name: String,
    pub(crate) table: usize,
    pub(crate) glob: usize,
}

pub(crate) struct LockModel {
    pub(crate) name: String,
    pub(crate) rank: i128,
    pub(crate) guards: Vec<usize>,
    /// The GLOBALS this lock `protects` (`gbraucht`), beside the tables.
    pub(crate) gguards: Vec<usize>,
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
    /// `tagged type T = { … }` -- the cases of a `Ty.sum`, in DECLARATION
    /// order (the order is the type: `Expr.fall` names a case by its `Fin`,
    /// and `Arms` lists one block per case in this order).
    tagged: std::collections::HashMap<String, Vec<(String, Option<(i128, i128)>)>>,
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

/// An integer range where G needs a `Ty`: `u32 in lo..hi`, `u32 in lo..<hi`,
/// or an alias for one. A bare word (`u32`) travels as its full range -- the
/// same numbers the checker computes with (`breite_von`/`grenzen`), spelled
/// by the word; an exclusive bound travels as `lo .. hi-1`, likewise the
/// same numbers.
fn int_ty(t: &TypExpr, scope: &Scope) -> Option<VTy> {
    match t {
        TypExpr::Int(i) => {
            if let Some(b) = &i.bereich {
                let lo = numeral(&b.von, scope)?;
                let hi = numeral(&b.bis, scope)?;
                // `lo ..< hi` is `lo .. hi-1` -- the SAME numbers the checker
                // computes with (`grenzen`), spelled with the half-open form.
                // An empty exclusive range (`n ..< n`) names no value and has
                // no `Ty`; it is left to the caller's refusal.
                let hi = if b.exklusiv { hi.checked_sub(1)? } else { hi };
                if hi < lo {
                    return None;
                }
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

/// A `Ty` where G needs one: an integer range or `bool` (`int_ty`), or a
/// declared `tagged type` as its `Ty.sum`. Every other spelling -- a record,
/// a float, an array, a function pointer -- has no `Ty` and is refused BY
/// NAME at the site that asked.
fn g_ty(t: &TypExpr, scope: &Scope) -> Option<VTy> {
    if let Some(v) = int_ty(t, scope) {
        return Some(v);
    }
    let TypExpr::Pfad(p) = t else {
        return None;
    };
    let name = p.einfach()?;
    let cases = scope.tagged.get(&name.text)?;
    Some(VTy::Sum { name: name.text.clone(), cases: cases.clone() })
}

/// **`tagged type T = { A, B(u32 in lo..hi), … }` is `Ty.sum`** (`Typen.lean`
/// §1, `SYNTAX.md:441`): the cases in declaration order, each carrying no
/// payload or ONE integer range.
///
/// What has no `Ty.sum` is refused BY NAME here, because `Nutzlast` is
/// exactly `Option (Int × Int)`: a `bool`, a pointer, a record, a float or a
/// nested tagged payload has no form, and a tagged type with NO case has no
/// value at all (`Val (.sum []) = Σ i : Fin 0, …` is empty, so no slot,
/// global or parameter of it can exist -- the same argument `W1` makes about
/// answers at empty types).
fn read_tagged(t: &TypDecl, scope: &Scope) -> Result<Vec<(String, Option<(i128, i128)>)>, Refusal> {
    if t.linear || t.ghost || t.ordnung.is_some() || t.parameter.is_some() {
        return Err(refuse(
            "LG001",
            format!(
                "tagged type {} is also `linear`/`ghost`/`order`: a `Ty.sum` is a VALUE and a \
                 `D.Marke` is a RESOURCE (`Res.marke m stufe`, held in `Λ`), and no `Deklaration` \
                 field carries both at once",
                t.name.text
            ),
        ));
    }
    let Some(TypExpr::Varianten(vs, _)) = t.rumpf.as_ref() else {
        return Err(refuse(
            "LG001",
            format!(
                "tagged type {} names no variant list, so it names no `Ty.sum` cases",
                t.name.text
            ),
        ));
    };
    // **A SECOND reader of `P035`.** The reader already refuses `{ }` ("neither
    // a record nor a sum type"), so no surface spelling reaches here; what this
    // guard buys is that `cases[0]` -- the `sp0` value of a `tagged` slot -- is
    // total, and that a future reader relaxation cannot make it partial in
    // silence. *Measured 2026-09-15: the poison probe for this arm exported
    // cleanly, because the item never survived the parse.*
    if vs.is_empty() {
        return Err(refuse(
            "LG002",
            format!(
                "tagged type {} has no case: `Val (.sum [])` is `Σ i : Fin 0, …` and holds no \
                 value at all, so no slot, global or parameter of it can exist",
                t.name.text
            ),
        ));
    }
    let mut cases = Vec::new();
    for v in vs {
        let payload = match &v.nutzlast {
            None => None,
            Some(ty) => match int_ty(ty, scope) {
                Some(VTy::Int { lo, hi, .. }) => Some((lo, hi)),
                _ => {
                    return Err(refuse(
                        "LG002",
                        format!(
                            "case {} of tagged type {} carries a payload with no `Ty.sum` form: a \
                             case payload is `Option (Int × Int)` (`Nutzlast`, Typen.lean), so ONE \
                             integer range and nothing else -- a `bool`, a pointer, a record, a \
                             float or a nested tagged payload has none",
                            v.name.text, t.name.text
                        ),
                    ));
                }
            },
        };
        if cases.iter().any(|(n, _): &(String, _)| n == &v.name.text) {
            return Err(refuse(
                "LG002",
                format!(
                    "tagged type {} names the case {} twice, and a `Ty.sum` case is its POSITION -- \
                     the exporter cannot tell which of the two a constructor or a `match` arm means",
                    t.name.text, v.name.text
                ),
            ));
        }
        cases.push((v.name.text.clone(), payload));
    }
    Ok(cases)
}

/// **The linear family, refused BY NAME** -- the last catch-all arm of the
/// type walk, and the twin of the item catch-all closed on 2026-09-15.
///
/// `linear`/`ghost type M;` is class (i) IN THE SPECIFICATION: `D.Marke`,
/// `stufen`, `Res.marke m stufe`, `Signatur.konsumiert`/`produziert`,
/// `D.eigner`/`braucht`, `Stmt.advances` and `Stmt.retires` are all there.
/// What it is NOT is a `Ty` -- a mark is a RESOURCE held in `Λ`, never a
/// value -- so the surface `fn f(m : Marke)` has no parameter to travel as,
/// only a `konsumiert` entry. **Measured 2026-09-15:** all ten corpus
/// programs whose first refusal is this one stop at a SECOND wall from
/// another group (a `walk`, a `backed` table, a device, a foreign body, an
/// `option` field, an `assume`), so the family is written down here and
/// built nowhere yet.
fn refuse_linear(t: &TypDecl) -> Refusal {
    let was = if t.parameter.is_some() {
        "a witness type with a parameter list (`type Duty(check)`) is a `D.Marke` whose \
         producer is the `check` and whose consumer is the `gates`"
    } else if t.ordnung.is_some() {
        "an `order { … }` names the STUFEN of a mark: `D.stufen m` is the number of them, a \
         mark stands at `Res.marke m s`, and `Stmt.advances` moves it from `s` to `s + 1`"
    } else if t.ghost && t.linear {
        "a `linear ghost` mark is `D.Marke` with `stufen m = 1`: it is held in `Λ` as \
         `Res.marke m 0`, consumed through `Signatur.konsumiert` and retired by \
         `Stmt.retires`; `ghost` itself is the carrier flag `D.geist`"
    } else {
        "a `linear` mark is `D.Marke`, held in `Λ` as `Res.marke m s` and moved by \
         `Signatur.konsumiert`/`produziert`, `Stmt.advances` and `Stmt.retires`"
    };
    refuse(
        "LG001",
        format!(
            "type {} has no `Ty` form, because a mark is a RESOURCE and not a value: {was}. This \
             exporter writes `Marke := Empty`, builds no `konsumiert`/`produziert` and exports \
             neither `advances` nor `retires`, so a mark that travelled would travel as nothing",
            t.name.text
        ),
    )
}

/// A type alias that is no `Ty`, refused BY NAME with the reason -- the arm
/// that used to say only "is not an integer range" over five different
/// shapes. A `Ty` is `int`, `bool`, `opt`, `sum`, `grund`, `never`, `fl`,
/// `fnptr` or `ptr` (`Typen.lean` §1), and nothing else is one.
fn refuse_kein_ty(t: &TypDecl, r: &TypExpr) -> Refusal {
    let grund: &str = match r {
        TypExpr::Float(_) => "a float alias is `Ty.fl lo hi` with its bounds as FRACTIONS, and \
            this exporter builds no `Ty.fl` and none of the `Block.gleit*` statements",
        TypExpr::Feld(_) => "an array alias has no `Ty` at all: a row of values is a `Tab` with \
            that many slots (`Syntax.lean` §9), not one `Wert`",
        TypExpr::FnZeiger(_) => "a function-pointer alias is `Ty.fnptr n`, where `n` is the \
            SIGNATURE NUMBER `D.sig`/`D.sigNr` gives it; this exporter numbers only the \
            functions it exports, and a declared signature with no body has no number",
        TypExpr::Zeiger(_) => "a pointer alias is `Ty.ptr t rw`, and `t` is the NUMBER of a \
            declared table (`D.tabNr`); an alias for a pointer to something that is no table \
            has none",
        TypExpr::Never(_) => "`never` is `Ty.never`, the type with no value: it is the answer \
            of a `divergent`/`prim` function, and this exporter exports no such function",
        TypExpr::Varianten(..) => "a variant list without the `tagged` word names no type this \
            exporter reads; write `tagged type`",
        TypExpr::Index { .. } => "an `index into T` alias is the GENERATED index type of `T` \
            (`Ty.index (D.count t)`), and it resolves only where `T` is an exported table",
        _ => "a `Ty` is an integer range, `bool`, `option`, a `tagged` sum, a reason, `never`, \
            a float, a function pointer or a pointer (`Typen.lean` §1), and this is none",
    };
    refuse("LG002", format!("type {} is not an integer range: {grund}", t.name.text))
}

/// Constants, integer aliases and `tagged` types, so `count`, field types
/// and constructors resolve. ONE walk, used by `collect` and by `rescope`:
/// two readers of the same declarations would be two scopes.
fn build_scope(scope: &mut Scope, items: &[Item]) -> Result<(), Refusal> {
    for item in items {
        match &item.art {
            ItemArt::Modul(m) => build_scope(scope, &m.items)?,
            ItemArt::Konst(k) => {
                let Some(v) = numeral(&k.wert, scope) else {
                    return Err(refuse("LG005", format!("const {} is not a numeral", k.name.text)));
                };
                scope.consts.insert(k.name.text.clone(), v);
            }
            ItemArt::Typ(t) => {
                // **A `tagged type` travels as `Ty.sum`** (2026-09-15): its
                // cases are the `List (Option (Int × Int))` index, and what
                // has no such case list is refused by name in `read_tagged`.
                if t.tagged {
                    let cases = read_tagged(t, scope)?;
                    scope.tagged.insert(t.name.text.clone(), cases);
                    continue;
                }
                // **`opaque` is a rule about a UNIT BOUNDARY**, exactly
                // like `pub`: outside the module the definition is not
                // visible, so no arithmetic reaches the range. Inside the
                // unit -- and `Deklaration` has no boundary at all -- the
                // alias IS its range, and that range travels. The drop is
                // named in the printed NO-FORM ledger, which is what this
                // ledger exists for.
                // **The linear family** -- `linear`, `ghost`, `order`, and the
                // witness parameter list of a `Duty` -- is NOT a `Ty` at all:
                // a mark is `D.Marke` with `stufen`, held in `Λ` as
                // `Res.marke m stufe`. Refused by name, with the fields it
                // would travel in; see `refuse_linear`.
                if t.linear || t.ghost || t.ordnung.is_some() || t.parameter.is_some() {
                    return Err(refuse_linear(t));
                }
                let Some(r) = t.rumpf.as_ref() else {
                    return Err(refuse(
                        "LG001",
                        format!(
                            "type {} has no body, so it names neither a `Ty` nor a carrier",
                            t.name.text
                        ),
                    ));
                };
                // **A RECORD is a carrier, not a value** -- a `Tab` with
                // `count 1`, per the sentence of `Syntax.lean` §1/§9 quoted
                // in the module header.
                // It is built in the walk below, where the model is; here it
                // only has to stop being read as an integer alias.
                if matches!(r, TypExpr::Verbund(..)) {
                    continue;
                }
                let Some(VTy::Int { lo, hi, bits }) = int_ty(r, scope) else {
                    return Err(refuse_kein_ty(t, r));
                };
                scope.aliases.insert(t.name.text.clone(), (lo, hi, bits));
            }
            _ => {}
        }
    }
    Ok(())
}

/// Every item of the unit, through modules. Anything without a G form is
/// refused here, so nothing below ever sees it.
fn collect(source_name: &str, tree: &Programm) -> Result<Model, Refusal> {
    let mut model = Model { tables: vec![], globs: vec![], arenas: vec![], locks: vec![], fns: vec![], concurrent: vec![], wurzeln: vec![], reasons: std::collections::HashMap::new() };
    let mut scope = Scope::default();
    // Pass one: constants, type aliases and `tagged` types.
    build_scope(&mut scope, &tree.items)?;
    // Pass two: carriers, locks, functions, concurrency.
    //
    // **The locks are read AFTER the walk, not during it.** A lock's
    // `protects` names a carrier, and a carrier declared BELOW the lock is
    // not in the model yet while the walk is at the lock -- with tables that
    // was a latent ordering hazard, with globals it fires (`110`, `125` both
    // happen to declare the `static` first, others need not). The lock
    // declarations are collected here and resolved once every carrier is in.
    fn walk<'a>(model: &mut Model, scope: &Scope, items: &'a [Item], sperren: &mut Vec<&'a LockDecl>) -> Result<(), Refusal> {
        for item in items {
            if item.when.is_some() {
                return Err(refuse("LG001", "`when` on an item has no G form".to_string()));
            }
            match &item.art {
                ItemArt::Modul(m) => walk(model, scope, &m.items, sperren)?,
                // **A record is a `Tab` with `count 1`** (`Syntax.lean`
                // §1/§9). Built HERE and not in `build_scope`, because a
                // table lives in the model and a scope holds only values;
                // every other alias travels through the scope and is done.
                ItemArt::Typ(t) => {
                    if let Some(TypExpr::Verbund(felder, _)) = t.rumpf.as_ref() {
                        if !t.tagged {
                            model.tables.push(read_record(t, felder, scope)?);
                        }
                    }
                }
                ItemArt::Konst(_) => {}
                ItemArt::Tabelle(t) => model.tables.push(read_table(t, scope)?),
                // A `static` is a `Glob` (`Syntax.lean` §1: "ein `static` ein
                // `Glob`"). What has no single `Wert` -- an array, a pointer,
                // a record, a float -- is refused BY NAME in `read_static`.
                ItemArt::Statisch(s) => model.globs.push(read_static(s, scope)?),
                ItemArt::Lock(l) => sperren.push(l),
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
                // **The arena travels as its PAIR** (O14, closed here
                // 2026-09-15): `Grammatik/ArenaZucker.lean` carries `alloc`
                // and `reset` as sugar over a table of `count = hi` slots
                // beside a global `used` counter, and `read_arena` builds
                // exactly that pair. The reservation `lo` does not travel --
                // it is the checker's static count (`N212`).
                ItemArt::Arena(a) => {
                    let (t, g) = read_arena(a, scope, model)?;
                    model.tables.push(t);
                    model.globs.push(g);
                    model.arenas.push(ArenaModel {
                        name: a.name.text.clone(),
                        table: model.tables.len() - 1,
                        glob: model.globs.len() - 1,
                    });
                }
                // An `entry`/`boot` item is hardware around one dispatch
                // (lane 198): the vector, the registers, the steps have no
                // G form and travel nowhere, but the dispatched function is
                // a declared start. What names no exported function is
                // refused where the starts resolve, by name.
                ItemArt::Entry(e) => model.wurzeln.push(e.dispatch.clone()),
                ItemArt::Boot(b) => model.wurzeln.push(b.dispatch.clone()),
                // **Every remaining item kind has its OWN arm**, and each
                // says what the specification would carry it as and what is
                // missing. *A catch-all that happens to fire is not a refusal
                // anybody can act on -- and the day an arm is added above,
                // it stops firing without a word* (the defect `N320` and O14
                // were written for). The name of the item is in the message
                // wherever the kind has one, so a reader can find the line.
                other => {
                    let wo = other.name().map(|n| format!(" {}", n.text)).unwrap_or_default();
                    let grund: &str = match other {
                        ItemArt::Device(_) => "a device is `D.Reg` with `rtyp`/`rklasse`/`spiegel`/`rzusage`, \
                            and its accesses are `Block.regLies`/`Stmt.regSchreib`; this exporter builds no `Reg`",
                        ItemArt::Assume(_) => "a named assumption is `D.Annahme`, which the specification \
                            consumes only at `Stmt.forever` and `Stmt.retires`; this exporter builds no `Annahme` \
                            and exports neither statement",
                        ItemArt::Format(_) => "a `format` is a `Tab` with `count 1` whose `where` clauses are \
                            `Block.pruefung` (Syntax.lean §9); this exporter builds no such table",
                        ItemArt::Atomic(_) => "an `atomic` is a `Glob` with `atomar = true` and a `nutzlast`, \
                            and its accesses are `Stmt.publish`/`Block.awaits`/`Block.exchange`; this exporter \
                            writes `atomar := fun _ => false` and exports none of the three",
                        ItemArt::Gruppe(_) => "a `group` is a `D.Inv` over more than one carrier (Syntax.lean §11); \
                            this exporter writes `Inv := Empty`",
                        ItemArt::Accumulates(_) => "an `accumulates` is a `Glob` plus a generated assignment \
                            (Syntax.lean §11); this exporter generates none",
                        ItemArt::State(_) => "a `state` declaration fills `D.erlaubt`, and its assignments are \
                            `Stmt.uebergang`; this exporter writes `erlaubt := fun _ _ _ _ => false`",
                        ItemArt::Axiom(_) | ItemArt::Entrust(_) | ItemArt::Syscall(_) =>
                            "a foreign body is `D.Ax` with `aparams`/`aerg`/`aschreibt`, called through \
                            `Stmt.axiomCall`/`Block.bindAxiom`; this exporter writes `Ax := Empty`",
                        ItemArt::Check(_) => "a `check` produces a `Duty` mark consumed by `gates` (Syntax.lean §13); \
                            this exporter writes `Marke := Empty`",
                        ItemArt::Rcu(_) => "an RCU domain is a `D.Lock` whose `observes` is `Stmt.locks`; \
                            this exporter reads only `lock` declarations",
                        ItemArt::Walk(_) => "a `walk` is one `Stmt.traverse` per level with `levels` constant \
                            (Syntax.lean §9); this exporter generates none",
                        ItemArt::Profil(_) | ItemArt::ProfilBedarf(_) =>
                            "a hardware profile is a set of NAMED ASSUMPTIONS about the machine, and `Deklaration` \
                            carries assumptions only as `D.Annahme` at the two statements that consume them",
                        ItemArt::Use(_) => "a `use` names another UNIT, and `Deklaration` has no unit boundary \
                            -- what it imports is not in this term at all",
                        _ => "no `Deklaration` field carries it",
                    };
                    return Err(refuse(
                        "LG001",
                        format!("{}{wo} has no G form: {grund}", other.benennung()),
                    ));
                }
            }
        }
        Ok(())
    }
    let mut sperren: Vec<&LockDecl> = Vec::new();
    walk(&mut model, &scope, &tree.items, &mut sperren)?;
    for l in sperren {
        let lm = read_lock(l, &model)?;
        model.locks.push(lm);
    }
    // A unit without tables travels with `Tab := Empty` (pure computation
    // over parameters); a unit without functions has no program at all.
    if model.fns.is_empty() {
        if model.tables.is_empty() && model.globs.is_empty() {
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
    /// `effects { writes G }` at a GLOBAL -- the `Signatur.gschreibt` half.
    gwrites: Vec<usize>,
    pub(crate) ensures: Vec<Pred>,
    /// `requires` past the signature-held locks: every non-`Held` clause
    /// travels as an `Expr` (lane 198), conjoined under `.und` (`.wahr`
    /// where there is none). A `Held`-only clause names the signature set
    /// above, never this list.
    pub(crate) requires: Vec<Pred>,
    pub(crate) body: Block,
    /// `-> T or R`: the case count of the named `reason`, 0 without one.
    pub(crate) gruende: usize,
    /// The lock floor (`Signatur.boden`, `StufenOk`) -- the value the
    /// signature carries, computed over the CALL GRAPH by `resolve_floors`.
    boden: Option<i128>,
    /// The minimum rank this body takes DIRECTLY, or `none` where it takes
    /// no lock at all. `boden` is derived from this and from the callees'.
    direct_floor: Option<i128>,
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
    /// A `tagged` value passed BY VALUE (`Ty.sum`) -- the shape
    /// `beispiele/34` names as "as a PARAMETER": the marked value is handed
    /// over, not reached through a pointer.
    Sum { name: String, cases: Vec<(String, Option<(i128, i128)>)> },
}

impl ParamTy {
    pub(crate) fn vty(&self, _model: &Model) -> VTy {
        match self {
            ParamTy::Ptr { table, write } => VTy::Ptr { table: *table, write: *write },
            ParamTy::Index { table } => VTy::Index { table: *table },
            ParamTy::Int { lo, hi, bits } => VTy::Int { lo: *lo, hi: *hi, bits: *bits },
            ParamTy::Bool => VTy::Bool,
            ParamTy::Sum { name, cases } => VTy::Sum { name: name.clone(), cases: cases.clone() },
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
            // **Lane O-1:** calls on the child path scan like any block.
            StmtArt::Child(x) => scan_block(x, acc),
            StmtArt::Alloc(al) => {
                scan_expr(&al.wert, acc);
                if let Some(b) = &al.sonst {
                    scan_block(b, acc);
                }
            }
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
        Some(t) => Some(match g_ty(t, scope) {
            Some(ty) => ty,
            None => {
                if let Some(rec) = record_named(t, model) {
                    return Err(refuse_record_value(&format!("the result of {}", f.name), &rec));
                }
                return Err(refuse("LG002", format!(
                    "result of {} has no integer-range, bool or tagged form", f.name)));
            }
        }),
    };
    // `requires` in two channels (lane 198): a `Held`-only clause names
    // the signature-held set; every other clause travels as an `Expr`
    // (translated like the `ensures`, refusing by name what has no `Expr`
    // form). A `Held` nested inside a value shape has neither channel and
    // is refused where the value translation meets it (LG003).
    let mut held = Vec::new();
    let mut requires = Vec::new();
    for r in &d.requires {
        if let Some(h) = held_aus_klausel(r, model, &f.name)? {
            for li in h {
                if !held.contains(&li) {
                    held.push(li);
                }
            }
        } else {
            requires.push(r.clone());
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
    let mut gwrites: Vec<usize> = Vec::new();
    for w in &effects.liste {
        if let WirkungArt::Schreibt(o) = &w.art {
            // `writes G` at a bare global name is the `gschreibt` half; a
            // suffixed place (`T.slots`) is the table half, as before.
            if o.suffixe.is_empty() {
                // `writes A` at an ARENA is a write to BOTH halves of its
                // pair: the slots and the `used` counter.
                if let Some(a) = model.arenas.iter().find(|a| a.name == o.basis.text) {
                    writes.push(a.table);
                    if !gwrites.contains(&a.glob) {
                        gwrites.push(a.glob);
                    }
                    continue;
                }
                if let Some(gi) = model.globs.iter().position(|g| g.name == o.basis.text) {
                    if !gwrites.contains(&gi) {
                        gwrites.push(gi);
                    }
                    continue;
                }
            }
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
    // The minimum rank the body takes DIRECTLY. The signature's floor is
    // computed from this over the whole call graph (`resolve_floors`).
    let direct_floor = taken.iter().map(|li| model.locks[*li].rank).min();
    Ok(CheckedFn { name: f.name.clone(), params, result, held, writes, gwrites, ensures: d.ensures.clone(), requires, body: body.clone(), gruende, boden: direct_floor, direct_floor, calls: scan.calls })
}

/// A `requires` clause as signature-held locks: `Some` where the whole
/// clause is `Held` (under `Und`/`Klammer`), `None` where any value shape
/// stands beside it (then the whole clause travels as an `Expr`). Shared
/// holding and unknown locks refuse exactly as before.
fn held_aus_klausel(p: &Pred, model: &Model, fname: &str) -> Result<Option<Vec<usize>>, Refusal> {
    match &p.art {
        PredArt::Held { sperre, geteilt, .. } => {
            if *geteilt {
                return Err(refuse("LG001", format!("shared `Held` in {fname} has no G form")));
            }
            let Some(li) = model.locks.iter().position(|l| l.name == sperre.text) else {
                return Err(refuse("LG005", format!("{fname} requires unknown lock {}", sperre.text)));
            };
            Ok(Some(vec![li]))
        }
        PredArt::Und(a, b) => {
            let (Some(mut x), Some(y)) = (held_aus_klausel(a, model, fname)?, held_aus_klausel(b, model, fname)?) else {
                return Ok(None);
            };
            for li in y {
                if !x.contains(&li) {
                    x.push(li);
                }
            }
            Ok(Some(x))
        }
        PredArt::Klammer(q) => held_aus_klausel(q, model, fname),
        _ => Ok(None),
    }
}

/// The table a `writes` place names: `writes k.slots` through a pointer
/// parameter, or `writes T.slots` at a table.
fn write_table(o: &Ort, params: &[(String, ParamTy)], model: &Model, fname: &str) -> Result<usize, Refusal> {
    // **`writes p` at a pointer to a RECORD** names the whole record, and
    // the record IS one slot: the write right is the table's. A table
    // pointer still has to name `p.slots` -- a table has more than one slot,
    // and naming the pointer would say less than the surface does.
    if o.suffixe.is_empty() {
        if let Some((_, ParamTy::Ptr { table, .. })) = params.iter().find(|(n, _)| n == &o.basis.text) {
            if model.tables[*table].record {
                return Ok(*table);
            }
        }
    }
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
        t => match g_ty(t, scope) {
            Some(VTy::Int { lo, hi, bits }) => Ok(ParamTy::Int { lo, hi, bits }),
            Some(VTy::Bool) => Ok(ParamTy::Bool),
            Some(VTy::Sum { name, cases }) => Ok(ParamTy::Sum { name, cases }),
            _ => match record_named(t, model) {
                Some(rec) => Err(refuse_record_value(&format!("a parameter of {fname}"), &rec)),
                None => Err(refuse("LG002", format!("parameter type in {fname} has no G form"))),
            },
        },
    }
}

/// A `let` annotation as a G type: an integer range, `bool`, a `tagged`
/// type, or an index.
fn annot_ty(t: &TypExpr, model: &Model, scope: &Scope, fname: &str) -> Result<VTy, Refusal> {
    if let Some(ty) = g_ty(t, scope) {
        return Ok(ty);
    }
    if let TypExpr::Index { tabelle, optional, .. } = t {
        if !optional {
            if let Some(ti) = model.tables.iter().position(|t| t.name == tabelle.text) {
                return Ok(VTy::Index { table: ti });
            }
        }
    }
    if let Some(rec) = record_named(t, model) {
        return Err(refuse_record_value(&format!("a `let` annotation in {fname}"), &rec));
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
                let Some(ty) = g_ty(ty, scope) else {
                    return Err(refuse("LG002", format!("field {} has no integer-range, bool or tagged form", f.name.text)));
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
    Ok(TableModel { name: t.name.text.clone(), count, fields, record: false })
}

/// **A RECORD is a `Tab` with `count 1`** -- `Syntax.lean` §1/§9 in as many
/// words; the sentence is quoted once, in the module header.
///
/// The record NAME becomes the table name, each record field a slot field,
/// and the one slot is index `0`. That is the whole lowering: a read `p->f`
/// is `Expr.durch p T rfl f (.lit 0)`, a write is `Stmt.assignDurch`, and
/// the guards are the table's guards. A record declared without a pointer to
/// it costs nothing: it is an unreferenced carrier.
///
/// **What has no form, refused BY NAME:** an array field, a nested record
/// field, a float field and a pointer field -- the same list `read_table`
/// refuses, for the same reason (`D.typ t f` is ONE `Ty`, and `Typen.lean`
/// has no product and no row). A record with NO field has no `Feld` type
/// and no slot to read.
///
/// **A record as a VALUE stays refused, and that is CLASS (ii)**: `Ty` has
/// no product former at all, so `-> Completion`, `let c = fertig(k, 7);` and
/// `Completion(id: k, len: n)` name no type the specification can carry.
/// The lowering above is a CARRIER lowering; it does not make a record a
/// value, and pretending otherwise would put a table read where the source
/// has a local.
fn read_record(t: &TypDecl, felder: &[FeldDecl], scope: &Scope) -> Result<TableModel, Refusal> {
    if felder.is_empty() {
        return Err(refuse(
            "LG002",
            format!(
                "record {} has no field: a `Tab` needs a `Feld` type with at least one \
                 constructor, and a slot of no fields can be neither read nor written",
                t.name.text
            ),
        ));
    }
    let mut fields = Vec::new();
    for f in felder {
        if f.bitpos.is_some() || f.offset_into.is_some() || f.bedingung.is_some() || f.reserviert {
            return Err(refuse(
                "LG002",
                format!(
                    "field {} of record {} carries a `format` clause (`@bitpos`, \
                     `offset_into`, `where`, `reserved`); a `where` is `Block.pruefung` and \
                     the byte views are `Expr.leseBytes`, and this exporter builds neither",
                    f.name.text, t.name.text
                ),
            ));
        }
        let Some(ty) = g_ty(&f.typ.typ, scope) else {
            return Err(refuse(
                "LG002",
                format!(
                    "field {} of record {} has no `Ty`: a slot field is ONE `Ty` (`D.typ t f`), \
                     so an integer range, `bool` or a `tagged` sum travels and an array, a \
                     nested record, a float or a pointer field does not",
                    f.name.text, t.name.text
                ),
            ));
        };
        fields.push(FieldModel { name: f.name.text.clone(), ty });
    }
    Ok(TableModel { name: t.name.text.clone(), count: 1, fields, record: true })
}

/// The record a type spelling names, where it names one.
fn record_named(t: &TypExpr, model: &Model) -> Option<String> {
    let TypExpr::Pfad(p) = t else {
        return None;
    };
    let name = p.einfach()?;
    model.tables.iter().find(|tb| tb.record && tb.name == name.text).map(|tb| tb.name.clone())
}

/// **A record in a VALUE position is CLASS (ii)** -- and this refusal is the
/// place that says so, because "has no integer-range or bool form" does not.
///
/// `Typen.lean` §1 lists every `Ty` there is: `int`, `bool`, `opt`, `sum`,
/// `grund`, `never`, `fl`, `fnptr`, `ptr`. **There is no product.** A record
/// travels as a CARRIER (`Syntax.lean` §1/§9: a `Tab` with `count 1`,
/// reached through a pointer), and that is built; it does not travel as a
/// value, and no amount of exporter work makes it one. Closing this needs a
/// `Ty` constructor, which is a change to the specification and a review of
/// `Spec.lean` -- not a lane of the exporter.
fn refuse_record_value(wo: &str, rec: &str) -> Refusal {
    refuse(
        "LG002",
        format!(
            "{wo} is the record {rec}, and a record has NO `Ty`: `Typen.lean` §1 is `int`, \
             `bool`, `opt`, `sum`, `grund`, `never`, `fl`, `fnptr`, `ptr` -- there is no \
             product. A record travels as a CARRIER (a `Tab` with `count 1`, reached through a \
             pointer, `Syntax.lean` §1/§9), and that is built; it does NOT travel as a value, so \
             a result, a parameter or a `let` of record type has no form at all. Passing a \
             `ptr<normal, r> {rec}` has one"
        ),
    )
}

/// The field name the synthesised arena table carries, and the suffix of its
/// `used` counter. Both are spelled once, here, so no site invents them.
const ARENA_FELD: &str = "wert";
const ARENA_ZAEHL: &str = "_used";

/// **`arena A capacity lo .. hi of T` as the pair `ArenaZucker.lean` names**
/// (`dokumente/OFFEN.md` O14): a table `A` of `count = hi` with one field
/// `wert : T`, and a global `A_used : int 0 hi` starting at zero -- literally
/// what the emitter writes (`A_arena_speicher.buf[hi]` beside a `used`
/// counter).
///
/// `ArenaForm` demands `gtyp zaehl = .int 0 (count tab)` (the counter must be
/// able to name a FULL arena) and `0 < count tab`. Both are decided here, in
/// Rust, and refused by name -- a `by decide` that fails is a Lean error and
/// not a refusal.
///
/// **The reservation `lo` does NOT travel.** It is the checker's static count
/// (`N212`), and its model-side consequence is already proved
/// (`arenaAlloc_unter_schranke`: below the hard bound the `else` cannot run).
fn read_arena(a: &ArenaDecl, scope: &Scope, model: &Model) -> Result<(TableModel, GlobModel), Refusal> {
    let Some(hi) = numeral(&a.hi, scope) else {
        return Err(refuse("LG005", format!("arena {} has no numeric hard bound", a.name.text)));
    };
    if hi <= 0 {
        return Err(refuse(
            "LG001",
            format!(
                "arena {} has hard bound {hi}: `ArenaForm.hpos` needs at least one slot, and an \
                 arena of none has no `alloc` that can succeed",
                a.name.text
            ),
        ));
    }
    let Some(elem) = int_ty(&a.element, scope) else {
        return Err(refuse(
            "LG002",
            format!(
                "arena {} holds elements with no `Ty` form: only an integer range or `bool` travels",
                a.name.text
            ),
        ));
    };
    let zaehl = format!("{}{ARENA_ZAEHL}", a.name.text);
    // The two synthesised names must not collide with a declared carrier.
    if model.tables.iter().any(|t| t.name == a.name.text) {
        return Err(refuse("LG005", format!("arena {} shares its name with a table", a.name.text)));
    }
    if model.globs.iter().any(|g| g.name == zaehl) {
        return Err(refuse(
            "LG005",
            format!("arena {} needs the counter name `{zaehl}`, which a `static` already holds", a.name.text),
        ));
    }
    Ok((
        TableModel {
            name: a.name.text.clone(),
            count: hi,
            fields: vec![FieldModel { name: ARENA_FELD.to_string(), ty: elem }],
            record: false,
        },
        GlobModel {
            name: zaehl,
            ty: VTy::Int { lo: 0, hi, bits: None },
            init: GInit::Int(0),
        },
    ))
}

/// One `static` as a `Glob`: its type and its declared initial value.
///
/// `Syntax.lean` §1 reads *"ein `static` ein `Glob`"*, and a `Glob` carries
/// ONE `Wert (D.gtyp g)` -- so an array static (`[u8; K]`), a pointer static
/// and a record static have no form here and are refused by name, each
/// naming what it is. The initialiser travels: it is the `sp0` entry the
/// loader establishes, and unlike a slot (which has no surface initialiser
/// and starts at zero) a `static` says what it starts at.
fn read_static(s: &StatischDecl, scope: &Scope) -> Result<GlobModel, Refusal> {
    // `section "…"` is a PLACEMENT, and a `Glob` has no placement. `N320`
    // refuses a `section` at a function for the same reason; at a `static`
    // it used to be invisible behind the blanket `LG001`.
    if s.section.is_some() {
        return Err(refuse(
            "LG001",
            format!("static {} carries a `section`, which is a PLACEMENT and has no `Glob` form", s.name.text),
        ));
    }
    let Some(ty) = g_ty(&s.typ, scope) else {
        return Err(refuse(
            "LG002",
            format!(
                "static {} has no `Glob` form: a `Glob` carries ONE value, so only an integer \
                 range, `bool` or a `tagged` type travels -- an array, a pointer, a record or a \
                 float static has none",
                s.name.text
            ),
        ));
    };
    let init = match (&ty, &s.wert.art) {
        (VTy::Bool, ExprArt::Wahr) => GInit::Bool(true),
        (VTy::Bool, ExprArt::Falsch) => GInit::Bool(false),
        (VTy::Bool, _) => {
            return Err(refuse(
                "LG003",
                format!("initialiser of static {} is not `true`/`false` and has no `sp0` form", s.name.text),
            ));
        }
        (VTy::Int { lo, hi, .. }, _) => {
            let Some(n) = numeral(&s.wert, scope) else {
                return Err(refuse(
                    "LG003",
                    format!("initialiser of static {} is not a numeral and has no `sp0` form", s.name.text),
                ));
            };
            if n < *lo || n > *hi {
                return Err(refuse(
                    "LG003",
                    format!(
                        "initialiser {n} of static {} lies outside {lo}..{hi} and has no `sp0` value",
                        s.name.text
                    ),
                ));
            }
            GInit::Int(n)
        }
        // **A `tagged` initialiser at file scope** (`beispiele/121`): the two
        // spellings the surface has, the bare case (`Leer`) and the call form
        // (`Kurz(5)`). A payload must be a NUMERAL -- `sp0` is a value the
        // loader establishes, not a computation -- and it must lie in the
        // case's declared range, which is decided here, in Rust.
        (VTy::Sum { name: tn, cases }, art) => {
            let (case_name, arg): (&str, Option<&Expr>) = match art {
                ExprArt::Ort(o) if o.suffixe.is_empty() => (o.basis.text.as_str(), None),
                ExprArt::Ruf(r) => {
                    let Some(path) = r.path() else {
                        return Err(refuse("LG003", format!(
                            "initialiser of static {} is not a case of {tn} and has no `sp0` form",
                            s.name.text)));
                    };
                    let [seg] = path.teile.as_slice() else {
                        return Err(refuse("LG003", format!(
                            "initialiser of static {} is not a case of {tn} and has no `sp0` form",
                            s.name.text)));
                    };
                    if r.argumente.len() != 1 {
                        return Err(refuse("LG003", format!(
                            "initialiser of static {} names {} with {} arguments; a `Ty.sum` case \
                             carries exactly one payload or none",
                            s.name.text, seg.text, r.argumente.len())));
                    }
                    (seg.text.as_str(), Some(&r.argumente[0]))
                }
                _ => {
                    return Err(refuse("LG003", format!(
                        "initialiser of static {} is not a case of {tn} and has no `sp0` form",
                        s.name.text)));
                }
            };
            let Some(ci) = cases.iter().position(|(n, _)| n == case_name) else {
                return Err(refuse("LG005", format!(
                    "initialiser of static {} names {case_name}, which is no case of {tn}",
                    s.name.text)));
            };
            match (cases[ci].1, arg) {
                (None, None) => GInit::Sum { case: ci, payload: None },
                (None, Some(_)) => {
                    return Err(refuse("LG003", format!(
                        "case {case_name} of {tn} carries no payload, and the initialiser of \
                         static {} passes one", s.name.text)));
                }
                (Some(_), None) => {
                    return Err(refuse("LG003", format!(
                        "case {case_name} of {tn} carries a payload, and the initialiser of \
                         static {} passes none", s.name.text)));
                }
                (Some((lo, hi)), Some(e)) => {
                    let Some(n) = numeral(e, scope) else {
                        return Err(refuse("LG003", format!(
                            "payload of the initialiser of static {} is not a numeral and has no \
                             `sp0` form", s.name.text)));
                    };
                    if n < lo || n > hi {
                        return Err(refuse("LG003", format!(
                            "payload {n} of the initialiser of static {} lies outside the {lo}..{hi} \
                             of case {case_name} and has no `sp0` value", s.name.text)));
                    }
                    GInit::Sum { case: ci, payload: Some(n) }
                }
            }
        }
        _ => {
            return Err(refuse(
                "LG002",
                format!("static {} has no `Glob` form", s.name.text),
            ));
        }
    };
    Ok(GlobModel { name: s.name.text.clone(), ty, init })
}

/// One lock: its rank and the carriers its `protects` names (a table, a
/// table field, or a global). Masking and the shared branch have no G form.
fn read_lock(l: &LockDecl, model: &Model) -> Result<LockModel, Refusal> {
    if l.maskiert.is_some() || l.geteilte_haltezeit.is_some() {
        return Err(refuse("LG001", format!("lock {} carries a form with no G counterpart", l.name.text)));
    }
    let ExprArt::Zahl(rank) = &l.rang.art else {
        return Err(refuse("LG005", format!("lock {} has no numeric rank", l.name.text)));
    };
    let rank = i128::try_from(*rank).map_err(|_| refuse("LG005", format!("lock {} rank too large", l.name.text)))?;
    let mut guards = Vec::new();
    let mut gguards = Vec::new();
    for o in &l.schuetzt {
        if !o.suffixe.is_empty() {
            return Err(refuse("LG005", format!("lock {} protects {}", l.name.text, o.text())));
        }
        if let Some(gi) = model.globs.iter().position(|g| g.name == o.basis.text) {
            if !gguards.contains(&gi) {
                gguards.push(gi);
            }
            continue;
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
    Ok(LockModel { name: l.name.text.clone(), rank, guards, gguards, invariant: l.invariante.clone() })
}

/// **The lock floor is a CHOICE, and the exporter used to make the worst one.**
///
/// `Signatur.boden` is not a measurement of the body; it is a promise to
/// callers: *"you may hold, beyond my `requires Held`, any lock of rank below
/// this"* (`RufPasst.hx`), and the duty it carries is `StufenOk` --
/// `(P.rumpf f).ueberBoden c = true`, i.e. every `locks L` in the body takes
/// a lock of rank at least `c`. **A body that takes no lock at all satisfies
/// `ueberBoden c` for EVERY `c`** (`Satz.lean`: only the `.locks` arm
/// constrains), so its floor is free -- and the exporter wrote `none`, the
/// one value that promises callers NOTHING.
///
/// That is what refused `beispiele/124` and `beispiele/109`: a caller that
/// takes a lock (floor `some 0`) calling a lock-free callee (floor `none`)
/// fails `RufPasst.hb` (`∀ c, V.boden = some c → ∃ c', S.boden = some c' ∧ c ≤ c'`),
/// although nothing inside the callee can undercut anything. **`hb` is a real
/// rule** -- the caller's own untracked extras (rank below its floor) are held
/// while the callee runs, and the callee must tolerate them -- and the defect
/// was the exporter's choice of `none`.
///
/// The floor chosen here is the **minimum rank taken anywhere in the function's
/// reachable call graph**, and `HOCH` (one above every declared rank) where
/// that set is empty. It is sound and it is the most permissive choice that is:
///
/// * `StufenOk`: the floor is at most every rank the body takes directly.
/// * `hb`: `reach g ⊆ reach f` for every callee `g` of `f`, so
///   `floor f ≤ floor g` -- never refused for a call inside the unit again.
/// * `hx`: an extra lock must rank below the floor, i.e. below every rank the
///   callee (or anything it calls) takes -- which is exactly `H006` carried
///   across the call boundary.
///
/// A unit with no locks keeps `none` throughout: there is no rank to be above,
/// and `hb`/`hx` are vacuous there.
fn resolve_floors(checked: &mut [CheckedFn], model: &Model) {
    if model.locks.is_empty() {
        return;
    }
    let hoch = model.locks.iter().map(|l| l.rank).max().expect("nonempty") + 1;
    let idx: std::collections::HashMap<&str, usize> =
        checked.iter().enumerate().map(|(i, f)| (f.name.as_str(), i)).collect();
    let mut floors = Vec::with_capacity(checked.len());
    for i in 0..checked.len() {
        // The reachable set, by worklist: recursion and cycles are a SET
        // question, not a recursive descent, so they terminate here.
        let mut seen = vec![false; checked.len()];
        let mut stack = vec![i];
        seen[i] = true;
        let mut floor: Option<i128> = None;
        while let Some(j) = stack.pop() {
            if let Some(c) = checked[j].direct_floor {
                floor = Some(floor.map_or(c, |m: i128| m.min(c)));
            }
            for name in &checked[j].calls {
                if let Some(&k) = idx.get(name.as_str()) {
                    if !seen[k] {
                        seen[k] = true;
                        stack.push(k);
                    }
                }
            }
        }
        floors.push(Some(floor.unwrap_or(hoch)));
    }
    for (f, c) in checked.iter_mut().zip(floors) {
        f.boden = c;
    }
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
    resolve_floors(&mut checked, &model);
    let mut out = Out::default();
    for c in &checked {
        check_contracts(c, &model, &scope, &mut out)?;
        check_body(c, &model)?;
    }
    check_locks(&model, &scope)?;
    check_sp0(&model)?;
    let startet = check_starts(&model)?;
    Ok(emit(source_name, namespace, &model, &checked, &scope, &mut out, &startet)?)
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
    resolve_floors(&mut checked, &model);
    let mut out = Out::default();
    for c in &checked {
        check_contracts(c, &model, &scope, &mut out)?;
        check_body(c, &model)?;
    }
    check_locks(&model, &scope)?;
    check_sp0(&model)?;
    check_starts(&model)?;
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
    build_scope(&mut scope, &tree.items)?;
    Ok(scope)
}

/// What translation collects for the emission: the call sites (caller,
/// held-context tag, callee, with the floor facts their proofs need) and
/// the guard facts (function, tag, table) each use site names.
#[derive(Default)]
struct Out {
    hps: Vec<HpNeeded>,
    darf: Vec<(String, String, usize)>,
    /// The same, for GLOBALS (`gdarf`): (function, tag, global).
    gdarf: Vec<(String, String, usize)>,
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

    fn gbraucht(&mut self, fname: &str, tag: &str, g: usize) {
        let key = (fname.to_string(), tag.to_string(), g);
        if !self.gdarf.contains(&key) {
            self.gdarf.push(key);
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
    /// A `requires` clause (lane 198): the same translator as the
    /// `ensures`, over the parameters alone -- no result slot, so
    /// `result` has no form here, and the messages name `requires`.
    in_requires: bool,
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
        in_requires: false,
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
        in_requires: false,
        gamma: format!("(ErgCtx (gD.params g_{g}) (gD.erg g_{g}))"),
        lambda: format!("gL_{g}"),
    }
}

fn requires_ctx<'a>(cf: &'a CheckedFn, model: &'a Model) -> Ctx<'a> {
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
        with_result: false,
        in_requires: true,
        gamma: format!("(gD.params g_{g})"),
        lambda: format!("gL_{g}"),
    }
}

impl<'a> Ctx<'a> {
    /// The clause kind for refusal messages: the `requires` shares the
    /// `ensures` translator, never its name.
    fn quelle(&self) -> &'static str {
        if self.in_requires { "requires" } else { "ensures" }
    }

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

/// The same for a GLOBAL (`gdarf`): the guards of `g` are among the held set.
fn gdarf_name(fname: &str, tag: &str, model: &Model, g: usize) -> String {
    format!("gGDarf_{}{}_{}", lean_fn(fname), tag, model.globs[g].name)
}

/// Every global `g`'s guards must be among `held` (the `gdarf` half).
fn holds_gguards(held: &[usize], model: &Model, g: usize) -> bool {
    model.locks.iter().enumerate()
        .filter(|(_, l)| l.gguards.contains(&g))
        .map(|(li, _)| li)
        .all(|li| held.contains(&li))
}

/// Some guard of the global `g` is signature-held (the footprint half).
fn gguard_held(held: &[usize], model: &Model, g: usize) -> bool {
    model.locks.iter().enumerate()
        .filter(|(_, l)| l.gguards.contains(&g))
        .map(|(li, _)| li)
        .any(|li| held.contains(&li))
}

fn glob_ctor(model: &Model, g: usize) -> String {
    format!("GGlob.{}", model.globs[g].name)
}

/// The guard proof a global access names: the theorem of its held context.
fn gdarf_at(ctx: &Ctx, model: &Model, fname: &str, g: usize, out: &mut Out) -> String {
    out.gbraucht(fname, &ctx.tag, g);
    gdarf_name(fname, &ctx.tag, model, g)
}

/// A bare name that is a declared global, as an `Expr.glob`/`Expr.altGlob`
/// under its guards. `None` where the name is no global -- the caller then
/// refuses as before, so an unknown name never becomes a silent global.
fn glob_read(
    o: &Ort, alt: bool, ctx: &Ctx, model: &Model, fname: &str, out: &mut Out,
) -> Option<Result<(String, VTy), Refusal>> {
    let gi = model.globs.iter().position(|g| g.name == o.basis.text)?;
    if !holds_gguards(&ctx.held, model, gi) {
        return Some(Err(refuse(
            "LG004",
            format!("read of the global {} in {fname} holds no guard (no proof)", o.basis.text),
        )));
    }
    let proof = gdarf_at(ctx, model, fname, gi, out);
    let ctor = if alt { "Expr.altGlob" } else { "Expr.glob" };
    Some(Ok((
        format!("({ctor} (D := gD) {} {proof})", glob_ctor(model, gi)),
        model.globs[gi].ty.clone(),
    )))
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
        ParamTy::Sum { cases, .. } => format!("(.sum {})", sum_list(cases)),
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
        // **A `Ty.sum` has no widening.** `Expr.weiter` is the one conversion
        // the grammar allows, and it is over integer ranges; two sums are the
        // same type or they are two types. Comparing the NAME and not just the
        // shape keeps two tagged types with identical payloads apart, exactly
        // as the surface keeps them apart.
        (VTy::Sum { name: a, cases: ca }, VTy::Sum { name: b, cases: cb }) => {
            if a == b && ca == cb {
                Ok(base)
            } else {
                Err(refuse("LG004", format!(
                    "a value of the tagged type {a} in {fname} is no value of {b}, and `Ty.sum` \
                     has no widening (`Expr.weiter` is over integer ranges)")))
            }
        }
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
    // **`A[i]` at an arena** (O14): the synthesised table has exactly one
    // field, so the arena read is the slot read of that field.
    if let [OrtSuffix::Index(idx)] = o.suffixe.as_slice() {
        if let Some(a) = model.arenas.iter().find(|a| a.name == o.basis.text) {
            let t = a.table;
            if !holds_guards(&ctx.held, model, t) {
                return Err(refuse("LG004", format!("access to {} in {fname} holds no guard (no proof)", o.text())));
            }
            let index = tr_index(idx, t, ctx, model, fname)?;
            let ty = model.tables[t].fields[0].ty.clone();
            return Ok((t, 0, index, None, ty));
        }
    }
    // **`p->f` at a pointer to a RECORD**: the record is a `Tab` with
    // `count 1` (`Syntax.lean` §1/§9), so the access is the slot read of
    // index `0` -- `Expr.durch` with the same guards as any other table.
    // The index type is `.index 1 = .int 0 0`, which `.lit 0` fits exactly.
    if let [OrtSuffix::Ueber(f)] = o.suffixe.as_slice() {
        let Some((j, ty, _)) = ctx.lookup(&o.basis.text) else {
            return Err(refuse("LG005", format!("unknown name {} in {fname}", o.basis.text)));
        };
        let VTy::Ptr { table, .. } = &ty else {
            return Err(refuse("LG003", format!("place {} in {fname} has no G form", o.text())));
        };
        let t = *table;
        // The G form is `Expr.durch`, which carries a slot INDEX. A record has
        // exactly one slot and the index is `0`; a table has `count` of them,
        // and no index is written here -- so the message names the surface
        // spelling that supplies one, which is what a user can act on.
        if !model.tables[t].record {
            return Err(refuse("LG003", format!(
                "`{}` in {fname} reaches past a pointer to the table {}, which is no record: a \
                 table has `count` slots and the access must name one, so write \
                 `{}.slots[i].{}`", o.text(), model.tables[t].name, o.basis.text, f.text)));
        }
        let Some(fi) = model.tables[t].fields.iter().position(|fd| fd.name == f.text) else {
            return Err(refuse("LG005", format!("unknown field {} in {fname}", o.text())));
        };
        if !holds_guards(&ctx.held, model, t) {
            return Err(refuse("LG004", format!("access to {} in {fname} holds no guard (no proof)", o.text())));
        }
        let index = format!("((.weiter (by decide) (by decide) (.lit 0) : {}))", ctx.index_ty(model, t));
        let ty = model.tables[t].fields[fi].ty.clone();
        return Ok((t, fi, index, Some(j), ty));
    }
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

/// The tagged type a bare case name belongs to, and the case's POSITION.
///
/// A name that two tagged types share has no unambiguous `Expr.fall` here:
/// the exporter translates bottom-up and has no expected type to pick with,
/// and guessing would build a value of the WRONG `Ty.sum`. Refused by name.
fn tagged_case(scope: &Scope, name: &str, fname: &str) -> Result<Option<(String, usize)>, Refusal> {
    let mut hits: Vec<(String, usize)> = scope
        .tagged
        .iter()
        .filter_map(|(tn, cs)| cs.iter().position(|(n, _)| n == name).map(|i| (tn.clone(), i)))
        .collect();
    hits.sort();
    match hits.len() {
        0 => Ok(None),
        1 => Ok(Some(hits.remove(0))),
        _ => Err(refuse(
            "LG005",
            format!(
                "the case name {name} in {fname} belongs to more than one tagged type ({}), and \
                 `Expr.fall` names exactly ONE `Ty.sum`: this exporter has no expected type here \
                 to choose with",
                hits.iter().map(|(t, _)| t.as_str()).collect::<Vec<_>>().join(", ")
            ),
        )),
    }
}

/// **A tagged constructor is `Expr.fall cs i nutz`** (`Syntax.lean` §3): the
/// case list, the case POSITION as a `Fin`, and the payload -- `.keine` where
/// the case carries none, `.zahl e` where it carries an integer range, with
/// `e` fitted to exactly that range (a `NutzlastExpr` carries the range in
/// its type, so a mismatch would be a Lean error and not a named refusal).
fn tr_fall(
    tyname: &str,
    ci: usize,
    arg: Option<&Expr>,
    ctx: &Ctx,
    model: &Model,
    scope: &Scope,
    fname: &str,
    out: &mut Out,
) -> Result<(String, VTy), Refusal> {
    let cases = scope.tagged[tyname].clone();
    let vty = VTy::Sum { name: tyname.to_string(), cases: cases.clone() };
    let case_name = cases[ci].0.clone();
    let nutz = match (cases[ci].1, arg) {
        (None, None) => ".keine".to_string(),
        (None, Some(_)) => {
            return Err(refuse("LG003", format!(
                "case {case_name} of {tyname} carries no payload, and {fname} passes one")));
        }
        (Some(_), None) => {
            return Err(refuse("LG003", format!(
                "case {case_name} of {tyname} carries a payload, and {fname} passes none")));
        }
        (Some((lo, hi)), Some(e)) => {
            let v = tr_value(e, &VTy::Int { lo, hi, bits: None }, ctx, model, scope, fname, out)?;
            format!("(.zahl {v})")
        }
    };
    // Fully ascribed: `Expr.fall` leaves `Γ`/`Λ`/`D` implicit, and an
    // implicit-only position (a `match` subject, a `return` value) would
    // leave them metavariables while the `Fin` proof elaborates.
    Ok((
        format!(
            "((.fall {} ⟨{ci}, by decide⟩ {nutz}) : Expr gD {} {} {})",
            sum_list(&cases),
            ctx.gamma,
            ctx.lambda,
            vty.term(model)
        ),
        vty,
    ))
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
            // A local name shadows a global, so the context is asked first.
            if let Some((j, ty, _)) = ctx.lookup(&o.basis.text) {
                return Ok((ctx.var(j), ty));
            }
            if let Some(r) = glob_read(o, false, ctx, model, fname, out) {
                return r;
            }
            // A payload-free case of a `tagged type` (`Leer`): `Expr.fall`
            // with `.keine`. Asked LAST, so a local, a parameter and a global
            // all still shadow it, exactly as they do in the surface.
            if let Some((tn, ci)) = tagged_case(scope, &o.basis.text, fname)? {
                return tr_fall(&tn, ci, None, ctx, model, scope, fname, out);
            }
            Err(refuse("LG005", format!("unknown name {} in {fname}", o.basis.text)))
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
            // No result slot in a body, and none in a `requires` (its
            // context is the parameters alone -- `.var .hier` there would
            // name the first parameter, not a result).
            if ctx.in_body || ctx.in_requires {
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
        ExprArt::Ruf(r) => {
            // A tagged constructor with a payload (`Kurz(x)`) is `Expr.fall`,
            // not a call: it names a CASE, and the checker has already held
            // the arity against the declaration.
            if r.marken.is_empty() {
                if let Some(path) = r.path() {
                    if let [seg] = path.teile.as_slice() {
                        if let Some((tn, ci)) = tagged_case(scope, &seg.text, fname)? {
                            if r.argumente.len() != 1 {
                                return Err(refuse("LG003", format!(
                                    "case {} of {tn} in {fname} is applied to {} arguments; a \
                                     `Ty.sum` case carries exactly one payload or none",
                                    seg.text, r.argumente.len())));
                            }
                            return tr_fall(&tn, ci, Some(&r.argumente[0]), ctx, model, scope, fname, out);
                        }
                    }
                }
            }
            tr_conversion(r, ctx, model, scope, fname, out)
        }
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
    // `old(G)` at a global is `Expr.altGlob`.
    if o.suffixe.is_empty() && ctx.lookup(&o.basis.text).is_none() {
        if let Some(r) = glob_read(o, true, ctx, model, fname, out) {
            let (term, ty) = r?;
            if !matches!(ty, VTy::Int { .. }) {
                return Err(refuse("LG003", format!("`old` of {} in {fname} has no G form", o.text())));
            }
            return Ok((term, ty));
        }
    }
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
            if let Some((j, ty, _)) = ctx.lookup(&o.basis.text) {
                return Ok((ctx.var(j), ty));
            }
            if let Some(r) = glob_read(o, false, ctx, model, fname, out) {
                return r;
            }
            Err(refuse("LG005", format!("unknown name {} in {fname}", o.basis.text)))
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
            if ctx.in_requires {
                return Err(refuse("LG003", format!("`result` in {fname} has no G form here")));
            }
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

/// One `ensures` predicate -- and, over a `requires` context, one
/// `requires` predicate (lane 198): the same translator, the clause name
/// off the context.
fn tr_ensures(p: &Pred, ctx: &Ctx, model: &Model, scope: &Scope, fname: &str, out: &mut Out) -> Result<String, Refusal> {
    match &p.art {
        PredArt::Vergleich(e) => match &e.art {
            ExprArt::Binaer(op, l, r) if op.ist_vergleich() => tr_cmp(op, l, r, ctx, model, scope, fname, out),
            ExprArt::Wahr => Ok(".wahr".to_string()),
            ExprArt::Falsch => Ok(".falsch".to_string()),
            _ => Err(refuse("LG003", format!("{}-clause in {fname} has no G form", ctx.quelle()))),
        },
        PredArt::Klammer(q) => tr_ensures(q, ctx, model, scope, fname, out),
        PredArt::Und(a, b) => Ok(format!("(.und {} {})", tr_ensures(a, ctx, model, scope, fname, out)?, tr_ensures(b, ctx, model, scope, fname, out)?)),
        PredArt::Oder(a, b) => Ok(format!("(.oder {} {})", tr_ensures(a, ctx, model, scope, fname, out)?, tr_ensures(b, ctx, model, scope, fname, out)?)),
        PredArt::Nicht(q) => Ok(format!("(.nicht {})", tr_ensures(q, ctx, model, scope, fname, out)?)),
        _ => Err(refuse("LG003", format!("{}-clause in {fname} has no G form", ctx.quelle()))),
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

/// The declared starts as function indices (lane 198): the `concurrent`
/// members first, then the `entry`/`boot` dispatch roots -- one pool,
/// because one boot assignment starts them all (the order
/// `startexklusiv.rs` reads). Every start resolves to exactly one exported
/// `impl fn`; a start with parameters has no `Env` form (the declaration
/// carries no arguments) and is refused by name, as is a dispatch that
/// names nothing exported.
fn check_starts(model: &Model) -> Result<Vec<usize>, Refusal> {
    fn nimm(model: &Model, kurz: &str, quelle: &str, aus: &mut Vec<usize>) -> Result<(), Refusal> {
        let treffer: Vec<usize> =
            model.fns.iter().enumerate().filter(|(_, f)| f.name == kurz).map(|(i, _)| i).collect();
        let Some((&i, rest)) = treffer.split_first() else {
            return Err(refuse("LG005", format!("{quelle} names unknown function {kurz}")));
        };
        if !rest.is_empty() {
            return Err(refuse("LG005", format!("{quelle} names ambiguous function {kurz}")));
        }
        if !model.fns[i].decl.parameter.is_empty() {
            return Err(refuse(
                "LG001",
                format!("start `{kurz}` takes parameters, which have no start-argument form"),
            ));
        }
        aus.push(i);
        Ok(())
    }
    let mut aus = Vec::new();
    for name in &model.concurrent {
        let quelle = format!("concurrent member `{name}`");
        nimm(model, name, &quelle, &mut aus)?;
    }
    for pfad in &model.wurzeln {
        let Some(last) = pfad.teile.last() else {
            return Err(refuse("LG005", "empty dispatch path has no G form".to_string()));
        };
        let quelle = format!("dispatch `{}`", pfad.text());
        nimm(model, &last.text, &quelle, &mut aus)?;
    }
    Ok(aus)
}

/// The declared initial memory (lane 198): every SLOT starts at zero
/// (`false` for `bool`) -- no surface form names a slot initialiser -- as
/// the loader establishes it (`Laufzeit.lader` of the goal theorem). An
/// integer field whose range holds no zero has no `sp0` value and is
/// refused here, by name. A GLOBAL is different: its `static` names an
/// initialiser, and that value travels (checked against the declared range
/// in `read_static`, so nothing is checked twice here).
fn check_sp0(model: &Model) -> Result<(), Refusal> {
    for t in &model.tables {
        for f in &t.fields {
            match &f.ty {
                VTy::Int { lo, hi, .. } => {
                    if *lo > 0 || 0 > *hi {
                        return Err(refuse(
                            "LG003",
                            format!(
                                "zero-initialised memory of {}.{} lies outside {lo}..{hi} and has no `sp0` form",
                                t.name, f.name
                            ),
                        ));
                    }
                }
                // **A `tagged` slot starts at its FIRST case** -- the same
                // rule "no surface form names a slot initialiser" gives the
                // integers zero. Where that case carries a payload, the
                // payload starts at zero too, and a payload range holding no
                // zero has no `sp0` value: refused BY NAME, never silently
                // moved to the range's low end.
                VTy::Sum { name, cases } => {
                    if let Some((lo, hi)) = cases[0].1 {
                        if lo > 0 || 0 > hi {
                            return Err(refuse(
                                "LG003",
                                format!(
                                    "zero-initialised memory of {}.{} is case {} of {name}, whose \
                                     payload range {lo}..{hi} holds no zero and has no `sp0` value",
                                    t.name, f.name, cases[0].0
                                ),
                            ));
                        }
                    }
                }
                _ => {}
            }
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
    // Every `requires` past the signature-held locks must translate too
    // (lane 198): over the parameters alone, refusing by name what has no
    // `Expr` form.
    let rctx = requires_ctx(cf, model);
    for p in &cf.requires {
        tr_ensures(p, &rctx, model, scope, &cf.name, out)?;
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
        (ParamTy::Int { .. }, _) | (ParamTy::Bool, _) | (ParamTy::Sum { .. }, _) =>
            tr_value(a, &expected, ctx, model, scope, fname, out),
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
    // `RufPasst.hg`: the same for GLOBALS.
    for g in &callee.gwrites {
        if !ctx.cf.gwrites.contains(g) {
            return Err(refuse("LG004", format!("call of {} in {fname} writes the global {} beyond its caller (`RufPasst.hg`)", callee.name, model.globs[*g].name)));
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
        // **Lane O-1:** a `return` on the child path is a return -- the
        // checker refuses it (`N448`); the exporter still sees it.
        StmtArt::Child(x) => contains_return(x),
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

/// **`match m { … }` over a `tagged` value is `Stmt.onTag`** (`Syntax.lean`
/// §7): the subject is an `Expr … (.sum cs)` and the arms are an `Arms`, ONE
/// block per case **in declaration order** -- a case is its position, so the
/// source order of the arms does not travel, only their assignment to cases.
///
/// `ArmCtx Γ c` pushes the payload of a case that has one, so an arm over
/// `Kurz(k)` translates with `k` at the head of `Γ`; an arm over a
/// payload-free case translates in the outer context. `D005` (exhaustive, no
/// catch-all) is the checker's; what is checked HERE is the thing the term
/// needs: exactly one arm per case, because `Arms` has exactly that shape.
///
/// A `match` over an `option` or a reason has its own forms (`Stmt.onOption`,
/// `Stmt.onGrund`) and neither is built here -- refused by NAME, never by the
/// tagged arm silently declining.
#[allow(clippy::too_many_arguments)]
fn tr_on_tag(m: &MatchStmt, rest_empty_tail: bool, ctx: &Ctx, model: &Model, scope: &Scope, fns: &[CheckedFn], fname: &str, out: &mut Out) -> Result<String, Refusal> {
    let (subj, sty) = tr_typed(&m.gegenstand, ctx, model, scope, fname, out)?;
    let VTy::Sum { name: tyname, cases } = sty else {
        return Err(refuse("LG004", format!(
            "`match` in {fname} is not over a `tagged` value: the specification carries an \
             `option` match as `Stmt.onOption` (with `Ty.opt`/`Expr.some`/`Expr.istSome`) and a \
             reason match as `Stmt.onGrund`; this exporter builds neither")));
    };
    for z in &m.zweige {
        if !cases.iter().any(|(n, _)| n == &z.variante.text) {
            return Err(refuse("LG005", format!(
                "`match` arm {} in {fname} names no case of {tyname}", z.variante.text)));
        }
    }
    let mut arme = Vec::new();
    for (ci, (cname, payload)) in cases.iter().enumerate() {
        let treffer: Vec<&MatchZweig> = m.zweige.iter().filter(|z| &z.variante.text == cname).collect();
        let [z] = treffer.as_slice() else {
            return Err(refuse("LG004", format!(
                "`match` in {fname} names case {cname} of {tyname} {} times; `Arms` carries \
                 exactly ONE block per case", treffer.len())));
        };
        if rest_empty_tail && contains_return(&z.rumpf) {
            return Err(refuse("LG004", format!(
                "`return` inside the `match` arm {cname} in {fname} has no G form")));
        }
        let inner = match payload {
            None => {
                if z.binder.is_some() {
                    return Err(refuse("LG004", format!(
                        "`match` arm {cname} in {fname} binds a payload, and case {cname} of \
                         {tyname} carries none")));
                }
                ctx.clone()
            }
            // A payload case pushes its range whether or not the surface
            // names a binder -- `ArmCtx` does, and `Γ` is the term. An
            // unnamed one gets a name no expression can spell.
            Some((lo, hi)) => {
                let bname = z.binder.as_ref().map(|b| b.text.clone())
                    .unwrap_or_else(|| format!(" arm{ci}"));
                ctx.push(bname, VTy::Int { lo: *lo, hi: *hi, bits: None }, NameKind::Let)
            }
        };
        arme.push(tr_block(&z.rumpf.anweisungen, &inner, model, scope, fns, fname, out)?);
    }
    let mut acc = ".nil".to_string();
    for a in arme.iter().rev() {
        acc = format!("(.cons {a} {acc})");
    }
    Ok(format!("(.onTag {subj} {acc})"))
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

/// A `traverse i over slots of T` loop -- or over a pointer-typed name
/// for `T` (lane 207): a `ptr<normal, _> T` statically names its table, and
/// the slots of what it points to are the slots of `T` itself, so the domain
/// is the same one the table spelling names (`beispiele/19`, `46` spell it
/// this way). The mode, the `decreases` witness
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
    let ti = match model.tables.iter().position(|t| t.name == o.basis.text) {
        Some(ti) => ti,
        // No table of that name: a pointer-typed name in scope (a parameter
        // or a `let`-bound pointer) resolves to the table its type names.
        // Anything else -- an integer, a `bool`, an unknown name -- is still
        // refused, naming the domain.
        None => match ctx.lookup(&o.basis.text) {
            Some((_, VTy::Ptr { table, .. }, _)) => table,
            _ => return Err(refuse("LG006", format!("`traverse` domain in {fname} is not a table"))),
        },
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
            // `G = e;` at a declared global is `Stmt.assignGlob`. The write
            // right (`hw : V.gschreibt g = true`) is decided HERE, in Rust:
            // a `by decide` that fails is a Lean error, not a named refusal.
            if z.ziel.suffixe.is_empty() && ctx.lookup(&z.ziel.basis.text).is_none() {
                if let Some(gi) = model.globs.iter().position(|g| g.name == z.ziel.basis.text) {
                    if !ctx.cf.gwrites.contains(&gi) {
                        return Err(refuse("LG004", format!(
                            "{fname} writes the global {} without an `effects {{ writes {} }}` -- \
                             the write right `Signatur.gschreibt` has nothing to stand on",
                            z.ziel.basis.text, z.ziel.basis.text)));
                    }
                    if !holds_gguards(&ctx.held, model, gi) {
                        return Err(refuse("LG004", format!(
                            "write of the global {} in {fname} holds no guard (no proof)",
                            z.ziel.basis.text)));
                    }
                    let gty = model.globs[gi].ty.clone();
                    let val = match &gty {
                        VTy::Int { lo, hi, .. } => tr_value(&z.wert, &VTy::Int { lo: *lo, hi: *hi, bits: None }, ctx, model, scope, fname, out)?,
                        VTy::Bool => tr_bool(&z.wert, ctx, model, scope, fname, out)?,
                        VTy::Sum { .. } => tr_value(&z.wert, &gty, ctx, model, scope, fname, out)?,
                        _ => return Err(refuse("LG004", format!("assignment to the global {} in {fname} has no G form", z.ziel.basis.text))),
                    };
                    let proof = gdarf_at(ctx, model, fname, gi, out);
                    let base = format!("(.assignGlob {} {val} (by decide) {proof})", glob_ctor(model, gi));
                    return Ok(format!("(.cons {base} {})", tr_rest(rest, ctx, model, scope, fns, fname, out, cont, endblock)?));
                }
            }
            let (t, fi, index, through, ty) = slot_access(&z.ziel, ctx, model, fname)?;
            // The value fits the field: an integer range, or `bool`.
            let val = match &ty {
                VTy::Int { lo, hi, .. } => tr_value(&z.wert, &VTy::Int { lo: *lo, hi: *hi, bits: None }, ctx, model, scope, fname, out)?,
                VTy::Bool => tr_bool(&z.wert, ctx, model, scope, fname, out)?,
                VTy::Sum { .. } => tr_value(&z.wert, &ty, ctx, model, scope, fname, out)?,
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
        StmtArt::Match(m) => {
            let tail = rest.is_empty() && endblock;
            let on_tag = tr_on_tag(m, tail, ctx, model, scope, fns, fname, out)?;
            Ok(format!("(.cons {on_tag} {})", tr_rest(rest, ctx, model, scope, fns, fname, out, cont, endblock)?))
        }
        StmtArt::Publish(_) => Err(refuse("LG004", format!("`publishes` in {fname} has no G form in this fragment"))),
        StmtArt::AwaitLoad(_) => Err(refuse("LG004", format!("`awaits` in {fname} has no G form in this fragment"))),
        StmtArt::Exchange(_) => Err(refuse("LG004", format!("`exchange` in {fname} has no G form in this fragment"))),
        StmtArt::LibraryCall(_) => Err(refuse("LG004", format!("library call in {fname} has no G form in this fragment"))),
        // **`reset A;` is `Stmt.arenaReset`** (O14): one store of zero into
        // the counter, which is what the emitter writes.
        StmtArt::ResetArena(name) => {
            let Some(ai) = model.arenas.iter().position(|a| &a.name == &name.text) else {
                return Err(refuse("LG005", format!("`reset` in {fname} names unknown arena {}", name.text)));
            };
            let gi = model.arenas[ai].glob;
            if !ctx.cf.gwrites.contains(&gi) {
                return Err(refuse("LG004", format!(
                    "`reset {}` in {fname} without an `effects {{ writes {} }}` -- \
                     the write right `Signatur.gschreibt` has nothing to stand on",
                    name.text, name.text)));
            }
            let proof = gdarf_at(ctx, model, fname, gi, out);
            let base = format!("(Stmt.arenaReset (D := gD) gArena_{} (by decide) {proof})",
                model.arenas[ai].name);
            Ok(format!("(.cons {base} {})", tr_rest(rest, ctx, model, scope, fns, fname, out, cont, endblock)?))
        }
        // **`let i = alloc A (v) else B;` is `Block.arenaAlloc`** (O14).
        StmtArt::Alloc(al) => tr_alloc(al, ctx, model, scope, fns, fname, out, rest, cont, endblock),
        StmtArt::Bricht(_) => Err(refuse("LG004", format!("`breaking` in {fname} has no G form in this fragment"))),
        // **Lane O-1:** `child` has no G form in this fragment -- the handed
        // stack and the no-return-into-caller-frame have no counterpart in
        // machine G (stacks are C-level). Refused by name, never skipped:
        // the hand models bridge, like for every other LG004 shape.
        StmtArt::Child(_) => Err(refuse("LG004", format!("`child` in {fname} has no G form in this fragment"))),
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

/// **`let i = alloc A (v) else { … };` as `Block.arenaAlloc`** (O14).
///
/// Three existing forms in a row: `Block.narrow` on the counter into
/// `0 ..< hi` with the `else` branch, `Stmt.assignSlot` at the index it
/// names, `Stmt.assignGlob` of `i + 1`. `narrow` IS the emitted guard.
///
/// **An `alloc` WITHOUT `else` is refused by name, and that is a decision,
/// not an omission.** `Block.arenaAlloc` always carries a full-arena branch;
/// the surface form without `else` carries none, and the C the emitter writes
/// for it carries none either (`buf[used++] = v;`, no bound check). Inventing
/// a branch -- a `return` the user did not write -- would put a guard into the
/// exported term that neither the source nor the emitted C has, and the
/// translation-validation chain would then compare two different programs.
/// *The checker's `N212` is what makes the branch dead, and `N212` is not in
/// the exported term.*
#[allow(clippy::too_many_arguments)]
fn tr_alloc(al: &AllocStmt, ctx: &mut Ctx, model: &Model, scope: &Scope, fns: &[CheckedFn], fname: &str, out: &mut Out, rest: &[Stmt], cont: String, endblock: bool) -> Result<String, Refusal> {
    let Some(ai) = model.arenas.iter().position(|a| a.name == al.tisch.text) else {
        return Err(refuse("LG005", format!("`alloc` in {fname} names unknown arena {}", al.tisch.text)));
    };
    let (aname, ti, gi) = (model.arenas[ai].name.clone(), model.arenas[ai].table, model.arenas[ai].glob);
    if endblock {
        return Err(refuse("LG004", format!(
            "`alloc {aname}` in {fname} has no G form at the top level of a body -- \
             `Block.arenaAlloc` is a `Block` former (its first half is `Block.narrow`), \
             and a body is an `Endblock`")));
    }
    let Some(sonst) = al.sonst.as_ref() else {
        return Err(refuse("LG004", format!(
            "`alloc {aname}` in {fname} carries no `else`, and this exporter will not invent one: \
             `Block.arenaAlloc` always carries a full-arena branch, the emitted C carries none, \
             and what makes the branch dead is the checker's static count `N212`, which does not \
             travel into the term -- see OFFEN.md O14")));
    };
    if !ctx.cf.writes.contains(&ti) || !ctx.cf.gwrites.contains(&gi) {
        return Err(refuse("LG004", format!(
            "`alloc {aname}` in {fname} without an `effects {{ writes {aname} }}` -- \
             the write rights `Signatur.schreibt`/`gschreibt` have nothing to stand on")));
    }
    if !holds_guards(&ctx.held, model, ti) || !holds_gguards(&ctx.held, model, gi) {
        return Err(refuse("LG004", format!("`alloc {aname}` in {fname} holds no guard (no proof)")));
    }
    // The value, at the element type of the synthesised table.
    let ety = model.tables[ti].fields[0].ty.clone();
    let v = match &ety {
        VTy::Bool => tr_bool(&al.wert, ctx, model, scope, fname, out)?,
        VTy::Int { lo, hi, .. } => tr_value(&al.wert, &VTy::Int { lo: *lo, hi: *hi, bits: None }, ctx, model, scope, fname, out)?,
        _ => return Err(refuse("LG004", format!("`alloc {aname}` in {fname} stores a value with no G form"))),
    };
    // The full-arena branch is an `Endblock`: it must end in a `return`, or
    // it would fall through past the `alloc`, for which there is no form.
    let Some((letzt, _)) = sonst.anweisungen.split_last() else {
        return Err(refuse("LG004", format!("empty `else` of `alloc {aname}` in {fname} has no G form")));
    };
    let StmtArt::Return(_) = &letzt.art else {
        return Err(refuse("LG004", format!("falling-off `else` of `alloc {aname}` in {fname} has no G form")));
    };
    let mut voll_ctx = ctx.clone();
    let voll = tr_rest(&sonst.anweisungen, &mut voll_ctx, model, scope, fns, fname, out, String::new(), true)?;
    let hlt = darf_at(ctx, model, fname, ti, out);
    let hlg = gdarf_at(ctx, model, fname, gi, out);
    if let Some(ann) = &al.typ {
        let aty = annot_ty(ann, model, scope, fname)?;
        check_annotation(&VTy::Index { table: ti }, &aty, model, fname, &al.name.text)?;
    }
    *ctx = ctx.push(al.name.text.clone(), VTy::Index { table: ti }, NameKind::Let);
    Ok(format!("(Block.arenaAlloc (D := gD) gArena_{aname} ({v}) (by decide) {hlt} (by decide) {hlg} {voll} {})",
        tr_rest(rest, ctx, model, scope, fns, fname, out, cont, false)?))
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

/// One `requires` contract as an `Expr` term (lane 198): the value
/// clauses past the signature-held locks, conjoined (`.wahr` where there
/// are none -- like the default `ensures` of `gP`).
fn tr_contract_requires(cf: &CheckedFn, model: &Model, scope: &Scope, out: &mut Out) -> Result<Option<String>, Refusal> {
    if cf.requires.is_empty() {
        return Ok(None);
    }
    let ctx = requires_ctx(cf, model);
    let mut it = cf.requires.iter();
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
/// Carriers are numbered tables first, then globals (`nt + gi`), so ONE
/// accumulator carries both halves of `fussOrteG` -- which is what
/// `gCs : List (gD.Tab ⊕ gD.Glob)` enumerates Lean-side.
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

/// The carrier number of an arena read `A[i]` -- the arena's synthesised
/// slot table -- or `None`.
fn foot_arena(o: &Ort, model: &Model) -> Option<usize> {
    if !matches!(o.suffixe.as_slice(), [OrtSuffix::Index(_)]) {
        return None;
    }
    model.arenas.iter().find(|a| a.name == o.basis.text).map(|a| a.table)
}

/// The carrier number of a bare global name (`nt + gi`), or `None`.
fn foot_glob(o: &Ort, model: &Model, params: &[(String, ParamTy)]) -> Option<usize> {
    if !o.suffixe.is_empty() {
        return None;
    }
    if params.iter().any(|(n, _)| n == &o.basis.text) {
        return None;
    }
    model.globs.iter().position(|g| g.name == o.basis.text).map(|gi| model.tables.len() + gi)
}

/// **Is this place a CARRIER access?** `T.slots[i].f` (three suffixes) and,
/// since records travel as `Tab count 1`, `p->f` (one `->` suffix).
///
/// *Found by LEAN, and by nothing else* (2026-09-15): with `p->f` missing
/// here the mirror saw no carrier, `fuss_holds` said the old footprint check
/// passes, and the export printed `example : fussOrtGB gP gFs = true := by
/// decide` -- which Lean then DISPROVED. A mirror that undercounts does not
/// refuse anything; it prints a false claim. The two must be spelled once.
fn ist_traegerzugriff(o: &Ort) -> bool {
    o.suffixe.len() == 3 || matches!(o.suffixe.as_slice(), [OrtSuffix::Ueber(_)])
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
                if ist_traegerzugriff(o) {
                    if let Some(ti) = foot_carrier(o, model, params) {
                        foot_push(acc, ti);
                    }
                }
                if let Some(ci) = foot_arena(o, model) {
                    foot_push(acc, ci);
                }
                if let Some(ci) = foot_glob(o, model, params) {
                    foot_push(acc, ci);
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
                if let Some(ci) = foot_glob(o, model, params) {
                    foot_push(acc, ci);
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
                if ist_traegerzugriff(&z.ziel) {
                    if let Some(ti) = foot_carrier(&z.ziel, model, params) {
                        foot_push(acc, ti);
                    }
                }
                if let Some(ci) = foot_arena(&z.ziel, model) {
                    foot_push(acc, ci);
                }
                if let Some(ci) = foot_glob(&z.ziel, model, params) {
                    foot_push(acc, ci);
                }
                foot_expr(&z.wert, model, params, acc);
            }
            // An `alloc` touches BOTH halves of the arena's pair; a `reset`
            // the counter alone.
            StmtArt::Alloc(al) => {
                if let Some(a) = model.arenas.iter().find(|a| a.name == al.tisch.text) {
                    foot_push(acc, a.table);
                    foot_push(acc, model.tables.len() + a.glob);
                }
                foot_expr(&al.wert, model, params, acc);
                if let Some(b) = &al.sonst {
                    foot_block(b, model, params, acc);
                }
            }
            StmtArt::ResetArena(name) => {
                if let Some(a) = model.arenas.iter().find(|a| &a.name == &name.text) {
                    foot_push(acc, model.tables.len() + a.glob);
                }
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
            // **Lane O-1:** carriers written on the child path count -- a
            // footprint missing them would clear a race it cannot see.
            StmtArt::Child(x) => foot_block(x, model, params, acc),
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

/// The footprint mirror of a function: its `ensures` and `requires`
/// carriers (lane 198: the `requires` travels now, so its carriers count),
/// its body carriers, and its direct callees' `ensures` carriers
/// (`fussOrte`, one level; invariants are not admitted).
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
                if ist_traegerzugriff(o) {
                    if let Some(ti) = foot_carrier(o, model, params) {
                        foot_push(acc, ti);
                    }
                }
                if let Some(ci) = foot_arena(o, model) {
                    foot_push(acc, ci);
                }
                if let Some(ci) = foot_glob(o, model, params) {
                    foot_push(acc, ci);
                }
            }
            ExprArt::Alt(o) => {
                if let Some(ti) = foot_carrier(o, model, params) {
                    foot_push(acc, ti);
                }
                if let Some(ci) = foot_glob(o, model, params) {
                    foot_push(acc, ci);
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
    for p in &cf.requires {
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
    let nt = model.tables.len();
    for f in fns {
        for c in foot_fn(f, model, fns) {
            if c < nt {
                if guard_held(&f.held, model, c) {
                    continue;
                }
                if fns.iter().all(|g| !g.writes.contains(&c)) {
                    continue;
                }
            } else {
                let gi = c - nt;
                if gguard_held(&f.held, model, gi) {
                    continue;
                }
                if fns.iter().all(|g| !g.gwrites.contains(&gi)) {
                    continue;
                }
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
fn emit(source_name: &str, ns: &str, model: &Model, fns: &[CheckedFn], scope: &Scope, collected: &mut Out, startet: &[usize]) -> Result<String, Refusal> {
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
    out.push_str("-- `pub` and `opaque` (both are unit-boundary rules, and\n");
    out.push_str("-- `Deklaration` has no boundary -- `pub` added 2026-09-15 after\n");
    out.push_str("-- being dropped here and named nowhere, which is the one thing\n");
    out.push_str("-- this ledger exists to prevent; `opaque` the same day, when its\n");
    out.push_str("-- alias started to travel as its range);\n");
    out.push_str("-- `concurrent` (its members travel as the declared starts\n");
    out.push_str("-- `gE.starts`; every start is parameterless, its argument list\n");
    out.push_str("-- `.nil`); `entry`/`boot` (the vector, the registers, the steps:\n");
    out.push_str("-- NO FORM; only the dispatch root travels, as a declared start\n");
    out.push_str("-- where exportable).\n--\n");
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
    for a in &model.arenas {
        out.push_str(&format!(
            "-- arena {}: table {} (count {}) + counter {} -- the reservation does NOT travel\n",
            a.name, model.tables[a.table].name, model.tables[a.table].count, model.globs[a.glob].name));
    }
    for (gi, g) in model.globs.iter().enumerate() {
        let ty = match &g.ty {
            VTy::Int { lo, hi, .. } => format!("{lo}..{hi}"),
            VTy::Bool => "bool".to_string(),
            VTy::Sum { name, .. } => format!("tagged {name}"),
            _ => "?".to_string(),
        };
        let init = match g.init {
            GInit::Int(n) => n.to_string(),
            GInit::Bool(b) => b.to_string(),
            GInit::Sum { case, payload } => match payload {
                None => format!("case {case}"),
                Some(n) => format!("case {case}({n})"),
            },
        };
        out.push_str(&format!("-- static {gi}: {} : {ty} = {init}\n", g.name));
    }
    for (li, l) in model.locks.iter().enumerate() {
        out.push_str(&format!("-- lock {li}: {} (rank {}) guards", l.name, l.rank));
        for g in &l.guards {
            out.push_str(&format!(" {}", model.tables[*g].name));
        }
        for g in &l.gguards {
            out.push_str(&format!(" {}", model.globs[*g].name));
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
        for w in &f.gwrites {
            out.push_str(&format!(" {}", model.globs[*w].name));
        }
        out.push_str(")\n");
    }
    for (n, i) in startet.iter().enumerate() {
        out.push_str(&format!("-- start {n}: {}\n", fns[*i].name));
    }
    out.push_str("import Grammatik.ZielOrtGeraetSem\nimport Grammatik.SperreSem\nimport Grammatik.Zielsatz.Spec\n");
    if !model.arenas.is_empty() {
        out.push_str("import Grammatik.ArenaZucker\n");
    }
    out.push_str("\nnamespace Gabbro.Grammatik\n\nnamespace ");
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
    // The globals (`static`): one constructor each, like the tables.
    if !model.globs.is_empty() {
        out.push_str("inductive GGlob where\n");
        for g in &model.globs {
            out.push_str(&format!("  | {}\n", g.name));
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
        let gschreibt = if model.globs.is_empty() {
            "fun e => nomatch e".to_string()
        } else if f.gwrites.is_empty() {
            "fun _ => false".to_string()
        } else if f.gwrites.len() == model.globs.len() {
            "fun _ => true".to_string()
        } else {
            let mut garms: Vec<String> = f.gwrites.iter()
                .map(|w| format!("| .{} => true", model.globs[*w].name)).collect();
            garms.push("| _ => false".to_string());
            format!("fun {}", garms.join(" "))
        };
        let gtyp = if model.globs.is_empty() { "Empty".to_string() } else { "GGlob".to_string() };
        out.push_str(&format!("def gSig_{} : Signatur GTab {gtyp} GLock Empty where\n", lean_fn(&f.name)));
        out.push_str(&format!("  params := [{}]\n", params.join(", ")));
        out.push_str(&format!("  erg := {erg}\n"));
        out.push_str(&format!("  gruende := {}\n", f.gruende));
        out.push_str(&format!("  haelt := [{held}]\n"));
        out.push_str(&format!("  boden := {boden}\n"));
        out.push_str(&format!("  schreibt := {schreibt}\n"));
        out.push_str(&format!("  gschreibt := {gschreibt}\n"));
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
    if model.globs.is_empty() {
        out.push_str("  Glob := Empty\n");
        out.push_str("  decGlob := inferInstance\n");
        out.push_str("  gtyp := fun e => nomatch e\n");
        out.push_str("  nutzlast := fun e => nomatch e\n");
        out.push_str("  atomar := fun e => nomatch e\n");
    } else {
        out.push_str("  Glob := GGlob\n");
        out.push_str("  decGlob := inferInstance\n");
        let garms: Vec<String> = model.globs.iter()
            .map(|g| format!("| .{} => {}", g.name, g.ty.term(model))).collect();
        out.push_str(&format!("  gtyp := fun {}\n", garms.join(" ")));
        // No `atomic` item exports (LG001), so no publication payload
        // travels and no global is ordered by the machine.
        out.push_str("  nutzlast := fun _ => []\n");
        out.push_str("  atomar := fun _ => false\n");
    }
    if model.tables.is_empty() {
        out.push_str("  geteilt := fun t => nomatch t\n");
    } else {
        let garms: Vec<String> = model.tables.iter().enumerate().map(|(ti, _)| {
            let guarded = model.locks.iter().any(|l| l.guards.contains(&ti));
            format!("| .{} => {guarded}", model.tables[ti].name)
        }).collect();
        out.push_str(&format!("  geteilt := fun {}\n", garms.join(" ")));
    }
    if model.globs.is_empty() {
        out.push_str("  ggeteilt := fun e => nomatch e\n");
    } else {
        // A global is SHARED exactly where a lock guards it -- the same rule
        // the tables travel under, and it is what discharges
        // `ggeteilt_bewacht` by `decide` (a guarded global has a `gbraucht`
        // entry; an unguarded one is not shared).
        let garms: Vec<String> = model.globs.iter().enumerate().map(|(gi, g)| {
            let guarded = model.locks.iter().any(|l| l.gguards.contains(&gi));
            format!("| .{} => {guarded}", g.name)
        }).collect();
        out.push_str(&format!("  ggeteilt := fun {}\n", garms.join(" ")));
    }
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
    if model.globs.is_empty() {
        out.push_str("  gbraucht := fun e => nomatch e\n");
    } else {
        let garms: Vec<String> = model.globs.iter().enumerate().map(|(gi, g)| {
            let mut guards = String::new();
            for li in model.locks.iter().enumerate().filter(|(_, l)| l.gguards.contains(&gi)).map(|(li, _)| li) {
                guards.push_str(&format!("{}.inl GLock.{}",
                    if guards.is_empty() { "" } else { ", " }, model.locks[li].name));
            }
            format!("| .{} => [{guards}]", g.name)
        }).collect();
        out.push_str(&format!("  gbraucht := fun {}\n", garms.join(" ")));
    }
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
    if model.globs.is_empty() {
        out.push_str("  ggeteilt_bewacht := fun e => nomatch e\n\n");
    } else {
        out.push_str("  ggeteilt_bewacht := fun g => by cases g <;> decide\n\n");
    }
    // The `ArenaForm` of each arena (O14): the pair the sugar speaks about.
    // `hz` and `hpos` were decided in Rust (`read_arena`), so both close.
    for a in &model.arenas {
        out.push_str(&format!(
            "def gArena_{} : ArenaForm gD where\n  tab := {}\n  feld := {}\n  zaehl := {}\n  hz := by decide\n  hpos := by decide\n\n",
            a.name, tab_ctor(model, a.table), feld_ctor(model, a.table, 0), glob_ctor(model, a.glob)));
    }
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
    let mut gdarfs = collected.gdarf.clone();
    gdarfs.sort();
    gdarfs.dedup();
    for (fname, tag, gi) in &gdarfs {
        out.push_str(&format!("theorem {} : gdarf gD {} gL_{}{} := by unfold gdarf; decide\n",
            gdarf_name(fname, tag, model, *gi), glob_ctor(model, *gi), lean_fn(fname), tag));
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
        if model.globs.is_empty() {
            out.push_str("  hg := fun g => nomatch g\n");
        } else {
            out.push_str("  hg := fun g => by cases g <;> decide\n");
        }
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
    // The `requires` past the signature-held locks (lane 198): one `Expr`
    // per function carrying a value clause, over the parameters alone.
    let mut reqs = Vec::new();
    for f in fns {
        reqs.push((f.name.clone(), tr_contract_requires(f, model, scope, collected)?));
    }
    for (name, term) in &reqs {
        if let Some(term) = term {
            out.push_str(&format!("def gReq_{name} : Expr gD (gD.params g_{name}) (Signatur.anfang gD (gD.signatur g_{name})) .bool :=\n  {term}\n\n"));
        }
    }
    for (name, term) in &bodies {
        out.push_str(&format!("def gBody_{name} : Endblock gD (vertragVon gD g_{name}) false gCtx_{name} gL_{name} :=\n  {term}\n\n", name = lean_fn(name)));
    }
    // The program, the member list, and the decidable checks.
    out.push_str("def gP : Programm gD where\n");
    out.push_str("  invariante := fun i => nomatch i\n");
    out.push_str("  requires\n");
    for f in fns {
        let rhs = if f.requires.is_empty() { ".wahr".to_string() } else { format!("gReq_{}", lean_fn(&f.name)) };
        out.push_str(&format!("    | .{} => {rhs}\n", lean_fn(&f.name)));
    }
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
    // The lock and carrier member lists (lane 198): the complete
    // enumerations the goal theorem's checker premise runs over (the
    // obligation export states their completeness beside them).
    out.push_str(&format!("def gLs : List gD.Lock := [{}]\n\n",
        (0..model.locks.len()).map(|li| lock_ctor(model, li)).collect::<Vec<_>>().join(", ")));
    let mut cs: Vec<String> = (0..model.tables.len())
        .map(|ti| format!("(.inl {})", tab_ctor(model, ti))).collect();
    cs.extend((0..model.globs.len()).map(|gi| format!("(.inr {})", glob_ctor(model, gi))));
    out.push_str(&format!("def gCs : List (gD.Tab ⊕ gD.Glob) := [{}]\n\n", cs.join(", ")));
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
        for g in &l.gguards {
            cs.push_str(&format!(
                "{}.inr {}",
                if cs.is_empty() { "" } else { ", " },
                glob_ctor(model, *g)
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
        for g in &l.gguards {
            let li = model.locks.iter().position(|x| x.name == l.name).expect("lock present");
            out.push_str(&format!(
                "example : ((gS.orte {}).elem (.inr {}) = true) := by decide\n",
                lock_ctor(model, li),
                glob_ctor(model, *g)
            ));
            out.push_str(&format!(
                "example : ((gD.gbraucht {}).elem (Sum.inl {}) = true) := by decide\n",
                glob_ctor(model, *g),
                lock_ctor(model, li)
            ));
        }
    }
    out.push('\n');
    // The declared initial memory `gSp0` (lane 198): the zero memory --
    // every slot at zero (`false` for `bool`), no globals -- as the loader
    // establishes it (`Laufzeit.lader`). `check_sp0` refused every integer
    // field whose range holds no zero, so each `by decide` below closes.
    out.push_str("-- The declared initial memory (`Speicher gD`): every slot at zero,\n");
    out.push_str("-- every global at its DECLARED initialiser (a `static` names one).\n");
    // **Both halves stand PARENTHESIZED, and that is a measured necessity.**
    // `⟨fun t => nomatch t, (fun g => nomatch g)⟩` does not parse as two
    // fields: `nomatch` takes a COMMA-SEPARATED list of discriminants, so the
    // second half is swallowed and Lean reports "only 1 was provided". Every
    // table-less export carried that since `gSp0` was introduced (lane 198),
    // and no run had compiled one -- found 2026-09-15 by compiling every
    // export with `lake env lean`. *An export that does not typecheck is a
    // refusal the exporter failed to make.*
    let slots = if model.tables.is_empty() {
        "fun t => nomatch t".to_string()
    } else {
        let mut arme = Vec::new();
        for t in model.tables.iter() {
            for f in &t.fields {
                let wert = match &f.ty {
                    VTy::Bool => "false".to_string(),
                    // A `tagged` slot starts at case 0, payload zero
                    // (`check_sp0` refused a first case whose range misses it).
                    VTy::Sum { cases, .. } => match cases[0].1 {
                        None => "⟨⟨0, by decide⟩, ()⟩".to_string(),
                        Some(_) => "⟨⟨0, by decide⟩, ⟨0, by decide, by decide⟩⟩".to_string(),
                    },
                    _ => "⟨0, by decide, by decide⟩".to_string(),
                };
                arme.push(format!("| .{}, .{} => {wert}", t.name, f.name));
            }
        }
        format!("fun t _ f => match t, f with {}", arme.join(" "))
    };
    let globs = if model.globs.is_empty() {
        "fun g => nomatch g".to_string()
    } else {
        let arme: Vec<String> = model.globs.iter().map(|g| {
            let wert = match g.init {
                GInit::Bool(b) => b.to_string(),
                GInit::Int(n) => format!("⟨{}, by decide, by decide⟩", int_num(n)),
                GInit::Sum { case, payload } => match payload {
                    None => format!("⟨⟨{case}, by decide⟩, ()⟩"),
                    Some(n) => format!("⟨⟨{case}, by decide⟩, ⟨{}, by decide, by decide⟩⟩", int_num(n)),
                },
            };
            format!("| .{} => {wert}", g.name)
        }).collect();
        format!("fun {}", arme.join(" "))
    };
    out.push_str(&format!("def gSp0 : Speicher gD :=\n  ⟨({slots}), ({globs})⟩\n\n"));
    // The program as ONE declaration (lane 198): the code with its
    // contracts (`gP`), the lock invariants (`gS`), the axioms' declared
    // ensures (no axiom exists: `fun _ _ _ => true`, the `axWahr` shape),
    // the declared starts with their arguments (`gE.starts`: every start
    // is parameterless, its argument list `.nil`) and the declared initial
    // memory (`gSp0`) -- exactly the `Einheit` the goal theorem quantifies
    // over (`GabbroZiel`, `Zielsatz/Spec.lean`).
    let startet_terme: Vec<String> = startet.iter()
        .map(|i| format!("⟨g_{}, .nil⟩", lean_fn(&fns[*i].name)))
        .collect();
    out.push_str("def gE : Zielsatz.Einheit gD where\n");
    out.push_str("  P := gP\n");
    out.push_str("  S := gS\n");
    out.push_str("  Q := fun _ _ _ => true\n");
    out.push_str(&format!("  starts := [{}]\n", startet_terme.join(", ")));
    out.push_str("  sp0 := gSp0\n\n");
    out.push_str(&format!("end {ns}\n\nend Gabbro.Grammatik\n"));
    Ok(out)
}

/// A Gabbro function name as a Lean name: verbatim (names travel, they are
/// not pretty-printed).
fn lean_fn(name: &str) -> String {
    name.to_string()
}
