//! **The working Rust compiler path that mirrors the proved Lean pipeline.**
//!
//! Rust mirror of `grammatik/Grammatik/X86/Pipeline.lean` (`PipeCfg`,
//! `senkTief`, `senkWertT`, `senkBedT`, `senkPruef`, `senkStmt`, `senkBlock`
//! (including its `ite` case), `optimise`, `compileProg`, `compile`,
//! `decodeAll`, `datenGetrennt`, `validate`),
//! `PipelineImage.lean` (`Platz`/`layoutVon`, `grundListe`, `ohneDoppel`,
//! `stubBytes`, `slotByte`, `codeAbschnittP`, `stubAbschnitte`,
//! `datenAbschnitte`, `baueBildP`, `bildFuer`/`bildFuerP`, `bauOk`) and
//! `PipelineEntry.lean` (`prologPaare`, `prolog`, `prologOk`), over a small
//! Rust input model of the Lean fragment (§1).
//!
//! **Rust produces candidates; Lean decides.** Nothing here is on the trust
//! path. The Lean `validate` recomputes the program from the source and the
//! certificates and accepts the candidate bytes only if they ARE its
//! encoding; `imageOk`/`weltOk`/`prologImageOk` re-decide the image over the
//! existing loader. The theorems `pipeline_correct_loaded`,
//! `kompiliert_geladen`, `pipeline_correct_entry` and friends speak about
//! what Lean accepted, never about this file. The golden cross-check
//! (`pipeline_golden.rs`) pins Rust bytes and images to Lean's own
//! computation for every witness program and poison probe.
//!
//! Reused, not duplicated:
//! * the optimiser certificates, their order/pass check and the oracle
//!   (`const_int`, `fold_bool`, `drop_check_ok`, `apply_stmt`,
//!   `apply_block`, `optimise`) from [`super::opt`] -- the only rewrite this
//!   file performs itself is `foldInt` on the `weiter`-carrying model
//!   (`opt.rs` erases `weiter`, so its `fold_int` cannot produce Lean's
//!   `.weiter (.lit v)`), and it computes the constant with `opt::const_int`;
//! * `lower.rs`'s `int_wort` (modular integer-to-word conversion); the
//!   one-level fragment lowering `senkFrag`/`senkAtom` it also carries is
//!   superseded here by the arbitrary-depth [`senk_tief`]/[`senk_vergleich`]
//!   (Lean's `ExpressionLoweringDeep.senkTief`/`senkVergleich`), which
//!   produce the SAME code at depth one (Lean `senkWert_als_tief`/
//!   `senkBed_als_tief`);
//! * the canonical encoder/decoder from [`super::codec`].
//!
//! ## The input model and its one adapter
//!
//! `opt.rs`'s `IExpr` erases the Lean `.weiter` constructor (a widening is a
//! re-typed node there). The lowering is NOT blind to `weiter`: [`senk_tief`]
//! strips it at every depth, and the optimiser's fold produces one. So this
//! file carries its own integer/boolean expression
//! model ([`IntExpr`], [`BoolExpr`]) WITH `weiter`, and one adapter
//! ([`to_opt_int`], [`to_opt_bool`], [`to_opt_block`]) that erases it for
//! the oracle. Statements and blocks outside the lowered fragment are
//! carried as `opt::Stmt`/`opt::Block` values (`Stmt::Other`,
//! `Block::Other`), on which certificates act through `opt.rs` and which
//! every lowering refuses, exactly like the Lean `_ => none` arms.
//!
//! ## CUTS (exactly what is NOT here)
//!
//! * No proof. Equality with Lean is TESTED on the golden cases
//!   (`pipeline_golden.rs`), not proved for every input.
//! * The input model is NOT the typed Lean syntax: a [`Program`] can be
//!   ill-typed. [`typ_ok_block`] re-checks the typing facts this file reads
//!   (literal ranges, variable ranges against the context, `weiter` only
//!   widens, operator result ranges) and [`compile_to_image`] refuses an
//!   ill-typed program; the store's value type against the slot type, the
//!   index type against the table count and the contract (`gruende`,
//!   `schreibt`) are NOT re-checked (Lean cannot even state such a program).
//! * Integer arithmetic of ranges and constants is `i128`; Lean's `Int` and
//!   `Nat` are unbounded. Range constructors saturate, `opt::const_int`
//!   refuses on overflow, and address arithmetic that leaves `u128` refuses
//!   ([`Refusal::Arithmetic`]): Rust may refuse where Lean accepts, it never
//!   accepts what Lean's own recomputation would not produce.
//! * Expression operators beyond `+ - neg *` (div, rem, bit operations,
//!   shifts, floats, slot reads with a real index) are not modelled
//!   individually; [`IntKind::Read`]/[`IntKind::Opaque`] stand for them
//!   (never folded, never lowered).
//! * `imageOk`, `weltOk`, `valX86`, the loader `geladen` and
//!   `prologImageOk` are NOT mirrored: they are Lean's verdict on the image
//!   this file builds. [`compile_to_image`] demands the decided builder side
//!   conditions [`bau_ok`] (Lean `bauOk`), under which Lean's
//!   `bildFuerP_ok`/`kompiliert_geladen` PROVE that verdict for Lean's own
//!   image; Rust's image equals it on the golden cases.
//! * No relocation, no parametric load bias (`Modus::Fest` only), no
//!   entry admission (`eintrittOk`), no executable file format (see
//!   `elf.rs` for the documented container layout).

use super::codec::{decode, encode};
use super::lower::int_wort;
use super::opt::{self, BlockCert, ExprCert, PassKind, Range, StmtCert};
use super::typen::{Bedingung, Befehl, Byte, Disp32, Register};

// =============================================================================
// §1. The input model
// =============================================================================

/// The type of a table field (Lean `Ty`, as far as this pipeline reads it).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FeldTyp {
    /// `.int lo hi`.
    Int(Range),
    /// `.bool`.
    Bool,
    /// Every other type (sum, option, float, pointer, ...).
    Andere,
}

/// One table of the declaration: its row count and field types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Tabelle {
    pub count: i128,
    pub felder: Vec<FeldTyp>,
}

/// The declaration (Lean `Deklaration`, its tables only). Tables and fields
/// are numbered in order.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Deklaration {
    pub tabellen: Vec<Tabelle>,
}

impl Deklaration {
    /// `D.typ t f`; `None` for a table or field that does not exist.
    pub fn typ(&self, t: usize, f: usize) -> Option<FeldTyp> {
        self.tabellen.get(t)?.felder.get(f).copied()
    }
}

/// An integer source expression, carrying its type range (the Lean index
/// `.int lo hi`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntExpr {
    pub range: Range,
    pub kind: IntKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IntKind {
    /// `.lit n` (type `.int n n`).
    Lit(i128),
    /// `.var x`, `x` the position in the context (`varIdx`).
    Var(u32),
    /// `.weiter h1 h2 e`: the same number at a wider type.
    Weiter(Box<IntExpr>),
    Add(Box<IntExpr>, Box<IntExpr>),
    Sub(Box<IntExpr>, Box<IntExpr>),
    Neg(Box<IntExpr>),
    Mul(Box<IntExpr>, Box<IntExpr>),
    /// A slot/global read: logs a read event, never constant.
    Read,
    /// Anything else: conservative, reads something, never folded.
    Opaque,
}

fn sat_min4(a: i128, b: i128, c: i128, d: i128) -> i128 {
    a.min(b).min(c).min(d)
}
fn sat_max4(a: i128, b: i128, c: i128, d: i128) -> i128 {
    a.max(b).max(c).max(d)
}

#[allow(clippy::should_implement_trait)]
impl IntExpr {
    /// `.lit n`.
    pub fn lit(n: i128) -> Self {
        IntExpr {
            range: Range::point(n),
            kind: IntKind::Lit(n),
        }
    }
    /// `.var x` at the variable's declared range.
    pub fn var(idx: u32, range: Range) -> Self {
        IntExpr {
            range,
            kind: IntKind::Var(idx),
        }
    }
    /// `.weiter`: re-type at `range` (checked by [`typ_ok_int`]).
    pub fn weiter(range: Range, e: IntExpr) -> Self {
        IntExpr {
            range,
            kind: IntKind::Weiter(Box::new(e)),
        }
    }
    /// `.add a b` at `.int (l1 + l2) (h1 + h2)`.
    pub fn add(a: IntExpr, b: IntExpr) -> Self {
        let range = Range::new(
            a.range.lo.saturating_add(b.range.lo),
            a.range.hi.saturating_add(b.range.hi),
        );
        IntExpr {
            range,
            kind: IntKind::Add(Box::new(a), Box::new(b)),
        }
    }
    /// `.sub a b` at `.int (l1 - h2) (h1 - l2)`.
    pub fn sub(a: IntExpr, b: IntExpr) -> Self {
        let range = Range::new(
            a.range.lo.saturating_sub(b.range.hi),
            a.range.hi.saturating_sub(b.range.lo),
        );
        IntExpr {
            range,
            kind: IntKind::Sub(Box::new(a), Box::new(b)),
        }
    }
    /// `.neg a` at `.int (-hi) (-lo)`.
    pub fn neg(a: IntExpr) -> Self {
        let range = Range::new(a.range.hi.saturating_neg(), a.range.lo.saturating_neg());
        IntExpr {
            range,
            kind: IntKind::Neg(Box::new(a)),
        }
    }
    /// `.mul a b` at the min/max of the four corner products.
    pub fn mul(a: IntExpr, b: IntExpr) -> Self {
        let (l1, h1, l2, h2) = (a.range.lo, a.range.hi, b.range.lo, b.range.hi);
        let p = [
            l1.saturating_mul(l2),
            l1.saturating_mul(h2),
            h1.saturating_mul(l2),
            h1.saturating_mul(h2),
        ];
        let range = Range::new(
            sat_min4(p[0], p[1], p[2], p[3]),
            sat_max4(p[0], p[1], p[2], p[3]),
        );
        IntExpr {
            range,
            kind: IntKind::Mul(Box::new(a), Box::new(b)),
        }
    }
    pub fn read(range: Range) -> Self {
        IntExpr {
            range,
            kind: IntKind::Read,
        }
    }
    pub fn opaque(range: Range) -> Self {
        IntExpr {
            range,
            kind: IntKind::Opaque,
        }
    }
}

/// A boolean source expression (Lean `Expr D Γ Λ .bool`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BoolExpr {
    Wahr,
    Falsch,
    Lt(IntExpr, IntExpr),
    Le(IntExpr, IntExpr),
    Eq(IntExpr, IntExpr),
    Und(Box<BoolExpr>, Box<BoolExpr>),
    Oder(Box<BoolExpr>, Box<BoolExpr>),
    Nicht(Box<BoolExpr>),
    /// Float comparisons, register predicates, ...: reads, never decided.
    Opaque,
}

/// A statement. Only `assignSlot` is spelled out; every other statement is
/// carried as an `opt.rs` statement (certificates still reach it, the
/// lowering refuses it).
#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    /// `.assignSlot t f i e`: table `t`, field `f`, row index `i`, value `e`.
    AssignSlot {
        t: usize,
        f: usize,
        index: IntExpr,
        value: IntExpr,
    },
    /// `.ite cnd t e`: a two-branch conditional whose condition is a deep
    /// comparison and whose branches are lowered blocks in the same
    /// fragment, recursively.
    Ite {
        cond: BoolExpr,
        then_: Box<Block>,
        else_: Box<Block>,
    },
    Other(opt::Stmt),
}

/// The `else` of a check (Lean `Endblock`): a bare reason, or anything else.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sonst {
    /// `.retGrund r`.
    RetGrund(u32),
    /// `ret`, `leave`, statements in the `else`, ...
    Andere,
}

/// A block. `nil`, `cons` and `pruefung` are spelled out; every other block
/// form (`bind`, `narrow`, calls, gates, `leave`, ...) is carried as an
/// `opt.rs` block. Do not wrap a `nil`/`cons`/`pruefung` in `Other`: an
/// `Other` block always refuses, as the Lean wildcard arms do for the forms
/// it stands for.
#[derive(Debug, Clone, PartialEq)]
pub enum Block {
    Nil,
    Cons(Stmt, Box<Block>),
    Pruefung {
        cond: BoolExpr,
        sonst: Sonst,
        rest: Box<Block>,
    },
    Other(opt::Block),
}

impl Block {
    pub fn cons(s: Stmt, rest: Block) -> Self {
        Block::Cons(s, Box::new(rest))
    }
    pub fn pruefung(cond: BoolExpr, sonst: Sonst, rest: Block) -> Self {
        Block::Pruefung {
            cond,
            sonst,
            rest: Box::new(rest),
        }
    }
}

/// One placed source slot `(t, k, f)` at byte address `a` (Lean `Platz`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Platz {
    pub t: usize,
    pub k: i128,
    pub f: usize,
    pub a: u128,
}

/// The layout of a placement list: the address of the FIRST placement that
/// names the slot (Lean `layoutVon`).
pub fn layout_von(ps: &[Platz], t: usize, k: i128, f: usize) -> Option<u128> {
    ps.iter()
        .find(|p| p.t == t && p.k == k && p.f == f)
        .map(|p| p.a)
}

/// The initial source world on the slots the image represents: the value
/// of `(t, k, f)`. Lean's `World` is total; here a slot the image needs and
/// the world does not name is a refusal ([`Refusal::Welt`]).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Welt {
    pub werte: Vec<((usize, i128, usize), i128)>,
}

impl Welt {
    pub fn wert(&self, t: usize, k: i128, f: usize) -> Option<i128> {
        self.werte
            .iter()
            .find(|(key, _)| *key == (t, k, f))
            .map(|(_, v)| *v)
    }
}

/// One computed table extent (Lean `TableLayout.TabLayout`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TabLayout {
    pub tab: u128,
    pub basis: u128,
    pub len: u128,
    pub ausr: u128,
}

/// The address profile (Lean `Profil`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Profil {
    P48,
    P57,
}

impl Profil {
    pub fn breite(self) -> u32 {
        match self {
            Profil::P48 => 48,
            Profil::P57 => 57,
        }
    }
}

/// The target configuration of one lowering (Lean `PipeCfg`), every Nat a
/// `u128`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PipeCfg {
    /// Register of the `i`-th context variable.
    pub regs: Vec<Register>,
    /// Value register.
    pub dst: Register,
    /// Scratch register.
    pub tmp: Register,
    /// Address register for slot stores.
    pub adr: Register,
    /// First code byte.
    pub code_base: u128,
    /// Refusal exits: reason `r` exits at `exit_base + exit_stride * r`.
    pub exit_base: u128,
    /// Distance between the exits of consecutive reasons (Lean default 1).
    pub exit_stride: u128,
    /// Further scratch registers for arbitrary-depth values and checks
    /// ([`senk_tief`]): the deep lowering works over the register stack
    /// `tmp :: frei`. The default `[]` keeps exactly the original
    /// one-level fragment's register budget (`tmp` alone).
    pub frei: Vec<Register>,
}

/// Everything [`compile_to_image`] needs besides the configuration.
#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub decl: Deklaration,
    /// The context `Γ`: the range of each variable, in order.
    pub ctx: Vec<Range>,
    pub block: Block,
    /// The optimiser certificates. `None`: produce them with
    /// `opt::optimise` over the erased block.
    pub certs: Option<Vec<(PassKind, BlockCert)>>,
    pub placements: Vec<Platz>,
    pub welt: Welt,
    pub extents: Vec<TabLayout>,
    pub profil: Profil,
    /// The parameter ABI of the entry sequence (`PipelineEntry.prolog`);
    /// `None`: no entry sequence (`bildFuer`).
    pub abi: Option<Vec<Register>>,
}

/// Why the compiler refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Refusal {
    /// The program is not well typed in the sense of [`typ_ok_block`].
    IllTyped,
    /// `cfgOk` is false: working registers clash or are `rsp`.
    Config,
    /// `senkBlock` refuses (unsupported form, unplaced or non-integer slot,
    /// a check outside the signed window, an unreachable exit, ...).
    Lowering,
    /// A written slot lies inside the code region (`datenGetrennt`).
    DataOverCode,
    /// The produced bytes do not decode back (never expected).
    Candidate,
    /// `prologOk` is false.
    Prologue,
    /// `bauOk` is false.
    Layout,
    /// The world misses a placed integer slot, or holds a value outside its
    /// type.
    Welt,
    /// Address arithmetic left `u128`.
    Arithmetic,
}

// =============================================================================
// §2. The adapter to `opt.rs` and the typing re-check
// =============================================================================

/// Erase `weiter` (a re-typed node in `opt.rs`).
pub fn to_opt_int(e: &IntExpr) -> opt::IExpr {
    let b = |x: &IntExpr| Box::new(to_opt_int(x));
    let kind = match &e.kind {
        IntKind::Lit(n) => opt::IKind::Lit(*n),
        IntKind::Var(i) => opt::IKind::Var(*i),
        IntKind::Weiter(inner) => return to_opt_int(inner).widen(e.range),
        IntKind::Add(a, c) => opt::IKind::Add(b(a), b(c)),
        IntKind::Sub(a, c) => opt::IKind::Sub(b(a), b(c)),
        IntKind::Neg(a) => opt::IKind::Neg(b(a)),
        IntKind::Mul(a, c) => opt::IKind::Mul(b(a), b(c)),
        IntKind::Read => opt::IKind::SlotRead,
        IntKind::Opaque => opt::IKind::Opaque,
    };
    opt::IExpr {
        range: e.range,
        kind,
    }
}

pub fn to_opt_bool(e: &BoolExpr) -> opt::BExpr {
    let b = |x: &BoolExpr| Box::new(to_opt_bool(x));
    match e {
        BoolExpr::Wahr => opt::BExpr::Wahr,
        BoolExpr::Falsch => opt::BExpr::Falsch,
        BoolExpr::Lt(x, y) => opt::BExpr::Lt(to_opt_int(x), to_opt_int(y)),
        BoolExpr::Le(x, y) => opt::BExpr::Le(to_opt_int(x), to_opt_int(y)),
        BoolExpr::Eq(x, y) => opt::BExpr::Eq(to_opt_int(x), to_opt_int(y)),
        BoolExpr::Und(x, y) => opt::BExpr::Und(b(x), b(y)),
        BoolExpr::Oder(x, y) => opt::BExpr::Oder(b(x), b(y)),
        BoolExpr::Nicht(x) => opt::BExpr::Nicht(b(x)),
        BoolExpr::Opaque => opt::BExpr::Opaque,
    }
}

pub fn to_opt_stmt(s: &Stmt) -> opt::Stmt {
    match s {
        Stmt::AssignSlot { index, value, .. } => {
            opt::Stmt::AssignSlot(to_opt_int(index), to_opt_int(value))
        }
        Stmt::Ite { cond, then_, else_ } => opt::Stmt::Ite(
            to_opt_bool(cond),
            Box::new(to_opt_block(then_)),
            Box::new(to_opt_block(else_)),
        ),
        Stmt::Other(o) => o.clone(),
    }
}

/// Erase the model to the `opt.rs` block the certificate producer walks.
pub fn to_opt_block(b: &Block) -> opt::Block {
    match b {
        Block::Nil => opt::Block::Nil,
        Block::Cons(s, rest) => {
            opt::Block::Cons(Box::new(to_opt_stmt(s)), Box::new(to_opt_block(rest)))
        }
        Block::Pruefung { cond, rest, .. } => {
            opt::Block::Pruefung(to_opt_bool(cond), Box::new(to_opt_block(rest)))
        }
        Block::Other(o) => o.clone(),
    }
}

/// The typing facts this file reads, re-checked: literal ranges are points,
/// variables carry their context range, `weiter` only widens, operators
/// carry their Lean result range (exactly, so no saturation happened).
pub fn typ_ok_int(ctx: &[Range], e: &IntExpr) -> bool {
    let r = e.range;
    match &e.kind {
        IntKind::Lit(n) => r == Range::point(*n),
        IntKind::Var(i) => ctx.get(*i as usize) == Some(&r),
        IntKind::Weiter(inner) => {
            typ_ok_int(ctx, inner) && r.lo <= inner.range.lo && inner.range.hi <= r.hi
        }
        IntKind::Add(a, b) => {
            typ_ok_int(ctx, a)
                && typ_ok_int(ctx, b)
                && a.range.lo.checked_add(b.range.lo) == Some(r.lo)
                && a.range.hi.checked_add(b.range.hi) == Some(r.hi)
        }
        IntKind::Sub(a, b) => {
            typ_ok_int(ctx, a)
                && typ_ok_int(ctx, b)
                && a.range.lo.checked_sub(b.range.hi) == Some(r.lo)
                && a.range.hi.checked_sub(b.range.lo) == Some(r.hi)
        }
        IntKind::Neg(a) => {
            typ_ok_int(ctx, a)
                && a.range.hi.checked_neg() == Some(r.lo)
                && a.range.lo.checked_neg() == Some(r.hi)
        }
        IntKind::Mul(a, b) => {
            let (l1, h1, l2, h2) = (a.range.lo, a.range.hi, b.range.lo, b.range.hi);
            let ps = [
                l1.checked_mul(l2),
                l1.checked_mul(h2),
                h1.checked_mul(l2),
                h1.checked_mul(h2),
            ];
            typ_ok_int(ctx, a) && typ_ok_int(ctx, b) && ps.iter().all(Option::is_some) && {
                let v: Vec<i128> = ps.iter().map(|p| p.unwrap_or(0)).collect();
                sat_min4(v[0], v[1], v[2], v[3]) == r.lo && sat_max4(v[0], v[1], v[2], v[3]) == r.hi
            }
        }
        IntKind::Read | IntKind::Opaque => r.lo <= r.hi,
    }
}

pub fn typ_ok_bool(ctx: &[Range], e: &BoolExpr) -> bool {
    match e {
        BoolExpr::Wahr | BoolExpr::Falsch | BoolExpr::Opaque => true,
        BoolExpr::Lt(a, b) | BoolExpr::Le(a, b) | BoolExpr::Eq(a, b) => {
            typ_ok_int(ctx, a) && typ_ok_int(ctx, b)
        }
        BoolExpr::Und(a, b) | BoolExpr::Oder(a, b) => typ_ok_bool(ctx, a) && typ_ok_bool(ctx, b),
        BoolExpr::Nicht(a) => typ_ok_bool(ctx, a),
    }
}

pub fn typ_ok_block(ctx: &[Range], b: &Block) -> bool {
    match b {
        Block::Nil | Block::Other(_) => true,
        Block::Cons(Stmt::AssignSlot { index, value, .. }, rest) => {
            typ_ok_int(ctx, index) && typ_ok_int(ctx, value) && typ_ok_block(ctx, rest)
        }
        Block::Cons(Stmt::Ite { cond, then_, else_ }, rest) => {
            typ_ok_bool(ctx, cond)
                && typ_ok_block(ctx, then_)
                && typ_ok_block(ctx, else_)
                && typ_ok_block(ctx, rest)
        }
        Block::Cons(Stmt::Other(_), rest) => typ_ok_block(ctx, rest),
        Block::Pruefung { cond, rest, .. } => typ_ok_bool(ctx, cond) && typ_ok_block(ctx, rest),
    }
}

// =============================================================================
// §3. The optimiser stage: Lean `applyPipeline` over the model
// =============================================================================

/// Lean `foldInt`: the constant, widened back to the SAME type
/// (`.weiter (.lit v)`), when it lies in the type.
pub fn fold_int(e: &IntExpr) -> Option<IntExpr> {
    let v = opt::const_int(&to_opt_int(e))?;
    if e.range.contains(v) {
        Some(IntExpr::weiter(e.range, IntExpr::lit(v)))
    } else {
        None
    }
}

fn apply_int(c: ExprCert, e: &IntExpr) -> Option<IntExpr> {
    match c {
        ExprCert::FoldInt => fold_int(e),
        ExprCert::FoldBool => None,
    }
}

fn apply_bool(c: ExprCert, e: &BoolExpr) -> Option<BoolExpr> {
    match c {
        ExprCert::FoldBool => match opt::fold_bool(&to_opt_bool(e))? {
            opt::BExpr::Wahr => Some(BoolExpr::Wahr),
            opt::BExpr::Falsch => Some(BoolExpr::Falsch),
            _ => None,
        },
        ExprCert::FoldInt => None,
    }
}

/// Lean `applyStmt` on the model.
pub fn apply_stmt(c: &StmtCert, s: &Stmt) -> Option<Stmt> {
    match (c, s) {
        (StmtCert::AssignSlotIndex(ec), Stmt::AssignSlot { t, f, index, value }) => {
            apply_int(*ec, index).map(|i2| Stmt::AssignSlot {
                t: *t,
                f: *f,
                index: i2,
                value: value.clone(),
            })
        }
        (StmtCert::AssignSlotValue(ec), Stmt::AssignSlot { t, f, index, value }) => {
            apply_int(*ec, value).map(|v2| Stmt::AssignSlot {
                t: *t,
                f: *f,
                index: index.clone(),
                value: v2,
            })
        }
        (StmtCert::IteCond(ec), Stmt::Ite { cond, then_, else_ }) => {
            apply_bool(*ec, cond).map(|c2| Stmt::Ite {
                cond: c2,
                then_: then_.clone(),
                else_: else_.clone(),
            })
        }
        (StmtCert::IteThen(bc), Stmt::Ite { cond, then_, else_ }) => {
            apply_block(bc, then_).map(|t2| Stmt::Ite {
                cond: cond.clone(),
                then_: Box::new(t2),
                else_: else_.clone(),
            })
        }
        (StmtCert::IteElse(bc), Stmt::Ite { cond, then_, else_ }) => {
            apply_block(bc, else_).map(|e2| Stmt::Ite {
                cond: cond.clone(),
                then_: then_.clone(),
                else_: Box::new(e2),
            })
        }
        (_, Stmt::Other(o)) => opt::apply_stmt(c, o).map(Stmt::Other),
        _ => None,
    }
}

/// Lean `applyBlock` on the model.
pub fn apply_block(c: &BlockCert, b: &Block) -> Option<Block> {
    match (c, b) {
        (BlockCert::DropCheck, Block::Pruefung { cond, rest, .. }) => {
            if opt::drop_check_ok(&to_opt_bool(cond)) {
                Some((**rest).clone())
            } else {
                None
            }
        }
        (BlockCert::CheckCond(ec), Block::Pruefung { cond, sonst, rest }) => apply_bool(*ec, cond)
            .map(|c2| Block::Pruefung {
                cond: c2,
                sonst: *sonst,
                rest: rest.clone(),
            }),
        (BlockCert::Head(sc), Block::Cons(s, rest)) => {
            apply_stmt(sc, s).map(|s2| Block::Cons(s2, rest.clone()))
        }
        (BlockCert::Rest(bc), Block::Cons(s, rest)) => {
            apply_block(bc, rest).map(|r2| Block::Cons(s.clone(), Box::new(r2)))
        }
        (BlockCert::Rest(bc), Block::Pruefung { cond, sonst, rest }) => {
            apply_block(bc, rest).map(|r2| Block::Pruefung {
                cond: cond.clone(),
                sonst: *sonst,
                rest: Box::new(r2),
            })
        }
        (_, Block::Other(o)) => opt::apply_block(c, o).map(Block::Other),
        _ => None,
    }
}

/// Lean `applyPipeline`: order check, pass-membership check, every step
/// validated.
pub fn apply_pipeline(certs: &[(PassKind, BlockCert)], b: &Block) -> Option<Block> {
    let passes: Vec<PassKind> = certs.iter().map(|(k, _)| *k).collect();
    if !(opt::admitted_order(&passes) && certs.iter().all(|(k, c)| c.fits(*k))) {
        return None;
    }
    let mut cur = b.clone();
    for (_, c) in certs {
        cur = apply_block(c, &cur)?;
    }
    Some(cur)
}

/// Lean `optimise`: the validated rewrite, or the unchanged block.
pub fn optimise(certs: &[(PassKind, BlockCert)], b: &Block) -> Block {
    apply_pipeline(certs, b).unwrap_or_else(|| b.clone())
}

/// The certificates the `opt.rs` producer proposes for the erased block.
pub fn produce_certs(b: &Block) -> Vec<(PassKind, BlockCert)> {
    opt::optimise(&to_opt_block(b))
}

// =============================================================================
// §4. The lowering: `senkWert`, `senkBed`, `senkStmt`, `senkPruef`, `senkBlock`
// =============================================================================

const ZWEI_64: u128 = 1u128 << 64;

/// Lean `natAdresse`: a Nat as a 64-bit address.
fn nat_adresse(n: u128) -> u64 {
    (n % ZWEI_64) as u64
}

/// Lean `exitAdr c g = exitBase + exitStride * g`.
pub fn exit_adr(c: &PipeCfg, g: u32) -> Option<u128> {
    c.exit_stride
        .checked_mul(u128::from(g))?
        .checked_add(c.exit_base)
}

/// Lean `abbOf`: the `i`-th variable lives in `regs[i]`, `rsp` past the list.
pub fn abb_of(c: &PipeCfg, idx: u32) -> Register {
    c.regs.get(idx as usize).copied().unwrap_or(Register::Rsp)
}

/// `List.Nodup`, restricted to `Register` (small lists, no `Hash` needed).
fn nodup(rs: &[Register]) -> bool {
    rs.iter().enumerate().all(|(i, r)| !rs[i + 1..].contains(r))
}

/// Lean `cfgOk`.
pub fn cfg_ok(c: &PipeCfg) -> bool {
    !c.regs.contains(&c.dst)
        && !c.regs.contains(&c.tmp)
        && !c.regs.contains(&c.adr)
        && c.dst != c.tmp
        && c.dst != c.adr
        && c.tmp != c.adr
        && c.dst != Register::Rsp
        && c.tmp != Register::Rsp
        && c.adr != Register::Rsp
        && nodup(&c.frei)
        && c.frei.iter().all(|r| {
            !c.regs.contains(r)
                && *r != c.dst
                && *r != c.tmp
                && *r != c.adr
                && *r != Register::Rsp
        })
}

/// Lean `encodeAll`.
pub fn encode_all(prog: &[Befehl]) -> Vec<Byte> {
    prog.iter().flat_map(encode).collect()
}

/// Lean `senkTief`: arbitrary-depth integer-expression lowering over the
/// shared scratch stack `frei`. `lit`/`var` as the one-level fragment;
/// `weiter` is a pure re-reading, stripped at EVERY depth (not just the
/// top) and costs no instruction; `add`/`sub` peel one scratch register
/// off `frei` for the right operand and recurse on BOTH operands into the
/// tail; `neg a` is lowered as `0 - a`. Every other form, and an empty
/// `frei` at a binary node, refuses with `none`.
pub fn senk_tief(
    c: &PipeCfg,
    e: &IntExpr,
    dst: Register,
    frei: &[Register],
) -> Option<Vec<Befehl>> {
    match &e.kind {
        IntKind::Lit(n) => Some(vec![Befehl::MovImm64 {
            dst,
            value: int_wort(*n),
        }]),
        IntKind::Var(i) => Some(vec![Befehl::MovReg64 {
            dst,
            src: abb_of(c, *i),
        }]),
        IntKind::Weiter(inner) => senk_tief(c, inner, dst, frei),
        IntKind::Add(a, b) => {
            let (&tmp, rest) = frei.split_first()?;
            let mut pa = senk_tief(c, a, dst, rest)?;
            pa.extend(senk_tief(c, b, tmp, rest)?);
            pa.push(Befehl::AddReg64 { dst, src: tmp });
            Some(pa)
        }
        IntKind::Sub(a, b) => {
            let (&tmp, rest) = frei.split_first()?;
            let mut pa = senk_tief(c, a, dst, rest)?;
            pa.extend(senk_tief(c, b, tmp, rest)?);
            pa.push(Befehl::SubReg64 { dst, src: tmp });
            Some(pa)
        }
        IntKind::Neg(a) => {
            let (&tmp, rest) = frei.split_first()?;
            let mut pa = senk_tief(c, a, dst, rest)?;
            pa.push(Befehl::XorReg64 { dst: tmp, src: tmp });
            pa.push(Befehl::SubReg64 { dst: tmp, src: dst });
            pa.push(Befehl::MovReg64 { dst, src: tmp });
            Some(pa)
        }
        _ => None,
    }
}

/// Lean `senkWertT`: the widened value lowering over the register stack
/// `tmp :: frei` of the configuration (`weiter` stripped at every depth
/// inside [`senk_tief`] itself, so no separate top-level strip remains
/// here).
pub fn senk_wert(c: &PipeCfg, e: &IntExpr) -> Option<Vec<Befehl>> {
    let mut frei = Vec::with_capacity(1 + c.frei.len());
    frei.push(c.tmp);
    frei.extend_from_slice(&c.frei);
    senk_tief(c, e, c.dst, &frei)
}

/// Lean `imSigned`: the range lies in the signed 64-bit window.
fn im_signed(r: Range) -> bool {
    -(1i128 << 63) <= r.lo && r.hi < (1i128 << 63)
}

/// Lean `imFensterB`: the decided range side condition of a comparison —
/// both operand TYPES lie in the signed 64-bit window; every other form
/// is refused.
fn im_fenster_b(e: &BoolExpr) -> bool {
    match e {
        BoolExpr::Lt(a, b) | BoolExpr::Le(a, b) | BoolExpr::Eq(a, b) => {
            im_signed(a.range) && im_signed(b.range)
        }
        _ => false,
    }
}

/// Lean `senkVergleich`: one comparison over arbitrary-depth operands
/// sharing the register stack, returning the condition that holds when
/// the source comparison is TRUE.
fn senk_vergleich(
    c: &PipeCfg,
    e: &BoolExpr,
    dst: Register,
    frei: &[Register],
) -> Option<(Vec<Befehl>, Bedingung)> {
    let (&tmp, rest) = frei.split_first()?;
    let (a, b, j) = match e {
        BoolExpr::Lt(a, b) => (a, b, Bedingung::L),
        BoolExpr::Le(a, b) => (a, b, Bedingung::Le),
        BoolExpr::Eq(a, b) => (a, b, Bedingung::E),
        _ => return None,
    };
    let mut code = senk_tief(c, a, dst, rest)?;
    code.extend(senk_tief(c, b, tmp, rest)?);
    code.push(Befehl::CmpReg64 { lhs: dst, rhs: tmp });
    Some((code, j))
}

/// Lean `negBed`: the x86 negation of a condition code.
fn neg_bed(j: Bedingung) -> Bedingung {
    use Bedingung::*;
    match j {
        O => No,
        No => O,
        B => Ae,
        Ae => B,
        E => Ne,
        Ne => E,
        Be => A,
        A => Be,
        S => Ns,
        Ns => S,
        P => Np,
        Np => P,
        L => Ge,
        Ge => L,
        Le => G,
        G => Le,
    }
}

/// Lean `senkBedT`: deep check lowering — the comparison code and the
/// jump-to-refusal (or jump-to-else) condition, i.e. the negation of the
/// truth condition that [`senk_vergleich`] names; only `<`/`<=`/`=` with
/// both operand types in the signed 64-bit window ([`im_fenster_b`]) are
/// accepted. The literal `true` is handled by [`senk_pruef`], not here.
pub fn senk_bed_t(c: &PipeCfg, e: &BoolExpr) -> Option<(Vec<Befehl>, Bedingung)> {
    if !im_fenster_b(e) {
        return None;
    }
    let mut frei = Vec::with_capacity(1 + c.frei.len());
    frei.push(c.tmp);
    frei.extend_from_slice(&c.frei);
    let (code, j) = senk_vergleich(c, e, c.dst, &frei)?;
    Some((code, neg_bed(j)))
}

/// Lean `repOk ty base 8 0`.
fn rep_ok(ty: Option<FeldTyp>, base: u128) -> bool {
    match ty {
        Some(FeldTyp::Int(r)) => {
            0 <= r.lo && r.hi < (1i128 << 64) && base.checked_add(8).is_some_and(|e| e <= ZWEI_64)
        }
        _ => false,
    }
}

/// Lean `senkStmt`: a store to a placed integer slot at a constant index.
pub fn senk_stmt(c: &PipeCfg, decl: &Deklaration, ps: &[Platz], s: &Stmt) -> Option<Vec<Befehl>> {
    match s {
        Stmt::AssignSlot { t, f, index, value } => {
            let k = opt::const_int(&to_opt_int(index))?;
            let a = layout_von(ps, *t, k, *f)?;
            if !rep_ok(decl.typ(*t, *f), a) {
                return None;
            }
            let mut p = senk_wert(c, value)?;
            p.push(Befehl::MovImm64 {
                dst: c.adr,
                value: nat_adresse(a),
            });
            p.push(Befehl::Store64 {
                base: c.adr,
                src: c.dst,
                disp: Disp32::von_bits(0),
            });
            Some(p)
        }
        // `senkStmt`'s wildcard arm: an `ite` is lowered by `senk_block`
        // directly (it needs the byte POSITION to compute its jumps), not
        // by `senkStmt`, exactly as the Lean `senkStmt` pattern match
        // never reaches a `.ite`.
        Stmt::Ite { .. } | Stmt::Other(_) => None,
    }
}

/// Lean `sprungDisp`: `BitVec.ofInt 32 (ziel - (codeBase + posJ + 6))`.
pub fn sprung_disp(c: &PipeCfg, pos_j: u128, ziel: u128) -> Option<Disp32> {
    let von = c.code_base.checked_add(pos_j)?.checked_add(6)?;
    let diff = i128::try_from(ziel)
        .ok()?
        .checked_sub(i128::try_from(von).ok()?)?;
    Some(Disp32::von_bits(diff.rem_euclid(1i128 << 32) as u32))
}

/// Lean `senkPruef`: the condition code and the jump to the reason's exit,
/// RE-CHECKED against the exit address (mod 2^64); `true` lowers to nothing.
pub fn senk_pruef(c: &PipeCfg, pos: u128, cond: &BoolExpr, sonst: Sonst) -> Option<Vec<Befehl>> {
    let r = match sonst {
        Sonst::RetGrund(r) => r,
        Sonst::Andere => return None,
    };
    if *cond == BoolExpr::Wahr {
        return Some(Vec::new());
    }
    let (mut code, j) = senk_bed_t(c, cond)?;
    let pos_j = pos.checked_add(encode_all(&code).len() as u128)?;
    let ziel = exit_adr(c, r)?;
    let disp = sprung_disp(c, pos_j, ziel)?;
    let sprung = Befehl::JumpIf32 { cond: j, disp };
    let nach = c
        .code_base
        .checked_add(pos_j)?
        .checked_add(encode(&sprung).len() as u128)?;
    let erreicht = (nach % ZWEI_64).wrapping_add(u128::from(disp.extended() as u64)) % ZWEI_64;
    if erreicht == ziel % ZWEI_64 {
        code.push(sprung);
        Some(code)
    } else {
        None
    }
}

/// Lean `sprungOk`: a forward jump of `k` bytes is representable as a
/// 32-bit displacement (`k < 2^31`, so the sign-extended read equals `k`).
fn sprung_ok(k: u128) -> bool {
    k < (1u128 << 31)
}

/// Lean `senkBlock` from byte position `pos` of the code region.
pub fn senk_block(
    c: &PipeCfg,
    decl: &Deklaration,
    ps: &[Platz],
    pos: u128,
    b: &Block,
) -> Option<Vec<Befehl>> {
    match b {
        Block::Nil => Some(Vec::new()),
        // `ite`: condition, jump on the NEGATED condition over the
        // then-block, then-block, jump over the else-block, else-block —
        // every displacement computed from the REAL byte position and
        // then re-checked representable (Lean `iteCode`/`sprungOk`).
        Block::Cons(Stmt::Ite { cond, then_, else_ }, rest) => {
            let (code, j) = senk_bed_t(c, cond)?;
            let pos_t = pos
                .checked_add(encode_all(&code).len() as u128)?
                .checked_add(6)?;
            let pt = senk_block(c, decl, ps, pos_t, then_)?;
            let pos_e = pos_t
                .checked_add(encode_all(&pt).len() as u128)?
                .checked_add(5)?;
            let pe = senk_block(c, decl, ps, pos_e, else_)?;
            let pt_jump = (encode_all(&pt).len() as u128).checked_add(5)?;
            let pe_len = encode_all(&pe).len() as u128;
            if !(sprung_ok(pt_jump) && sprung_ok(pe_len)) {
                return None;
            }
            let mut ite = code;
            ite.push(Befehl::JumpIf32 {
                cond: j,
                disp: Disp32::von_bits(pt_jump as u32),
            });
            ite.extend(pt);
            ite.push(Befehl::Jump32 {
                disp: Disp32::von_bits(pe_len as u32),
            });
            ite.extend(pe);
            let weiter = pos.checked_add(encode_all(&ite).len() as u128)?;
            ite.extend(senk_block(c, decl, ps, weiter, rest)?);
            Some(ite)
        }
        Block::Cons(s, rest) => {
            let mut p = senk_stmt(c, decl, ps, s)?;
            let weiter = pos.checked_add(encode_all(&p).len() as u128)?;
            p.extend(senk_block(c, decl, ps, weiter, rest)?);
            Some(p)
        }
        Block::Pruefung { cond, sonst, rest } => {
            let mut p = senk_pruef(c, pos, cond, *sonst)?;
            let weiter = pos.checked_add(encode_all(&p).len() as u128)?;
            p.extend(senk_block(c, decl, ps, weiter, rest)?);
            Some(p)
        }
        Block::Other(_) => None,
    }
}

/// Lean `compileProg`: optimise, then lower from the start of the code.
pub fn compile_prog(
    c: &PipeCfg,
    decl: &Deklaration,
    ps: &[Platz],
    certs: &[(PassKind, BlockCert)],
    src: &Block,
) -> Option<Vec<Befehl>> {
    if cfg_ok(c) {
        senk_block(c, decl, ps, 0, &optimise(certs, src))
    } else {
        None
    }
}

/// Lean `compile`: source block to code bytes.
pub fn compile(
    c: &PipeCfg,
    decl: &Deklaration,
    ps: &[Platz],
    certs: &[(PassKind, BlockCert)],
    src: &Block,
) -> Option<Vec<Byte>> {
    compile_prog(c, decl, ps, certs, src).map(|p| encode_all(&p))
}

/// Lean `decodeAll fuel bytes` with the independent decoder.
pub fn decode_all(fuel: usize, bytes: &[Byte]) -> Option<Vec<Befehl>> {
    let mut out = Vec::new();
    let mut rest = bytes;
    let mut fuel = fuel;
    while !rest.is_empty() {
        if fuel == 0 {
            return None;
        }
        fuel -= 1;
        let d = decode(rest)?;
        let n = usize::try_from(d.laenge).ok()?;
        if n == 0 || n > rest.len() {
            return None;
        }
        out.push(d.befehl);
        rest = &rest[n..];
    }
    Some(out)
}

/// Lean `slotAdressen`: the slot addresses a block writes.
pub fn slot_adressen(ps: &[Platz], b: &Block) -> Vec<u128> {
    match b {
        Block::Nil | Block::Other(_) => Vec::new(),
        Block::Cons(s, rest) => {
            let mut v: Vec<u128> = match s {
                Stmt::AssignSlot { t, f, index, .. } => opt::const_int(&to_opt_int(index))
                    .and_then(|k| layout_von(ps, *t, k, *f))
                    .into_iter()
                    .collect(),
                Stmt::Ite { then_, else_, .. } => {
                    let mut v = slot_adressen(ps, then_);
                    v.extend(slot_adressen(ps, else_));
                    v
                }
                Stmt::Other(_) => Vec::new(),
            };
            v.extend(slot_adressen(ps, rest));
            v
        }
        Block::Pruefung { rest, .. } => slot_adressen(ps, rest),
    }
}

/// Lean `datenGetrennt`: every written slot lies off `[codeBase, codeBase + len)`.
pub fn daten_getrennt(c: &PipeCfg, ps: &[Platz], b: &Block, len: u128) -> bool {
    slot_adressen(ps, b)
        .iter()
        .all(|&a| a.saturating_add(8) <= c.code_base || c.code_base.saturating_add(len) <= a)
}

/// Lean `validate`, mirrored (the Lean one is the authority).
pub fn validate(
    c: &PipeCfg,
    decl: &Deklaration,
    ps: &[Platz],
    certs: &[(PassKind, BlockCert)],
    src: &Block,
    bytes: &[Byte],
) -> bool {
    match compile_prog(c, decl, ps, certs, src) {
        Some(prog) => {
            bytes == encode_all(&prog).as_slice()
                && decode_all(bytes.len(), bytes).as_deref() == Some(prog.as_slice())
                && daten_getrennt(c, ps, &optimise(certs, src), bytes.len() as u128)
        }
        None => false,
    }
}

// =============================================================================
// §5. The entry sequence (`PipelineEntry.lean`)
// =============================================================================

/// The System V integer parameter registers, in order (`sysvParameter`).
pub const SYSV_PARAMETER: [Register; 6] = [
    Register::Rdi,
    Register::Rsi,
    Register::Rdx,
    Register::Rcx,
    Register::R8,
    Register::R9,
];

/// Lean `prologPaare`: `(regs[i], abi[i])`.
pub fn prolog_paare(c: &PipeCfg, abi: &[Register], n: usize) -> Vec<(Register, Register)> {
    (0..n)
        .map(|i| {
            (
                c.regs.get(i).copied().unwrap_or(Register::Rsp),
                abi.get(i).copied().unwrap_or(Register::Rsp),
            )
        })
        .collect()
}

/// Lean `prolog`: `mov regs[i], abi[i]`.
pub fn prolog(c: &PipeCfg, abi: &[Register], n: usize) -> Vec<Befehl> {
    prolog_paare(c, abi, n)
        .into_iter()
        .map(|(dst, src)| Befehl::MovReg64 { dst, src })
        .collect()
}

/// Lean `prologOk`: enough registers, no copy clobbers a later one, `rsp`
/// is never written.
pub fn prolog_ok(c: &PipeCfg, abi: &[Register], n: usize) -> bool {
    let qs = prolog_paare(c, abi, n);
    let paarweise = qs
        .iter()
        .enumerate()
        .all(|(i, q)| qs[i + 1..].iter().all(|r| q.0 != r.1 && q.0 != r.0));
    n <= c.regs.len() && n <= abi.len() && paarweise && qs.iter().all(|q| q.0 != Register::Rsp)
}

// =============================================================================
// §6. The image builder (`PipelineImage.lean` §§5-6, 9)
// =============================================================================

/// One section extent (Lean `Abschnitt`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Abschnitt {
    pub datei_off: u128,
    pub datei_len: u128,
    pub vaddr: u128,
    pub mem_len: u128,
    pub lesbar: bool,
    pub schreibbar: bool,
    pub ausfuehrbar: bool,
    pub ausr: u128,
}

/// The candidate image (Lean `Bild`). The builder never produces
/// relocations or a parametric mode: `reloks = []`, `modus = .fest`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bild {
    pub datei: Vec<Byte>,
    pub abschnitte: Vec<Abschnitt>,
    pub eintraege: Vec<u128>,
}

/// Lean `grundListe`: the reasons of the checks, in order.
pub fn grund_liste(b: &Block) -> Vec<u32> {
    match b {
        Block::Nil | Block::Other(_) => Vec::new(),
        Block::Cons(Stmt::Ite { then_, else_, .. }, rest) => {
            let mut v = grund_liste(then_);
            v.extend(grund_liste(else_));
            v.extend(grund_liste(rest));
            v
        }
        Block::Cons(_, rest) => grund_liste(rest),
        Block::Pruefung { sonst, rest, .. } => {
            let mut v = match sonst {
                Sonst::RetGrund(r) => vec![*r],
                Sonst::Andere => Vec::new(),
            };
            v.extend(grund_liste(rest));
            v
        }
    }
}

/// Lean `ohneDoppel`: the LAST occurrence of each reason is kept.
pub fn ohne_doppel(gs: &[u32]) -> Vec<u32> {
    gs.iter()
        .enumerate()
        .filter(|(i, g)| !gs[i + 1..].contains(g))
        .map(|(_, g)| *g)
        .collect()
}

/// Lean `stubBefehl`: `mov rax, g`.
pub fn stub_befehl(g: u32) -> Befehl {
    Befehl::MovImm64 {
        dst: Register::Rax,
        value: int_wort(i128::from(g)),
    }
}

pub fn stub_bytes(g: u32) -> Vec<Byte> {
    encode(&stub_befehl(g))
}

/// Lean `slotWort`: the representation word of an integer slot, zero for
/// every other type. `None`: the world does not name an integer slot.
fn slot_wort(decl: &Deklaration, w: &Welt, p: &Platz) -> Option<u64> {
    match decl.typ(p.t, p.f) {
        Some(FeldTyp::Int(r)) => {
            let v = w.wert(p.t, p.k, p.f)?;
            if !r.contains(v) {
                return None;
            }
            // `zahlWort v = BitVec.ofNat 64 v.n.toNat`.
            Some((v.max(0) as u128 % ZWEI_64) as u64)
        }
        _ => Some(0),
    }
}

/// Lean `slotByte`: the byte of the first placement covering `x`, else 0.
fn slot_byte(decl: &Deklaration, ps: &[Platz], w: &Welt, x: u128) -> Option<Byte> {
    match ps.iter().find(|p| p.a <= x && x < p.a.saturating_add(8)) {
        Some(p) => {
            let wort = slot_wort(decl, w, p)?;
            let i = x - p.a;
            Some(((wort >> (8 * i)) & 0xFF) as u8)
        }
        None => Some(0),
    }
}

/// Lean `datenChunk`.
fn daten_chunk(decl: &Deklaration, ps: &[Platz], w: &Welt, e: &TabLayout) -> Option<Vec<Byte>> {
    let len = usize::try_from(e.len).ok()?;
    (0..len)
        .map(|i| slot_byte(decl, ps, w, e.basis.checked_add(i as u128)?))
        .collect()
}

/// Lean `codeAbschnittP`.
pub fn code_abschnitt_p(c: &PipeCfg, pro_len: u128, code_len: u128) -> Abschnitt {
    Abschnitt {
        datei_off: 0,
        datei_len: pro_len + code_len,
        vaddr: c.code_base.saturating_sub(pro_len),
        mem_len: pro_len + code_len,
        lesbar: true,
        schreibbar: false,
        ausfuehrbar: true,
        ausr: 1,
    }
}

/// Lean `stubAbschnitte`.
pub fn stub_abschnitte(c: &PipeCfg, off: u128, gs: &[u32]) -> Option<Vec<Abschnitt>> {
    gs.iter()
        .enumerate()
        .map(|(i, &g)| {
            Some(Abschnitt {
                datei_off: off.checked_add(10 * i as u128)?,
                datei_len: 10,
                vaddr: exit_adr(c, g)?,
                mem_len: 10,
                lesbar: true,
                schreibbar: false,
                ausfuehrbar: true,
                ausr: 1,
            })
        })
        .collect()
}

/// Lean `datenAbschnitte`.
pub fn daten_abschnitte(off: u128, es: &[TabLayout]) -> Option<Vec<Abschnitt>> {
    let mut out = Vec::new();
    let mut o = off;
    for e in es {
        out.push(Abschnitt {
            datei_off: o,
            datei_len: e.len,
            vaddr: e.basis,
            mem_len: e.len,
            lesbar: true,
            schreibbar: true,
            ausfuehrbar: false,
            ausr: e.ausr,
        });
        o = o.checked_add(e.len)?;
    }
    Some(out)
}

/// Lean `baueBildP`: the entry sequence `pro` and the code in one section
/// (code at `codeBase`), one stub per listed reason, one data section per
/// extent holding the initial world. `None`: the world misses a placed
/// integer slot, or arithmetic left `u128`.
#[allow(clippy::too_many_arguments)]
pub fn baue_bild_p(
    c: &PipeCfg,
    decl: &Deklaration,
    pro: &[Byte],
    bytes: &[Byte],
    gs: &[u32],
    ps: &[Platz],
    w: &Welt,
    es: &[TabLayout],
) -> Option<Bild> {
    let pl = pro.len() as u128;
    let bl = bytes.len() as u128;
    let mut datei = Vec::new();
    datei.extend_from_slice(pro);
    datei.extend_from_slice(bytes);
    for &g in gs {
        datei.extend(stub_bytes(g));
    }
    for e in es {
        datei.extend(daten_chunk(decl, ps, w, e)?);
    }
    let mut abschnitte = vec![code_abschnitt_p(c, pl, bl)];
    abschnitte.extend(stub_abschnitte(c, pl + bl, gs)?);
    abschnitte.extend(daten_abschnitte(pl + bl + 10 * gs.len() as u128, es)?);
    Some(Bild {
        datei,
        abschnitte,
        eintraege: vec![c.code_base.saturating_sub(pl), c.code_base],
    })
}

/// Lean `bildFuerP` (and `bildFuer` with an empty `pro`): one stub for each
/// reachable reason of the OPTIMISED block.
#[allow(clippy::too_many_arguments)]
pub fn bild_fuer_p(
    c: &PipeCfg,
    decl: &Deklaration,
    pro: &[Byte],
    certs: &[(PassKind, BlockCert)],
    src: &Block,
    bytes: &[Byte],
    ps: &[Platz],
    w: &Welt,
    es: &[TabLayout],
) -> Option<Bild> {
    let gs = ohne_doppel(&grund_liste(&optimise(certs, src)));
    baue_bild_p(c, decl, pro, bytes, &gs, ps, w, es)
}

/// Lean `apartB`.
fn apart(a1: u128, l1: u128, a2: u128, l2: u128) -> bool {
    a1.saturating_add(l1) <= a2 || a2.saturating_add(l2) <= a1
}

/// Lean `halbe`.
fn halbe(p: Profil) -> u128 {
    1u128 << (p.breite() - 1)
}

/// Lean `regionDisjunkt` of two extents.
fn region_disjunkt(a_basis: u128, a_len: u128, b_basis: u128, b_len: u128) -> bool {
    apart(a_basis, a_len, b_basis, b_len)
}

/// Lean `layoutOk`: every extent nonempty, aligned, no wrap; pairwise
/// disjoint.
pub fn layout_ok(es: &[TabLayout]) -> bool {
    let eintrag_ok = |e: &TabLayout| {
        0 < e.len
            && 0 < e.ausr
            && e.basis % e.ausr == 0
            && e.basis.checked_add(e.len).is_some_and(|x| x <= ZWEI_64)
    };
    let paar_ok = es.iter().enumerate().all(|(i, e)| {
        es[i + 1..]
            .iter()
            .all(|t| region_disjunkt(e.basis, e.len, t.basis, t.len))
    });
    es.iter().all(eintrag_ok) && paar_ok
}

/// Lean `bauOk`: the decided layout side conditions of the image builder.
#[allow(clippy::too_many_arguments)]
pub fn bau_ok(
    p: Profil,
    c: &PipeCfg,
    decl: &Deklaration,
    pro: &[Byte],
    bytes: &[Byte],
    gs: &[u32],
    ps: &[Platz],
    es: &[TabLayout],
) -> bool {
    let pl = pro.len() as u128;
    let bl = bytes.len() as u128;
    let h = halbe(p);
    let start = c.code_base.saturating_sub(pl);
    let stubs_ok = gs.iter().all(|&g| match exit_adr(c, g) {
        Some(x) => {
            x.saturating_add(c.exit_stride) <= h
                && apart(x, c.exit_stride, start, pl + bl + 1)
                && es.iter().all(|e| apart(x, c.exit_stride, e.basis, e.len))
        }
        None => false,
    });
    let daten_ok = es
        .iter()
        .all(|e| e.basis.saturating_add(e.len) <= h && apart(start, pl + bl, e.basis, e.len));
    let platz_in = ps.iter().all(|q| {
        es.iter()
            .any(|e| e.basis <= q.a && q.a.saturating_add(8) <= e.basis.saturating_add(e.len))
    });
    let platz_getrennt = ps.iter().enumerate().all(|(i, a)| {
        ps[i + 1..]
            .iter()
            .all(|b| a.a.saturating_add(8) <= b.a || b.a.saturating_add(8) <= a.a)
    });
    0 < bl
        && pl <= c.code_base
        && 11 <= c.exit_stride
        && c.code_base.saturating_add(bl).saturating_add(1) <= h
        && stubs_ok
        && daten_ok
        && layout_ok(es)
        && platz_in
        && platz_getrennt
        && ps.iter().all(|q| rep_ok(decl.typ(q.t, q.f), q.a))
}

// =============================================================================
// §7. The library entry
// =============================================================================

/// A compiled, imaged program: every piece the Lean side re-decides.
#[derive(Debug, Clone, PartialEq)]
pub struct Image {
    pub bild: Bild,
    /// The lowered instruction list (Lean `compileProg`).
    pub prog: Vec<Befehl>,
    /// The code bytes (Lean `compile`).
    pub code: Vec<Byte>,
    /// The entry-sequence bytes (empty without an ABI).
    pub prolog: Vec<Byte>,
    /// The reasons with a stub (`ohneDoppel (grundListe (optimise ...))`).
    pub gruende: Vec<u32>,
    /// The certificates the optimiser stage used.
    pub certs: Vec<(PassKind, BlockCert)>,
}

/// THE COMPILER: certificates (given, or produced by `opt.rs`), then the
/// Lean optimiser stage and lowering mirrored, the validator mirrored, the
/// entry sequence, the builder side conditions `bauOk`, and the image.
/// Every refusal of the Lean path is a refusal here; additionally the
/// image is only built under `bauOk`, the condition under which Lean's
/// `kompiliert_geladen`/`bildFuerP_ok` prove `imageOk` and `weltOk`.
pub fn compile_to_image(p: &Program, c: &PipeCfg) -> Result<Image, Refusal> {
    if !typ_ok_block(&p.ctx, &p.block) {
        return Err(Refusal::IllTyped);
    }
    if !cfg_ok(c) {
        return Err(Refusal::Config);
    }
    let certs = p.certs.clone().unwrap_or_else(|| produce_certs(&p.block));
    let prog =
        compile_prog(c, &p.decl, &p.placements, &certs, &p.block).ok_or(Refusal::Lowering)?;
    let code = encode_all(&prog);
    if decode_all(code.len(), &code).as_deref() != Some(prog.as_slice()) {
        return Err(Refusal::Candidate);
    }
    let optimiert = optimise(&certs, &p.block);
    if !daten_getrennt(c, &p.placements, &optimiert, code.len() as u128) {
        return Err(Refusal::DataOverCode);
    }
    let pro = match &p.abi {
        Some(abi) => {
            if !prolog_ok(c, abi, p.ctx.len()) {
                return Err(Refusal::Prologue);
            }
            encode_all(&prolog(c, abi, p.ctx.len()))
        }
        None => Vec::new(),
    };
    let gruende = ohne_doppel(&grund_liste(&optimiert));
    if !bau_ok(
        p.profil,
        c,
        &p.decl,
        &pro,
        &code,
        &gruende,
        &p.placements,
        &p.extents,
    ) {
        return Err(Refusal::Layout);
    }
    let bild = baue_bild_p(
        c,
        &p.decl,
        &pro,
        &code,
        &gruende,
        &p.placements,
        &p.welt,
        &p.extents,
    )
    .ok_or(Refusal::Welt)?;
    Ok(Image {
        bild,
        prog,
        code,
        prolog: pro,
        gruende,
        certs,
    })
}

// =============================================================================
// §8. Unit tests (the golden cross-check with Lean is `pipeline_golden.rs`)
// =============================================================================

#[cfg(test)]
pub(crate) mod proben {
    use super::*;
    use Register::*;

    /// The witness declaration of `PipelineWitnesses.lean`: one table of two
    /// rows, one field in `0 .. 1000`.
    pub(crate) fn pw_decl() -> Deklaration {
        Deklaration {
            tabellen: vec![Tabelle {
                count: 2,
                felder: vec![FeldTyp::Int(Range::new(0, 1000))],
            }],
        }
    }

    pub(crate) fn pw_ctx() -> Vec<Range> {
        vec![Range::new(0, 100)]
    }

    pub(crate) fn pw_x() -> IntExpr {
        IntExpr::var(0, Range::new(0, 100))
    }

    pub(crate) fn idx(k: i128, count: i128) -> IntExpr {
        IntExpr::weiter(Range::new(0, count - 1), IntExpr::lit(k))
    }

    pub(crate) fn feld() -> Range {
        Range::new(0, 1000)
    }

    /// `T[0].f = x + 5; check x < 50 else reason r; T[1].f = 2 * 3;`
    pub(crate) fn pw_src(r: u32) -> Block {
        Block::cons(
            Stmt::AssignSlot {
                t: 0,
                f: 0,
                index: idx(0, 2),
                value: IntExpr::weiter(feld(), IntExpr::add(pw_x(), IntExpr::lit(5))),
            },
            Block::pruefung(
                BoolExpr::Lt(pw_x(), IntExpr::lit(50)),
                Sonst::RetGrund(r),
                Block::cons(
                    Stmt::AssignSlot {
                        t: 0,
                        f: 0,
                        index: idx(1, 2),
                        value: IntExpr::weiter(
                            feld(),
                            IntExpr::mul(IntExpr::lit(2), IntExpr::lit(3)),
                        ),
                    },
                    Block::Nil,
                ),
            ),
        )
    }

    pub(crate) fn pw_certs() -> Vec<(PassKind, BlockCert)> {
        vec![(
            PassKind::Fold,
            BlockCert::Rest(Box::new(BlockCert::Rest(Box::new(BlockCert::Head(
                Box::new(StmtCert::AssignSlotValue(ExprCert::FoldInt)),
            ))))),
        )]
    }

    pub(crate) fn pw_cfg() -> PipeCfg {
        PipeCfg {
            regs: vec![R10],
            dst: Rax,
            tmp: Rcx,
            adr: Rbx,
            code_base: 4096,
            exit_base: 12288,
            exit_stride: 1,
            frei: vec![],
        }
    }

    pub(crate) fn pi_ps() -> Vec<Platz> {
        vec![
            Platz {
                t: 0,
                k: 0,
                f: 0,
                a: 8192,
            },
            Platz {
                t: 0,
                k: 1,
                f: 0,
                a: 8200,
            },
        ]
    }

    pub(crate) fn pi_es() -> Vec<TabLayout> {
        vec![TabLayout {
            tab: 0,
            basis: 8192,
            len: 16,
            ausr: 8,
        }]
    }

    pub(crate) fn pw_welt() -> Welt {
        Welt {
            werte: vec![((0, 0, 0), 7), ((0, 1, 0), 9)],
        }
    }

    /// The untrusted candidate `pwProg` of the witness file, written out.
    fn pw_prog() -> Vec<Befehl> {
        vec![
            Befehl::MovReg64 { dst: Rax, src: R10 },
            Befehl::MovImm64 { dst: Rcx, value: 5 },
            Befehl::AddReg64 { dst: Rax, src: Rcx },
            Befehl::MovImm64 {
                dst: Rbx,
                value: 8192,
            },
            Befehl::Store64 {
                base: Rbx,
                src: Rax,
                disp: Disp32::von_bits(0),
            },
            Befehl::MovReg64 { dst: Rax, src: R10 },
            Befehl::MovImm64 {
                dst: Rcx,
                value: 50,
            },
            Befehl::CmpReg64 { lhs: Rax, rhs: Rcx },
            Befehl::JumpIf32 {
                cond: Bedingung::Ge,
                disp: Disp32::von_bits(8137),
            },
            Befehl::MovImm64 { dst: Rax, value: 6 },
            Befehl::MovImm64 {
                dst: Rbx,
                value: 8200,
            },
            Befehl::Store64 {
                base: Rbx,
                src: Rax,
                disp: Disp32::von_bits(0),
            },
        ]
    }

    #[test]
    fn witness_program_lowers_to_the_lean_candidate() {
        let prog = compile_prog(&pw_cfg(), &pw_decl(), &pi_ps(), &pw_certs(), &pw_src(0)).unwrap();
        assert_eq!(prog, pw_prog());
        let bytes = encode_all(&prog);
        assert_eq!(bytes.len(), 82); // `pw_laenge`
        assert!(validate(
            &pw_cfg(),
            &pw_decl(),
            &pi_ps(),
            &pw_certs(),
            &pw_src(0),
            &bytes
        ));
    }

    #[test]
    fn the_producer_proposes_the_witness_certificate() {
        assert_eq!(produce_certs(&pw_src(0)), pw_certs());
    }

    #[test]
    fn fold_keeps_the_weiter_lean_produces() {
        let e = IntExpr::weiter(feld(), IntExpr::mul(IntExpr::lit(2), IntExpr::lit(3)));
        assert_eq!(fold_int(&e), Some(IntExpr::weiter(feld(), IntExpr::lit(6))));
    }

    #[test]
    fn without_the_fold_nothing_is_produced() {
        // `pw_ohne_optimiser_verweigert`.
        assert_eq!(
            compile(&pw_cfg(), &pw_decl(), &pi_ps(), &[], &pw_src(0)),
            None
        );
    }

    #[test]
    fn tampered_candidates_are_refused() {
        let bytes = compile(&pw_cfg(), &pw_decl(), &pi_ps(), &pw_certs(), &pw_src(0)).unwrap();
        // `gift_byte`
        let mut b1 = bytes.clone();
        b1[1] = 0;
        assert!(!validate(
            &pw_cfg(),
            &pw_decl(),
            &pi_ps(),
            &pw_certs(),
            &pw_src(0),
            &b1
        ));
        // `gift_falscher_fold`: the immediate 6 claimed as 7.
        let mut p = pw_prog();
        p[9] = Befehl::MovImm64 { dst: Rax, value: 7 };
        assert!(!validate(
            &pw_cfg(),
            &pw_decl(),
            &pi_ps(),
            &pw_certs(),
            &pw_src(0),
            &encode_all(&p)
        ));
        // `gift_falscher_sprung`
        let mut p = pw_prog();
        p[8] = Befehl::JumpIf32 {
            cond: Bedingung::Ge,
            disp: Disp32::von_bits(0),
        };
        assert!(!validate(
            &pw_cfg(),
            &pw_decl(),
            &pi_ps(),
            &pw_certs(),
            &pw_src(0),
            &encode_all(&p)
        ));
    }

    #[test]
    fn wrong_certificates_are_refused() {
        // `gift_falsches_zertifikat`: no constant at the head.
        let falsch = vec![(
            PassKind::Fold,
            BlockCert::Head(Box::new(StmtCert::AssignSlotValue(ExprCert::FoldInt))),
        )];
        assert_eq!(apply_pipeline(&falsch, &pw_src(0)), None);
        assert_eq!(
            compile(&pw_cfg(), &pw_decl(), &pi_ps(), &falsch, &pw_src(0)),
            None
        );
        // `gift_falscher_pass`: the right rule under the wrong pass.
        let pass = vec![(PassKind::Strength, pw_certs()[0].1.clone())];
        assert_eq!(apply_pipeline(&pass, &pw_src(0)), None);
    }

    #[test]
    fn unsupported_forms_are_refused() {
        // `gift_nicht_unterstuetzt`: a variable index, a `bind`, a deep check.
        let var_idx = Block::cons(
            Stmt::AssignSlot {
                t: 0,
                f: 0,
                index: IntExpr::var(0, Range::new(0, 1)),
                value: IntExpr::weiter(Range::new(3, 3), IntExpr::lit(3)),
            },
            Block::Nil,
        );
        let bind = Block::Other(opt::Block::Bind(
            opt::IExpr::lit(1),
            Box::new(opt::Block::Nil),
        ));
        let tief = Block::pruefung(
            BoolExpr::Lt(IntExpr::add(pw_x(), IntExpr::lit(1)), IntExpr::lit(50)),
            Sonst::RetGrund(0),
            Block::Nil,
        );
        for b in [var_idx, bind, tief] {
            assert_eq!(compile(&pw_cfg(), &pw_decl(), &pi_ps(), &[], &b), None);
        }
    }

    #[test]
    fn register_clashes_are_refused() {
        // `gift_register`
        let klash = PipeCfg {
            dst: R10,
            ..pw_cfg()
        };
        let rsp = PipeCfg {
            tmp: Rsp,
            ..pw_cfg()
        };
        assert!(!cfg_ok(&klash) && !cfg_ok(&rsp));
        assert_eq!(
            compile(&klash, &pw_decl(), &pi_ps(), &pw_certs(), &pw_src(0)),
            None
        );
    }

    #[test]
    fn code_data_overlap_is_refused_by_the_validator() {
        // `gift_ueberlapp`: the compiler still produces bytes.
        let ps = vec![
            Platz {
                t: 0,
                k: 0,
                f: 0,
                a: 4100,
            },
            Platz {
                t: 0,
                k: 1,
                f: 0,
                a: 8200,
            },
        ];
        let bytes = compile(&pw_cfg(), &pw_decl(), &ps, &pw_certs(), &pw_src(0)).unwrap();
        assert!(!validate(
            &pw_cfg(),
            &pw_decl(),
            &ps,
            &pw_certs(),
            &pw_src(0),
            &bytes
        ));
    }

    #[test]
    fn an_unreachable_exit_is_refused_by_the_lowering() {
        // `gift_ferner_ausgang`
        let fern = PipeCfg {
            exit_base: 1u128 << 40,
            ..pw_cfg()
        };
        assert_eq!(
            compile(&fern, &pw_decl(), &pi_ps(), &pw_certs(), &pw_src(0)),
            None
        );
    }

    #[test]
    fn ohne_doppel_keeps_the_last_occurrence() {
        // `ohneDoppel_probe`
        assert_eq!(ohne_doppel(&[1, 0, 1, 2, 0]), vec![1, 2, 0]);
    }

    #[test]
    fn prologue_checks() {
        let c = PipeCfg {
            exit_stride: 16,
            ..pw_cfg()
        };
        assert_eq!(
            prolog(&c, &SYSV_PARAMETER, 1),
            vec![Befehl::MovReg64 { dst: R10, src: Rdi }]
        );
        assert!(prolog_ok(&c, &SYSV_PARAMETER, 1));
        // `gift_prolog_klobber`, `gift_prolog_rsp`, `gift_prolog_ohne_abi`.
        assert!(!prolog_ok(
            &PipeCfg {
                regs: vec![Rsi, Rdi],
                ..c.clone()
            },
            &SYSV_PARAMETER,
            2
        ));
        assert!(!prolog_ok(
            &PipeCfg {
                regs: vec![Rsp],
                ..c.clone()
            },
            &SYSV_PARAMETER,
            1
        ));
        assert!(!prolog_ok(&c, &[], 1));
    }

    fn pw3_programm(abi: Option<Vec<Register>>, extents: Vec<TabLayout>) -> Program {
        Program {
            decl: pw_decl(),
            ctx: pw_ctx(),
            block: Block::cons(
                Stmt::AssignSlot {
                    t: 0,
                    f: 0,
                    index: idx(0, 2),
                    value: IntExpr::weiter(feld(), IntExpr::add(pw_x(), IntExpr::lit(5))),
                },
                Block::pruefung(
                    BoolExpr::Lt(pw_x(), IntExpr::lit(60)),
                    Sonst::RetGrund(1),
                    match pw_src(0) {
                        Block::Cons(_, rest) => *rest,
                        _ => unreachable!(),
                    },
                ),
            ),
            certs: None,
            placements: pi_ps(),
            welt: pw_welt(),
            extents,
            profil: Profil::P48,
            abi,
        }
    }

    #[test]
    fn compile_to_image_builds_the_stride_witness() {
        let c = PipeCfg {
            exit_stride: 16,
            ..pw_cfg()
        };
        let img = compile_to_image(&pw3_programm(None, pi_es()), &c).unwrap();
        assert_eq!(img.code.len(), 104); // `pw3_laenge`
        assert_eq!(img.gruende, vec![1, 0]); // `pw3_gruende`
        assert_eq!(img.bild.abschnitte.len(), 4); // `pw3_bild_form`
        assert_eq!(img.bild.eintraege, vec![4096, 4096]);
        // Stubs at 12304 (reason 1) and 12288 (reason 0), `mov rax, r`.
        assert_eq!(img.bild.abschnitte[1].vaddr, 12304);
        assert_eq!(img.bild.abschnitte[2].vaddr, 12288);
        assert_eq!(&img.bild.datei[104..114], stub_bytes(1).as_slice());
        // The data section holds 7 and 9 little endian.
        assert_eq!(img.bild.datei[124], 7);
        assert_eq!(img.bild.datei[132], 9);
    }

    #[test]
    fn compile_to_image_refuses_what_lean_refuses() {
        let c = PipeCfg {
            exit_stride: 16,
            ..pw_cfg()
        };
        // `gift_stride_eins`, `gift_stride_zehn`, `gift_ausgang_in_daten`.
        for bad in [
            PipeCfg {
                exit_stride: 1,
                ..c.clone()
            },
            PipeCfg {
                exit_stride: 10,
                ..c.clone()
            },
            PipeCfg {
                exit_base: 8192,
                ..c.clone()
            },
        ] {
            assert_eq!(
                compile_to_image(&pw3_programm(None, pi_es()), &bad),
                Err(Refusal::Layout)
            );
        }
        // `gift_bau_platz`: overlapping placements.
        let mut p = pw3_programm(None, pi_es());
        p.placements = vec![
            Platz {
                t: 0,
                k: 0,
                f: 0,
                a: 8192,
            },
            Platz {
                t: 0,
                k: 1,
                f: 0,
                a: 8196,
            },
        ];
        assert_eq!(compile_to_image(&p, &c), Err(Refusal::Layout));
        // A clobbering prologue.
        let p = pw3_programm(Some(vec![]), pi_es());
        assert_eq!(compile_to_image(&p, &c), Err(Refusal::Prologue));
        // Register clash.
        assert_eq!(
            compile_to_image(
                &pw3_programm(None, pi_es()),
                &PipeCfg {
                    dst: R10,
                    ..c.clone()
                }
            ),
            Err(Refusal::Config)
        );
        // A world without the placed slot's value.
        let mut p = pw3_programm(None, pi_es());
        p.welt = Welt::default();
        assert_eq!(compile_to_image(&p, &c), Err(Refusal::Welt));
        // A world value outside the slot type.
        let mut p = pw3_programm(None, pi_es());
        p.welt = Welt {
            werte: vec![((0, 0, 0), 7), ((0, 1, 0), 1001)],
        };
        assert_eq!(compile_to_image(&p, &c), Err(Refusal::Welt));
    }

    #[test]
    fn ill_typed_programs_are_refused() {
        let c = PipeCfg {
            exit_stride: 16,
            ..pw_cfg()
        };
        // A `weiter` that NARROWS.
        let mut p = pw3_programm(None, pi_es());
        p.block = Block::cons(
            Stmt::AssignSlot {
                t: 0,
                f: 0,
                index: idx(0, 2),
                value: IntExpr::weiter(Range::new(0, 50), IntExpr::add(pw_x(), IntExpr::lit(5))),
            },
            Block::Nil,
        );
        assert_eq!(compile_to_image(&p, &c), Err(Refusal::IllTyped));
        // A variable at the wrong range.
        let mut p = pw3_programm(None, pi_es());
        p.block = Block::pruefung(
            BoolExpr::Lt(IntExpr::var(0, Range::new(0, 7)), IntExpr::lit(5)),
            Sonst::RetGrund(0),
            Block::Nil,
        );
        assert_eq!(compile_to_image(&p, &c), Err(Refusal::IllTyped));
    }

    #[test]
    fn entry_image_puts_the_prologue_before_the_code() {
        let c = PipeCfg {
            exit_stride: 16,
            ..pw_cfg()
        };
        let mut es = pi_es();
        es.push(TabLayout {
            tab: 1,
            basis: 16384,
            len: 64,
            ausr: 16,
        });
        let img = compile_to_image(&pw3_programm(Some(SYSV_PARAMETER.to_vec()), es), &c).unwrap();
        assert_eq!(img.prolog, vec![0x49, 0x89, 0xFA]); // `mov r10, rdi`
        assert_eq!(img.bild.eintraege, vec![4093, 4096]);
        assert_eq!(img.bild.abschnitte[0].vaddr, 4093);
        assert_eq!(&img.bild.datei[..3], img.prolog.as_slice());
    }

    #[test]
    fn decode_all_inverts_encode_all() {
        let p = pw_prog();
        assert_eq!(decode_all(p.len(), &encode_all(&p)), Some(p.clone()));
        assert_eq!(decode_all(p.len() - 1, &encode_all(&p)), None);
    }
}
