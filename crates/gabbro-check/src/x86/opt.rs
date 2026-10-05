//! **The certified optimiser's Rust certificate PRODUCER (wave, optimiser rule library).**
//!
//! Mirrors `grammatik/Grammatik/X86/OptimizationRules.lean` (certificate
//! schemas, `PassKind`, the validators and their soundness) and the probes of
//! `grammatik/Grammatik/X86/OptimizationWitnesses.lean`. **Rust proposes, Lean
//! disposes**: this module's job is to walk a source fragment, find places
//! where a rule of `OptimizationRules.lean` applies, and emit a certificate
//! (`ExprCert` / `StmtCert` / `BlockCert`, or a `(PassKind, BlockCert)`
//! pipeline) that the LEAN validator will accept. Nothing here is on the
//! trust path: the Lean validator recomputes every fact from the source text
//! and is the only thing that ever decides correctness. Every function in
//! this file that recomputes a Lean side condition (the "oracle" section) is
//! an UNTRUSTED mirror, used only so the producer can check its own proposals
//! and so tests have an independent recompute path.
//!
//! ## Constructor mapping (Lean -> Rust)
//!
//! | Lean (`OptimizationRules.lean`)     | Rust (this file)                          |
//! |--------------------------------------|--------------------------------------------|
//! | `ExprCert.foldInt`                   | `ExprCert::FoldInt`                       |
//! | `ExprCert.foldBool`                  | `ExprCert::FoldBool`                      |
//! | `TargetOp.shl k`                     | `TargetOp::Shl(k)`                        |
//! | `TargetOp.shr k`                     | `TargetOp::Shr(k)`                        |
//! | `TargetOp.mask k`                    | `TargetOp::Mask(k)`                       |
//! | `BlockCert.dropCheck`                | `BlockCert::DropCheck`                    |
//! | `BlockCert.narrowEntailed`           | `BlockCert::NarrowEntailed`               |
//! | `BlockCert.checkCond c`              | `BlockCert::CheckCond(ExprCert)`          |
//! | `BlockCert.bindValue c`              | `BlockCert::BindValue(ExprCert)`          |
//! | `BlockCert.narrowValue c`            | `BlockCert::NarrowValue(ExprCert)`        |
//! | `BlockCert.head c`                   | `BlockCert::Head(Box<StmtCert>)`          |
//! | `BlockCert.rest c`                   | `BlockCert::Rest(Box<BlockCert>)`         |
//! | `StmtCert.iteCond c`                 | `StmtCert::IteCond(ExprCert)`             |
//! | `StmtCert.iteThen c`                 | `StmtCert::IteThen(Box<BlockCert>)`       |
//! | `StmtCert.iteElse c`                 | `StmtCert::IteElse(Box<BlockCert>)`       |
//! | `StmtCert.lockBody c`                | `StmtCert::LockBody(Box<BlockCert>)`      |
//! | `StmtCert.assignSlotIndex c`         | `StmtCert::AssignSlotIndex(ExprCert)`     |
//! | `StmtCert.assignSlotValue c`         | `StmtCert::AssignSlotValue(ExprCert)`     |
//! | `StmtCert.assignVarValue c`          | `StmtCert::AssignVarValue(ExprCert)`      |
//! | `StmtCert.assignGlobValue c`         | `StmtCert::AssignGlobValue(ExprCert)`     |
//! | `StmtCert.breakingBody c`            | `StmtCert::BreakingBody(Box<BlockCert>)`  |
//! | `StmtCert.optSomeBranch c`           | `StmtCert::OptSomeBranch(Box<BlockCert>)` |
//! | `StmtCert.optNoneBranch c`           | `StmtCert::OptNoneBranch(Box<BlockCert>)` |
//! | `StmtCert.traverseBody c`            | `StmtCert::TraverseBody(Box<BlockCert>)`  |
//! | `StmtCert.retryCond c`               | `StmtCert::RetryCond(ExprCert)`           |
//! | `StmtCert.retryBody c`               | `StmtCert::RetryBody(Box<BlockCert>)`     |
//! | `StmtCert.retryOverflow c`           | `StmtCert::RetryOverflow(Box<BlockCert>)` |
//! | `StmtCert.foreverBody c`             | `StmtCert::ForeverBody(Box<BlockCert>)`   |
//! | `PassKind.fold/.cfg/.gvn/.checks/.strength/.alias/.licm/.inline/.unroll/.peephole` | `PassKind::{Fold,Cfg,Gvn,Checks,Strength,Alias,Licm,Inline,Unroll,Peephole}` |
//!
//! ## What is NOT here (honest `CUTS`, see also the block at the end)
//!
//! * **No conversion from the real checked AST.** `gabbro-check`'s checked
//!   representation (`crate::umgebung`, `crate::typen::Typ`) annotates the
//!   PARSED `gabbro_syntax::ast` with side tables (types, ranges, effects);
//!   it is not a dependently-typed indexed tree like the Lean
//!   `Expr D Γ Λ τ`/`Block D V l Γ Λ Λ'`, and there is no existing pass that
//!   already computes, at every AST position, the exact declared integer
//!   range the Lean side's `.weiter`/type index carries. Building that
//!   mapping correctly would duplicate a slice of `m1.rs`/`umgebung.rs`
//!   (owned by other passes) and is out of scope for this file. This module
//!   therefore works over the small self-contained input model in §1, which
//!   mirrors the SHAPE the Lean rules read (typed-range expressions, the
//!   block/statement constructors the validator descends through). A real
//!   `gabbro_syntax`/checked-AST -> this model conversion is future work.
//! * **Strength reduction is not a `BlockCert`.** `checkStrength` in
//!   `OptimizationRules.lean` has no `ExprCert`/`BlockCert`/`StmtCert`
//!   wrapper and is never reachable through `applyPipeline` (`BlockCert.fits`
//!   never maps to `PassKind.strength`): it is a standalone validated
//!   analysis the x86 lowering lane calls directly against source text. This
//!   producer mirrors that: §6 reports strength-reduction opportunities as a
//!   separate `Vec<StrengthOpportunity>`, never mixed into the certificate
//!   pipeline.
//! * The oracle (§2, §5, §6) is an UNTRUSTED self-check, not a proof. Any
//!   divergence from the Lean validator is a bug in THIS file; the Lean
//!   validator's verdict is the only one that matters.

use std::fmt;

// =============================================================================
// §1. The input model: a small, self-contained mirror of the source fragment
//     the Lean rules cover (OPTIMIZER.md scope: literals, typed ranges,
//     variables, slot reads, the pure int/bitwise ops, comparisons, bool
//     connectives, float comparisons as opaque, and the block/statement
//     shapes the validator descends through).
// =============================================================================

/// A closed integer interval `[lo, hi]`: the Lean side's `Ty.int lo hi`.
/// `i128` so a poison-probe constant like `2^65` (used in
/// `OptimizationWitnesses.lean`'s `strength_refuses_wide_mask`) still fits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Range {
    pub lo: i128,
    pub hi: i128,
}

impl Range {
    pub const fn new(lo: i128, hi: i128) -> Self {
        Range { lo, hi }
    }
    /// A one-point range: the type of a bare literal.
    pub const fn point(v: i128) -> Self {
        Range::new(v, v)
    }
    pub fn contains(&self, v: i128) -> bool {
        self.lo <= v && v <= self.hi
    }
}

/// An integer-typed source expression, carrying its OWN declared range
/// (the Lean type index `.int lo hi` at that node) the way every node of
/// `Expr D Γ Λ (.int lo hi)` does.
#[derive(Debug, Clone, PartialEq)]
pub struct IExpr {
    pub range: Range,
    pub kind: IKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum IKind {
    /// `.lit n`.
    Lit(i128),
    /// `.var _`: a bound local. Reads nothing (`orte` empty).
    Var(u32),
    /// `.slot _ _ i _`: a table read. Carries a read event.
    SlotRead,
    /// Anything this model does not spell out (register reads, float-derived
    /// integers, …). Conservative: treated as reading something and never
    /// folded, matching "unknown falls loud" (`Unwissen faellt nach
    /// lautstark`).
    Opaque,
    Add(Box<IExpr>, Box<IExpr>),
    Sub(Box<IExpr>, Box<IExpr>),
    Neg(Box<IExpr>),
    Mul(Box<IExpr>, Box<IExpr>),
    /// Unsigned/truncating `div` (`.div`).
    Div(Box<IExpr>, Box<IExpr>),
    /// Unsigned/truncating `rem` (`.rem`).
    Rem(Box<IExpr>, Box<IExpr>),
    /// Signed `sdiv` (`.sdiv`): folds as a constant like `Div`, but is
    /// REFUSED by strength reduction (R4).
    SDiv(Box<IExpr>, Box<IExpr>),
    /// Signed `srem` (`.srem`): same refusal as `SDiv`.
    SRem(Box<IExpr>, Box<IExpr>),
    Band(Box<IExpr>, Box<IExpr>),
    Bor(Box<IExpr>, Box<IExpr>),
    Bxor(Box<IExpr>, Box<IExpr>),
    Shl(Box<IExpr>, Box<IExpr>),
    Shr(Box<IExpr>, Box<IExpr>),
}

impl IExpr {
    pub fn lit(v: i128) -> Self {
        IExpr { range: Range::point(v), kind: IKind::Lit(v) }
    }
    pub fn var(id: u32, range: Range) -> Self {
        IExpr { range, kind: IKind::Var(id) }
    }
    pub fn slot(range: Range) -> Self {
        IExpr { range, kind: IKind::SlotRead }
    }
    pub fn opaque(range: Range) -> Self {
        IExpr { range, kind: IKind::Opaque }
    }
    /// Re-type an expression at a (wider) declared range, mirroring the
    /// Lean `.weiter` widening that `narrowEntailed`/`foldInt` produce.
    pub fn widen(&self, range: Range) -> Self {
        IExpr { range, kind: self.kind.clone() }
    }
}

macro_rules! bin_ctor {
    ($name:ident, $variant:ident) => {
        impl IExpr {
            pub fn $name(a: IExpr, b: IExpr, range: Range) -> Self {
                IExpr { range, kind: IKind::$variant(Box::new(a), Box::new(b)) }
            }
        }
    };
}
bin_ctor!(add, Add);
bin_ctor!(sub, Sub);
bin_ctor!(mul, Mul);
bin_ctor!(div, Div);
bin_ctor!(rem, Rem);
bin_ctor!(sdiv, SDiv);
bin_ctor!(srem, SRem);
bin_ctor!(band, Band);
bin_ctor!(bor, Bor);
bin_ctor!(bxor, Bxor);
bin_ctor!(shl, Shl);
bin_ctor!(shr, Shr);

impl IExpr {
    pub fn neg(a: IExpr, range: Range) -> Self {
        IExpr { range, kind: IKind::Neg(Box::new(a)) }
    }
}

/// A boolean-typed source expression (Lean `Expr D Γ Λ .bool`).
#[derive(Debug, Clone, PartialEq)]
pub enum BExpr {
    Wahr,
    Falsch,
    Lt(IExpr, IExpr),
    Le(IExpr, IExpr),
    Eq(IExpr, IExpr),
    Und(Box<BExpr>, Box<BExpr>),
    Oder(Box<BExpr>, Box<BExpr>),
    Nicht(Box<BExpr>),
    /// `fllt`: an opaque float comparison. No fold rule exists for floats
    /// (F2-F4 refused by absence); modelled with no payload since nothing
    /// here ever inspects a float operand.
    FloatLt,
    /// `flle`, same story.
    FloatLe,
    /// Anything else not spelled out here (float `eq`, a register
    /// predicate, …): conservative, reads something, never decided.
    Opaque,
}

/// A statement (Lean `Stmt D V l Γ Λ Λ'`), carrying only the fields the
/// optimiser rules touch.
#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Ite(BExpr, Box<Block>, Box<Block>),
    Locks(Box<Block>),
    /// `.assignSlot t f index value h1 h2` (index, value).
    AssignSlot(IExpr, IExpr),
    AssignVar(IExpr),
    AssignGlob(IExpr),
    Breaking(Box<Block>),
    /// `.onOption o some-branch none-branch`.
    OnOption(Box<Block>, Box<Block>),
    /// `.traverse t inv body`. The invariant is a contract site and is not
    /// part of this model (never rewritten, as in the Lean side).
    Traverse(Box<Block>),
    /// `.retry n cond body overflow`.
    Retry(BExpr, Box<Block>, Box<Block>),
    /// `.forever a inv body`. Same invariant note as `Traverse`.
    Forever(Box<Block>),
    /// Anything else (`exchange`, `awaits`, register/float binders, `on
    /// tag`/`on reason` arms, …): never reachable by any certificate, as in
    /// the Lean validator's final wildcard arm.
    Opaque,
}

/// A block (Lean `Block D V l Γ Λ Λ'`), carrying only the continuation
/// shapes `applyBlock` descends through.
#[derive(Debug, Clone, PartialEq)]
pub enum Block {
    /// `.nil` / `.leave` / any terminal: nothing left to rewrite.
    Nil,
    Cons(Box<Stmt>, Box<Block>),
    Bind(IExpr, Box<Block>),
    /// `.bindCall f args … rest`: the call itself is never rewritten here
    /// (no certificate reaches into a call's arguments), only `rest` via
    /// `BlockCert::Rest`.
    BindCall(Box<Block>),
    Pruefung(BExpr, Box<Block>),
    /// `.narrow e lo' hi' sonst rest`.
    Narrow(IExpr, Range, Box<Block>),
}

// =============================================================================
// §2. Oracle, part 1: the constant evaluator / condition decider. UNTRUSTED
//     mirrors of `constInt?`, `constBool?`, `bounds`, `decideLe/Lt/Eq`,
//     `andOpt`/`orOpt` and the `orte`/read-event checks.
// =============================================================================

fn nat_trunc(v: i128) -> i128 {
    if v < 0 {
        0
    } else {
        v
    }
}

/// `2^k` as `i128`, or `None` if it would not fit (defensive: Lean's `Int`
/// has no overflow, Rust's `i128` does).
fn pow2(k: u32) -> Option<i128> {
    if k >= 127 {
        None
    } else {
        Some(1i128 << k)
    }
}

/// Mirrors `OptimizationRules.constInt?`. `None` on anything that reads a
/// location, a variable or is otherwise not built purely from literals.
pub fn const_int(e: &IExpr) -> Option<i128> {
    use IKind::*;
    match &e.kind {
        Lit(n) => Some(*n),
        Var(_) | SlotRead | Opaque => None,
        Add(a, b) => Some(const_int(a)?.checked_add(const_int(b)?)?),
        Sub(a, b) => Some(const_int(a)?.checked_sub(const_int(b)?)?),
        Neg(a) => const_int(a)?.checked_neg(),
        Mul(a, b) => Some(const_int(a)?.checked_mul(const_int(b)?)?),
        Div(a, b) | SDiv(a, b) => {
            let (x, y) = (const_int(a)?, const_int(b)?);
            if y == 0 {
                None
            } else {
                Some(x / y)
            }
        }
        Rem(a, b) | SRem(a, b) => {
            let (x, y) = (const_int(a)?, const_int(b)?);
            if y == 0 {
                None
            } else {
                Some(x % y)
            }
        }
        Band(a, b) => Some(nat_trunc(const_int(a)?) & nat_trunc(const_int(b)?)),
        Bor(a, b) => Some(nat_trunc(const_int(a)?) | nat_trunc(const_int(b)?)),
        Bxor(a, b) => Some(nat_trunc(const_int(a)?) ^ nat_trunc(const_int(b)?)),
        Shl(a, b) => {
            let (x, y) = (const_int(a)?, const_int(b)?);
            let k = u32::try_from(nat_trunc(y)).ok()?;
            Some(x.checked_mul(pow2(k)?)?)
        }
        Shr(a, b) => {
            let (x, y) = (const_int(a)?, const_int(b)?);
            let k = u32::try_from(nat_trunc(y)).ok()?;
            Some(x / pow2(k)?)
        }
    }
}

/// Does `e` log any read event (`e.orte`, non-empty)? `Var` does not (a
/// local bind is not a memory read); `SlotRead` and `Opaque` do.
pub fn reads_i(e: &IExpr) -> bool {
    use IKind::*;
    match &e.kind {
        Lit(_) | Var(_) => false,
        SlotRead | Opaque => true,
        Neg(a) => reads_i(a),
        Add(a, b) | Sub(a, b) | Mul(a, b) | Div(a, b) | Rem(a, b) | SDiv(a, b) | SRem(a, b)
        | Band(a, b) | Bor(a, b) | Bxor(a, b) | Shl(a, b) | Shr(a, b) => {
            reads_i(a) || reads_i(b)
        }
    }
}

pub fn reads_b(e: &BExpr) -> bool {
    use BExpr::*;
    match e {
        Wahr | Falsch => false,
        Lt(a, b) | Le(a, b) | Eq(a, b) => reads_i(a) || reads_i(b),
        Und(a, b) | Oder(a, b) => reads_b(a) || reads_b(b),
        Nicht(a) => reads_b(a),
        FloatLt | FloatLe | Opaque => true,
    }
}

/// Mirrors `OptimizationRules.bounds`: the point value when constant,
/// otherwise the node's declared type range.
pub fn bounds(e: &IExpr) -> Range {
    match const_int(e) {
        Some(x) => Range::point(x),
        None => e.range,
    }
}

pub fn decide_le(pa: Range, pb: Range) -> Option<bool> {
    if pa.hi <= pb.lo {
        Some(true)
    } else if pb.hi < pa.lo {
        Some(false)
    } else {
        None
    }
}

pub fn decide_lt(pa: Range, pb: Range) -> Option<bool> {
    if pa.hi < pb.lo {
        Some(true)
    } else if pb.hi <= pa.lo {
        Some(false)
    } else {
        None
    }
}

pub fn decide_eq(pa: Range, pb: Range) -> Option<bool> {
    if pa.lo == pa.hi && pb.lo == pb.hi && pa.lo == pb.lo {
        Some(true)
    } else if pa.hi < pb.lo || pb.hi < pa.lo {
        Some(false)
    } else {
        None
    }
}

fn and_opt(a: Option<bool>, b: Option<bool>) -> Option<bool> {
    match (a, b) {
        (Some(false), _) | (_, Some(false)) => Some(false),
        (Some(true), Some(true)) => Some(true),
        _ => None,
    }
}

fn or_opt(a: Option<bool>, b: Option<bool>) -> Option<bool> {
    match (a, b) {
        (Some(true), _) | (_, Some(true)) => Some(true),
        (Some(false), Some(false)) => Some(false),
        _ => None,
    }
}

/// Mirrors `OptimizationRules.constBool?`.
pub fn const_bool(e: &BExpr) -> Option<bool> {
    use BExpr::*;
    match e {
        Wahr => Some(true),
        Falsch => Some(false),
        Lt(a, b) => decide_lt(bounds(a), bounds(b)),
        Le(a, b) => decide_le(bounds(a), bounds(b)),
        Eq(a, b) => decide_eq(bounds(a), bounds(b)),
        Und(a, b) => and_opt(const_bool(a), const_bool(b)),
        Oder(a, b) => or_opt(const_bool(a), const_bool(b)),
        Nicht(a) => const_bool(a).map(|v| !v),
        FloatLt | FloatLe | Opaque => None,
    }
}

// =============================================================================
// §3. Certificate types. Exact mirrors of `OptimizationRules.lean`'s
//     `ExprCert`/`StmtCert`/`BlockCert`/`PassKind`/`TargetOp`.
// =============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExprCert {
    FoldInt,
    FoldBool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TargetOp {
    Shl(u32),
    Shr(u32),
    Mask(u32),
}

impl TargetOp {
    /// Mirrors `TargetOp.run`: the accepted canonical word helpers,
    /// `shlW`/`shrW`/`&&& maskW`, computed here only for the self-check
    /// oracle (`strength_word_probe`-style tests) and never trusted as the
    /// emitted instruction.
    pub fn run(self, w: u64) -> u64 {
        match self {
            TargetOp::Shl(k) => (((w as u128) << k.min(127)) & u128::from(u64::MAX)) as u64,
            TargetOp::Shr(k) => {
                if k >= 64 {
                    0
                } else {
                    w >> k
                }
            }
            TargetOp::Mask(k) => {
                let mask = if k >= 64 { u64::MAX } else { (1u64 << k) - 1 };
                w & mask
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum StmtCert {
    IteCond(ExprCert),
    IteThen(Box<BlockCert>),
    IteElse(Box<BlockCert>),
    LockBody(Box<BlockCert>),
    AssignSlotIndex(ExprCert),
    AssignSlotValue(ExprCert),
    AssignVarValue(ExprCert),
    AssignGlobValue(ExprCert),
    BreakingBody(Box<BlockCert>),
    OptSomeBranch(Box<BlockCert>),
    OptNoneBranch(Box<BlockCert>),
    TraverseBody(Box<BlockCert>),
    RetryCond(ExprCert),
    RetryBody(Box<BlockCert>),
    RetryOverflow(Box<BlockCert>),
    ForeverBody(Box<BlockCert>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum BlockCert {
    DropCheck,
    NarrowEntailed,
    CheckCond(ExprCert),
    BindValue(ExprCert),
    NarrowValue(ExprCert),
    Head(Box<StmtCert>),
    Rest(Box<BlockCert>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PassKind {
    Fold,
    Cfg,
    Gvn,
    Checks,
    Strength,
    Alias,
    Licm,
    Inline,
    Unroll,
    Peephole,
}

impl PassKind {
    /// Mirrors `PassKind.rank`: fixed table order, OPTIMIZER.md §9.
    pub fn rank(self) -> u32 {
        match self {
            PassKind::Fold => 1,
            PassKind::Cfg => 2,
            PassKind::Gvn => 3,
            PassKind::Checks => 4,
            PassKind::Strength => 5,
            PassKind::Alias => 6,
            PassKind::Licm => 7,
            PassKind::Inline => 8,
            PassKind::Unroll => 9,
            PassKind::Peephole => 10,
        }
    }
}

/// Mirrors `admittedOrder`: ranks never decrease along the list.
pub fn admitted_order(passes: &[PassKind]) -> bool {
    passes.windows(2).all(|w| w[0].rank() <= w[1].rank())
}

impl ExprCert {
    /// Mirrors `ExprCert.pass`.
    pub fn pass(self) -> PassKind {
        match self {
            ExprCert::FoldInt | ExprCert::FoldBool => PassKind::Fold,
        }
    }
}

impl StmtCert {
    /// Mirrors `StmtCert.fits`.
    pub fn fits(&self, k: PassKind) -> bool {
        use StmtCert::*;
        match self {
            IteCond(c) | AssignSlotIndex(c) | AssignSlotValue(c) | AssignVarValue(c)
            | AssignGlobValue(c) | RetryCond(c) => c.pass() == k,
            IteThen(c) | IteElse(c) | LockBody(c) | BreakingBody(c) | OptSomeBranch(c)
            | OptNoneBranch(c) | TraverseBody(c) | RetryBody(c) | RetryOverflow(c)
            | ForeverBody(c) => c.fits(k),
        }
    }
}

impl BlockCert {
    /// Mirrors `BlockCert.fits`.
    pub fn fits(&self, k: PassKind) -> bool {
        use BlockCert::*;
        match self {
            DropCheck | NarrowEntailed => k == PassKind::Checks,
            CheckCond(c) | BindValue(c) | NarrowValue(c) => c.pass() == k,
            Head(c) => c.fits(k),
            Rest(c) => c.fits(k),
        }
    }
}

// =============================================================================
// §4. Serialisation: a stable, one-certificate-per-line, S-expression-like
//     text form. Grammar (whitespace-separated tokens, parens group):
//
//       expr-cert   := "(fold-int)" | "(fold-bool)"
//       target-op   := "(shl" NAT ")" | "(shr" NAT ")" | "(mask" NAT ")"
//       block-cert  := "(drop-check)" | "(narrow-entailed)"
//                    | "(check-cond" expr-cert ")" | "(bind-value" expr-cert ")"
//                    | "(narrow-value" expr-cert ")"
//                    | "(head" stmt-cert ")" | "(rest" block-cert ")"
//       stmt-cert   := "(ite-cond" expr-cert ")" | "(ite-then" block-cert ")"
//                    | "(ite-else" block-cert ")" | "(lock-body" block-cert ")"
//                    | "(assign-slot-index" expr-cert ")"
//                    | "(assign-slot-value" expr-cert ")"
//                    | "(assign-var-value" expr-cert ")"
//                    | "(assign-glob-value" expr-cert ")"
//                    | "(breaking-body" block-cert ")"
//                    | "(opt-some-branch" block-cert ")"
//                    | "(opt-none-branch" block-cert ")"
//                    | "(traverse-body" block-cert ")"
//                    | "(retry-cond" expr-cert ")" | "(retry-body" block-cert ")"
//                    | "(retry-overflow" block-cert ")" | "(forever-body" block-cert ")"
//       pass        := "fold" | "cfg" | "gvn" | "checks" | "strength" | "alias"
//                    | "licm" | "inline" | "unroll" | "peephole"
//       pipeline-line := "(pass" pass block-cert ")"
//
//     A pipeline is rendered as one `pipeline-line` per `\n`-terminated line,
//     in list order (the admitted-order check reads top to bottom).
// =============================================================================

impl fmt::Display for ExprCert {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExprCert::FoldInt => write!(f, "(fold-int)"),
            ExprCert::FoldBool => write!(f, "(fold-bool)"),
        }
    }
}

impl fmt::Display for TargetOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TargetOp::Shl(k) => write!(f, "(shl {k})"),
            TargetOp::Shr(k) => write!(f, "(shr {k})"),
            TargetOp::Mask(k) => write!(f, "(mask {k})"),
        }
    }
}

impl fmt::Display for StmtCert {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use StmtCert::*;
        match self {
            IteCond(c) => write!(f, "(ite-cond {c})"),
            IteThen(c) => write!(f, "(ite-then {c})"),
            IteElse(c) => write!(f, "(ite-else {c})"),
            LockBody(c) => write!(f, "(lock-body {c})"),
            AssignSlotIndex(c) => write!(f, "(assign-slot-index {c})"),
            AssignSlotValue(c) => write!(f, "(assign-slot-value {c})"),
            AssignVarValue(c) => write!(f, "(assign-var-value {c})"),
            AssignGlobValue(c) => write!(f, "(assign-glob-value {c})"),
            BreakingBody(c) => write!(f, "(breaking-body {c})"),
            OptSomeBranch(c) => write!(f, "(opt-some-branch {c})"),
            OptNoneBranch(c) => write!(f, "(opt-none-branch {c})"),
            TraverseBody(c) => write!(f, "(traverse-body {c})"),
            RetryCond(c) => write!(f, "(retry-cond {c})"),
            RetryBody(c) => write!(f, "(retry-body {c})"),
            RetryOverflow(c) => write!(f, "(retry-overflow {c})"),
            ForeverBody(c) => write!(f, "(forever-body {c})"),
        }
    }
}

impl fmt::Display for BlockCert {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use BlockCert::*;
        match self {
            DropCheck => write!(f, "(drop-check)"),
            NarrowEntailed => write!(f, "(narrow-entailed)"),
            CheckCond(c) => write!(f, "(check-cond {c})"),
            BindValue(c) => write!(f, "(bind-value {c})"),
            NarrowValue(c) => write!(f, "(narrow-value {c})"),
            Head(c) => write!(f, "(head {c})"),
            Rest(c) => write!(f, "(rest {c})"),
        }
    }
}

impl fmt::Display for PassKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            PassKind::Fold => "fold",
            PassKind::Cfg => "cfg",
            PassKind::Gvn => "gvn",
            PassKind::Checks => "checks",
            PassKind::Strength => "strength",
            PassKind::Alias => "alias",
            PassKind::Licm => "licm",
            PassKind::Inline => "inline",
            PassKind::Unroll => "unroll",
            PassKind::Peephole => "peephole",
        };
        write!(f, "{s}")
    }
}

/// Render a pipeline as its stable text form: one `(pass <PassKind>
/// <BlockCert>)` line per entry, in order.
pub fn render_pipeline(pipeline: &[(PassKind, BlockCert)]) -> String {
    let mut out = String::new();
    for (k, c) in pipeline {
        out.push_str(&format!("(pass {k} {c})\n"));
    }
    out
}

/// A tiny tokenizer: parens are their own tokens, everything else splits on
/// whitespace. Enough for the grammar above (no strings, no escapes).
fn tokenize(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    for ch in s.chars() {
        match ch {
            '(' | ')' => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
                out.push(ch.to_string());
            }
            c if c.is_whitespace() => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
            }
            c => cur.push(c),
        }
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

/// A minimal cursor over tokens, for the hand-rolled recursive-descent
/// parser below.
struct Cursor<'a> {
    toks: &'a [String],
    pos: usize,
}

impl<'a> Cursor<'a> {
    fn next(&mut self) -> Option<&'a str> {
        let t = self.toks.get(self.pos).map(|s| s.as_str());
        self.pos += 1;
        t
    }
    fn expect(&mut self, want: &str) -> Result<(), String> {
        match self.next() {
            Some(t) if t == want => Ok(()),
            other => Err(format!("expected {want:?}, got {other:?}")),
        }
    }
}

fn parse_expr_cert(c: &mut Cursor) -> Result<ExprCert, String> {
    c.expect("(")?;
    let head = c.next().ok_or("unexpected end of input")?;
    let r = match head {
        "fold-int" => ExprCert::FoldInt,
        "fold-bool" => ExprCert::FoldBool,
        other => return Err(format!("unknown expr-cert head {other:?}")),
    };
    c.expect(")")?;
    Ok(r)
}

fn parse_block_cert(c: &mut Cursor) -> Result<BlockCert, String> {
    c.expect("(")?;
    let head = c.next().ok_or("unexpected end of input")?.to_string();
    let r = match head.as_str() {
        "drop-check" => BlockCert::DropCheck,
        "narrow-entailed" => BlockCert::NarrowEntailed,
        "check-cond" => BlockCert::CheckCond(parse_expr_cert(c)?),
        "bind-value" => BlockCert::BindValue(parse_expr_cert(c)?),
        "narrow-value" => BlockCert::NarrowValue(parse_expr_cert(c)?),
        "head" => BlockCert::Head(Box::new(parse_stmt_cert(c)?)),
        "rest" => BlockCert::Rest(Box::new(parse_block_cert(c)?)),
        other => return Err(format!("unknown block-cert head {other:?}")),
    };
    c.expect(")")?;
    Ok(r)
}

fn parse_stmt_cert(c: &mut Cursor) -> Result<StmtCert, String> {
    c.expect("(")?;
    let head = c.next().ok_or("unexpected end of input")?.to_string();
    let r = match head.as_str() {
        "ite-cond" => StmtCert::IteCond(parse_expr_cert(c)?),
        "ite-then" => StmtCert::IteThen(Box::new(parse_block_cert(c)?)),
        "ite-else" => StmtCert::IteElse(Box::new(parse_block_cert(c)?)),
        "lock-body" => StmtCert::LockBody(Box::new(parse_block_cert(c)?)),
        "assign-slot-index" => StmtCert::AssignSlotIndex(parse_expr_cert(c)?),
        "assign-slot-value" => StmtCert::AssignSlotValue(parse_expr_cert(c)?),
        "assign-var-value" => StmtCert::AssignVarValue(parse_expr_cert(c)?),
        "assign-glob-value" => StmtCert::AssignGlobValue(parse_expr_cert(c)?),
        "breaking-body" => StmtCert::BreakingBody(Box::new(parse_block_cert(c)?)),
        "opt-some-branch" => StmtCert::OptSomeBranch(Box::new(parse_block_cert(c)?)),
        "opt-none-branch" => StmtCert::OptNoneBranch(Box::new(parse_block_cert(c)?)),
        "traverse-body" => StmtCert::TraverseBody(Box::new(parse_block_cert(c)?)),
        "retry-cond" => StmtCert::RetryCond(parse_expr_cert(c)?),
        "retry-body" => StmtCert::RetryBody(Box::new(parse_block_cert(c)?)),
        "retry-overflow" => StmtCert::RetryOverflow(Box::new(parse_block_cert(c)?)),
        "forever-body" => StmtCert::ForeverBody(Box::new(parse_block_cert(c)?)),
        other => return Err(format!("unknown stmt-cert head {other:?}")),
    };
    c.expect(")")?;
    Ok(r)
}

fn parse_pass(s: &str) -> Result<PassKind, String> {
    Ok(match s {
        "fold" => PassKind::Fold,
        "cfg" => PassKind::Cfg,
        "gvn" => PassKind::Gvn,
        "checks" => PassKind::Checks,
        "strength" => PassKind::Strength,
        "alias" => PassKind::Alias,
        "licm" => PassKind::Licm,
        "inline" => PassKind::Inline,
        "unroll" => PassKind::Unroll,
        "peephole" => PassKind::Peephole,
        other => return Err(format!("unknown pass {other:?}")),
    })
}

fn parse_pipeline_line(c: &mut Cursor) -> Result<(PassKind, BlockCert), String> {
    c.expect("(")?;
    c.expect("pass")?;
    let pass = parse_pass(c.next().ok_or("unexpected end of input")?)?;
    let cert = parse_block_cert(c)?;
    c.expect(")")?;
    Ok((pass, cert))
}

/// Parse the stable text form back into a pipeline. Round-trips with
/// [`render_pipeline`]; used by the serialisation tests.
pub fn parse_pipeline(s: &str) -> Result<Vec<(PassKind, BlockCert)>, String> {
    let mut out = Vec::new();
    for line in s.lines() {
        if line.trim().is_empty() {
            continue;
        }
        let toks = tokenize(line);
        let mut c = Cursor { toks: &toks, pos: 0 };
        out.push(parse_pipeline_line(&mut c)?);
        if c.pos != toks.len() {
            return Err(format!("trailing tokens after pipeline line: {line:?}"));
        }
    }
    Ok(out)
}

// =============================================================================
// §5. Oracle, part 2: the validators. UNTRUSTED mirrors of `foldInt`,
//     `foldBool`, `applyExpr`, `narrowEntailed`, `dropCheckOk`, `applyStmt`,
//     `applyBlock`, `applyOrKeep`, `runCerts`, `applyPipeline`.
// =============================================================================

/// Mirrors `foldInt`.
pub fn fold_int(e: &IExpr) -> Option<IExpr> {
    let v = const_int(e)?;
    if e.range.contains(v) {
        Some(IExpr { range: e.range, kind: IKind::Lit(v) })
    } else {
        None
    }
}

/// Mirrors `foldBool`: only when the condition reads nothing.
pub fn fold_bool(e: &BExpr) -> Option<BExpr> {
    if reads_b(e) {
        return None;
    }
    match const_bool(e)? {
        true => Some(BExpr::Wahr),
        false => Some(BExpr::Falsch),
    }
}

/// Mirrors `applyExpr` on the integer side (type-indexed in Lean; here the
/// Rust type of `e` already pins the arm, so a `FoldBool` certificate
/// applied to an `IExpr` simply refuses, exactly like Lean's `_, _, _ =>
/// none`).
pub fn apply_int_cert(c: ExprCert, e: &IExpr) -> Option<IExpr> {
    match c {
        ExprCert::FoldInt => fold_int(e),
        ExprCert::FoldBool => None,
    }
}

/// The boolean-side twin of [`apply_int_cert`].
pub fn apply_bool_cert(c: ExprCert, e: &BExpr) -> Option<BExpr> {
    match c {
        ExprCert::FoldBool => fold_bool(e),
        ExprCert::FoldInt => None,
    }
}

/// Mirrors `dropCheckOk`.
pub fn drop_check_ok(cond: &BExpr) -> bool {
    !reads_b(cond) && const_bool(cond) == Some(true)
}

/// Mirrors `narrowEntailed`'s side condition.
pub fn narrow_entailed_ok(e: &IExpr, target: Range) -> bool {
    target.lo <= e.range.lo && e.range.hi <= target.hi
}

/// Mirrors `narrowEntailed`.
pub fn narrow_entailed(e: &IExpr, target: Range, rest: &Block) -> Option<Block> {
    if narrow_entailed_ok(e, target) {
        Some(Block::Bind(e.widen(target), Box::new(rest.clone())))
    } else {
        None
    }
}

/// Mirrors `applyStmt`.
pub fn apply_stmt(c: &StmtCert, s: &Stmt) -> Option<Stmt> {
    use Stmt::*;
    use StmtCert as SC;
    match (c, s) {
        (SC::IteCond(ec), Ite(cond, t, f)) => {
            apply_bool_cert(*ec, cond).map(|c2| Ite(c2, t.clone(), f.clone()))
        }
        (SC::IteThen(bc), Ite(cond, t, f)) => {
            apply_block(bc, t).map(|t2| Ite(cond.clone(), Box::new(t2), f.clone()))
        }
        (SC::IteElse(bc), Ite(cond, t, f)) => {
            apply_block(bc, f).map(|f2| Ite(cond.clone(), t.clone(), Box::new(f2)))
        }
        (SC::LockBody(bc), Locks(body)) => apply_block(bc, body).map(|b2| Locks(Box::new(b2))),
        (SC::AssignSlotIndex(ec), AssignSlot(idx, val)) => {
            apply_int_cert(*ec, idx).map(|i2| AssignSlot(i2, val.clone()))
        }
        (SC::AssignSlotValue(ec), AssignSlot(idx, val)) => {
            apply_int_cert(*ec, val).map(|v2| AssignSlot(idx.clone(), v2))
        }
        (SC::AssignVarValue(ec), AssignVar(val)) => apply_int_cert(*ec, val).map(AssignVar),
        (SC::AssignGlobValue(ec), AssignGlob(val)) => apply_int_cert(*ec, val).map(AssignGlob),
        (SC::BreakingBody(bc), Breaking(body)) => {
            apply_block(bc, body).map(|b2| Breaking(Box::new(b2)))
        }
        (SC::OptSomeBranch(bc), OnOption(p, a)) => {
            apply_block(bc, p).map(|p2| OnOption(Box::new(p2), a.clone()))
        }
        (SC::OptNoneBranch(bc), OnOption(p, a)) => {
            apply_block(bc, a).map(|a2| OnOption(p.clone(), Box::new(a2)))
        }
        (SC::TraverseBody(bc), Traverse(body)) => {
            apply_block(bc, body).map(|b2| Traverse(Box::new(b2)))
        }
        (SC::RetryCond(ec), Retry(cond, body, ov)) => {
            apply_bool_cert(*ec, cond).map(|c2| Retry(c2, body.clone(), ov.clone()))
        }
        (SC::RetryBody(bc), Retry(cond, body, ov)) => {
            apply_block(bc, body).map(|b2| Retry(cond.clone(), Box::new(b2), ov.clone()))
        }
        (SC::RetryOverflow(bc), Retry(cond, body, ov)) => {
            apply_block(bc, ov).map(|o2| Retry(cond.clone(), body.clone(), Box::new(o2)))
        }
        (SC::ForeverBody(bc), Forever(body)) => {
            apply_block(bc, body).map(|b2| Forever(Box::new(b2)))
        }
        _ => None,
    }
}

/// Mirrors `applyBlock`, including the shared `.rest` arm over every
/// continuation-carrying constructor (`cons`, `bind`, `bindCall`,
/// `pruefung`, `narrow`).
pub fn apply_block(c: &BlockCert, b: &Block) -> Option<Block> {
    use Block::*;
    use BlockCert as BC;
    match (c, b) {
        (BC::DropCheck, Pruefung(cond, rest)) => {
            if drop_check_ok(cond) {
                Some((**rest).clone())
            } else {
                None
            }
        }
        (BC::NarrowEntailed, Narrow(e, range, rest)) => narrow_entailed(e, *range, rest),
        (BC::CheckCond(ec), Pruefung(cond, rest)) => {
            apply_bool_cert(*ec, cond).map(|c2| Pruefung(c2, rest.clone()))
        }
        (BC::BindValue(ec), Bind(e, rest)) => {
            apply_int_cert(*ec, e).map(|e2| Bind(e2, rest.clone()))
        }
        (BC::NarrowValue(ec), Narrow(e, range, rest)) => {
            apply_int_cert(*ec, e).map(|e2| Narrow(e2, *range, rest.clone()))
        }
        (BC::Head(sc), Cons(s, rest)) => {
            apply_stmt(sc, s).map(|s2| Cons(Box::new(s2), rest.clone()))
        }
        (BC::Rest(bc), Cons(s, rest)) => {
            apply_block(bc, rest).map(|r2| Cons(s.clone(), Box::new(r2)))
        }
        (BC::Rest(bc), Bind(e, rest)) => {
            apply_block(bc, rest).map(|r2| Bind(e.clone(), Box::new(r2)))
        }
        (BC::Rest(bc), BindCall(rest)) => apply_block(bc, rest).map(|r2| BindCall(Box::new(r2))),
        (BC::Rest(bc), Pruefung(cond, rest)) => {
            apply_block(bc, rest).map(|r2| Pruefung(cond.clone(), Box::new(r2)))
        }
        (BC::Rest(bc), Narrow(e, range, rest)) => {
            apply_block(bc, rest).map(|r2| Narrow(e.clone(), *range, Box::new(r2)))
        }
        _ => None,
    }
}

/// Mirrors `applyOrKeep`: the conservative route, always sound.
pub fn apply_or_keep(c: &BlockCert, b: &Block) -> Block {
    apply_block(c, b).unwrap_or_else(|| b.clone())
}

/// Mirrors `runCerts`.
pub fn run_certs(pipeline: &[(PassKind, BlockCert)], b: &Block) -> Option<Block> {
    let mut cur = b.clone();
    for (_, c) in pipeline {
        cur = apply_block(c, &cur)?;
    }
    Some(cur)
}

/// Mirrors `applyPipeline`: order check, pass-membership check, then every
/// step validated.
pub fn apply_pipeline(pipeline: &[(PassKind, BlockCert)], b: &Block) -> Option<Block> {
    let passes: Vec<PassKind> = pipeline.iter().map(|(k, _)| *k).collect();
    if admitted_order(&passes) && pipeline.iter().all(|(k, c)| c.fits(*k)) {
        run_certs(pipeline, b)
    } else {
        None
    }
}

// =============================================================================
// §6. Oracle, part 3: strength reduction (R1-R4). UNTRUSTED mirror of
//     `strengthMul`, `strengthMulComm`, `strengthDiv`, `strengthRem`,
//     `checkStrength`. NOT a `BlockCert` (see the module header): reported
//     separately, never mixed into a certificate pipeline.
// =============================================================================

fn pow2_log2(v: i128) -> Option<u32> {
    if v >= 1 && (v & (v - 1)) == 0 {
        Some(v.trailing_zeros())
    } else {
        None
    }
}

const SIXTY_FOUR: i128 = 1i128 << 64;

/// `hi * 2^k < 2^64`, without panicking on a large `k` (mirrors the shift
/// overflow guard `h1 * 2 ^ k < 2 ^ 64`).
fn product_fits_64(hi: i128, k: u32) -> bool {
    match pow2(k) {
        Some(p) => match hi.checked_mul(p) {
            Some(prod) => prod < SIXTY_FOUR,
            None => false,
        },
        None => false,
    }
}

fn strength_mul(k: u32, a: &IExpr, b: &IExpr) -> Option<TargetOp> {
    if const_int(b) == pow2(k) && a.range.lo >= 0 && product_fits_64(a.range.hi, k) {
        Some(TargetOp::Shl(k))
    } else {
        None
    }
}

fn strength_mul_comm(k: u32, a: &IExpr, b: &IExpr) -> Option<TargetOp> {
    if const_int(a) == pow2(k)
        && const_int(b).is_none()
        && b.range.lo >= 0
        && product_fits_64(b.range.hi, k)
    {
        Some(TargetOp::Shl(k))
    } else {
        None
    }
}

fn strength_div(k: u32, a: &IExpr, b: &IExpr) -> Option<TargetOp> {
    if const_int(b) == pow2(k) && a.range.lo >= 0 && a.range.hi < SIXTY_FOUR {
        Some(TargetOp::Shr(k))
    } else {
        None
    }
}

fn strength_rem(k: u32, a: &IExpr, b: &IExpr) -> Option<TargetOp> {
    if const_int(b) == pow2(k) && a.range.lo >= 0 && a.range.hi < SIXTY_FOUR && k <= 64 {
        Some(TargetOp::Mask(k))
    } else {
        None
    }
}

/// Mirrors `checkStrength`: `sdiv`/`srem` and everything else is refused by
/// absence (R4; `checkStrength_sdiv`/`_srem`).
pub fn check_strength(k: u32, e: &IExpr) -> Option<TargetOp> {
    match &e.kind {
        IKind::Mul(a, b) => strength_mul(k, a, b).or_else(|| strength_mul_comm(k, a, b)),
        IKind::Div(a, b) => strength_div(k, a, b),
        IKind::Rem(a, b) => strength_rem(k, a, b),
        _ => None,
    }
}

/// One place in the source where strength reduction applies: the recomputed
/// `k` and selected [`TargetOp`], alongside a rendering of the expression
/// for a human/log consumer. Not a certificate (see the module header).
#[derive(Debug, Clone, PartialEq)]
pub struct StrengthOpportunity {
    pub k: u32,
    pub op: TargetOp,
    pub expr: IExpr,
}

/// Try both the direct and commuted side conditions at exactly this node,
/// deriving the candidate `k` from whichever operand is the constant power
/// of two.
fn strength_at_node(e: &IExpr) -> Option<(u32, TargetOp)> {
    match &e.kind {
        IKind::Mul(a, b) => {
            if let Some(k) = const_int(b).and_then(pow2_log2) {
                if let Some(op) = strength_mul(k, a, b) {
                    return Some((k, op));
                }
            }
            if let Some(k) = const_int(a).and_then(pow2_log2) {
                if let Some(op) = strength_mul_comm(k, a, b) {
                    return Some((k, op));
                }
            }
            None
        }
        IKind::Div(a, b) => {
            let k = const_int(b).and_then(pow2_log2)?;
            strength_div(k, a, b).map(|op| (k, op))
        }
        IKind::Rem(a, b) => {
            let k = const_int(b).and_then(pow2_log2)?;
            strength_rem(k, a, b).map(|op| (k, op))
        }
        _ => None,
    }
}

fn walk_iexpr<'a>(e: &'a IExpr, out: &mut Vec<&'a IExpr>) {
    out.push(e);
    use IKind::*;
    match &e.kind {
        Lit(_) | Var(_) | SlotRead | Opaque => {}
        Neg(a) => walk_iexpr(a, out),
        Add(a, b) | Sub(a, b) | Mul(a, b) | Div(a, b) | Rem(a, b) | SDiv(a, b) | SRem(a, b)
        | Band(a, b) | Bor(a, b) | Bxor(a, b) | Shl(a, b) | Shr(a, b) => {
            walk_iexpr(a, out);
            walk_iexpr(b, out);
        }
    }
}

/// Every integer-expression slot reachable from a block (every operand of
/// `AssignSlot`/`AssignVar`/`AssignGlob`, every `Bind`/`Narrow` value, and
/// recursively through every statement/block shape `applyStmt`/`applyBlock`
/// know about), used as the root set for the strength-reduction search.
fn collect_iexpr_slots<'a>(b: &'a Block, out: &mut Vec<&'a IExpr>) {
    match b {
        Block::Nil => {}
        Block::Cons(s, rest) => {
            collect_iexpr_slots_stmt(s, out);
            collect_iexpr_slots(rest, out);
        }
        Block::Bind(e, rest) => {
            out.push(e);
            collect_iexpr_slots(rest, out);
        }
        Block::BindCall(rest) => collect_iexpr_slots(rest, out),
        Block::Pruefung(_, rest) => collect_iexpr_slots(rest, out),
        Block::Narrow(e, _, rest) => {
            out.push(e);
            collect_iexpr_slots(rest, out);
        }
    }
}

fn collect_iexpr_slots_stmt<'a>(s: &'a Stmt, out: &mut Vec<&'a IExpr>) {
    match s {
        Stmt::Ite(_, t, f) => {
            collect_iexpr_slots(t, out);
            collect_iexpr_slots(f, out);
        }
        Stmt::Locks(body) => collect_iexpr_slots(body, out),
        Stmt::AssignSlot(idx, val) => {
            out.push(idx);
            out.push(val);
        }
        Stmt::AssignVar(val) | Stmt::AssignGlob(val) => out.push(val),
        Stmt::Breaking(body) => collect_iexpr_slots(body, out),
        Stmt::OnOption(p, a) => {
            collect_iexpr_slots(p, out);
            collect_iexpr_slots(a, out);
        }
        Stmt::Traverse(body) | Stmt::Forever(body) => collect_iexpr_slots(body, out),
        Stmt::Retry(_, body, ov) => {
            collect_iexpr_slots(body, out);
            collect_iexpr_slots(ov, out);
        }
        Stmt::Opaque => {}
    }
}

/// Find every strength-reduction opportunity reachable from `b`, each
/// independently re-verified against [`check_strength`].
pub fn find_strength_opportunities(b: &Block) -> Vec<StrengthOpportunity> {
    let mut roots = Vec::new();
    collect_iexpr_slots(b, &mut roots);
    let mut nodes = Vec::new();
    for r in roots {
        walk_iexpr(r, &mut nodes);
    }
    let mut out = Vec::new();
    for n in nodes {
        if let Some((k, op)) = strength_at_node(n) {
            debug_assert_eq!(check_strength(k, n), Some(op));
            out.push(StrengthOpportunity { k, op, expr: n.clone() });
        }
    }
    out
}

// =============================================================================
// §7. The producer: find fold / condition-fold / droppable-check /
//     entailed-narrow opportunities and emit a rank-ordered
//     `(PassKind, BlockCert)` pipeline the Lean validator accepts.
// =============================================================================

fn fold_int_opportunity(e: &IExpr) -> Option<ExprCert> {
    if matches!(e.kind, IKind::Lit(_)) {
        return None; // already a literal: no opportunity, not a refusal.
    }
    fold_int(e).map(|_| ExprCert::FoldInt)
}

fn fold_bool_opportunity(e: &BExpr) -> Option<ExprCert> {
    if matches!(e, BExpr::Wahr | BExpr::Falsch) {
        return None;
    }
    fold_bool(e).map(|_| ExprCert::FoldBool)
}

/// First fold opportunity reachable from `s`, as a [`StmtCert`] path.
fn find_fold_in_stmt(s: &Stmt) -> Option<StmtCert> {
    use Stmt::*;
    match s {
        Ite(cond, t, f) => fold_bool_opportunity(cond)
            .map(StmtCert::IteCond)
            .or_else(|| find_fold_in_block(t).map(|c| StmtCert::IteThen(Box::new(c))))
            .or_else(|| find_fold_in_block(f).map(|c| StmtCert::IteElse(Box::new(c)))),
        Locks(body) => find_fold_in_block(body).map(|c| StmtCert::LockBody(Box::new(c))),
        AssignSlot(idx, val) => fold_int_opportunity(idx)
            .map(StmtCert::AssignSlotIndex)
            .or_else(|| fold_int_opportunity(val).map(StmtCert::AssignSlotValue)),
        AssignVar(val) => fold_int_opportunity(val).map(StmtCert::AssignVarValue),
        AssignGlob(val) => fold_int_opportunity(val).map(StmtCert::AssignGlobValue),
        Breaking(body) => find_fold_in_block(body).map(|c| StmtCert::BreakingBody(Box::new(c))),
        OnOption(p, a) => find_fold_in_block(p)
            .map(|c| StmtCert::OptSomeBranch(Box::new(c)))
            .or_else(|| find_fold_in_block(a).map(|c| StmtCert::OptNoneBranch(Box::new(c)))),
        Traverse(body) => find_fold_in_block(body).map(|c| StmtCert::TraverseBody(Box::new(c))),
        Retry(cond, body, ov) => fold_bool_opportunity(cond)
            .map(StmtCert::RetryCond)
            .or_else(|| find_fold_in_block(body).map(|c| StmtCert::RetryBody(Box::new(c))))
            .or_else(|| find_fold_in_block(ov).map(|c| StmtCert::RetryOverflow(Box::new(c)))),
        Forever(body) => find_fold_in_block(body).map(|c| StmtCert::ForeverBody(Box::new(c))),
        Opaque => None,
    }
}

/// First fold opportunity reachable from `b`, as a [`BlockCert`] path.
fn find_fold_in_block(b: &Block) -> Option<BlockCert> {
    use Block::*;
    match b {
        Nil => None,
        Cons(s, rest) => find_fold_in_stmt(s)
            .map(|c| BlockCert::Head(Box::new(c)))
            .or_else(|| find_fold_in_block(rest).map(|c| BlockCert::Rest(Box::new(c)))),
        Bind(e, rest) => fold_int_opportunity(e)
            .map(BlockCert::BindValue)
            .or_else(|| find_fold_in_block(rest).map(|c| BlockCert::Rest(Box::new(c)))),
        BindCall(rest) => find_fold_in_block(rest).map(|c| BlockCert::Rest(Box::new(c))),
        Pruefung(cond, rest) => fold_bool_opportunity(cond)
            .map(BlockCert::CheckCond)
            .or_else(|| find_fold_in_block(rest).map(|c| BlockCert::Rest(Box::new(c)))),
        Narrow(e, _, rest) => fold_int_opportunity(e)
            .map(BlockCert::NarrowValue)
            .or_else(|| find_fold_in_block(rest).map(|c| BlockCert::Rest(Box::new(c)))),
    }
}

/// First droppable-check / entailed-narrow opportunity reachable from `s`.
fn find_checks_in_stmt(s: &Stmt) -> Option<StmtCert> {
    use Stmt::*;
    match s {
        Ite(_, t, f) => find_checks_in_block(t)
            .map(|c| StmtCert::IteThen(Box::new(c)))
            .or_else(|| find_checks_in_block(f).map(|c| StmtCert::IteElse(Box::new(c)))),
        Locks(body) => find_checks_in_block(body).map(|c| StmtCert::LockBody(Box::new(c))),
        AssignSlot(_, _) | AssignVar(_) | AssignGlob(_) => None,
        Breaking(body) => find_checks_in_block(body).map(|c| StmtCert::BreakingBody(Box::new(c))),
        OnOption(p, a) => find_checks_in_block(p)
            .map(|c| StmtCert::OptSomeBranch(Box::new(c)))
            .or_else(|| find_checks_in_block(a).map(|c| StmtCert::OptNoneBranch(Box::new(c)))),
        Traverse(body) => find_checks_in_block(body).map(|c| StmtCert::TraverseBody(Box::new(c))),
        Retry(_, body, ov) => find_checks_in_block(body)
            .map(|c| StmtCert::RetryBody(Box::new(c)))
            .or_else(|| find_checks_in_block(ov).map(|c| StmtCert::RetryOverflow(Box::new(c)))),
        Forever(body) => find_checks_in_block(body).map(|c| StmtCert::ForeverBody(Box::new(c))),
        Opaque => None,
    }
}

/// First droppable-check / entailed-narrow opportunity reachable from `b`.
fn find_checks_in_block(b: &Block) -> Option<BlockCert> {
    use Block::*;
    match b {
        Nil => None,
        Pruefung(cond, rest) => {
            if drop_check_ok(cond) {
                Some(BlockCert::DropCheck)
            } else {
                find_checks_in_block(rest).map(|c| BlockCert::Rest(Box::new(c)))
            }
        }
        Narrow(e, range, rest) => {
            if narrow_entailed_ok(e, *range) {
                Some(BlockCert::NarrowEntailed)
            } else {
                find_checks_in_block(rest).map(|c| BlockCert::Rest(Box::new(c)))
            }
        }
        Bind(_, rest) | BindCall(rest) => {
            find_checks_in_block(rest).map(|c| BlockCert::Rest(Box::new(c)))
        }
        Cons(s, rest) => find_checks_in_stmt(s)
            .map(|c| BlockCert::Head(Box::new(c)))
            .or_else(|| find_checks_in_block(rest).map(|c| BlockCert::Rest(Box::new(c)))),
    }
}

/// The producer: repeatedly find and apply fold opportunities (pass
/// [`PassKind::Fold`]), then repeatedly find and apply droppable-check /
/// entailed-narrow opportunities (pass [`PassKind::Checks`]), against a
/// working copy that is re-scanned after every step (so later paths are
/// computed against the ALREADY-rewritten tree, exactly as
/// [`apply_pipeline`]/`applyPipeline` would walk it). The result is
/// `admitted_order`-sound by construction: every `Fold` entry precedes
/// every `Checks` entry.
pub fn optimise(block: &Block) -> Vec<(PassKind, BlockCert)> {
    let mut pipeline = Vec::new();
    let mut current = block.clone();

    // Safety cap against a producer bug looping forever; a real source
    // fragment is finite and every step either literalises a node or
    // removes a block constructor, so this is never hit in practice.
    const STEP_CAP: usize = 100_000;

    for _ in 0..STEP_CAP {
        match find_fold_in_block(&current) {
            Some(cert) => match apply_block(&cert, &current) {
                Some(next) => {
                    pipeline.push((PassKind::Fold, cert));
                    current = next;
                }
                None => break, // defensive: the oracle disagrees with the finder.
            },
            None => break,
        }
    }

    for _ in 0..STEP_CAP {
        match find_checks_in_block(&current) {
            Some(cert) => match apply_block(&cert, &current) {
                Some(next) => {
                    pipeline.push((PassKind::Checks, cert));
                    current = next;
                }
                None => break,
            },
            None => break,
        }
    }

    pipeline
}

// CUTS (exactly what is NOT here):
//   - No conversion from `gabbro_syntax`/`gabbro-check`'s checked AST: this
//     file works over the self-contained input model of §1 (see the module
//     header for why). A real conversion is future work, off this file's
//     scope.
//   - No CLI wiring: `optimise`/`find_strength_opportunities` are library
//     functions nothing calls yet.
//   - Strength reduction is reported, never certified as a `BlockCert`
//     (matches the Lean side: `checkStrength` has no certificate wrapper).
//   - GVN/CSE, dead code, alias motion, LICM, inlining, unrolling and
//     peephole/allocation rules have no Lean validator yet
//     (`OptimizationRules.lean`'s own CUTS), so this producer finds nothing
//     for `PassKind::{Cfg,Gvn,Strength,Alias,Licm,Inline,Unroll,Peephole}`
//     certificates — there are none to find.
//   - The producer's search order (which opportunity it finds first) is an
//     implementation choice, not a specification; soundness does not depend
//     on it, only on every emitted certificate being independently accepted
//     by [`apply_pipeline`]/the Lean validator.
//   - `const_int`'s `Shl`/`Shr`/arithmetic folding guards against Rust
//     `i128` overflow with `checked_*` (returning `None`, i.e. "not
//     foldable") where Lean's unbounded `Int` would not overflow; this can
//     only make the Rust producer MISS a fold Lean would accept, never
//     propose one Lean would refuse.

#[cfg(test)]
mod proben {
    use super::*;

    // -------------------------------------------------------------------
    // §A. Helpers mirroring `OptimizationWitnesses.lean`'s fixtures.
    // -------------------------------------------------------------------

    /// `2 + 3`, widened to `0 .. 10`: `OptimizationWitnesses.five`.
    fn five() -> IExpr {
        IExpr::add(IExpr::lit(2), IExpr::lit(3), Range::new(0, 10))
    }

    /// The folded form of `five`: `OptimizationWitnesses.fiveLit`.
    fn five_lit() -> IExpr {
        IExpr::lit(5).widen(Range::new(0, 10))
    }

    /// A variable bound at `0 .. 5`: `OptimizationWitnesses.xVar`.
    fn x_var() -> IExpr {
        IExpr::var(0, Range::new(0, 5))
    }

    /// `x <= 10`, decided by `x`'s type range: `OptimizationWitnesses.xCheck`.
    fn x_check() -> BExpr {
        BExpr::Le(x_var(), IExpr::lit(10))
    }

    fn store(e: IExpr) -> Stmt {
        Stmt::AssignSlot(IExpr::lit(0), e)
    }

    /// `OptimizationWitnesses.wP`:
    /// `bind x; where x <= 10; narrow x to 0..10; T[0] = x; T[0] = 2 + 3;`
    ///
    /// Inside the `narrow`'s body, `.var .hier` is de Bruijn-innermost: it
    /// names the FRESHLY bound narrowed value (type `0 .. 10`), shadowing
    /// the outer `x` (type `0 .. 5`) that is `narrow`'s own source
    /// expression. Lean's `xVar` plays both roles at different context
    /// depths; this model has no real de Bruijn indices, so the two uses
    /// are spelled out with their own (here identical, since `0 .. 5`
    /// narrows trivially into `0 .. 10`) ranges.
    fn w_p() -> Block {
        Block::Bind(
            IExpr::lit(3).widen(Range::new(0, 5)),
            Box::new(Block::Pruefung(
                x_check(),
                Box::new(Block::Narrow(
                    x_var(),
                    Range::new(0, 10),
                    Box::new(Block::Cons(
                        Box::new(store(x_var().widen(Range::new(0, 10)))),
                        Box::new(Block::Cons(Box::new(store(five())), Box::new(Block::Nil))),
                    )),
                )),
            )),
        )
    }

    /// `OptimizationWitnesses.wPOpt`.
    fn w_p_opt() -> Block {
        Block::Bind(
            IExpr::lit(3).widen(Range::new(0, 5)),
            Box::new(Block::Bind(
                x_var().widen(Range::new(0, 10)),
                Box::new(Block::Cons(
                    Box::new(store(x_var().widen(Range::new(0, 10)))),
                    Box::new(Block::Cons(Box::new(store(five_lit())), Box::new(Block::Nil))),
                )),
            )),
        )
    }

    // -------------------------------------------------------------------
    // §B. Positive probes mirroring §1-2 of OptimizationWitnesses.lean.
    // -------------------------------------------------------------------

    #[test]
    fn wpipe_accepts_matches_witness() {
        // `OptimizationWitnesses.wPipe_accepts`, hand-written exactly as the
        // witness file lays it out: fold the deep store, then drop, then
        // widen.
        let c_fold = BlockCert::Rest(Box::new(BlockCert::Rest(Box::new(BlockCert::Rest(
            Box::new(BlockCert::Rest(Box::new(BlockCert::Head(Box::new(
                StmtCert::AssignSlotValue(ExprCert::FoldInt),
            ))))),
        )))));
        let c_drop = BlockCert::Rest(Box::new(BlockCert::DropCheck));
        let c_narrow = BlockCert::Rest(Box::new(BlockCert::NarrowEntailed));
        let pipeline =
            vec![(PassKind::Fold, c_fold), (PassKind::Checks, c_drop), (PassKind::Checks, c_narrow)];
        assert_eq!(apply_pipeline(&pipeline, &w_p()), Some(w_p_opt()));
    }

    #[test]
    fn producer_reproduces_the_witness_pipeline_outcome() {
        // The PRODUCER must find an admitted pipeline with the same effect
        // as the hand-written witness pipeline (not necessarily the SAME
        // certificates, since search order is an implementation choice).
        let pipeline = optimise(&w_p());
        assert_eq!(apply_pipeline(&pipeline, &w_p()), Some(w_p_opt()));
        let passes: Vec<PassKind> = pipeline.iter().map(|(k, _)| *k).collect();
        assert!(admitted_order(&passes));
        assert!(pipeline.iter().all(|(k, c)| c.fits(*k)));
    }

    #[test]
    fn constint_sound_zeuge() {
        assert_eq!(const_int(&five()), Some(5));
        assert_eq!(const_int(&five()).unwrap(), 5);
    }

    #[test]
    fn constint_orte_zeuge() {
        assert!(!reads_i(&five()));
    }

    #[test]
    fn bounds_sound_zeuge() {
        let b = bounds(&x_var());
        assert_eq!(b, Range::new(0, 5));
    }

    #[test]
    fn constbool_sound_zeuge() {
        assert_eq!(const_bool(&x_check()), Some(true));
    }

    #[test]
    fn foldint_sound_zeuge() {
        assert_eq!(fold_int(&five()), Some(five_lit()));
    }

    #[test]
    fn foldbool_sound_zeuge() {
        assert_eq!(fold_bool(&x_check()), Some(BExpr::Wahr));
    }

    // -------------------------------------------------------------------
    // §C. Strength reduction: positive and poison probes mirroring §4.
    // -------------------------------------------------------------------

    fn y_var() -> IExpr {
        IExpr::var(1, Range::new(0, 100))
    }

    fn y_mul8() -> IExpr {
        IExpr::mul(y_var(), IExpr::lit(8), Range::new(0, 800))
    }

    fn y_div4() -> IExpr {
        IExpr::div(y_var(), IExpr::lit(4), Range::new(0, 25))
    }

    fn y_rem16() -> IExpr {
        IExpr::rem(y_var(), IExpr::lit(16), Range::new(0, 15))
    }

    #[test]
    fn strength_accepts_witness() {
        assert_eq!(check_strength(3, &y_mul8()), Some(TargetOp::Shl(3)));
        assert_eq!(check_strength(2, &y_div4()), Some(TargetOp::Shr(2)));
        assert_eq!(check_strength(4, &y_rem16()), Some(TargetOp::Mask(4)));
    }

    #[test]
    fn strength_word_probe() {
        assert_eq!(TargetOp::Shl(3).run(7), 56);
        assert_eq!(TargetOp::Shr(2).run(7), 1);
        assert_eq!(TargetOp::Mask(4).run(23), 7);
    }

    #[test]
    fn strength_refuses_sdiv_and_srem() {
        let a = IExpr::sdiv(y_var(), IExpr::lit(4), Range::new(0, 25));
        let b = IExpr::srem(y_var(), IExpr::lit(4), Range::new(0, 3));
        assert_eq!(check_strength(2, &a), None);
        assert_eq!(check_strength(2, &b), None);
    }

    #[test]
    fn strength_refuses_non_pow2() {
        let e = IExpr::mul(y_var(), IExpr::lit(6), Range::new(0, 600));
        assert_eq!(check_strength(1, &e), None);
        assert_eq!(check_strength(2, &e), None);
    }

    #[test]
    fn strength_refuses_signed_operand() {
        let signed = IExpr::var(2, Range::new(-5, 5));
        let e = IExpr::mul(signed, IExpr::lit(8), Range::new(-40, 40));
        assert_eq!(check_strength(3, &e), None);
    }

    #[test]
    fn strength_refuses_overflow() {
        let big = IExpr::var(2, Range::new(0, 1i128 << 62));
        let e = IExpr::mul(big, IExpr::lit(8), Range::new(0, (1i128 << 62) * 8));
        assert_eq!(check_strength(3, &e), None);
    }

    #[test]
    fn strength_refuses_wrong_k() {
        assert_eq!(check_strength(2, &y_mul8()), None);
    }

    #[test]
    fn strength_accepts_commuted() {
        let e = IExpr::mul(IExpr::lit(8), y_var(), Range::new(0, 800));
        assert_eq!(check_strength(3, &e), Some(TargetOp::Shl(3)));
    }

    #[test]
    fn strength_commuted_operand_value() {
        // The commuted product's shifted operand is the VARIABLE, not the
        // constant: `strength_commuted_operand`.
        let e = IExpr::mul(IExpr::lit(8), y_var(), Range::new(0, 800));
        match &e.kind {
            IKind::Mul(a, b) => {
                assert!(const_int(a).is_some());
                assert!(const_int(b).is_none());
            }
            _ => panic!("expected Mul"),
        }
    }

    #[test]
    fn strength_refuses_commuted_signed() {
        let signed = IExpr::var(2, Range::new(-5, 5));
        let e = IExpr::mul(IExpr::lit(8), signed, Range::new(-40, 40));
        assert_eq!(check_strength(3, &e), None);
    }

    #[test]
    fn strength_refuses_commuted_overflow() {
        let big = IExpr::var(2, Range::new(0, 1i128 << 62));
        let e = IExpr::mul(IExpr::lit(8), big, Range::new(0, (1i128 << 62) * 8));
        assert_eq!(check_strength(3, &e), None);
    }

    #[test]
    fn strength_refuses_variable_divisor() {
        let divisor = IExpr::var(3, Range::new(1, 4));
        let e = IExpr::div(divisor.clone(), divisor, Range::new(0, 4));
        assert_eq!(check_strength(2, &e), None);
    }

    #[test]
    fn strength_refuses_wide_mask() {
        let e = IExpr::rem(y_var(), IExpr::lit(1i128 << 65), Range::new(0, (1i128 << 65) - 1));
        assert_eq!(check_strength(65, &e), None);
    }

    #[test]
    fn strength_refuses_wide_dividend() {
        let wide = IExpr::var(4, Range::new(0, 1i128 << 64));
        let e = IExpr::div(wide, IExpr::lit(4), Range::new(0, 1i128 << 64));
        assert_eq!(check_strength(2, &e), None);
    }

    #[test]
    fn find_strength_opportunities_finds_mul_div_rem() {
        let b = Block::Cons(
            Box::new(Stmt::AssignVar(y_mul8())),
            Box::new(Block::Cons(
                Box::new(Stmt::AssignVar(y_div4())),
                Box::new(Block::Cons(
                    Box::new(Stmt::AssignVar(y_rem16())),
                    Box::new(Block::Nil),
                )),
            )),
        );
        let hits = find_strength_opportunities(&b);
        let ops: Vec<TargetOp> = hits.iter().map(|h| h.op).collect();
        assert!(ops.contains(&TargetOp::Shl(3)));
        assert!(ops.contains(&TargetOp::Shr(2)));
        assert!(ops.contains(&TargetOp::Mask(4)));
    }

    // -------------------------------------------------------------------
    // §D. Poison probes mirroring §6 of OptimizationWitnesses.lean.
    // -------------------------------------------------------------------

    fn slot_read() -> IExpr {
        IExpr::slot(Range::new(0, 10))
    }

    #[test]
    fn foldbool_refuses_read() {
        let e = BExpr::Le(slot_read(), IExpr::lit(100));
        assert_eq!(const_bool(&e), Some(true));
        assert_eq!(fold_bool(&e), None);
    }

    #[test]
    fn dropcheck_refuses_read() {
        let b = Block::Pruefung(
            BExpr::Le(slot_read(), IExpr::lit(100)),
            Box::new(Block::Nil),
        );
        assert_eq!(apply_block(&BlockCert::DropCheck, &b), None);
    }

    #[test]
    fn dropcheck_refuses_undecided() {
        let b = Block::Pruefung(BExpr::Le(x_var(), IExpr::lit(3)), Box::new(Block::Nil));
        assert_eq!(apply_block(&BlockCert::DropCheck, &b), None);
    }

    #[test]
    fn dropcheck_refuses_false() {
        let b = Block::Pruefung(
            BExpr::Le(IExpr::lit(5), IExpr::lit(2)),
            Box::new(Block::Nil),
        );
        assert_eq!(apply_block(&BlockCert::DropCheck, &b), None);
    }

    #[test]
    fn narrow_refuses_unentailed() {
        let b = Block::Narrow(x_var(), Range::new(0, 3), Box::new(Block::Nil));
        assert_eq!(apply_block(&BlockCert::NarrowEntailed, &b), None);
    }

    #[test]
    fn foldint_refuses_variable() {
        assert_eq!(fold_int(&x_var()), None);
    }

    #[test]
    fn applyexpr_refuses_wrong_type() {
        assert_eq!(apply_bool_cert(ExprCert::FoldInt, &x_check()), None);
        assert_eq!(apply_int_cert(ExprCert::FoldBool, &five()), None);
    }

    #[test]
    fn constbool_refuses_float() {
        assert_eq!(const_bool(&BExpr::FloatLt), None);
        assert_eq!(const_bool(&BExpr::FloatLe), None);
    }

    #[test]
    fn applyblock_refuses_bad_path() {
        assert_eq!(apply_block(&BlockCert::DropCheck, &w_p()), None);
    }

    #[test]
    fn pipeline_refuses_order() {
        let c_drop = BlockCert::Rest(Box::new(BlockCert::DropCheck));
        let c_fold = BlockCert::Rest(Box::new(BlockCert::Rest(Box::new(BlockCert::Rest(
            Box::new(BlockCert::Rest(Box::new(BlockCert::Head(Box::new(
                StmtCert::AssignSlotValue(ExprCert::FoldInt),
            ))))),
        )))));
        let c_narrow = BlockCert::Rest(Box::new(BlockCert::NarrowEntailed));
        let pipeline = vec![
            (PassKind::Checks, c_drop),
            (PassKind::Fold, c_fold),
            (PassKind::Checks, c_narrow),
        ];
        assert_eq!(apply_pipeline(&pipeline, &w_p()), None);
    }

    #[test]
    fn pipeline_refuses_mislabel() {
        let c_fold = BlockCert::Rest(Box::new(BlockCert::Rest(Box::new(BlockCert::Rest(
            Box::new(BlockCert::Rest(Box::new(BlockCert::Head(Box::new(
                StmtCert::AssignSlotValue(ExprCert::FoldInt),
            ))))),
        )))));
        let pipeline = vec![(PassKind::Checks, c_fold)];
        assert_eq!(apply_pipeline(&pipeline, &w_p()), None);
    }

    #[test]
    fn checkcond_refuses_read() {
        let b = Block::Pruefung(
            BExpr::Le(slot_read(), IExpr::lit(100)),
            Box::new(Block::Nil),
        );
        assert_eq!(apply_block(&BlockCert::CheckCond(ExprCert::FoldBool), &b), None);
    }

    #[test]
    fn bindvalue_refuses_variable() {
        let b = Block::Bind(x_var(), Box::new(Block::Nil));
        assert_eq!(apply_block(&BlockCert::BindValue(ExprCert::FoldInt), &b), None);
    }

    #[test]
    fn narrowvalue_refuses_variable() {
        let b = Block::Narrow(x_var(), Range::new(0, 10), Box::new(Block::Nil));
        assert_eq!(apply_block(&BlockCert::NarrowValue(ExprCert::FoldInt), &b), None);
    }

    #[test]
    fn applyorkeep_refused_keeps() {
        assert_eq!(apply_or_keep(&BlockCert::DropCheck, &w_p()), w_p());
    }

    // -------------------------------------------------------------------
    // §E. Loops and option branches, mirroring §7.
    // -------------------------------------------------------------------

    fn loop_body(e: IExpr) -> Block {
        Block::Cons(Box::new(store(e)), Box::new(Block::Nil))
    }

    fn w_l() -> Block {
        Block::Cons(Box::new(Stmt::Traverse(Box::new(loop_body(five())))), Box::new(Block::Nil))
    }

    fn w_l_opt() -> Block {
        Block::Cons(
            Box::new(Stmt::Traverse(Box::new(loop_body(five_lit())))),
            Box::new(Block::Nil),
        )
    }

    #[test]
    fn loop_accepts_and_sound() {
        let c_loop = BlockCert::Head(Box::new(StmtCert::TraverseBody(Box::new(BlockCert::Head(
            Box::new(StmtCert::AssignSlotValue(ExprCert::FoldInt)),
        )))));
        assert_eq!(apply_block(&c_loop, &w_l()), Some(w_l_opt()));
    }

    #[test]
    fn producer_reaches_into_loop_body() {
        let pipeline = optimise(&w_l());
        assert_eq!(apply_pipeline(&pipeline, &w_l()), Some(w_l_opt()));
    }

    #[test]
    fn loop_path_refuses_wrong_shape() {
        let wrong_target = Block::Cons(
            Box::new(Stmt::OnOption(Box::new(Block::Nil), Box::new(Block::Nil))),
            Box::new(Block::Nil),
        );
        let c = BlockCert::Head(Box::new(StmtCert::TraverseBody(Box::new(BlockCert::Head(
            Box::new(StmtCert::AssignSlotValue(ExprCert::FoldInt)),
        )))));
        assert_eq!(apply_block(&c, &wrong_target), None);
    }

    #[test]
    fn pipeline_refuses_loop_mislabel() {
        let c_loop = BlockCert::Head(Box::new(StmtCert::TraverseBody(Box::new(BlockCert::Head(
            Box::new(StmtCert::AssignSlotValue(ExprCert::FoldInt)),
        )))));
        let pipeline = vec![(PassKind::Checks, c_loop)];
        assert_eq!(apply_pipeline(&pipeline, &w_l()), None);
    }

    #[test]
    fn retry_accepts() {
        let cond = BExpr::Le(IExpr::lit(1), IExpr::lit(2));
        let b = Block::Cons(
            Box::new(Stmt::Retry(cond, Box::new(loop_body(five())), Box::new(Block::Nil))),
            Box::new(Block::Nil),
        );
        let pipeline = vec![
            (PassKind::Fold, BlockCert::Head(Box::new(StmtCert::RetryCond(ExprCert::FoldBool)))),
            (
                PassKind::Fold,
                BlockCert::Head(Box::new(StmtCert::RetryBody(Box::new(BlockCert::Head(
                    Box::new(StmtCert::AssignSlotValue(ExprCert::FoldInt)),
                ))))),
            ),
        ];
        let expect = Block::Cons(
            Box::new(Stmt::Retry(BExpr::Wahr, Box::new(loop_body(five_lit())), Box::new(Block::Nil))),
            Box::new(Block::Nil),
        );
        assert_eq!(apply_pipeline(&pipeline, &b), Some(expect));
    }

    #[test]
    fn opt_none_branch_accepts() {
        let b = Block::Cons(
            Box::new(Stmt::OnOption(Box::new(Block::Nil), Box::new(loop_body(five())))),
            Box::new(Block::Nil),
        );
        let c = BlockCert::Head(Box::new(StmtCert::OptNoneBranch(Box::new(BlockCert::Head(
            Box::new(StmtCert::AssignSlotValue(ExprCert::FoldInt)),
        )))));
        let expect = Block::Cons(
            Box::new(Stmt::OnOption(Box::new(Block::Nil), Box::new(loop_body(five_lit())))),
            Box::new(Block::Nil),
        );
        assert_eq!(apply_block(&c, &b), Some(expect));
    }

    // -------------------------------------------------------------------
    // §F. Serialisation round-trip.
    // -------------------------------------------------------------------

    #[test]
    fn pipeline_serialisation_round_trips() {
        let pipeline = optimise(&w_p());
        let text = render_pipeline(&pipeline);
        let parsed = parse_pipeline(&text).expect("parse");
        assert_eq!(parsed, pipeline);
    }

    #[test]
    fn serialisation_is_stable_text() {
        let cert = BlockCert::Head(Box::new(StmtCert::AssignSlotValue(ExprCert::FoldInt)));
        assert_eq!(cert.to_string(), "(head (assign-slot-value (fold-int)))");
        let op = TargetOp::Shl(3);
        assert_eq!(op.to_string(), "(shl 3)");
    }

    // -------------------------------------------------------------------
    // §G. Property-style tests: every emitted certificate satisfies the
    // oracle, over a small exhaustive sweep of ranges and constants.
    // -------------------------------------------------------------------

    #[test]
    fn exhaustive_fold_and_checks_over_small_programs() {
        for lo in -2i128..=2 {
            for hi in lo..=4 {
                for k in lo..=hi {
                    // `let x : lo..hi = k; where x <= hi+1 else leave; T[0] = 1 + 1;`
                    let block = Block::Bind(
                        IExpr::lit(k).widen(Range::new(lo, hi)),
                        Box::new(Block::Pruefung(
                            BExpr::Le(IExpr::var(0, Range::new(lo, hi)), IExpr::lit(hi + 1)),
                            Box::new(Block::Cons(
                                Box::new(store(IExpr::add(
                                    IExpr::lit(1),
                                    IExpr::lit(1),
                                    Range::new(0, 10),
                                ))),
                                Box::new(Block::Nil),
                            )),
                        )),
                    );
                    let pipeline = optimise(&block);
                    // Every emitted pipeline must be admitted order and
                    // pass-correct, and must actually be accepted when
                    // run against the ORIGINAL block.
                    let passes: Vec<PassKind> = pipeline.iter().map(|(p, _)| *p).collect();
                    assert!(admitted_order(&passes), "pipeline out of rank order: {pipeline:?}");
                    assert!(
                        pipeline.iter().all(|(p, c)| c.fits(*p)),
                        "mislabelled certificate: {pipeline:?}"
                    );
                    assert!(
                        apply_pipeline(&pipeline, &block).is_some(),
                        "producer emitted a pipeline the oracle refuses: {pipeline:?}"
                    );
                    // The check is always decided true here (hi <= hi+1
                    // always), with no read, so the producer MUST have
                    // found the drop.
                    assert!(pipeline.iter().any(|(p, c)| *p == PassKind::Checks
                        && matches!(c, BlockCert::Rest(inner) if matches!(**inner, BlockCert::DropCheck))));
                }
            }
        }
    }

    #[test]
    fn exhaustive_strength_candidates_agree_with_check_strength() {
        for k in 0u32..=6 {
            for a_hi in [0i128, 1, 7, 100] {
                let pow = 1i128 << k;
                let a = IExpr::var(0, Range::new(0, a_hi));
                let mul = IExpr::mul(a.clone(), IExpr::lit(pow), Range::new(0, a_hi * pow));
                let found = strength_at_node(&mul);
                if let Some((fk, op)) = found {
                    assert_eq!(fk, k);
                    assert_eq!(check_strength(fk, &mul), Some(op));
                }
                // And whatever `check_strength` says at the derived `k`
                // must agree with what the finder found (or did not find).
                let direct = check_strength(k, &mul);
                assert_eq!(found.map(|(_, op)| op), direct);
            }
        }
    }

    #[test]
    fn exhaustive_decide_functions_agree_with_brute_force() {
        for a_lo in -3i128..=0 {
            for a_hi in a_lo..=3 {
                for b_lo in -3i128..=0 {
                    for b_hi in b_lo..=3 {
                        let pa = Range::new(a_lo, a_hi);
                        let pb = Range::new(b_lo, b_hi);
                        let le = decide_le(pa, pb);
                        let lt = decide_lt(pa, pb);
                        let eq = decide_eq(pa, pb);
                        for x in a_lo..=a_hi {
                            for y in b_lo..=b_hi {
                                if let Some(v) = le {
                                    assert_eq!(x <= y, v, "decideLe disagreement at {x},{y}");
                                }
                                if let Some(v) = lt {
                                    assert_eq!(x < y, v, "decideLt disagreement at {x},{y}");
                                }
                                if let Some(v) = eq {
                                    assert_eq!(x == y, v, "decideEq disagreement at {x},{y}");
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
