module

public import Grammatik.Parser.Elab.Uebersetze.Loops.Headers
public import Grammatik.Parser.Elab.Uebersetze.Folds.Expressions
public import Grammatik.Parser.Stmt.LibrarySource
public import Grammatik.Parser.Namen.Gebunden

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Only closed integer arithmetic over declared constants is static. A local with a singleton
    range is still a runtime value, so it cannot silently become a loop bound. -/
def uLoopStatic (ctx : UCtx) (value : SExpr) : Option Int :=
  uSchranke ((ctx.lits.filter fun p => !ctx.names.any (strEq · p.1)).map fun p => (p.1, (p.2, p.2))) value

/-- The same lexical context is used by ordinary export and source check instrumentation. -/
def uLoopBodyContext (ctx : UCtx) : SBoundedHeader → Except String UCtx
  | .whileLoop .. => pure { ctx with loops := "" :: ctx.loops }
  | .forRange binder loExpr hiExpr _ => do
    let (lo, hi) ← match uLoopStatic ctx loExpr, uLoopStatic ctx hiExpr with
      | some lo, some hi => pure (lo, hi)
      | _, _ => throw "for.range.static-integer-required"
    if lo < -9223372036854775808 || 18446744073709551615 < lo ||
        hi < -9223372036854775808 || 18446744073709551615 < hi then
      throw "for.range.machine-integer-required"
    pure { (uMitLokal ctx binder .int (.int (min lo hi) (max lo hi)) (binder :: ctx.muts)) with
      loops := binder :: ctx.loops }

/-- The existing named foreign-call rule, shared by both bounded loop sugars. -/
def uLoopOverflow (ctx : UCtx) (tabs : List UTab) (heads : List UFnKopf)
    (handler : String) : Except String (List UStmt) := do
  let (callee, args) ← uRuf ctx tabs heads handler []
  if !callee.ext then throw "on_exceeded names no foreign body"
  pure [.axCall handler args]

/-- Every explicit `next i` completes the generated index increment as well. The flat
    representation keeps nested markers balanced and retains every other control transfer. -/
def uForNext (binder : String) (increment : List UStmt) (code : List UStmt) : List UStmt :=
  code.flatMap fun s => match s with
    | .next target => if strEq target binder then increment ++ [s] else [s]
    | _ => [s]

/-- Whether a body shadows or may write the index. A store through an index only reads
    that local; ordinary calls receive its value. Opaque source forms remain conservative.
    The shared source-child traversal visits every nested binding and assignment scope. -/
def uForIndexEffects : Nat → String → SAnw → Bool × Bool
  | 0, _, _ => (true, true)
  | fuel + 1, binder, statement =>
    let extra := match statement with
      | .each name .. => [name]
      | .arm _ name _ => name.toList
      | .boundedLoop raw _ => (boundedLoopLocals raw).map Prod.fst
      | .bindElse _ _ _ reason _ | .bindAxiomOptElse _ _ _ reason _
      | .callElse _ _ reason _ | .callIndElse _ _ reason _ => [reason]
      | _ => []
    let writes := match statement with
      | .set (.variable name) _ _ => strEq name binder
      | .other .. | .lcall .. | .bindLib .. | .genericCall .. => true
      | _ => false
    let nested := (libraryChildren statement).map (uForIndexEffects fuel binder)
    (((Aufloesung.gebunden statement) ++ extra).any (strEq · binder) || nested.any (·.1),
      writes || nested.any (·.2))
termination_by structural fuel => fuel

/-- Export the complete source header to the existing retry path. The constant-true branch
    delimits the range index's lexical lifetime, including shadowing of an outer local.
    Required narrowing on the increment preserves arithmetic duties; it never clips a value. -/
def uBoundedLoop (tabs : List UTab) (heads : List UFnKopf)
    (recur : UCtx → List SAnw → Except String (List UStmt × UCtx))
    (ctx : UCtx) (raw : String) (sourceBody : SAnw) (rest : List SAnw) :
    Except String (List UStmt × UCtx) := do
  let header ← readBoundedHeader raw
  let .block statements ending := sourceBody | throw "loop.body.block-required"
  let inner ← uLoopBodyContext ctx header
  match header with
  | .whileLoop condition bound handler =>
    let count ← match uLoopStatic ctx bound with
      | some n => if 0 ≤ n then pure n.toNat else throw "while.bound.static-natural-required"
      | none => throw "while.bound.static-natural-required"
    let test ← uBool ctx condition
    let (body, bodyCtx) ← recur inner statements
    let exits ← uFoldEndeStmt bodyCtx ending
    let overflow ← uLoopOverflow ctx tabs heads handler
    let (tail, after) ← recur ctx rest
    pure ([.retryBeg count (.not test)] ++ body ++ exits ++
      [.ifElse] ++ overflow ++ [.blkEnd] ++ tail, after)
  | .forRange binder loExpr hiExpr handler =>
    let (lo, hi) ← match uLoopStatic ctx loExpr, uLoopStatic ctx hiExpr with
      | some lo, some hi => pure (lo, hi)
      | _, _ => throw "for.range.static-integer-required"
    let (shadowed, writes) := uForIndexEffects 100000 binder sourceBody
    if shadowed then throw "for.index.shadowed"
    if handler.isNone && lo < hi && writes then
      throw "for.on_exceeded.required-for-index-write"
    let lower := min lo hi
    let upper := max lo hi
    let (body, bodyCtx) ← recur inner statements
    let exits ← uFoldEndeStmt bodyCtx ending
    let increment : List UStmt :=
      [.bind "#for-next" none (.add (.param binder) (.lit 1)),
       .narrowReqBeg "#for-next" lower upper, .setVar binder (.param "#for-next")]
    let overflow ← match handler with
      | some name => uLoopOverflow ctx tabs heads name
      | none => pure []
    let (tail, after) ← recur ctx rest
    pure ([.ifBeg .tru, .bindMut binder lower upper (.lit lo),
        .retryBeg (hi - lo).toNat (.not (.cmp "<" (.param binder) (.lit hi)))] ++
      uForNext binder increment (body ++ exits) ++ increment ++ [.ifElse] ++ overflow ++
      [.blkEnd, .ifElse, .blkEnd] ++ tail, after)

end Gabbro.Grammatik.Parser.Uebersetze
