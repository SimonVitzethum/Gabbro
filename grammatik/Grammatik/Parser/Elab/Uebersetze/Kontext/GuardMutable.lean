module

public import Grammatik.Parser.Elab.Uebersetze.Kontext.GuardRelation

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

/-! ### Block-local snapshots of guarded mutable numbers

Only `uCond` with `ctx.narrow` on applies these facts. The fresh immutable `#mut:x` is evaluated at the start
of the selected block, directly after the guard was tested on that path; no source statement lies between
the test and the block start. Other generated prefix bindings are pure and cannot assign `x`. Every replaced
read lies in straight-line order before the first statement that may assign or rebind `x`; only the value of
a plain `x = v` is still rewritten, never its target. Thus `x` still holds the snapshot's value at each
replaced read. These expressions replace pure local reads. Nothing inside a nested block or loop body is
rewritten, and every such statement is a barrier, so no replaced read can execute after an assignment by
coming around a loop. A guard inside an enclosing loop takes a new snapshot on each entry to its block.
The unary fact holds at the snapshot, so the fallback of the total `USide.eng` is unreachable.

Only then blocks and plain else blocks get snapshots; an else-if chain gets no outer mutable fact. Mutable
facts NEVER reach the continuation, even when the then block always ends: an else block may have assigned
the local. Immutable narrowing and its continuation rule retain their existing implementation. -/

/-- Unary facts about mutable numbers at the instant of the guard test. Unknown ranges stay hidden;
    immutable and relational fact extraction still use the original context that hides mutable names. -/
def uMutFakten (ctx : UCtx) (cv : UEns) (pos : Bool) : List (String × Int × Int) :=
  (uWaechterFakten {ctx with muts := []} cv pos).filter (fun f => ctx.muts.any (strEq f.1))

/-- An unspellable source name for the immutable snapshot of `x`. -/
def uMutName (x : String) : String := "#mut:" ++ x

mutual
/-- Replace pure reads of `x` in the same expression forms as relational narrowing. Other forms keep
    their text; in particular no fold, quantifier or `old` expression is traversed. -/
def uMutErsetzeE (x n : String) : SExpr → SExpr
  | .variable v => if strEq v x then .variable n else .variable v
  | .bin op a b => .bin op (uMutErsetzeE x n a) (uMutErsetzeE x n b)
  | .un op a => .un op (uMutErsetzeE x n a)
  | .index a i => .index (uMutErsetzeE x n a) (uMutErsetzeE x n i)
  | .field a f => .field (uMutErsetzeE x n a) f
  | .call g args => .call g (uMutErsetzeEL x n args)
  | e => e
/-- `uMutErsetzeE` over call arguments. -/
def uMutErsetzeEL (x n : String) : List SExpr → List SExpr
  | [] => []
  | a :: rest => uMutErsetzeE x n a :: uMutErsetzeEL x n rest
end

/-- Rewrite only an ending's return value. -/
def uMutErsetzeEnde (x n : String) : Option SEnde → Option SEnde
  | some (.ret (some v)) => some (.ret (some (uMutErsetzeE x n v)))
  | en => en

/-- The straight-line forms we understand. Every nested block and every other form is a barrier,
    even if `uBindetS` could show that it binds no relevant name. -/
def uMutGerade : SAnw → Bool
  | .bind .. | .bindQ .. | .set .. | .call .. | .callQ .. | .ret .. => true
  | _ => false

/-- Rewrite one understood statement; the list walker first checks its binders and assigned place.
    Never recurse into a nested block. -/
def uMutErsetzeS (x n : String) : SAnw → SAnw
  | .bind m v t a => .bind m v t (uMutErsetzeE x n a)
  | .bindQ m v t a => .bindQ m v t (uMutErsetzeE x n a)
  | .set p o a => .set p o (uMutErsetzeE x n a)
  | .call g xs => .call g (uMutErsetzeEL x n xs)
  | .callQ g xs => .callQ g (uMutErsetzeEL x n xs)
  | .ret v => .ret (v.map (uMutErsetzeE x n))
  | s => s

/-- Rewrite until the first potential assignment or rebinding. A plain `x = v` rewrites `v`, preserves
    the target and stops; every other barrier keeps itself and the rest unchanged. The Boolean says whether
    the ending may also be rewritten. The conservative assigned-place test is shared with `uRelErsetzeL`. -/
def uMutErsetzeL (x n : String) : List SAnw → List SAnw × Bool
  | [] => ([], true)
  | s :: rest =>
    let plain := match s with
      | .set (.variable v) op _ => strEq v x && strEq op "="
      | _ => false
    if plain then (uMutErsetzeS x n s :: rest, false)
    else if !uMutGerade s || (uBindetS uLiestTiefe s).any
        (fun b => strEq b x || strEq b n || strEq b "*") then (s :: rest, false)
    else
      let (rest', whole) := uMutErsetzeL x n rest
      (uMutErsetzeS x n s :: rest', whole)

/-- Bind a fresh immutable snapshot, retaining the source local's storage width for bit operations.
    The original mutable local remains in the context with its declared type and assignment target. -/
def uMutBindung (ctx : UCtx) (x : String) (lo hi : Int) : UStmt × UCtx :=
  let n := uMutName x
  let bits : Nat := match uParamNr ctx x with
    | .ok j => ctx.bits.getD j 0
    | .error _ => 0
  (UStmt.bind n (some (lo, hi)) (USide.eng (USide.param x) lo hi),
   { ctx with names := n :: ctx.names, kinds := UParamArt.int :: ctx.kinds,
              types := Ty.int lo hi :: ctx.types, bits := bits :: ctx.bits })

/-- Apply block facts only where a read is actually replaced before the first barrier. Each fact adds
    at most one snapshot; a block with no replaced read adds neither a binding nor a context entry. -/
def uMutBlock (ctx : UCtx) (fs : List (String × Int × Int)) (ss : List SAnw) (e : Option SEnde) :
    List UStmt × UCtx × List SAnw × Option SEnde :=
  fs.foldl (fun (acc : List UStmt × UCtx × List SAnw × Option SEnde) f =>
    let n := uMutName f.1
    let (ss', whole) := uMutErsetzeL f.1 n acc.2.2.1
    let e' := if whole then uMutErsetzeEnde f.1 n acc.2.2.2 else acc.2.2.2
    if (uLiestL (ss' ++ [SAnw.block [] e'])).any (fun r => strEq r n) then
      let (stmt, ctx') := uMutBindung acc.2.1 f.1 f.2.1 f.2.2
      (acc.1 ++ [stmt], ctx', ss', e')
    else acc) ([], ctx, ss, e)

end Gabbro.Grammatik.Parser.Uebersetze
