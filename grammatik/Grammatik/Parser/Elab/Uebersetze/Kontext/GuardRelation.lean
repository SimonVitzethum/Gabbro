module

public import Grammatik.Parser.Elab.Uebersetze.Kontext.GuardNarrowing
public import Grammatik.Kern.Semantik.Semantik.T1.Teil1
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

/-! ### Relational facts of a guard

A comparison of two immutable number locals, `x >= y`, `x > y`, `x <= y`, `x < y`, `x == y` (and their
negations), relates the two: it is kept as facts `p - q ≥ k`, each a triple `(p, q, k)`. The facts of a block
are applied to the block itself (`uRelBlock`): every difference `p - q` it reads is replaced by a fresh local
`#rel:p:q`, bound once at the start of the block to `p - q` narrowed to the bound (`USide.eng`, no `else`, no
new return path), exactly as the unary narrowing rebinds a local (`uWaechterBindung`).

Why the bound holds wherever the fresh local is read, so that the fallback of `eng` is never taken:
- the block starts only on paths where the guard (or its negation) has just been tested, and `p`, `q` are
  immutable and keep their value between the test and the start (a unary rebinding at the start keeps the value);
- the declared ranges of `p` and `q` bound `p - q` by `lo p - hi q .. hi p - lo q` (machine G's `Expr.sub` is the
  exact integer difference, `Zahl.sub`; no wrap, no refusal before `eng` sees the value), the facts add `k ≤ p - q`;
- a difference is replaced only up to the first statement that may bind `p`, `q` or the fresh name
  (`uBindetS`, which answers `"*"` for every form it does not know): after that statement the source names may
  denote other values, so the rest keeps its text.
The local is evaluated once at the start of the block; the expression it replaces is pure and its operands do not
change inside the block, so every read sees the value the replaced difference would have. -/

/-- What `x op y` (`pos`) or its negation says as facts `p - q ≥ k`. -/
def uRelCmp (pos : Bool) (op x y : String) : List (String × String × Int) :=
  if pos then
    if strEq op ">=" then [(x, y, 0)] else if strEq op ">" then [(x, y, 1)]
    else if strEq op "<=" then [(y, x, 0)] else if strEq op "<" then [(y, x, 1)]
    else if strEq op "==" then [(x, y, 0), (y, x, 0)] else []
  else
    if strEq op ">=" then [(y, x, 1)] else if strEq op ">" then [(y, x, 0)]
    else if strEq op "<=" then [(x, y, 1)] else if strEq op "<" then [(x, y, 0)]
    else if strEq op "!=" then [(x, y, 0), (y, x, 0)] else []

/-- The facts of a guard over two locals (under `and`; their negations under `or`), as `uGrenzen` reads bounds. -/
def uRelAus : Bool → UEns → List (String × String × Int)
  | pos, .cmp op (.param x) (.param y) => uRelCmp pos op x y
  | true, .and a b => uRelAus true a ++ uRelAus true b
  | false, .or a b => uRelAus false a ++ uRelAus false b
  | pos, .not a => uRelAus (!pos) a
  | _, _ => []

/-- The facts of one side of a guard about two different immutable number locals: the names hidden by
    `uWaechterCtx` (`let mut` locals, untyped locals of deferred range) and every kind but a plain number carry
    none. -/
def uRelFakten (ctx : UCtx) (cv : UEns) (pos : Bool) : List (String × String × Int) :=
  let hidden := uWaechterCtx ctx
  (uRelAus pos cv).filter (fun f =>
    !strEq f.1 f.2.1 && (uWaechterBereich hidden f.1).isSome && (uWaechterBereich hidden f.2.1).isSome)

/-- The ordered differences the facts concern, each once: both `p - q` and `q - p` of every fact. -/
def uRelPaare (fs : List (String × String × Int)) : List (String × String) :=
  fs.foldl (fun (acc : List (String × String)) f =>
    [(f.1, f.2.1), (f.2.1, f.1)].foldl (fun (acc : List (String × String)) pq =>
      if acc.any (fun r => strEq r.1 pq.1 && strEq r.2 pq.2) then acc else acc ++ [pq]) acc) []

/-- The range of `p - q` in `ctx` under the facts: the declared ranges give `lo p - hi q .. hi p - lo q`, a fact
    `p - q ≥ k` raises the bottom to `k`, a fact `q - p ≥ k` lowers the top to `-k`. Only a non-empty range that
    is smaller than the declared one counts. -/
def uRelBereich (ctx : UCtx) (fs : List (String × String × Int)) (p q : String) : Option (Int × Int) :=
  let hidden := uWaechterCtx ctx
  match uWaechterBereich hidden p, uWaechterBereich hidden q with
  | some (lp, hp), some (lq, hq) =>
    let lo := lp - hq
    let hi := hp - lq
    let lo' := fs.foldl (fun acc f => if strEq f.1 p && strEq f.2.1 q then max acc f.2.2 else acc) lo
    let hi' := fs.foldl (fun acc f => if strEq f.1 q && strEq f.2.1 p then min acc (-f.2.2) else acc) hi
    if lo' ≤ hi' && !(lo' == lo && hi' == hi) then some (lo', hi') else none
  | _, _ => none

/-- The fresh local that stands for `p - q` (no source name contains `#`). -/
def uRelName (p q : String) : String := "#rel:" ++ p ++ ":" ++ q

/-- Whether an expression is the name `v`. -/
def uRelIst (v : String) : SExpr → Bool
  | .variable p => strEq p v
  | _ => false

mutual
/-- Every `x - y` of two names read as the name `n`, through arithmetic, comparisons, indices, fields and call
    arguments; every other form (folds, quantifiers, `old`, ...) keeps its text. -/
def uRelErsetzeE (x y n : String) : SExpr → SExpr
  | .bin op a b =>
    if strEq op "-" && uRelIst x a && uRelIst y b then .variable n
    else .bin op (uRelErsetzeE x y n a) (uRelErsetzeE x y n b)
  | .un op a => .un op (uRelErsetzeE x y n a)
  | .index a i => .index (uRelErsetzeE x y n a) (uRelErsetzeE x y n i)
  | .field a f => .field (uRelErsetzeE x y n a) f
  | .call g args => .call g (uRelErsetzeEL x y n args)
  | e => e
/-- `uRelErsetzeE` over call arguments, in order. -/
def uRelErsetzeEL (x y n : String) : List SExpr → List SExpr
  | [] => []
  | a :: rest => uRelErsetzeE x y n a :: uRelErsetzeEL x y n rest
end

/-- Rewrite the value of a return, preserving all other endings. -/
def uRewriteRuntimeReturn (rewrite : SExpr → SExpr) : Option SEnde → Option SEnde
  | some (.ret (some v)) => some (.ret (some (rewrite v)))
  | en => en

/-- Shared traversal of runtime reads for snapshot substitutions. The caller must first
    exclude every statement that can change or hide the substituted place (`uBindetS`). -/
def uRewriteRuntimeReads (rewrite : SExpr → SExpr) : Nat → SAnw → SAnw
  | 0, s => s
  | f + 1, s =>
    match s with
    | .bind m v t a => .bind m v t (rewrite a)
    | .bindQ m v t a => .bindQ m v t (rewrite a)
    | .bindElse v t a r b => .bindElse v t (rewrite a) r (uRewriteRuntimeReads rewrite f b)
    | .set p o a => .set (rewrite p) o (rewrite a)
    | .call g xs => .call g (xs.map rewrite)
    | .callQ g xs => .callQ g (xs.map rewrite)
    | .callElse g xs r b => .callElse g (xs.map rewrite) r (uRewriteRuntimeReads rewrite f b)
    | .cond c t ei els =>
      .cond (rewrite c) (uRewriteRuntimeReads rewrite f t) (ei.map (uRewriteRuntimeReads rewrite f))
        (els.map (uRewriteRuntimeReads rewrite f))
    | .elsif c b => .elsif (rewrite c) (uRewriteRuntimeReads rewrite f b)
    | .cases c as => .cases (rewrite c) (as.map (uRewriteRuntimeReads rewrite f))
    | .arm c k b => .arm c k (uRewriteRuntimeReads rewrite f b)
    | .locks sh l b => .locks sh l (uRewriteRuntimeReads rewrite f b)
    | .child b => .child (uRewriteRuntimeReads rewrite f b)
    | .ret v => .ret (v.map rewrite)
    | .block as en => .block (as.map (uRewriteRuntimeReads rewrite f)) (uRewriteRuntimeReturn rewrite en)
    | s => s
termination_by structural fuel => fuel

/-- Relational narrowing uses the common read traversal after its binder barrier check. -/
def uRelErsetzeS (x y n : String) := uRewriteRuntimeReads (uRelErsetzeE x y n)

def uRelErsetzeEnde (x y n : String) := uRewriteRuntimeReturn (uRelErsetzeE x y n)

/-- The root changed by an assignment. Indices are reads, rather than additional targets.
    Unknown place forms conservatively stand for every local. -/
def uAssignmentRoots : SExpr → List String
  | .variable name => [name]
  | .field base _ | .index base _ | .arrow base _ => uAssignmentRoots base
  | _ => ["*"]

/-- The names a statement may bind or change, nested blocks included: every binder,
    the root of each assigned place, and `"*"` for an unknown form or exhausted fuel. -/
def uBindetS : Nat → SAnw → List String
  | 0, _ => ["*"]
  | f + 1, a => match a with
    | .bind _ x _ _ | .bindLib _ x _ _ | .allocVon _ x _ _ | .bindQ _ x _ _ | .bindAxiomOpt x _ _
    | .reset x _ | .retires x => [x]
    | .await x _ _ w | .swap x _ _ w => [x, w]
    | .bindElse x _ _ r b | .bindAxiomOptElse x _ _ r b => x :: r :: uBindetS f b
    | .set p _ _ => uAssignmentRoots p
    | .shift p o w => uLiestE f p ++ [o, w]
    | .call .. | .lcall .. | .callQ .. | .genericCall .. | .leave .. | .next .. | .ret .. | .free ..
    | .start .. => []
    | .emit _ _ w => [w]
    | .step x y => [x, y]
    | .cond _ t ei els => uBindetS f t ++ ei.flatMap (uBindetS f) ++ (els.map (uBindetS f)).getD []
    | .elsif _ b | .waive _ b | .child b | .locks _ _ b => uBindetS f b
    | .boundedLoop raw b => (boundedLoopLocals raw).map Prod.fst ++ uBindetS f b
    | .retry l b | .loop l b | .watch l b => l :: uBindetS f b
    | .cases _ as => as.flatMap (uBindetS f)
    | .arm _ k b => k.toList ++ uBindetS f b
    | .each x _ _ _ _ _ _ b => x :: uBindetS f b
    | .trim c _ b => uLiestE f c ++ uBindetS f b
    | .trimReq c _ => uLiestE f c
    | .alloc _ x _ _ _ b => x :: (b.map (uBindetS f)).getD []
    | .grow x _ b => x :: uBindetS f b
    | .callElse _ _ r b | .callIndElse _ _ r b => r :: uBindetS f b
    | .block as _ => as.flatMap (uBindetS f)
    | _ => ["*"]
termination_by structural fuel => fuel

/-- The statements of a run with every `x - y` read as `n`, up to the first statement that may bind `x`, `y` or
    `n` (that statement and the rest keep their text), and whether the whole run was rewritten. -/
def uRelErsetzeL (x y n : String) : List SAnw → List SAnw × Bool
  | [] => ([], true)
  | s :: rest =>
    if (uBindetS uLiestTiefe s).any (fun b => strEq b x || strEq b y || strEq b n || strEq b "*") then
      (s :: rest, false)
    else
      let (rest', whole) := uRelErsetzeL x y n rest
      (uRelErsetzeS x y n uLiestTiefe s :: rest', whole)

/-- The binding of the fresh local `n` to `p - q` narrowed to `lo .. hi`, and the context in which `n` is an
    immutable number of that range. -/
def uRelBindung (ctx : UCtx) (p q : String) (lo hi : Int) : UStmt × UCtx :=
  let n := uRelName p q
  (UStmt.bind n (some (lo, hi)) (USide.eng (USide.sub (USide.param p) (USide.param q)) lo hi),
   { ctx with names := n :: ctx.names, kinds := UParamArt.int :: ctx.kinds,
              types := Ty.int lo hi :: ctx.types, bits := 0 :: ctx.bits })

/-- A block (its statements and its ending) under the facts `fs`, elaborated in `ctx`: for every difference
    `p - q` the facts bound better than the declared ranges (`uRelBereich`) and the block reads, the binding of
    `#rel:p:q` (`uRelBindung`), the context with it, and the block with the difference read as that local
    (`uRelErsetzeL`; the ending only when no statement binds the names). A difference the block does not read adds
    nothing. -/
def uRelBlock (ctx : UCtx) (fs : List (String × String × Int)) (ss : List SAnw) (e : Option SEnde) :
    List UStmt × UCtx × List SAnw × Option SEnde :=
  (uRelPaare fs).foldl (fun (acc : List UStmt × UCtx × List SAnw × Option SEnde) pq =>
    match uRelBereich acc.2.1 fs pq.1 pq.2 with
    | none => acc
    | some (lo, hi) =>
      let n := uRelName pq.1 pq.2
      let (ss', whole) := uRelErsetzeL pq.1 pq.2 n acc.2.2.1
      let e' := if whole then uRelErsetzeEnde pq.1 pq.2 n acc.2.2.2 else acc.2.2.2
      if (uLiestL (ss' ++ [SAnw.block [] e'])).any (fun r => strEq r n) then
        let (stmt, ctx') := uRelBindung acc.2.1 pq.1 pq.2 lo hi
        (acc.1 ++ [stmt], ctx', ss', e')
      else acc) ([], ctx, ss, e)

/-- A continuation guard on these operands can narrow their difference
    after the first arm exits. The ordinary elaborator still decides
    whether the operands actually retain their values at each later read. -/
def uRelContinuation (left right : String) : SAnw → Bool
  | .cond (.bin op (.variable x) (.variable y)) (.block _ ending) [] none =>
    ending.isSome &&
      (uRelCmp false op x y).any fun fact =>
        (strEq fact.1 left && strEq fact.2.1 right) ||
          (strEq fact.1 right && strEq fact.2.1 left)
  | _ => false

/-- Let the ordinary statement reader see a guarded final return. Its
    result is separated from the statement list after elaboration. -/
def uRelReturn : List SAnw → Option SEnde → Option (List SAnw)
  | [], _ => none
  | statements@(_ :: _), some (.ret (some value@(.bin "-" (.variable left) (.variable right)))) =>
    if statements.any (uRelContinuation left right) then
      some (statements ++ [.ret (some value)])
    else none
  | _, _ => none

/-- The continuation reader receives the same return expression, with no
    extra source binding. -/
theorem uRelReturn_difference (statements : List SAnw) (left right : String)
    (guarded : statements.any (uRelContinuation left right) = true) :
    uRelReturn statements (some (.ret (some (.bin "-" (.variable left) (.variable right))))) =
      some (statements ++ [.ret (some (.bin "-" (.variable left) (.variable right)))]) := by
  cases statements with
  | nil => cases guarded
  | cons first rest => simp only [uRelReturn, guarded, ↓reduceIte]

/-- The false side of the less-than guard gives the lower bound used by
    subtraction. The declared intervals still bound the signed difference. -/
theorem uRelReturn_bounds {left right loLeft hiLeft loRight hiRight : Int}
    (leftRange : loLeft ≤ left ∧ left ≤ hiLeft)
    (rightRange : loRight ≤ right ∧ right ≤ hiRight)
    (passed : ¬ left < right) :
    max (loLeft - hiRight) 0 ≤ left - right ∧ left - right ≤ hiLeft - loRight := by
  constructor <;> omega

/-- The lowered value on the fallthrough of a less-than guard is the
    mathematical difference. Its narrowing never evaluates the fallback. -/
theorem uRelReturn_eval {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {loLeft hiLeft loRight hiRight : Int}
    (left : Expr D Γ Λ (.int loLeft hiLeft)) (right : Expr D Γ Λ (.int loRight hiRight))
    (fallback : Expr D Γ Λ (.int (max (loLeft - hiRight) 0) (hiLeft - loRight)))
    (initial current : World D) (env : Env D Γ)
    (passed : ¬ (eval initial left current env).n < (eval initial right current env).n) :
    (eval initial (.eng (.sub left right) (max (loLeft - hiRight) 0) (hiLeft - loRight) fallback)
      current env).n = (eval initial left current env).n - (eval initial right current env).n := by
  let a := eval initial left current env
  let b := eval initial right current env
  have bounded := uRelReturn_bounds (loLeft := loLeft) (hiLeft := hiLeft)
    (loRight := loRight) (hiRight := hiRight) ⟨a.lo_le, a.le_hi⟩ ⟨b.lo_le, b.le_hi⟩ passed
  simp only [eval, Zahl.sub]
  dsimp only [a, b] at bounded
  rw [dif_pos bounded]

-- Keep a partially applied large-fuel visitor as a function during closed cbv checks.
-- Its canonical equation evaluates only the fully supplied statement.
attribute [cbv_opaque] uRewriteRuntimeReads
attribute [cbv_eval] uRewriteRuntimeReads.eq_def

end Gabbro.Grammatik.Parser.Uebersetze
