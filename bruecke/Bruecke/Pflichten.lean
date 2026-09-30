import Grammatik.Parser.Uebersetze
import Gabbro.Body

/-!
# S1 + S2: the duty statements and the body datum, COMPUTED IN LEAN from the parser's `UProg`

`gabbro pflichten --lean` (`crates/gabbro-check/src/lean.rs`) PRINTS, per unit, a duty file: the
body of every routine as a `Body.Stmt` datum, its precondition, its postcondition, its frame, the
`meets` statement a person proves and the wiring. This file COMPUTES the same things from
`UProg` -- the elaborated output of the Lean parser `uebersetzeAllg`, itself computed from the
source text in Lean -- so a wrong Rust print is a failed per-unit check (`Instanz*.lean`), never
a wrong theorem. The definitions here are the reference; the Rust printer is checked against them.

FRAGMENT: exactly what the Lean parser elaborates (`UStmt`: slot writes through a pointer or at
a table, direct calls; a trailing `return`; `ensures` comparisons and their boolean
combination). Everything else is outside the bridge: `zuBody` answers `none` with a reason.
-/

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik (Ty)

namespace Gabbro.Bruecke

open Gabbro.Body

/-! ## 0. Lookups -/

def fnSuch (u : UProg) (n : String) : Option UFn := u.fns.find? (fun f => f.name == n)

/-- The name of the table a pointer parameter points at. -/
def ptrTab (u : UProg) (f : UFn) (p : String) : Option String :=
  match f.params.find? (fun q => q.1 == p) with
  | some (_, .ptr t _) => (u.tabellen[t]?).map (·.name)
  | _ => none

/-- The pointer parameter of `f` that points at the table `tab` -- only when there is exactly one
    (a call that passes "a pointer to `tab`" names no variable in `UArg.freshPtr`). -/
def ptrParam (u : UProg) (f : UFn) (tab : String) : Option String :=
  match f.params.filter (fun q => match q.2 with
      | .ptr t _ => (u.tabellen[t]?).map (·.name) == some tab
      | _ => false) with
  | [q] => some q.1
  | _ => none

/-! ## 1. Expressions -/

def idxExpr : UIdx → Expr
  | .lit n => .lit (.int n)
  | .param p => .name p

/-- One side of a comparison. `alt` (the entry value) is handled by the caller (`altSides`), and
    reads here as the `old#i` binder it is numbered to. -/
def oldName : Nat → String
  | 0 => "old#1" | 1 => "old#2" | 2 => "old#3" | 3 => "old#4" | 4 => "old#5" | 5 => "old#6"
  | 6 => "old#7" | 7 => "old#8" | _ => "old#9"

/-- The place a slot read names. -/
def slotPlace (u : UProg) (f : UFn) : USide → Option Expr
  | .slot p fld i => (ptrTab u f p).map (fun t => .place t (idxExpr i) fld)
  | .tab t fld i => some (.place t (idxExpr i) fld)
  | .alt p fld i => (ptrTab u f p).map (fun t => .place t (idxExpr i) fld)
  | _ => none

/-- Two operands under one Body operator (both must have a Body form). -/
def binE (op : BinOp) : Option Expr → Option Expr → Option Expr
  | some x, some y => some (.bin op x y)
  | _, _ => none

/-- A side outside an `ensures` (a call argument, a returned value, an assigned value): no
    `alt`, no `erg`. Integer arithmetic and the bit operations are Body's `bin` (`binop`: exact
    integers, the masks over non-negative operands); an integer conversion `T(e)` is a WIDENING, so
    it leaves the number alone and reads as its operand (P2 wall 2). -/
def sideExpr (u : UProg) (f : UFn) : USide → Option Expr
  | .lit n => some (.lit (.int n))
  | .param p => some (.name p)
  | .slot p fld i => slotPlace u f (.slot p fld i)
  | .tab t fld i => slotPlace u f (.tab t fld i)
  | .alt .. => none
  | .erg => none
  | .add a b => binE .add (sideExpr u f a) (sideExpr u f b)
  | .sub a b => binE .sub (sideExpr u f a) (sideExpr u f b)
  | .mul a b => binE .mul (sideExpr u f a) (sideExpr u f b)
  | .conv _ _ a => sideExpr u f a
  | .band a b => binE .band (sideExpr u f a) (sideExpr u f b)
  | .bor a b => binE .bor (sideExpr u f a) (sideExpr u f b)
  | .bxor a b => binE .bxor (sideExpr u f a) (sideExpr u f b)

/-- An `ensures` side, numbering the `old(..)` reads met so far: the term, the reads in order,
    whether `result` occurs. -/
structure Acc where
  olds : List Expr := []
  result : Bool := false

def ensSide (u : UProg) (f : UFn) (a : Acc) : USide → Option (Expr × Acc)
  | .alt p fld i =>
      (slotPlace u f (.alt p fld i)).map (fun pl => (.name (oldName a.olds.length), { a with olds := a.olds ++ [pl] }))
  | .erg => some (.name "result", { a with result := true })
  -- Arithmetic INSIDE an `ensures` side has no bridge form yet (the `old`/`result` numbering would
  -- have to thread through the operands): REFUSED by name, so `postU` is `none` and the duty is
  -- false, never a weaker one.
  | .add .. | .sub .. | .mul .. | .conv .. | .band .. | .bor .. | .bxor .. => none
  | s => (sideExpr u f s).map (fun e => (e, a))

def opOf : String → Option BinOp
  | "==" => some .eq | "<" => some .lt | "<=" => some .le | _ => none

def ensExpr (u : UProg) (f : UFn) (a : Acc) : UEns → Option (Expr × Acc)
  | .wahr => some (.lit (.bool true), a)
  | .falsch => some (.lit (.bool false), a)
  | .cmp op l r =>
      match opOf op, ensSide u f a l with
      | some o, some (le, a1) =>
          match ensSide u f a1 r with
          | some (re, a2) => some (.bin o le re, a2)
          | none => none
      | _, _ => none
  | .und x y =>
      match ensExpr u f a x with
      | some (xe, a1) =>
          match ensExpr u f a1 y with
          | some (ye, a2) => some (.bin .and xe ye, a2)
          | none => none
      | none => none
  | .oder x y =>
      match ensExpr u f a x with
      | some (xe, a1) =>
          match ensExpr u f a1 y with
          | some (ye, a2) => some (.bin .or xe ye, a2)
          | none => none
      | none => none
  | .nicht x =>
      match ensExpr u f a x with
      | some (xe, a1) => some (.un .not xe, a1)
      | none => none
  -- A `bool` slot read has no bridge form yet (Body's shapes know numbers only): REFUSED by name,
  -- so `postU` is `none` and the duty is false, never weaker. (A unit with a bool field or a bool
  -- result is refused up front by `stimmigB`'s `keinBoolB`.)
  | .slotB .. | .tabB .. => none

/-! ## 2. Shapes, the precondition, the frame -/

def shapeOfTy : Ty → Option Shape
  | .int lo hi => some (.intIn lo hi)
  | _ => none

/-- `conj`: right-nested `and`, the empty conjunction is `true` (as the printer writes it). -/
def conjE : List Expr → Expr
  | [] => .lit (.bool true)
  | [e] => e
  | e :: es => .bin .and e (conjE es)

def shapeConjuncts (f : UFn) : List Expr :=
  f.params.filterMap (fun q => (shapeOfTy q.2).map (fun sh => Expr.hasShape q.1 sh))

/-- `requires`: the fragment states `Held(L)` only, one clause per held lock, and it reads as
    `true` (a held lock is the caller's duty, carried by the lock rule, not by the value). -/
def preExpr (f : UFn) : Expr :=
  conjE (shapeConjuncts f ++ f.held.map (fun _ => Expr.lit (.bool true)))

/-- The typing of the world: every declared slot field has its range. -/
def slotShape (ts : List UTab) (c : String) (fld : String) : Option Shape :=
  match ts with
  | [] => none
  | t :: rest =>
      if c = t.name then (t.felder.find? (fun q => q.1 == fld)).map (fun q => .intIn q.2.1 q.2.2)
      else slotShape rest c fld

def shapeOfU (u : UProg) : Typing := fun p =>
  match p with
  | .slot c _ fld => slotShape u.tabellen c fld
  | _ => none

/-! ## 3. The body -/

def argExpr (u : UProg) (f : UFn) : UArg → Option Expr
  | .var p => some (.name p)
  | .freshPtr tab _ => (ptrParam u f tab).map (fun p => .name p)
  | .wert s => sideExpr u f s

def argsExpr (u : UProg) (f : UFn) : List UArg → Option (List Expr)
  | [] => some []
  | a :: as =>
      match argExpr u f a, argsExpr u f as with
      | some e, some es => some (e :: es)
      | _, _ => none

def stmtBody (u : UProg) (f : UFn) : UStmt → Option Stmt
  | .assign p fld i v =>
      match ptrTab u f p, sideExpr u f v with
      | some t, some ve => some (.assign t (idxExpr i) fld ve)
      | _, _ => none
  | .assignTab t fld i v => (sideExpr u f v).map (fun ve => .assign t (idxExpr i) fld ve)
  | .assignB .. | .assignTabB .. | .sperrtAuf _ | .sperrtZu => none
  | .call g as =>
      match fnSuch u g, argsExpr u f as with
      | some gf, some es => some (.call g (gf.params.map (·.1)) es (preExpr gf))
      | _, _ => none

def stmtsBody (u : UProg) (f : UFn) : List UStmt → Option (List Stmt)
  | [] => some []
  | s :: ss =>
      match stmtBody u f s, stmtsBody u f ss with
      | some x, some xs => some (x :: xs)
      | _, _ => none

/-- **`zuBody`** -- the body of `f` as `Gabbro.Body` sees it. `none` = outside the fragment. -/
def zuBody (u : UProg) (f : UFn) : Option (List Stmt) :=
  match stmtsBody u f f.saetze with
  | none => none
  | some ss =>
      match f.rueck with
      | .keine => some ss
      | .wert v => (sideExpr u f v).map (fun e => ss ++ [Stmt.ret (some e)])
      | .bool _ => none

/-! ## 4. The postcondition -/

/-- One `ensures` clause as the Prop the printer writes: `old#i` bound over the ENTRY state,
    `result` bound to the answer, the term evaluated at the EXIT world. -/
def clauseAux (t : Expr) (uses : Bool) (s s' : State) (r : Option Value) :
    List Expr → Nat → Binding → Prop
  | [], _, β =>
      if uses then
        ∃ v, r = some v ∧ eval { world := s'.world, local' := bindLocal β "result" v } t = some (.bool true)
      else eval { world := s'.world, local' := β } t = some (.bool true)
  | o :: os, n, β =>
      ∀ ov, eval s o = some ov → clauseAux t uses s s' r os (n + 1) (bindLocal β (oldName n) ov)

def clauseProp (t : Expr) (a : Acc) (s s' : State) (r : Option Value) : Prop :=
  clauseAux t a.result s s' r a.olds 0 s.local'

/-- The clause of an `ensures`, or `none` when it leaves the fragment. -/
def ensClause (u : UProg) (f : UFn) (e : UEns) (s s' : State) (r : Option Value) : Option Prop :=
  (ensExpr u f {} e).map (fun p => clauseProp p.1 p.2 s s' r)

/-- The answer clause: the declared range of the result. -/
def resultClause (f : UFn) (r : Option Value) : Option Prop :=
  f.ergebnis.map (fun lr => ∃ x, r = some (.int x) ∧ lr.1 ≤ x ∧ x ≤ lr.2)

/-- All clauses of the promise beyond well-formedness, in the printer's order. `False`-free:
    a clause outside the fragment makes `ensList` answer `none`. -/
def ensList (u : UProg) (f : UFn) (s s' : State) (r : Option Value) : List UEns → Option (List Prop)
  | [] => some []
  | e :: es =>
      match ensClause u f e s s' r, ensList u f s s' r es with
      | some p, some ps => some (p :: ps)
      | _, _ => none

def andAll : Prop → List Prop → Prop
  | p, [] => p
  | p, q :: qs => p ∧ andAll q qs

/-- `wf s' ∧ answer ∧ clause₁ ∧ …` right-nested. -/
def chain (wf : Prop) : List Prop → Prop
  | [] => wf
  | p :: ps => wf ∧ andAll p ps

/-- **The promise of `f`** -- `_post` of the duty file. `none` = a clause is outside the
    fragment. -/
def postU (u : UProg) (wf : State → Prop) (f : UFn) (s s' : State) (r : Option Value) : Option Prop :=
  match ensList u f s s' r f.sichert with
  | none => none
  | some cs => some (chain (wf s') ((resultClause f r).toList ++ cs))

/-! ## 5. The statements a person owes -/

def preProp (wf : State → Prop) (f : UFn) (t : State) : Prop :=
  wf t ∧ eval t (preExpr f) = some (.bool true)

/-- Insert into a sorted list without repeating (the printer walks a `BTreeSet<String>`; the
    recursion is structural so that `rfl` can reduce it). -/
def insertS (x : String) : List String → List String
  | [] => [x]
  | y :: ys => if x < y then x :: y :: ys else if x = y then y :: ys else y :: insertS x ys

def sortDedup : List String → List String
  | [] => []
  | x :: xs => insertS x (sortDedup xs)

/-- The callees of the body, in the printer's order (sorted by name, each once). -/
def calleesOf (f : UFn) : List String :=
  sortDedup (f.saetze.filterMap (fun s => match s with | .call g _ => some g | _ => none))

/-- The callee hypotheses in front of the turnstile: contract and frame of every callee. -/
def hyps (u : UProg) (wf : State → Prop) (ρ : Env) : List String → Prop → Prop
  | [], c => c
  | g :: gs, c =>
      match fnSuch u g with
      | some gf => Contract ρ g (preProp wf gf) (fun s s' r => (postU u wf gf s s' r).getD False) →
                   Frame ρ g gf.schreibt → hyps u wf ρ gs c
      | none => False

/-- **`meets`** -- what a person proves about `f` (`_meets_statement`). -/
def meetsU (u : UProg) (wf : State → Prop) (f : UFn) (body : List Stmt) : Prop :=
  ∀ (ρ : Env) (s : State), wf s → eval s (preExpr f) = some (.bool true) →
    hyps u wf ρ (calleesOf f)
      (∃ s', finalState (exec ρ body s) = some s' ∧
        (postU u wf f s s' (finalValue (exec ρ body s))).getD False)

end Gabbro.Bruecke
