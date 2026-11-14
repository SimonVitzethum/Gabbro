module
public import Grammatik.Parser.Elab.Uebersetze
public import Gabbro.Body
public import Bruecke.Ausdruck.RecordData
public import Grammatik.Parser.Elab.Generic.SignatureData
@[expose] public section


/-!
# S1 + S2: the duty statements and the body datum, COMPUTED IN LEAN from the parser's `UProg`

`gabbro pflichten --lean` (`crates/gabbro-check/src/lean.rs`) PRINTS, per unit, a duty file: the
body of every routine as a `Body.Stmt` datum, its precondition, its postcondition, its frame, the
`meets` statement a person proves and the wiring. This file COMPUTES the same things from
`UProg` -- the elaborated output of the Lean parser `uebersetzeAllg`, itself computed from the
source text in Lean -- so a wrong Rust print is a failed per-unit check (`Instanz*.lean`), never
a wrong theorem. The definitions here are the reference; the Rust printer is checked against them.

FRAGMENT: numeric module-static and slot writes through a pointer or at a table, direct calls with scalar or
capability and bool arguments, numeric/bool local bindings and assignments, bool conditions,
scalar, record or void returns, and numeric `ensures` comparisons and bool variables with boolean combinations. This is a subset of the Lean parser's output.
indirect/fallible/foreign call binders, consuming traversals, scoped returns and required
narrowing have no Body representation here: the readers' catch-all arms return `none`.
The positional reader in `Anweisung/Lokal/Benannt` also carries scalar direct-result
bindings. Its shared call discovery includes those calls in contracts, closure and rank checks.
-/

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik (Ty)

namespace Gabbro.Bruecke

open Gabbro.Body
open Gabbro.Grammatik.Parser.UebersetzeAllg

/-! ## 0. Lookups -/

def fnSuch (u : UProg) (n : String) : Option UFn := u.fns.find? (fun f => f.name == n)

/-- The name of the table a pointer parameter points at. -/
def ptrTab (u : UProg) (f : UFn) (p : String) : Option String :=
  match f.params.find? (fun q => q.1 == p) with
  | some (_, .ptr ⟨_, _, .table t⟩) => (u.tabs[t]?).map (·.name)
  | _ => none

/-- The pointer parameter of `f` that points at the table `tab` -- only when there is exactly one
    (a call that passes "a pointer to `tab`" names no variable in `UArg.freshPtr`). -/
def ptrParam (u : UProg) (f : UFn) (tab : String) : Option String :=
  match f.params.filter (fun q => match q.2 with
      | .ptr ⟨_, _, .table t⟩ => (u.tabs[t]?).map (·.name) == some tab
      | _ => false) with
  | [q] => some q.1
  | _ => none

/-! ## 1. Expressions -/

def idxExpr : UIdx → Expr
  | .lit n => .lit (.int n)
  | .param p => .name p

/-- One side of a comparison. `old` (the entry value) is handled by the caller (`altSides`), and
    reads here as the `old#i` binder it is numbered to. -/
def oldName : Nat → String
  | 0 => "old#1" | 1 => "old#2" | 2 => "old#3" | 3 => "old#4" | 4 => "old#5" | 5 => "old#6"
  | 6 => "old#7" | 7 => "old#8" | _ => "old#9"

/-- The place a slot read names. -/
def slotPlace (u : UProg) (f : UFn) : USide → Option Expr
  | .slot p fld i => (ptrTab u f p).map (fun t => .place t (idxExpr i) fld)
  | .tab t fld i => some (.place t (idxExpr i) fld)
  | .old p fld i => (ptrTab u f p).map (fun t => .place t (idxExpr i) fld)
  | _ => none

/-- Two operands under one Body operator (both must have a Body form). -/
def binE (op : BinOp) : Option Expr → Option Expr → Option Expr
  | some x, some y => some (.bin op x y)
  | _, _ => none

/-- Scalar parameters are distinguished from the capability parameters of `argExpr`. -/
def numericParam (f : UFn) (p : String) : Bool :=
  match f.params.find? (fun q => q.1 == p) with
  | some (_, .int ..) => true
  | _ => false

/-- Assignment supports value parameters; capability parameters remain protected. -/
def assignableParam (f : UFn) (p : String) : Bool :=
  numericParam f p || (valueParamTy f p).isSome

/-- A scalar side outside an `ensures`: no `old` or `erg`. Integer arithmetic and bit
    operations use Body's exact integer operators; a widening conversion retains its number.
    Capability values are represented only by `argExpr`'s pointer-argument cases. -/
def numericSideExpr (u : UProg) (f : UFn) : USide → Option Expr
  | .lit n => some (.lit (.int n))
  | .param p => if numericParam f p then some (.name p) else none
  | .slot p fld i => slotPlace u f (.slot p fld i)
  | .tab t fld i => slotPlace u f (.tab t fld i)
  | .old .. => none
  | .erg => none
  | .add a b => binE .add (numericSideExpr u f a) (numericSideExpr u f b)
  | .sub a b => binE .sub (numericSideExpr u f a) (numericSideExpr u f b)
  | .mul a b => binE .mul (numericSideExpr u f a) (numericSideExpr u f b)
  | .conv _ _ a => numericSideExpr u f a
  | .band a b => binE .band (numericSideExpr u f a) (numericSideExpr u f b)
  | .bor a b => binE .bor (numericSideExpr u f a) (numericSideExpr u f b)
  | .bxor a b => binE .bxor (numericSideExpr u f a) (numericSideExpr u f b)
  | _ => none

/-- Only numeric, non-atomic module statics belong to this bridge fragment. -/
def NumericStatics (u : UProg) : Prop :=
  ∀ g : Fin u.globs.length, ∃ lo hi : Int,
    (globAt u g).ty = .int lo hi ∧ (globAt u g).atomic = false

/-- Numeric expressions including module statics; nonnumeric static access is refused by lowering. -/
def numericSideExprG (u : UProg) (f : UFn) : USide → Option Expr
  | .lit n => some (.lit (.int n))
  | .param p => if numericParam f p then some (.name p) else none
  | .slot p fld i => slotPlace u f (.slot p fld i)
  | .tab t fld i => slotPlace u f (.tab t fld i)
  | .glob g =>
      match globIdx u.globs g with
      | .error _ => none
      | .ok i =>
          match (globAt u i).ty with
          | .int .. => some (.global g)
          | .bool | .wert _ => none
  | .old .. => none
  | .erg => none
  | .add a b => binE .add (numericSideExprG u f a) (numericSideExprG u f b)
  | .sub a b => binE .sub (numericSideExprG u f a) (numericSideExprG u f b)
  | .mul a b => binE .mul (numericSideExprG u f a) (numericSideExprG u f b)
  | .conv _ _ a => numericSideExprG u f a
  | .band a b => binE .band (numericSideExprG u f a) (numericSideExprG u f b)
  | .bor a b => binE .bor (numericSideExprG u f a) (numericSideExprG u f b)
  | .bxor a b => binE .bxor (numericSideExprG u f a) (numericSideExprG u f b)
  | _ => none

/-- Source values, including positional nominal records; the scalar reader is shared. -/
def sideExpr (u : UProg) (f : UFn) (sd : USide) : Option Expr :=
  (recordRead u f (numericSideExpr u f) sd).map (·.2)

def sideExprG (u : UProg) (f : UFn) (sd : USide) : Option Expr :=
  (recordRead u f (numericSideExprG u f) sd).map (·.2)

/-- An `ensures` side, numbering the `old(..)` reads met so far: the term, the reads in order,
    whether `result` occurs. -/
structure Acc where
  olds : List Expr := []
  result : Bool := false

def ensSide (u : UProg) (f : UFn) (a : Acc) : USide → Option (Expr × Acc)
  | .old p fld i =>
      (slotPlace u f (.old p fld i)).map (fun pl => (.name (oldName a.olds.length), { a with olds := a.olds ++ [pl] }))
  | .erg => some (.name "result", { a with result := true })
  -- Pure arithmetic reuses the scalar reader without changing the accumulator. Nested
  -- `old`/`result` still have no scalar form and are refused by `sideExprG`.
  | s => (numericSideExprG u f s).map (fun e => (e, a))

def opOf : String → Option BinOp
  | "==" => some .eq | "<" => some .lt | "<=" => some .le
  | ">" => some .gt | ">=" => some .ge | "!=" => some .ne | _ => none

def ensExpr (u : UProg) (f : UFn) (a : Acc) : UEns → Option (Expr × Acc)
  | .tru => some (.lit (.bool true), a)
  | .fls => some (.lit (.bool false), a)
  | .var p => some (.name p, a)
  | .cmp op l r =>
      match opOf op, ensSide u f a l with
      | some o, some (le, a1) =>
          match ensSide u f a1 r with
          | some (re, a2) => some (.bin o le re, a2)
          | none => none
      | _, _ => none
  | .and x y =>
      match ensExpr u f a x with
      | some (xe, a1) =>
          match ensExpr u f a1 y with
          | some (ye, a2) => some (.bin .and xe ye, a2)
          | none => none
      | none => none
  | .or x y =>
      match ensExpr u f a x with
      | some (xe, a1) =>
          match ensExpr u f a1 y with
          | some (ye, a2) => some (.bin .or xe ye, a2)
          | none => none
      | none => none
  | .not x =>
      match ensExpr u f a x with
      | some (xe, a1) => some (.un .not xe, a1)
      | none => none
  -- Bool fields have no slot encoding in this bridge and remain refused by name.
  | .slotB .. | .tabB .. => none
  | _ => none

def rawCond (u : UProg) (fn : UFn) (c : UEns) : Option Gabbro.Body.Expr :=
  match ensExpr u fn {} c with
  | some (x, a) => if a.olds.length = 0 ∧ a.result = false then some x else none
  | none => none

/-! ## 2. Shapes, the precondition, the frame -/

/-- `conj`: right-nested `and`, the empty conjunction is `true` (as the printer writes it). -/
def conjE : List Expr → Expr
  | [] => .lit (.bool true)
  | [e] => e
  | e :: es => .bin .and e (conjE es)

def shapeConjuncts (f : UFn) : List Expr :=
  f.params.filterMap (fun q => entryCheck q.1 q.2)

/-- `requires`: the fragment states `Held(L)` only, one clause per held lock, and it reads as
    `true` (a held lock is the caller's duty, carried by the lock rule, not by the value). -/
def preExpr (f : UFn) : Expr :=
  conjE (shapeConjuncts f ++ f.held.map (fun _ => Expr.lit (.bool true)))

/-- The typing of the world: every declared slot field has its range. -/
def slotShape (ts : List UTab) (c : String) (fld : String) : Option Shape :=
  match ts with
  | [] => none
  | t :: rest =>
      if c = t.name then (t.cols.find? (fun q => q.1 == fld)).map (fun q => .intIn q.2.1 q.2.2)
      else slotShape rest c fld

def shapeOfU (u : UProg) : Typing := fun p =>
  match p with
  | .slot c _ fld => slotShape u.tabs c fld
  | _ => none

/-! ## 3. The body -/

def argExpr (u : UProg) (f : UFn) : UArg → Option Expr
  | .var p => some (.name p)
  | .freshPtr tab _ => (ptrParam u f tab).map (fun p => .name p)
  | .val s => sideExprG u f s
  | .bval b => rawCond u f b
  | _ => none

def argsExpr (u : UProg) (f : UFn) : List UArg → Option (List Expr)
  | [] => some []
  | a :: as =>
      match argExpr u f a, argsExpr u f as with
      | some e, some es => some (e :: es)
      | _, _ => none

def stmtBody (u : UProg) (f : UFn) : UStmt → Option Stmt
  | .assign p fld i v =>
      match ptrTab u f p, sideExprG u f v with
      | some t, some ve => some (.assign t (idxExpr i) fld ve)
      | _, _ => none
  | .assignTab t fld i v => (sideExprG u f v).map (fun ve => .assign t (idxExpr i) fld ve)
  | .assignGlob g v => (sideExprG u f v).map (fun ve => .assignGlobal g ve)
  | .call g as =>
      match fnSuch u g, argsExpr u f as with
      | some gf, some es => some (.call g (gf.params.map (·.1)) es (preExpr gf))
      | _, _ => none
  -- The simulation's `stmtBody = some ...` premise excludes every other statement form.
  | _ => none

def stmtsBody (u : UProg) (f : UFn) : List UStmt → Option (List Stmt)
  | [] => some []
  | s :: ss =>
      match stmtBody u f s, stmtsBody u f ss with
      | some x, some xs => some (x :: xs)
      | _, _ => none

/-- **`zuBody`** -- the body of `f` as `Gabbro.Body` sees it. `none` = outside the fragment. -/
def zuBody (u : UProg) (f : UFn) : Option (List Stmt) :=
  match stmtsBody u f f.body with
  | none => none
  | some ss =>
      match f.ret with
      | .empty => some ss
      | .val v => (sideExprG u f v).map (fun e => ss ++ [Stmt.ret (some e)])
      | _ => none

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

/-- Whether an aggregate result has a complete representable shape. -/
def resultTypeB (f : UFn) : Bool :=
  match f.resTy with
  | none => true
  | some ty => (shapeOfTy ty).isSome

/-- The declared result shape, including all fields of a record result. -/
def resultClause (f : UFn) (r : Option Value) : Option Prop :=
  match f.resTy with
  | some ty => (shapeOfTy ty).map (fun sh => ∃ v, r = some v ∧ v.hasShape sh = true)
  | none => if f.resBool then some (∃ b, r = some (.bool b))
    else f.res.map (fun lr => ∃ x, r = some (.int x) ∧ lr.1 ≤ x ∧ x ≤ lr.2)

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
  match ensList u f s s' r f.gives with
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

/-- Every direct call, including a call whose answer is bound. -/
def directCall : UStmt → Option (String × List UArg)
  | .call g args | .bindCall _ g args => some (g, args)
  | _ => none

def CallsIn (ss : List UStmt) (g : String) (args : List UArg) : Prop :=
  ∃ st ∈ ss, directCall st = some (g, args)

theorem CallsIn.discard {ss : List UStmt} {g : String} {args : List UArg}
    (h : UStmt.call g args ∈ ss) : CallsIn ss g args := ⟨_, h, rfl⟩

theorem CallsIn.bind {ss : List UStmt} {g x : String} {args : List UArg}
    (h : UStmt.bindCall x g args ∈ ss) : CallsIn ss g args := ⟨_, h, rfl⟩

theorem CallsIn.mono {ss ts : List UStmt} {g : String} {args : List UArg}
    (h : CallsIn ss g args) (hm : ∀ st ∈ ss, st ∈ ts) : CallsIn ts g args := by
  obtain ⟨st, hs, hc⟩ := h
  exact ⟨st, hm st hs, hc⟩

theorem CallsIn.cons {ss : List UStmt} {g : String} {args : List UArg}
    (h : CallsIn ss g args) (st : UStmt) : CallsIn (st :: ss) g args :=
  h.mono (fun _ hm => List.mem_cons_of_mem st hm)

theorem CallsIn.tail {ss : List UStmt} {g : String} {args : List UArg} {st : UStmt}
    (hn : directCall st = none) (h : CallsIn (st :: ss) g args) : CallsIn ss g args := by
  obtain ⟨s, hm, hc⟩ := h
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [hn] at hc
    cases hc
  · exact ⟨s, hm, hc⟩

theorem CallsIn.head_or_tail {ss : List UStmt} {g : String} {args : List UArg} {st : UStmt}
    (h : CallsIn (st :: ss) g args) :
    directCall st = some (g, args) ∨ CallsIn ss g args := by
  obtain ⟨s, hm, hc⟩ := h
  rcases List.mem_cons.mp hm with rfl | hm
  · exact .inl hc
  · exact .inr ⟨s, hm, hc⟩

/-- The callees of the body, sorted by name, each once. -/
def calleesOf (f : UFn) : List String :=
  sortDedup (f.body.filterMap (fun s => (directCall s).map Prod.fst))

/-- A proof-only carrier: source expressions cannot read its field `#`. Each call may
    advance this clock, including a pure call. It separates answer-table keys without
    changing any canonical table/static write right. -/
def callClock : String := "#bridge:call"

/-- Body frames contain the source carriers and the private answer-table clock. -/
def writesU (f : UFn) : List String := f.puts ++ (f.gputs ++ [callClock])

theorem writesU_table {f : UFn} {w : String} (h : w ∈ f.puts) : w ∈ writesU f :=
  List.mem_append_left _ h

theorem writesU_global {f : UFn} {w : String} (h : w ∈ f.gputs) : w ∈ writesU f :=
  List.mem_append_right _ (List.mem_append_left _ h)

/-- The callee hypotheses in front of the turnstile: contract and frame of every callee. -/
def hyps (u : UProg) (wf : State → Prop) (ρ : Env) : List String → Prop → Prop
  | [], c => c
  | g :: gs, c =>
      match fnSuch u g with
      | some gf => Contract ρ g (preProp wf gf) (fun s s' r => (postU u wf gf s s' r).getD False) →
                   Frame ρ g (writesU gf) → hyps u wf ρ gs c
      | none => False

/-- **`meets`** -- what a person proves about `f` (`_meets_statement`). -/
def meetsU (u : UProg) (wf : State → Prop) (f : UFn) (body : List Stmt) : Prop :=
  ∀ (ρ : Env) (s : State), wf s → eval s (preExpr f) = some (.bool true) →
    hyps u wf ρ (calleesOf f)
      (∃ s', finalState (exec ρ body s) = some s' ∧
        (postU u wf f s s' (finalValue (exec ρ body s))).getD False)

end Gabbro.Bruecke
