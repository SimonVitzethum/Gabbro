/-
  The binding of declared costs (`costs <= n ops` on a function).

  The export gate admits a constant cost expression on an ordinary function (`ExportMetadata.costUnbound`). The
  duty does not disappear: `holds` is the K001 Bool of the model (`kostenPasst`) over every function
  that declares a cost, with each call counted at the callee's declared cost. A function that
  declares a cost calls only functions that declare one, and takes no indirect call. `holds_sound`
  is the bound: a frame of such a function takes at most its declared number of own steps of machine G.
-/
module
public import Grammatik.Logik.Fortschritt.KostenG
public import Grammatik.Parser.Elab.UebersetzePipeline
public import Grammatik.Parser.Lex.Tafel
public import Grammatik.Parser.Elab.Generic.PointerTypes
@[expose] public section

namespace Gabbro.Grammatik.Parser.CostBinding
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

/-- The value of a constant cost expression: literals, the unit's integer constants, `+`, `*`, `-`
    (never below zero) and `/` (never by zero). Anything else has no value. -/
def costValue (consts : List (String × Nat)) : SExpr → Option Nat
  | .lit n => some n
  | .variable v => (consts.find? fun entry => strEq entry.1 v).map (·.2)
  | .bin op a b =>
    match costValue consts a, costValue consts b with
    | some x, some y =>
      if strEq op "+" then some (x + y)
      else if strEq op "*" then some (x * y)
      else if strEq op "-" then (if y ≤ x then some (x - y) else none)
      else if strEq op "/" then (if y = 0 then none else some (x / y))
      else none
    | _, _ => none
  | _ => none

/-- The integer constants of a unit with a value of that kind, each read under the ones before it.
    The unit's items are flattened over its modules, so a name may be declared more than once; such a
    name has no value here (which module's constant a cost means is not decided by a name alone). -/
def constants (items : List SItemTief) : List (String × Nat) :=
  let names := items.filterMap fun | .constT name _ _ => some name | _ => none
  (items.foldl (fun known item =>
    match item with
    | .constT name _ (.one e) =>
      match costValue known e with
      | some n => known ++ [(name, n)]
      | none => known
    | _ => known) []).filter fun entry => (names.filter (strEq · entry.1)).length == 1

/-- The cost clauses of a head, each with its value if it has one. A parameter hides a constant of
    its name (as in every other expression of the function), and a cost over a parameter is no
    constant: the constants are read without the names of the parameters. -/
def costClauses (consts : List (String × Nat)) (sig : FnSig) : List (Option Nat) :=
  let visible := consts.filter fun entry => !sig.params.any fun p => strEq p.1 entry.1
  sig.klauseln.filterMap fun | .cost e => some (costValue visible e) | _ => none

/-- The cost an ordinary function declares: the SMALLEST of its cost clauses, if it has one and every
    one of them is a constant expression. A head may repeat `costs`; every clause binds. -/
def declaredCost (consts : List (String × Nat)) (sig : FnSig) : Option Nat :=
  match costClauses consts sig with
  | [] => none
  | first :: rest =>
    (first :: rest).foldl (fun least clause =>
      match least, clause with
      | some a, some b => some (min a b)
      | _, _ => none) first

/-- The declared costs of the ordinary source functions, by name: a constant expression over the
    unit's constants. A `const fn` runs at compile time only and is no function of the unit; a
    library function keeps its cost refused at the gate. -/
def declared (items : List SItemTief) : Tafel (String × Nat) (·.1) :=
  let consts := constants items
  Tafel.von _ (items.filterMap fun
    | .fnT sig _ => if sig.art != "" && sig.art != "impl" then none else
      (declaredCost consts sig).map fun n => (sig.name, n)
    | _ => none)

/-- The first ordinary function with a cost clause that has no constant value. The gate admits the
    shape of the expression (`ExportMetadata.costUnbound`); a cost without a value is refused here,
    so no declared cost goes unchecked. -/
def unvalued (items : List SItemTief) : Option String :=
  let consts := constants items
  items.findSome? fun
    | .fnT sig _ => if sig.art != "" && sig.art != "impl" then none else
      if (costClauses consts sig).any (·.isNone) then some sig.name
      else none
    | _ => none

variable (T : Tafel (String × Nat) (·.1)) (u : UProg)

/-- The declared cost of a function of the unit, if its source declares one. -/
def costOf (g : Fin u.fns.length) : Option Nat := (T.finde (fnAt u g).name).map (·.2)

/-- The cost table of the K001 check: the declared cost, `0` for a function without one (such a
    function is no member, and no member may call it). -/
def decl (g : Fin u.fns.length) : Nat := (costOf T u g).getD 0

/-- The functions that declare a cost. -/
def members : List (Fin u.fns.length) :=
  (List.finRange u.fns.length).filter fun g => (costOf T u g).isSome

/-- The cost a pointer type declares: `some none` without a cost clause, `some (some n)` for a literal
    cost, `none` (refused) for a text that does not read, a cost that is no literal, or any other clause
    the gate would refuse at a function head (a deadline, a measure, a section, ...): the gate admits a
    written pointer type by its first words only, so its clauses are checked here. -/
def ptrCost (raw : String) : Option (Option Nat) :=
  match uZeigerSig raw with
  | .error _ => none
  | .ok sig =>
    if ExportMetadata.clausesMetadata (sig.klauseln.filter fun | .cost _ => false | _ => true) then none else
    match sig.klauseln.filter (fun | .cost _ => true | _ => false) with
    | [] => some none
    | [.cost (.lit n)] => some (some n)
    | _ => none

/-- Whether a function may stand behind a pointer type of declared cost `c`: it is no value of the
    type, or it declares a cost within `c`. -/
def ptrFits (j c : Nat) (g : Fin u.fns.length) : Bool :=
  !passtAt u g (u.fns.length + j) ||
    (match costOf T u g with | some n => decide (n ≤ c) | none => false)

/-- **The costs of the pointer types hold**: every function admitted as a value of a pointer type
    that declares a cost declares a cost within it. -/
def ptrHolds : Bool :=
  u.ptrKeys.zipIdx.all fun p =>
    match ptrCost p.1 with
    | none => false
    | some none => true
    | some (some c) => (List.finRange u.fns.length).all (ptrFits T u p.2 c)

/-- **A pointer type's cost bounds its values.** A function admitted as a value of the `j`th
    pointer type, whose text declares the cost `c`, declares a cost of at most `c`. -/
theorem ptrHolds_sound (h : ptrHolds T u = true) (j : Nat) (raw : String) (c : Nat)
    (key : u.ptrKeys[j]? = some raw) (cost : ptrCost raw = some (some c))
    (g : Fin u.fns.length) (value : passtAt u g (u.fns.length + j) = true) :
    ∃ n, costOf T u g = some n ∧ n ≤ c := by
  have entry : (raw, j) ∈ u.ptrKeys.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    exact key
  have row := List.all_eq_true.mp h (raw, j) entry
  simp only [cost] at row
  have fit := List.all_eq_true.mp row g (List.mem_finRange g)
  unfold ptrFits at fit
  rw [value] at fit
  cases known : costOf T u g with
  | none => simp only [known, Bool.not_true, Bool.false_or, Bool.false_eq_true] at fit
  | some n =>
    simp only [known, Bool.not_true, Bool.false_or, decide_eq_true_eq] at fit
    exact ⟨n, rfl, fit⟩

/-- Whether one member's body fits under its declaration and calls only members. -/
def fits (P : Programm (declOf u)) (passes : Nat) (g : Fin u.fns.length) : Bool :=
  decide (kostenEnd (D := declOf u) (decl T u) passes (P.rumpf g) ≤ decl T u g) &&
    rufeE (D := declOf u) (fun h => (costOf T u h).isSome) (fun _ => false) true (P.rumpf g)

/-- **The declared costs hold**: every source function with a declared cost is a function of the
    unit, every such function fits, and the pointer types' costs hold. -/
def holds (P : Programm (declOf u)) (passes : Nat) : Bool :=
  T.liste.all (fun p => (fnNr u p.1).toOption.isSome) && (members T u).all (fits T u P passes) &&
    ptrHolds T u

/-- Why the declared costs do not hold, for the refusal. -/
def failing (P : Programm (declOf u)) (passes : Nat) : Option String :=
  match T.liste.find? (fun p => !(fnNr u p.1).toOption.isSome) with
  | some p => some (p.1 ++ " declares a cost and is no function of the unit")
  | none =>
    match (members T u).find? fun g => !fits T u P passes g with
    | some g => some ((fnAt u g).name ++ " exceeds its declared cost or calls a function without one")
    | none => if ptrHolds T u then none else
        some "a pointer type declares a cost and admits a function without a declared cost within it"

/-- A member is a function with a declared cost. -/
theorem members_mem (h : Fin u.fns.length) :
    h ∈ members T u ↔ (costOf T u h).isSome = true := by
  unfold members
  rw [List.mem_filter]
  exact ⟨fun m => m.2, fun m => ⟨List.mem_finRange h, m⟩⟩

/-- `holds` is the model's K001 Bool over the members. -/
theorem holds_kostenPasst {P : Programm (declOf u)} {passes : Nat} (h : holds T u P passes = true) :
    kostenPasst (D := declOf u) P passes (decl T u) (members T u) = true := by
  unfold holds at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  have hall := List.all_eq_true.mp h.1.2
  unfold kostenPasst
  refine List.all_eq_true.mpr fun g hg => ?_
  have hfit := hall g hg
  unfold fits at hfit
  have same : ∀ x : Fin u.fns.length, (members T u).contains x = (costOf T u x).isSome := fun x => by
    rw [Bool.eq_iff_iff, List.contains_iff_mem]
    exact members_mem T u x
  have key : rufeE (D := declOf u) (fun x => (members T u).contains x) (fun _ => false) true (P.rumpf g) =
      rufeE (D := declOf u) (fun x => (costOf T u x).isSome) (fun _ => false) true (P.rumpf g) :=
    congrArg (fun Z => rufeE (D := declOf u) Z (fun _ => false) true (P.rumpf g)) (funext same)
  exact Bool.and_eq_true_iff.mpr
    ⟨(Bool.and_eq_true_iff.mp hfit).1, key.trans (Bool.and_eq_true_iff.mp hfit).2⟩

/-- **A declared cost bounds the frame.** On every run on which a frame of a function with a
    declared cost has not returned before the last step, the frame takes at most that many own steps. -/
theorem holds_sound {P : Programm (declOf u)} {passes : Nat} (h : holds T u P passes = true)
    (O : Orakel (declOf u)) (f : Faden) (g : Fin u.fns.length) (n : Nat) (hn : costOf T u g = some n)
    {rho : Env (declOf u) ((declOf u).params g)} {s0 : World (declOf u)} {k : Nat}
    {M1 M2 : RufMaschineG (declOf u)} (hE : Eintritt P f g rho s0 k M1)
    (run : SegLauf P O passes M1 M2) (hA : aktivVor f k run) : segZaehle run f ≤ n := by
  have member : g ∈ members T u := (members_mem T u g).mpr (by rw [hn]; rfl)
  have bound := kosten_passt_deklaration (D := declOf u) P O passes (decl T u) (members T u)
    (holds_kostenPasst T u h) f g member hE run hA
  have same : decl T u g = n := by
    unfold decl
    rw [hn]
    rfl
  rw [same] at bound
  exact bound

end Gabbro.Grammatik.Parser.CostBinding
