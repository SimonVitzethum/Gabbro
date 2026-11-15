module

public import Grammatik.Nebenlaeufigkeit.Async.Representation.Reachability
public import Grammatik.Nebenlaeufigkeit.Async.Zeuge
public import Mathlib.Data.Nat.Pairing

namespace Gabbro.Grammatik.Async.Representation.Fixture
open Segment

@[expose] public def nameCode : List Nat → Nat
  | [] => 0
  | head :: tail => Nat.pair head (nameCode tail) + 1

private theorem nameCode_injective (left right : List Nat)
    (same : nameCode left = nameCode right) : left = right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons head tail => change 0 = Nat.succ (Nat.pair head (nameCode tail)) at same; cases same
  | cons head tail ih =>
    cases right with
    | nil => change Nat.succ (Nat.pair head (nameCode tail)) = 0 at same; cases same
    | cons other rest =>
      have paired : Nat.pair head (nameCode tail) = Nat.pair other (nameCode rest) :=
        Nat.succ.inj same
      obtain ⟨headEq, tailEq⟩ := Nat.pair_eq_pair.mp paired
      cases headEq
      have tails := ih rest tailEq
      cases tails
      rfl

@[expose] public def scalarType : Ty := Ty.int 0 18446744073709551615
@[expose] public def countdownType : Ty := Ty.int 0 1
@[expose] public def childType : Ty := Ty.prod (nameCode [8]) [countdownType, scalarType]

/-- This fixture's explicit raw product is the second await's join result. -/
@[expose] public def types : TypeResolution where
  recordName := nameCode
  namesUnique := nameCode_injective
  ordinary := fun
    | Parser.STyp.raw _ => Ty.prod (nameCode [3, 2]) [scalarType, scalarType]
    | _ => scalarType
  childState := fun _ => childType
  childResult := fun _ => scalarType

/-- Concrete declaration for representation witnesses. There is a global
    world counter, named child poll functions, and actual owner identity 7. -/
@[expose] public def declaration : Deklaration where
  Tab := Empty
  decTab := inferInstance
  count := fun t => nomatch t
  Feld := fun t => nomatch t
  decFeld := fun t => nomatch t
  typ := fun t => nomatch t
  erlaubt := fun t => nomatch t
  tabNr := fun _ => none
  Glob := Unit
  decGlob := inferInstance
  gtyp := fun _ => scalarType
  nutzlast := fun _ => []
  atomar := fun _ => false
  geteilt := fun t => nomatch t
  ggeteilt := fun _ => false
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Nat
  decMarke := inferInstance
  stufen := fun _ => 1
  braucht := fun t => nomatch t
  gbraucht := fun _ => []
  eigner := fun t => nomatch t
  Fn := String
  sig := fun _ => 0
  sigNr := fun _ => {
    params := [childType], erg := some (Ty.sum [some scalarType, some childType]),
    gruende := 0, haelt := [], schreibt := fun t => nomatch t,
    gschreibt := fun _ => true, konsumiert := [], produziert := [] }
  eigner_nie_erzeugt := fun _ t => nomatch t
  Inv := Empty
  traeger := fun i => nomatch i
  invs := []
  Ax := Empty
  aparams := fun a => nomatch a
  aerg := fun a => nomatch a
  aschreibt := fun a => nomatch a
  agschreibt := fun a => nomatch a
  Reg := Empty
  rtyp := fun r => nomatch r
  rklasse := fun r => nomatch r
  spiegel := fun r => nomatch r
  rzusage := fun r => nomatch r
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t => nomatch t
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun _ impossible => nomatch impossible
  ownerNr := fun number => some number

@[expose] public def owned : Phase → List (declaration.Marke × Nat)
  | Phase.running _ | Phase.waiting _ _ => [(7, 0)]
  | Phase.cancelled | Phase.completed => []

@[expose] public def inventory : Inventory declaration where
  number := fun number => number
  injective := fun _ _ same => same
  owned := owned
  unique := by
    intro phase
    cases phase <;> simp only [owned, List.map_cons, List.map_nil, List.nodup_cons,
      List.not_mem_nil, List.nodup_nil, not_false_eq_true, and_self]
  resources := fun phase => savedResources (owned phase)
  exact := fun _ => rfl

private theorem ten_bounds : 0 ≤ (10 : Int) ∧ 10 ≤ 18446744073709551615 := by decide
private theorem eleven_bounds : 0 ≤ (11 : Int) ∧ 11 ≤ 18446744073709551615 := by decide
private theorem twenty_bounds : 0 ≤ (20 : Int) ∧ 20 ≤ 18446744073709551615 := by decide

@[expose] public def ten : Wert declaration scalarType := ⟨10, ten_bounds.1, ten_bounds.2⟩
@[expose] public def eleven : Wert declaration scalarType := ⟨11, eleven_bounds.1, eleven_bounds.2⟩
@[expose] public def twenty : Wert declaration scalarType := ⟨20, twenty_bounds.1, twenty_bounds.2⟩
@[expose] public def zero : Wert declaration countdownType := ⟨0, Int.le_refl 0, (by decide)⟩

@[expose] public def frame : Frame (Value declaration) :=
  ⟨[("first", Value.typed scalarType eleven), ("live", Value.typed scalarType ten)], [7]⟩

@[expose] public def partialJoin : Task (Value declaration) (Child declaration types) :=
  Task.join (Task.ready (Value.typed scalarType ten))
    (Task.leaf (Child.active "slow" (zero, twenty, ())))

@[expose] public def waiting : State (Value declaration) (Child declaration types) :=
  State.waiting 2 frame partialJoin

@[expose] public def future : FutureExpr :=
  FutureExpr.join (FutureExpr.call "fast" [Parser.SExpr.variable "live"])
    (FutureExpr.call "slow" [Parser.SExpr.variable "live"])

@[expose] public def taskValue : Wert declaration (taskStorageType types [2] future) :=
  readyAnswer declaration
    (Ty.prod (nameCode [4, 2])
      [taskStorageType types [0, 2] (FutureExpr.call "fast" [Parser.SExpr.variable "live"]),
        taskStorageType types [1, 2] (FutureExpr.call "slow" [Parser.SExpr.variable "live"])])
    (taskResultType types [2] future)
    (pendingAnswer declaration childType scalarType ten,
      readyAnswer declaration childType scalarType (zero, twenty, ()), ())

@[expose] public def frameValue : Wert declaration (frameType types fixture) :=
  (presentValue declaration scalarType ten, presentValue declaration scalarType eleven,
    absentValue declaration (Ty.prod (nameCode [3, 2]) [scalarType, scalarType]), ())

@[expose] public def startFrame : Frame (Value declaration) := ⟨[], [7]⟩

@[expose] public def startFrameValue : Wert declaration (frameType types fixture) :=
  (absentValue declaration scalarType, absentValue declaration scalarType,
    absentValue declaration (Ty.prod (nameCode [3, 2]) [scalarType, scalarType]), ())

@[expose] public def startValue : Wert declaration (stateType types fixture) :=
  (prefixValue declaration types fixture (commandPhases 0 fixture.body)
    (firstPhaseValue declaration types fixture (Phase.running 0)
      (commandPhases 1 fixture.body.tail) startFrameValue) [Phase.cancelled, Phase.completed], ())

@[expose] public def world : World declaration where
  slots := fun t => nomatch t
  globs := fun _ => ten
  spur := []

end Gabbro.Grammatik.Async.Representation.Fixture
