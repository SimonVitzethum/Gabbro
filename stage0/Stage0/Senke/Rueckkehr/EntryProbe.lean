/- Joint entry protocol witness: two distinct two-word old values and two-word parameters. -/
import Stage0.Senke.Rueckkehr.Entry
import Stage0.Senke.Ausdruck.Old.Distinct

namespace Gabbro.Stage0.Senke.EntryProtocolProbe
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR Runner.Mem
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

abbrev wide : Ty := .int 0 (2 ^ 128 - 1)
def unit : UProg := {
  tabs := [], locks := []
  fns := [{
    name := "entry"
    params := [("arg", .arr (.int 0 100) 2)]
    kinds := [.wert]
    res := none
    held := []
    puts := []
    gives := []
    body := []
    ret := .empty }]
  globs := [{name := "first", ty := .wert wide, init := 0},
    {name := "second", ty := .wert wide, init := 0}] }
abbrev D := declOf unit
abbrev first : D.Glob := ⟨0, by decide⟩
abbrev second : D.Glob := ⟨1, by decide⟩
abbrev function : D.Fn := ⟨0, by decide⟩

def program : Programm D where
  invariante i := Fin.elim0 i
  requires _ := .tru
  ensures _ := .lt (.oldG first (by intro w h; cases h)) (.oldG second (by intro w h; cases h))
  rumpf f := by
    obtain ⟨f, hf⟩ := f
    have zero : f = 0 := by change f < 1 at hf; omega
    subst f
    exact .ret .empty (.refl [])

def world : World D where
  slots t := Fin.elim0 t
  globs g := by
    obtain ⟨g, hg⟩ := g
    cases g with
    | zero => exact ⟨2 ^ 64 + 7, by decide, by decide⟩
    | succ g =>
      have zero : g = 0 := by change g + 1 < 2 at hg; omega
      subst g
      exact ⟨2 ^ 65 + 9, by decide, by decide⟩
  spur := []

def layout : Lay D where
  col t := Fin.elim0 t
  ga g := 8192 + 16 * g.val
  lo := 8192
  hi := 8224
  tor _ := none
  byte _ := none

def argument : Wert D (.arr (.int 0 100) 2) :=
  fun i => if i.val = 0 then ⟨33, by decide, by decide⟩ else ⟨34, by decide, by decide⟩
def params : Env D (D.params function) := .cons argument .nil
def placement := functionFrame program function
def snapshots : List II := loadSpan 2 4 8192 ++ loadSpan 2 6 8208
def code : List II := relocateC FB placement.ensReserved placement.parameterWords ++
  (snapshots ++ relocateC placement.ensParams
    (placement.bodyReserved - placement.ensReserved) placement.parameterWords)

def memory : Runner.Mem where
  b a := if a.toNat < 192 then
      ((code.flatMap (fun i => Runner.Prog.insB i.o i.a i.b i.c))[a.toNat]?).getD 0
    else if a.toNat = 4128 then 33 else if a.toNat = 4136 then 34
    else if a.toNat = 8192 then 7 else if a.toNat = 8200 then 1
    else if a.toNat = 8208 then 9 else if a.toNat = 8216 then 2 else 0
  rd _ := true
  wr _ := true

theorem frame : FrameOK memory 4096 64 :=
  ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩

theorem code_at : CodeAt memory 0 code := by
  intro k hk
  have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 := by
    change k < 12 at hk; omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    constructor <;> decide +kernel +revert

theorem params_at : EnvAt layout memory 4096 params := by
  apply envAt_cons (ρ := (Env.nil : Env D [])) (fun _ x => nomatch x)
  constructor
  · intro i; trivial
  · change WordsAt memory 4096 4 [33, 34]
    intro i hi
    have cases : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
    rcases cases with rfl | rfl <;> decide +kernel +revert

theorem layout_in : LayIn layout := by
  refine ⟨(fun t => Fin.elim0 t), ?_, by decide⟩
  intro g
  obtain ⟨g, hg⟩ := g
  have cases : g = 0 ∨ g = 1 := by change g < 2 at hg; omega
  rcases cases with rfl | rfl <;> decide +kernel +revert

theorem world_at [Kern] : WeltAt memory layout world := by
  refine ⟨(fun t => Fin.elim0 t), ?_, fun _ _ _ => rfl⟩
  intro g
  obtain ⟨g, hg⟩ := g
  have cases : g = 0 ∨ g = 1 := by change g < 2 at hg; omega
  rcases cases with rfl | rfl <;> constructor
  all_goals try trivial
  all_goals
    intro i hi
    have cases : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
    rcases cases with rfl | rfl <;> decide +kernel +revert

/-- The actual prelude preserves the original two limbs, captures both unequal
    high limbs, and establishes a separate writable body environment. -/
theorem entryFrame_run_zeuge [Kern] :
    placement.snapshotWords = 4 ∧ placement.parameterWords = 2 ∧
    wahr? (eval world (program.ensures function) world params) = true ∧
    ∃ m', Star ⟨0, 4096⟩ memory ⟨192, 4096⟩ m' ∧
      Agree 4096 FB 64 memory m' ∧
      EnvAt layout m' 4096 params placement.ensReserved ∧
      EnvAt layout m' 4096 params placement.bodyReserved ∧
      EntrySnapshots.At layout world m' 4096 (oldCells (program.ensures function)) FB ∧
      WeltAt m' layout world := by
  refine ⟨rfl, rfl, by decide +kernel, ?_⟩
  exact entryFrame_run program function
    (snap := snapshots) (by decide +kernel) frame (by decide) (by decide)
    code_at (by unfold CodeFar; decide +kernel) params_at world_at layout_in (by decide)

end Gabbro.Stage0.Senke.EntryProtocolProbe
