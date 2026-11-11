/- Joint runtime-index simulation: entry payload, current index and preserved parameters. -/
module
public import Stage0.Senke.Ausdruck.Old.Proben
import Grammatik.Kern.Taktik.KernelRfl
@[expose] public section

namespace Gabbro.Stage0.Senke.RuntimeOldProbe
open Gabbro.Grammatik Runner.IR Runner.Mem
open QuantProbe (D tab field access)
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def layout : Lay D where
  col _ _ := 8192
  ga g := Fin.elim0 g
  lo := 8192
  hi := 8224
  tor _ := none
  byte _ := none
def placement : FrameLayout := ⟨[.index 4], some (.opt 4), 0, 4, 0⟩
def entry : World D := QuantProbe.world (fun k =>
  if k = 1 then some ⟨2, by decide, by decide⟩ else none)
def exitWorld : World D := QuantProbe.initial
def params : Env D [.index 4] := .cons ⟨1, by decide, by decide⟩ .nil
def expr : Expr D [.index 4] [] (.opt 4) := .oldS tab field (.var .here) access
def code : List II := [ci 2 10 8 0] ++ selectFrameSpan 1 4 9 10 11

/-- The four saved entry words are [-1, 2, -1, -1] (an absent option is -1), the original
    parameter is 1, and every current-world slot holds -1, so reading the exit column
    would be wrong. -/
def memory : Runner.Mem where
  b a := if 4136 ≤ a.toNat ∧ a.toNat < 4144 then (if a.toNat = 4136 then 2 else 0)
    else if (4128 ≤ a.toNat ∧ a.toNat < 4160) ∨ (8192 ≤ a.toNat ∧ a.toNat < 8224) then 255
    else if a.toNat = 4160 then 1
    else ((code.flatMap encII)[a.toNat]?).getD 0
  rd _ := true
  wr _ := true

theorem frame : FrameOK memory 4096 32 :=
  ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩

theorem code_at : CodeAt memory 0 code := by
  intro k hk
  have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by
    change k < 8 at hk
    omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    constructor <;> decide +kernel +revert

theorem params_at : EnvAt layout memory 4096 params 4 := by
  apply envAt_cons (ρ := (Env.nil : Env D [])) (fun _ x => nomatch x)
  exact ValueAt.of_enc (w := 1) (by decide) (by decide +kernel) rfl

theorem saved : EntrySnapshots.At layout entry memory 4096 (oldCells expr) 4 := by
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · exact ValueAt.of_enc (w := 18446744073709551615) (by decide) (by decide +kernel) (by show _ = _; kernel_rfl)
  · exact ValueAt.of_enc (w := 2) (by decide) (by decide +kernel) (by show _ = _; kernel_rfl)
  · exact ValueAt.of_enc (w := 18446744073709551615) (by decide) (by decide +kernel) (by show _ = _; kernel_rfl)
  · exact ValueAt.of_enc (w := 18446744073709551615) (by decide) (by decide +kernel) (by show _ = _; kernel_rfl)

theorem layout_in : LayIn layout := by
  refine ⟨?_, (fun g => Fin.elim0 g), by decide⟩
  intro t f k hk
  obtain ⟨t, ht⟩ := t
  have zero : t = 0 := by change t < 1 at ht; omega
  subst t
  obtain ⟨f, hf⟩ := f
  have zero : f = 0 := by change f < 1 at hf; omega
  subst f
  change (k : Int) < 4 at hk
  change 8192 ≤ 8192 + 8 * k ∧ 8192 + 8 * k + 8 ≤ 8224
  omega

theorem world_at [Kern] : WeltAt memory layout exitWorld := by
  refine ⟨?_, (fun g => Fin.elim0 g), fun _ _ _ => rfl⟩
  intro t f k hk
  obtain ⟨t, ht⟩ := t
  have zero : t = 0 := by change t < 1 at ht; omega
  subst t
  obtain ⟨f, hf⟩ := f
  have zero : f = 0 := by change f < 1 at hf; omega
  subst f
  have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by change (k : Int) < 4 at hk; omega
  rcases cases with rfl | rfl | rfl | rfl <;>
    exact ValueAt.ofCellWord (w := 18446744073709551615) (by rfl) (by decide +kernel +revert)
      (by show _ = _; kernel_rfl)

theorem pre [Kern] : PreS layout memory 0 4096 32 9 code params 4 :=
  ⟨by decide, by decide, frame, code_at, by unfold CodeFar; decide +kernel,
    params_at, trivial, wstab_true _ _⟩

/-- The actual lowEns correctness theorem has all premises inhabited jointly.
    The returned option is the saved Some(2), although the exit field is None. -/
theorem runtime_oldS_ok_zeuge [Kern] :
    lowEns layout placement expr 9 = some (code, 12) ∧
    PreS layout memory 0 4096 32 9 code params 4 ∧
    EntrySnapshots.At layout entry memory 4096 (oldCells expr) 4 ∧
    eval entry expr exitWorld params ≠ eval exitWorld expr exitWorld params ∧
    ValueOk layout memory 0 4096 32 9 code (.opt 4) (eval entry expr exitWorld params) := by
  refine ⟨rfl, pre, saved, ?_, ?_⟩
  · intro same
    have numbers := congrArg (optN (n := 4)) same
    kernel_change ((2 : Int) = -1) at numbers
    omega
  · exact lowEns_ok placement entry exitWorld (fun _ h => h) layout_in expr 9 code 12
      rfl (by decide) memory 0 params
      (PreS.welt pre (Nat.le_refl _) world_at layout_in (by decide)) saved rfl

/-- The complete column is captured in ascending order below the original parameter. -/
theorem column_layout_zeuge :
    oldCells expr = [.elem tab field 0, .elem tab field 1, .elem tab field 2, .elem tab field 3] ∧
    EntrySnapshots.words (oldCells expr) = 4 ∧
    EntrySnapshots.capture layout (oldCells expr) 4 =
      some (loadSpan 1 4 8192 ++ loadSpan 1 5 8200 ++ loadSpan 1 6 8208 ++ loadSpan 1 7 8216) := by
  exact ⟨rfl, rfl, by decide +kernel⟩

def oversizedUnit : Parser.Uebersetze.UProg := {QuantProbe.u with
  tabs := [{name := "Links", count := 2147483648, cols := [("link", (0, 1))], opts := [("link", 0)]}] }
abbrev oversizedD := Parser.UebersetzeAllg.declOf oversizedUnit

abbrev oversizedTab : oversizedD.Tab := ⟨0, by decide⟩
abbrev oversizedField : oversizedD.Feld oversizedTab := ⟨0, by decide⟩

def oversizedExpr : Expr oversizedD [.index (2147483648)] [] (.opt (2147483648)) :=
  .oldS oversizedTab oversizedField (.var .here) (by intro w hw; change w ∈ [] at hw; cases hw)

/-- The bound is checked before enumeration, so this never constructs 2^31 cells. -/
theorem oversized_oldS_refused_zeuge :
    oldCells oversizedExpr = [] ∧
    lowEns (layU oversizedUnit (fun _ => none) 8192)
      ⟨[.index (2147483648)], some (.opt (2147483648)), 0, 0, 0⟩ oversizedExpr 8 = none := by
  exact ⟨by kernel_rfl, by kernel_rfl⟩

end Gabbro.Stage0.Senke.RuntimeOldProbe
