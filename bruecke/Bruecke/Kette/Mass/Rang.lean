module
public import Bruecke.Kette.Mass.Pflicht
public import Grammatik.Zielsatz.Faeden.Verbund.T1
@[expose] public section

/-!
# The call-graph rank of a unit, computed

`ErreichtU u f g`: the function named `g` is reached from `f` along direct calls (`calleesOf`).
`rangU u n` counts the functions of the unit that `n` reaches, itself included. Along a call
edge `f → g` the rank never rises (`rangU_kante_le`), and it falls strictly unless `g` lies on
a cycle with `f` (`rangU_kante_lt`). So the rank alone carries every acyclic call; only the
calls inside a cycle need the `decreases` clause -- the same split as the canonical measure
duty, which concerns the cycle calls alone (`zykS`, `massPflicht_ohne_zyklus`).
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- `g` is reached from `f` by one or more direct calls. -/
inductive ErreichtU (u : UProg) : String → String → Prop
  | kante {f g : String} {gf : UFn} : fnSuch u f = some gf → g ∈ calleesOf gf → ErreichtU u f g
  | weiter {f g h : String} : ErreichtU u f g → ErreichtU u g h → ErreichtU u f h

/-- `m` is `n` or reached from `n`. -/
def UnterU (u : UProg) (n m : String) : Prop := m = n ∨ ErreichtU u n m

/-- **`g` lies on a cycle with its caller `f`**: `g` is `f` or reaches `f` back. -/
def ZyklusU (u : UProg) (f g : String) : Prop := UnterU u g f

open Classical in
/-- **The rank of a name**: the number of functions of the unit it reaches, itself included. -/
noncomputable def rangU (u : UProg) (n : String) : Nat :=
  u.fns.countP (fun h => decide (UnterU u n h.name))

variable {u : UProg}

/-- What the callee reaches, the caller reaches. -/
theorem unterU_kante {f g : String} {gf : UFn} (hf : fnSuch u f = some gf)
    (hg : g ∈ calleesOf gf) {h : String} (hu : UnterU u g h) : UnterU u f h := by
  unfold UnterU at hu ⊢
  right
  rcases hu with rfl | hr
  · exact .kante hf hg
  · exact .weiter (.kante hf hg) hr

/-- Along a call edge the rank never rises. -/
theorem rangU_kante_le {f g : String} {gf : UFn} (hf : fnSuch u f = some gf)
    (hg : g ∈ calleesOf gf) : rangU u g ≤ rangU u f := by
  unfold rangU
  apply List.countP_mono_left
  intro x _ hx
  simp only [decide_eq_true_eq] at hx ⊢
  exact unterU_kante hf hg hx

/-- **Off a cycle the rank falls**: the caller reaches itself, the callee does not reach it. -/
theorem rangU_kante_lt {f g : String} {gf : UFn} (hf : fnSuch u f = some gf)
    (hg : g ∈ calleesOf gf) (hz : ¬ ZyklusU u f g) : rangU u g < rangU u f := by
  have hn : gf.name = f := by simpa using List.find?_some hf
  unfold rangU
  apply Zielsatz.countP_lt_of
  · intro x hx
    simp only [decide_eq_true_eq] at hx ⊢
    exact unterU_kante hf hg hx
  · refine ⟨gf, List.mem_of_find?_eq_some hf, ?_, ?_⟩
    · simp only [decide_eq_true_eq]
      exact Or.inl hn
    · simp only [decide_eq_false_iff_not]
      intro hu
      apply hz
      rw [hn] at hu
      exact hu

end Gabbro.Bruecke
