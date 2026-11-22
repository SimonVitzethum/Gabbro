module
public import Bruecke.Kette.Andocken.BildErfuellbar
@[expose] public section

/-!
# Every carried language form occurs in a unit whose duties hold

One lemma per form added to the bridge (owner, 2026-11-19): an instance in which the form occurs
and the premise bundle of the theorems that cover it (`PflichtenEinheit`, the duties the generator
states) holds jointly, with the function's duty `meetsU` proved.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

/-- The bare tagged type `enum T { A, B }`. -/
def summeErfuellbar : USum := { name := "T", cases := [("A", none), ("B", none)] }

/-- `impl fn main() -> u8 { let x = T::B; return 42; }`. -/
def mainSummeErfuellbar : UFn :=
  { mainErfuellbar with body := [.bindSum "x" 0 (.fall 1 none)] }

def einheitSummeErfuellbar : UProg :=
  { einheitErfuellbar with sums := [summeErfuellbar], fns := [mainSummeErfuellbar] }

/-- **`let x = T::C;` (`bindSum`) is carried**: it occurs in a unit whose duties hold, its Body
    reading computed and its duty `meetsU` proved. -/
theorem bindSum_erfuellbar :
    ∃ u : UProg, PflichtenEinheit u ∧ ∃ f ∈ u.fns, ∃ x sidx v, UStmt.bindSum x sidx v ∈ f.body := by
  refine ⟨einheitSummeErfuellbar, ⟨⟨by with_unfolding_all decide, by with_unfolding_all decide,
    by with_unfolding_all decide⟩, fun _ => 0, ?_⟩, mainSummeErfuellbar, List.mem_singleton_self _,
    "x", 0, .fall 1 none, List.mem_singleton_self _⟩
  intro f hf
  have hf' : f = mainSummeErfuellbar := by
    simpa only [einheitSummeErfuellbar, List.mem_singleton] using hf
  subst hf'
  refine ⟨by with_unfolding_all decide, by with_unfolding_all decide, by with_unfolding_all decide,
    _, by with_unfolding_all rfl, ?_⟩
  intro ρ s hwf _
  refine ⟨_, rfl, ?_⟩
  simp only [postU, ensList, mainSummeErfuellbar, mainErfuellbar, resultClause, Gabbro.Body.finalValue,
    Gabbro.Body.exec, Gabbro.Body.step, Gabbro.Body.eval, chain, Option.toList, List.append_nil,
    Option.map_some, Option.getD_some]
  exact ⟨hwf, 42, rfl, by decide, by decide⟩

#print axioms bindSum_erfuellbar

end Gabbro.Bruecke
