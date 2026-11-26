module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.RfindIterationRun
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.RfindBlock

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The pinned divergence obligation holds: a search whose source evaluation is
    total and never zero keeps returning to the loop entry, so no step count
    kills the run. -/
theorem rfindDivergenz (cfBlk : List Befehl) (cf : Nat.Partrec.Code)
    (a aus frei freiCf freiP : Nat) :
    rfindDivergenzAussage cfBlk cf a aus frei freiCf freiP := by
  intro m r hpc ha hm hy hcfBlk hbleib hvBlk hfreiCf hfreiP hP
  constructor
  · intro _
    rw [laufStirbtNicht_iff]
    intro hdead
    rcases hdead with ⟨k, hk⟩
    have hBound : ∀ t : Nat, ∃ K, t ≤ K ∧ ∃ rt : Rahmen,
        (Schritt (rfindSchleife cfBlk aus frei))^[K] (some r) = some rt ∧
        rt.pc = 0 ∧
        rt.temp (frei + 0) = some (natVal a) ∧
        rt.temp (frei + 1) = some (natVal m) ∧
        rt.temp (frei + 2) = some (natVal (m + t)) := by
      intro t
      induction t with
      | zero =>
        refine ⟨0, by omega, r, by simp, hpc, ha, hm, hy⟩
      | succ t ih =>
        obtain ⟨K, hKge, rt, hrun, rpc, ra, rm, ry⟩ := ih
        have hdef : ∃ v, Nat.Partrec.Code.eval cf (Nat.pair a (m + t)) = Part.some v :=
          hP.1 (m + t) (by omega)
        have hnz : Nat.Partrec.Code.eval cf (Nat.pair a (m + t)) ≠ Part.some 0 :=
          hP.2 (m + t) (by omega)
        obtain ⟨k1, r1, hk1pos, hrun1, rpc1, ra1, rm1, ry1, _, _, _⟩ :=
          rfindWeiterIter cfBlk cf a aus frei freiCf m (m + t) rt rpc ra rm ry
            hcfBlk hvBlk hdef hnz
        refine ⟨k1 + K, by omega, r1, ?_, rpc1, ra1, rm1, ?_⟩
        · rw [Function.iterate_add_apply, hrun, hrun1]
        · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ry1
    obtain ⟨K, hKge, rt, hrun, _⟩ := hBound k
    obtain ⟨rk, hrk⟩ := laufHatZwischen (rfindSchleife cfBlk aus frei) r K k rt hrun (by omega)
    rw [hk] at hrk
    cases hrk
  · intro _
    exact hP

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
