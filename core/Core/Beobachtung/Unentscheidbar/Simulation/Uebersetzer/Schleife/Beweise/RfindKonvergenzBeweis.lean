module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.Beweise.RfindDivergenzBeweis

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The pinned convergence obligation holds: when the first zero candidate is
    `y0`, every arrival at the loop end has `y0` in the output slot. -/
theorem rfindKonvergenz (cfBlk : List Befehl) (cf : Nat.Partrec.Code)
    (a aus frei freiCf freiP : Nat) :
    rfindKonvergenzAussage cfBlk cf a aus frei freiCf freiP := by
  intro m y0 v r rEnd schr hpc ha hm hy hmy hzero hdef hnz
    hcfBlk hvBlk hbleib hfreiCf hfreiP hrun hpcEnd
  have hErreich : ∀ d m0 m1 y1 : Nat, y1 - m1 = d → m0 ≤ m1 → m1 ≤ y1 → ∀ (r1 : Rahmen),
      r1.pc = 0 →
      r1.temp (frei + 0) = some (natVal a) →
      r1.temp (frei + 1) = some (natVal m0) →
      r1.temp (frei + 2) = some (natVal m1) →
      Nat.Partrec.Code.eval cf (Nat.pair a y1) = Part.some 0 →
      (∀ y, m1 ≤ y → y < y1 → ∃ v', Nat.Partrec.Code.eval cf (Nat.pair a y) = Part.some v') →
      (∀ y, m1 ≤ y → y < y1 → Nat.Partrec.Code.eval cf (Nat.pair a y) ≠ Part.some 0) →
      ∃ K rE, (Schritt (rfindSchleife cfBlk aus frei))^[K] (some r1) = some rE ∧
        rE.pc = (rfindSchleife cfBlk aus frei).length ∧ rE.temp aus = some (natVal y1) := by
    intro d
    induction d with
    | zero =>
      intro m0 m1 y1 hgap hm0m hmy r1 hpc1 ha1 hm1 hy1 hz hd hn
      have hy1m : y1 = m1 := by omega
      have hzM : Nat.Partrec.Code.eval cf (Nat.pair a m1) = Part.some 0 := by
        rw [← hy1m]
        exact hz
      obtain ⟨k, rE, hrunE, hpcE, haus, _, _, _, _⟩ :=
        rfindExitIter cfBlk cf a aus frei freiCf m0 m1 r1 hpc1 ha1 hm1 hy1 hcfBlk hvBlk hzM
      refine ⟨k, rE, hrunE, hpcE, ?_⟩
      simpa only [hy1m] using haus
    | succ d ih =>
      intro m0 m1 y1 hgap hm0m hmy r1 hpc1 ha1 hm1 hy1 hz hd hn
      have hmlt : m1 < y1 := by omega
      have hdM : ∃ v', Nat.Partrec.Code.eval cf (Nat.pair a m1) = Part.some v' :=
        hd m1 (by omega) hmlt
      have hnM : Nat.Partrec.Code.eval cf (Nat.pair a m1) ≠ Part.some 0 :=
        hn m1 (by omega) hmlt
      obtain ⟨k1, r2, _, hrun1, rpc2, ra2, hm2, hy2, _, _, _, _⟩ :=
        rfindWeiterIter cfBlk cf a aus frei freiCf m0 m1 r1 hpc1 ha1 hm1 hy1
          hcfBlk hvBlk hdM hnM
      have hgap' : y1 - (m1 + 1) = d := by omega
      have hmy' : m1 + 1 ≤ y1 := by omega
      have hm0' : m0 ≤ m1 + 1 := by omega
      have hd' : ∀ y, m1 + 1 ≤ y → y < y1 → ∃ v',
          Nat.Partrec.Code.eval cf (Nat.pair a y) = Part.some v' :=
        fun y hy1 hy2 => hd y (by omega) hy2
      have hn' : ∀ y, m1 + 1 ≤ y → y < y1 →
          Nat.Partrec.Code.eval cf (Nat.pair a y) ≠ Part.some 0 :=
        fun y hy1 hy2 => hn y (by omega) hy2
      obtain ⟨k2, rE, hrun2, hpcE, hausE⟩ :=
        ih m0 (m1 + 1) y1 hgap' hm0' hmy' r2 rpc2 ra2 hm2 hy2 hz hd' hn'
      refine ⟨k2 + k1, rE, ?_, hpcE, ?_⟩
      · rw [Function.iterate_add_apply, hrun1, hrun2]
      · exact hausE
  obtain ⟨K, rE, hrunK, hpcK, hausK⟩ :=
    hErreich (y0 - m) m m y0 rfl (Nat.le_refl _) hmy r hpc ha hm hy hzero hdef hnz
  have hKle : K ≤ schr := by
    by_contra hnot
    have hlt : schr < K := Nat.lt_of_not_ge hnot
    exact laufStirbtNach (rfindSchleife cfBlk aus frei) r schr K rEnd rE hrun hpcEnd hrunK hlt
  have hschrLe : schr ≤ K := by
    by_contra hnot
    have hlt : K < schr := Nat.lt_of_not_ge hnot
    exact laufStirbtNach (rfindSchleife cfBlk aus frei) r K schr rE rEnd hrunK hpcK hrun hlt
  have heq : schr = K := Nat.le_antisymm hschrLe hKle
  have hframes : rEnd = rE := by
    rw [heq] at hrun
    exact Option.some.inj (hrun.symm.trans hrunK)
  rw [hframes]
  exact hausK

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
