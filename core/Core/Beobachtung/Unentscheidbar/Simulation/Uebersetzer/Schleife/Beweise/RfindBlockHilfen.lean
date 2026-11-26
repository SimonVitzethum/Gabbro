module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.Beweise.RfindIterationRun
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.Beweise.RfindSchleifeRueck

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The minimisation loop is relocatable: its only backward jump targets the
    loop entry, and all other instructions are relocatable. -/
theorem verschiebbarRfindSchleife (cfBlk : List Befehl) (aus frei : Nat)
    (hvBlk : VerschiebbaresProgramm cfBlk) :
    VerschiebbaresProgramm (rfindSchleife cfBlk aus frei) := by
  rw [← verschiebbarVonNull]
  rw [rfindSchleifeAlsAnhang]
  have hvsPaar : VerschiebbaresProgramm (rfindPaar frei) := by
    rw [rfindPaar]
    exact verschiebbarPaarBerechnung (frei + 0) (frei + 2) (frei + 4) (frei + 10)
  have hlenPaar : (rfindPaar frei).length = 44 := by
    rw [rfindPaar, paarBerechnungLaenge]
  apply verschiebbarVonAppend
  · apply verschiebbarVonAppend
    · exact verschiebbarVonLift 0 (rfindPaar frei) hvsPaar
    · rw [show 0 + (rfindPaar frei).length = 44 by rw [hlenPaar]]
      exact verschiebbarVonLift 44 cfBlk hvBlk
  · rw [show 0 + (rfindPaar frei ++ cfBlk).length = 44 + cfBlk.length by
      rw [List.length_append, hlenPaar]
      omega]
    rw [rfindRest]
    apply verschiebbarVonAppend
    · apply verschiebbarVonAppend
      · unfold VerschiebbarVon
        intro j hj
        simp only [rfindNullTest, List.length_cons, List.length_nil] at hj
        interval_cases j <;> refine ⟨_, rfl, by simp [Verschiebbar], ?_⟩ <;>
          intro d hd <;> cases hd
      · rw [rfindNullTestLaenge]
        unfold VerschiebbarVon
        intro j hj
        simp only [rfindRueck, List.length_cons, List.length_nil] at hj
        interval_cases j
        · refine ⟨_, rfl, ?_, ?_⟩
          · simp only [Verschiebbar]
          · intro d hd
            cases hd
        · refine ⟨_, rfl, ?_, ?_⟩
          · simp only [Verschiebbar]
          · intro d hd
            cases hd
        · refine ⟨_, rfl, ?_, ?_⟩
          · simp only [Verschiebbar]
          · intro d hd
            injection hd with hdeq
            subst d
            omega
    · rw [show 44 + cfBlk.length + (rfindNullTest frei ++ rfindRueck cfBlk frei).length =
          44 + cfBlk.length + 3 + 3 by
        simp only [rfindNullTestLaenge, rfindRueckLaenge, List.length_append]]
      exact verschiebbarVonLift (44 + cfBlk.length + 3 + 3) (kopie aus (frei + 2))
        (verschiebbarKopie aus (frei + 2))

/-- A copy segment stays inside itself: every instruction advances the program
    counter by one. -/
theorem bleibtImBlockKopie (ziel quelle : Nat) : BleibtImBlock (kopie ziel quelle) := by
  unfold BleibtImBlock
  intro r b hlt hget
  rw [kopieLaenge] at hlt ⊢
  have hcases : r.pc = 0 ∨ r.pc = 1 ∨ r.pc = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [h0] at hget
    simp only [kopie, List.getElem?_cons_zero] at hget
    injection hget with hb
    subst b
    simp only [Befehl.auswerten, Rahmen.schreibe, h0]
    omega
  · rw [h1] at hget
    simp only [kopie, List.getElem?_cons_succ, List.getElem?_cons_zero] at hget
    injection hget with hb
    subst b
    simp only [Befehl.auswerten, Rahmen.schreibe, h1]
    omega
  · rw [h2] at hget
    simp only [kopie, List.getElem?_cons_succ, List.getElem?_cons_succ,
      List.getElem?_cons_zero] at hget
    injection hget with hb
    subst b
    simp only [Befehl.auswerten, Rahmen.schreibe, h2]
    omega

/-- Forward reachability of the loop end with the first zero candidate in the
    output slot, by induction over the remaining gap. -/
theorem rfindErreich (cfBlk : List Befehl) (cf : Nat.Partrec.Code)
    (a aus frei freiCf : Nat) (hcfBlk : BlockKorrekt cfBlk cf (frei + 4) (frei + 6) freiCf)
    (hvBlk : VerschiebbaresProgramm cfBlk) :
    ∀ d m0 m1 y1 : Nat, y1 - m1 = d → m0 ≤ m1 → m1 ≤ y1 → ∀ (r1 : Rahmen),
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

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
