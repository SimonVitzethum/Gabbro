module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.PaarBeweise.Hilfen

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Relocatability with an explicit base offset: a backward jump at local index
    `j` stays at or before `base + j`. At base zero this is exactly
    `VerschiebbaresProgramm`. -/
def VerschiebbarVon (base : Nat) (blk : List Befehl) : Prop :=
  ∀ j, j < blk.length → ∃ b, blk[j]? = some b ∧ Verschiebbar b ∧
    (∀ d, b = .zurueckSprung d → d ≤ base + j)

theorem verschiebbarVonNull (blk : List Befehl) :
    VerschiebbarVon 0 blk ↔ VerschiebbaresProgramm blk := by
  simp only [VerschiebbarVon, VerschiebbaresProgramm, Nat.zero_add]

/-- A larger base only weakens the backward-jump bound. -/
theorem verschiebbarVonLift (base : Nat) (blk : List Befehl)
    (hv : VerschiebbaresProgramm blk) : VerschiebbarVon base blk := by
  intro j hj
  obtain ⟨b, hb, hvb, hzd⟩ := hv j hj
  refine ⟨b, hb, hvb, ?_⟩
  intro d hd
  have hd' := hzd d hd
  omega

/-- Relocatability from a base is preserved by appending: the second block's
    local index is shifted by the first block's length. -/
theorem verschiebbarVonAppend (base : Nat) (A B : List Befehl)
    (hA : VerschiebbarVon base A)
    (hB : VerschiebbarVon (base + A.length) B) :
    VerschiebbarVon base (A ++ B) := by
  intro j hj
  by_cases hjA : j < A.length
  · obtain ⟨b, hb, hvb, hzd⟩ := hA j hjA
    refine ⟨b, ?_, hvb, hzd⟩
    rw [getAnhangLinks A B j hjA]
    exact hb
  · have hjB : j - A.length < B.length := by
      simp only [List.length_append] at hj
      omega
    obtain ⟨b, hb, hvb, hzd⟩ := hB (j - A.length) hjB
    refine ⟨b, ?_, hvb, ?_⟩
    · have heq : A.length + (j - A.length) = j := by omega
      rw [← heq]
      exact (getNachPrefix A B (j - A.length) hjB).trans hb
    · intro d hd
      have hd' := hzd d hd
      omega

/-- Every instruction of a copy segment is relocatable and none is a backward
    jump. -/
theorem verschiebbarKopie (ziel quelle : Nat) :
    VerschiebbaresProgramm (kopie ziel quelle) := by
  unfold VerschiebbaresProgramm kopie
  intro j hj
  simp only [List.length_cons, List.length_nil] at hj
  interval_cases j <;>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil]
  all_goals
    refine ⟨_, rfl, ?_, ?_⟩
    · simp only [Verschiebbar]
    · intro d hd
      cases hd

/-- The check before each primitive-recursion iteration: copy the counter and
    the limit into the comparison slots and compare them. Length seven. -/
def precCheck (frei : Nat) : List Befehl :=
  kopie (frei + 6) (frei + 2) ++ kopie (frei + 7) (frei + 1) ++
    [.vergleichen .lt (frei + 6)]

theorem precCheckLaenge (frei : Nat) : (precCheck frei).length = 7 := by
  simp only [precCheck, kopieLaenge, List.length_append, List.length_cons, List.length_nil]

theorem verschiebbarPrecCheck (base : Nat) (frei : Nat) :
    VerschiebbarVon base (precCheck frei) := by
  apply verschiebbarVonLift
  unfold VerschiebbaresProgramm
  intro j hj
  rw [precCheckLaenge] at hj
  unfold precCheck
  interval_cases j <;>
    simp only [kopie, List.append_assoc, List.nil_append, List.append_nil,
      List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.getElem?_nil, List.length_cons, List.length_nil]
  all_goals
    refine ⟨_, rfl, ?_, ?_⟩
    · simp only [Verschiebbar]
    · intro d hd
      cases hd

/-- One primitive-recursion step: form `pair y i`, then `pair a (pair y i)`,
    and run the step block on that input into the accumulator slot `aus`. -/
def precRumpf (cgBlk : List Befehl) (aus frei : Nat) : List Befehl :=
  paarBerechnung (frei + 2) aus (frei + 4) (frei + 10) ++
    paarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20) ++
    cgBlk

theorem precRumpfLaenge (cgBlk : List Befehl) (aus frei : Nat) :
    (precRumpf cgBlk aus frei).length = 88 + cgBlk.length := by
  simp only [precRumpf, paarBerechnungLaenge, List.length_append]

theorem verschiebbarPrecRumpf (base : Nat) (cgBlk : List Befehl) (aus frei : Nat)
    (hv : VerschiebbaresProgramm cgBlk) : VerschiebbarVon base (precRumpf cgBlk aus frei) := by
  unfold precRumpf
  apply verschiebbarVonAppend
  · apply verschiebbarVonAppend
    · exact verschiebbarVonLift base _ (verschiebbarPaarBerechnung _ _ _ _)
    · exact verschiebbarVonLift (base + 44) _ (verschiebbarPaarBerechnung _ _ _ _)
  · exact verschiebbarVonLift (base + 44 + 44) _ hv

/-- Increment the counter and jump back to the check. The backward jump
    distance is relative to the whole loop, not to this tail. -/
def precEnde (cgBlk : List Befehl) (frei : Nat) : List Befehl :=
  [.literal (frei + 3) 1, .binaer .add (frei + 2),
    .zurueckSprung (cgBlk.length + 98)]

theorem precEndeLaenge (cgBlk : List Befehl) (frei : Nat) :
    (precEnde cgBlk frei).length = 3 := by
  rfl

theorem verschiebbarPrecEnde (base : Nat) (cgBlk : List Befehl) (frei : Nat)
    (hbase : base = cgBlk.length + 96) : VerschiebbarVon base (precEnde cgBlk frei) := by
  subst base
  unfold VerschiebbarVon precEnde
  intro j hj
  simp only [List.length_cons, List.length_nil] at hj
  interval_cases j <;>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil]
  · refine ⟨_, rfl, ?_, ?_⟩
    · simp only [Verschiebbar]
    · intro d hd; cases hd
  · refine ⟨_, rfl, ?_, ?_⟩
    · simp only [Verschiebbar]
    · intro d hd; cases hd
  · refine ⟨_, rfl, ?_, ?_⟩
    · simp only [Verschiebbar]
    · intro d hd
      cases hd
      omega

/-- The primitive-recursion loop. Slots relative to `frei`: `a` at 0, `k` at 1,
    `y` at 2, the increment scratch at 3, `q = pair y i` at 4, `p = pair a q` at 5,
    and the comparison pair at 6 and 7. The check sits at the top so no step
    runs once the counter has reached the limit. -/
def precSchleife (cgBlk : List Befehl) (aus frei : Nat) : List Befehl :=
  precCheck frei ++
    [.springeWenn (frei + 6) false (cgBlk.length + 92)] ++
    precRumpf cgBlk aus frei ++
    precEnde cgBlk frei

theorem precSchleifeLaenge (cgBlk : List Befehl) (aus frei : Nat) :
    (precSchleife cgBlk aus frei).length = cgBlk.length + 99 := by
  simp only [precSchleife, precCheckLaenge, precRumpfLaenge, precEndeLaenge,
    List.length_append, List.length_cons, List.length_nil]
  omega

/-- The loop is relocatable. Its two jumps land at the loop end and at the loop
    start respectively, so both stay inside the loop's own bounds. -/
theorem verschiebbarPrecSchleife (cgBlk : List Befehl) (aus frei : Nat)
    (hv : VerschiebbaresProgramm cgBlk) :
    VerschiebbaresProgramm (precSchleife cgBlk aus frei) := by
  rw [← verschiebbarVonNull]
  unfold precSchleife
  apply verschiebbarVonAppend
  · apply verschiebbarVonAppend
    · apply verschiebbarVonAppend
      · exact verschiebbarPrecCheck 0 frei
      · unfold VerschiebbarVon
        intro j hj
        simp only [List.length_cons, List.length_nil] at hj
        interval_cases j
        · refine ⟨_, rfl, ?_, ?_⟩
          · simp only [Verschiebbar]
          · intro d hd; cases hd
    · have hlen : (precCheck frei ++ [(.springeWenn (frei + 6) false (cgBlk.length + 92) : Befehl)]).length = 8 := by
        simp only [precCheckLaenge, List.length_cons, List.length_nil]
      rw [hlen]
      exact verschiebbarPrecRumpf 8 cgBlk aus frei hv
  · have hlen : (precCheck frei ++ [(.springeWenn (frei + 6) false (cgBlk.length + 92) : Befehl)] ++
        precRumpf cgBlk aus frei).length = cgBlk.length + 96 := by
      simp only [precCheckLaenge, precRumpfLaenge, List.length_append,
        List.length_cons, List.length_nil]
      omega
    rw [hlen]
    exact verschiebbarPrecEnde (cgBlk.length + 96) cgBlk frei rfl

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
