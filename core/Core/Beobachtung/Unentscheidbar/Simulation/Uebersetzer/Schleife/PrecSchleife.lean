module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.PaarBeweise.Hilfen

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- Reading the middle part of a three-part concatenation. -/
theorem getElemAppend3 (A B C : List Befehl) (j : Nat)
    (hA : A.length ≤ j) (hAB : j < A.length + B.length) :
    (A ++ B ++ C)[j]? = B[j - A.length]? := by
  rw [getAnhangLinks (A ++ B) C j]
  · have heq : A.length + (j - A.length) = j := by omega
    rw [← heq]
    exact getNachPrefix A B (j - A.length) (by omega)
  · simp only [List.length_append]
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

/-- A block that is relocatable at a fixed offset inside a concatenation: the
    local backward-jump bound implies the global one because the global index
    is at least the local one. -/
theorem verschiebbarBei (pre mid post : List Befehl)
    (hv : VerschiebbaresProgramm mid) (r : Nat) (hr : r < mid.length) :
    ∃ b, (pre ++ mid ++ post)[pre.length + r]? = some b ∧ Verschiebbar b ∧
      (∀ d, b = .zurueckSprung d → d ≤ pre.length + r) := by
  obtain ⟨b, hb, hvb, hzd⟩ := hv r hr
  refine ⟨b, ?_, hvb, ?_⟩
  · rw [getElemAppend3 pre mid post (pre.length + r)]
    · simpa only [Nat.add_sub_cancel_left] using hb
    · omega
    · omega
  · intro d hd
    have hd' := hzd d hd
    omega

/-- The check before each primitive-recursion iteration: copy the counter and
    the limit into the comparison slots and compare them. Length seven. -/
def precCheck (frei : Nat) : List Befehl :=
  kopie (frei + 6) (frei + 2) ++ kopie (frei + 7) (frei + 1) ++
    [.vergleichen .lt (frei + 6)]

theorem precCheckLaenge (frei : Nat) : (precCheck frei).length = 7 := by
  simp only [precCheck, kopieLaenge, List.length_append, List.length_cons, List.length_nil]

theorem verschiebbarPrecCheck (frei : Nat) : VerschiebbaresProgramm (precCheck frei) := by
  unfold VerschiebbaresProgramm precCheck
  intro j hj
  rw [precCheckLaenge] at hj
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

/-- Increment the counter and jump back to the check. The backward jump
    distance is relative to the whole loop, not to this tail. -/
def precEnde (cgBlk : List Befehl) (frei : Nat) : List Befehl :=
  [.literal (frei + 3) 1, .binaer .add (frei + 2),
    .zurueckSprung (cgBlk.length + 98)]

theorem precEndeLaenge (cgBlk : List Befehl) (frei : Nat) :
    (precEnde cgBlk frei).length = 3 := by
  rfl

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
  unfold VerschiebbaresProgramm
  intro j hj
  rw [precSchleifeLaenge] at hj
  by_cases h7 : j < 7
  · obtain ⟨b, hb, hvb, hzd⟩ := verschiebbarPrecCheck frei j h7
    refine ⟨b, ?_, hvb, hzd⟩
    change (precCheck frei ++ [.springeWenn (frei + 6) false (cgBlk.length + 92)] ++
      precRumpf cgBlk aus frei ++ precEnde cgBlk frei)[j]? = some b
    rw [getAnhangLinks]
    · exact hb
    · simp only [precCheckLaenge]
      omega
  · have hj7 : 7 ≤ j := by omega
    by_cases h8 : j < 8
    · have hjEq : j = 7 := by omega
      subst j
      refine ⟨.springeWenn (frei + 6) false (cgBlk.length + 92), ?_, ?_, ?_⟩
      · change (precCheck frei ++ [.springeWenn (frei + 6) false (cgBlk.length + 92)] ++
          precRumpf cgBlk aus frei ++ precEnde cgBlk frei)[7]? =
          some (.springeWenn (frei + 6) false (cgBlk.length + 92))
        rw [getAnhangLinks]
        · rw [getNachPrefix]
          · rfl
          · rw [precCheckLaenge]; omega
        · rw [precCheckLaenge]; simp only [List.length_cons, List.length_nil]; omega
      · simp only [Verschiebbar]
      · intro d hd
        cases hd
    · have hj8 : 8 ≤ j := by omega
      by_cases h52 : j < 52
      · obtain ⟨b, hb, hvb, hzd⟩ := verschiebbarBei
          (precCheck frei ++ [.springeWenn (frei + 6) false (cgBlk.length + 92)])
          (paarBerechnung (frei + 2) aus (frei + 4) (frei + 10))
          (paarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20) ++
            cgBlk ++ precEnde cgBlk frei)
          (verschiebbarPaarBerechnung _ _ _ _) (j - 8) (by omega)
        refine ⟨b, ?_, hvb, hzd⟩
        change (precCheck frei ++ [.springeWenn (frei + 6) false (cgBlk.length + 92)] ++
          precRumpf cgBlk aus frei ++ precEnde cgBlk frei)[j]? = some b
        simpa only [precRumpf, List.append_assoc, precCheckLaenge,
          Nat.add_sub_cancel_left] using hb
      · have hj52 : 52 ≤ j := by omega
        by_cases h96 : j < 96
        · obtain ⟨b, hb, hvb, hzd⟩ := verschiebbarBei
            (precCheck frei ++ [.springeWenn (frei + 6) false (cgBlk.length + 92)] ++
              paarBerechnung (frei + 2) aus (frei + 4) (frei + 10))
            (paarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20))
            (cgBlk ++ precEnde cgBlk frei)
            (verschiebbarPaarBerechnung _ _ _ _) (j - 52) (by omega)
          refine ⟨b, ?_, hvb, hzd⟩
          change (precCheck frei ++ [.springeWenn (frei + 6) false (cgBlk.length + 92)] ++
            precRumpf cgBlk aus frei ++ precEnde cgBlk frei)[j]? = some b
          simpa only [precRumpf, List.append_assoc, precCheckLaenge,
            paarBerechnungLaenge, Nat.add_sub_cancel_left] using hb
        · have hj96 : 96 ≤ j := by omega
          by_cases hCg : j < 96 + cgBlk.length
          · obtain ⟨b, hb, hvb, hzd⟩ := verschiebbarBei
              (precCheck frei ++ [.springeWenn (frei + 6) false (cgBlk.length + 92)] ++
                paarBerechnung (frei + 2) aus (frei + 4) (frei + 10) ++
                paarBerechnung (frei + 0) (frei + 4) (frei + 5) (frei + 20))
              cgBlk (precEnde cgBlk frei) hv (j - 96) (by omega)
            refine ⟨b, ?_, hvb, hzd⟩
            change (precCheck frei ++ [.springeWenn (frei + 6) false (cgBlk.length + 92)] ++
              precRumpf cgBlk aus frei ++ precEnde cgBlk frei)[j]? = some b
            simpa only [precRumpf, List.append_assoc, precCheckLaenge,
              paarBerechnungLaenge, Nat.add_sub_cancel_left] using hb
          · have hjCg : 96 + cgBlk.length ≤ j := by omega
            have hjCases : j = 96 + cgBlk.length ∨ j = 97 + cgBlk.length ∨
                j = 98 + cgBlk.length := by omega
            let pre := precCheck frei ++
              [.springeWenn (frei + 6) false (cgBlk.length + 92)] ++
              precRumpf cgBlk aus frei
            have hprelen : pre.length = 96 + cgBlk.length := by
              simp only [pre, precCheckLaenge, precRumpfLaenge,
                List.length_append, List.length_cons, List.length_nil]
              omega
            have hget := getNachPrefix pre (precEnde cgBlk frei) (j - (96 + cgBlk.length))
            rcases hjCases with hjEq | hjEq | hjEq
            · subst j
              have hr0 : j - (96 + cgBlk.length) = 0 := by
                rw [hprelen]; omega
              refine ⟨.literal (frei + 3) 1, ?_, ?_, ?_⟩
              · change (pre ++ precEnde cgBlk frei)[96 + cgBlk.length]? =
                  some (.literal (frei + 3) 1)
                rw [show 96 + cgBlk.length = pre.length by omega, hprelen]
                simpa only [hr0, precEnde, List.getElem?_cons_zero] using hget (by omega)
              · simp only [Verschiebbar]
              · intro d hd; cases hd
            · subst j
              have hr1 : 97 + cgBlk.length - (96 + cgBlk.length) = 1 := by omega
              refine ⟨.binaer .add (frei + 2), ?_, ?_, ?_⟩
              · change (pre ++ precEnde cgBlk frei)[97 + cgBlk.length]? =
                  some (.binaer .add (frei + 2))
                rw [hprelen]
                simpa only [hr1, precEnde, List.getElem?_cons_succ,
                  List.getElem?_cons_zero] using hget (by omega)
              · simp only [Verschiebbar]
              · intro d hd; cases hd
            · subst j
              have hr2 : 98 + cgBlk.length - (96 + cgBlk.length) = 2 := by omega
              refine ⟨.zurueckSprung (cgBlk.length + 98), ?_, ?_, ?_⟩
              · change (pre ++ precEnde cgBlk frei)[98 + cgBlk.length]? =
                  some (.zurueckSprung (cgBlk.length + 98))
                rw [hprelen]
                simpa only [hr2, precEnde, List.getElem?_cons_succ,
                  List.getElem?_cons_zero] using hget (by omega)
              · simp only [Verschiebbar]
              · intro d hd
                omega

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
