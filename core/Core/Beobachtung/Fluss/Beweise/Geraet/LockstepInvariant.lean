module

public import Core.Beobachtung.Fluss.Beweise.Geraet.Lockstep
public import Core.Beobachtung.Fluss.Beweise.Geraet.Issue
public import Core.Beobachtung.Fluss.Beweise.Geraet.Consume
public import Core.Beobachtung.Fluss.Beweise.Geraet.Recovery
public import Core.Ast.LowLevel.DeviceUnit

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device
open Gabbro.Core.Ast
open Gabbro.Core.Ast.LowLevel (entryContext)

variable {k : Katalog}

/-- In the one-unmatched-question shape the answer ledger is one shorter than the question
    ledger, the questions are numbered by their position and the earlier answers match the
    earlier questions. A fresh offered answer that matches a recorded question therefore
    matches exactly the last question, and the matched prefix extends by one. -/
theorem geraete_antwort_erklaert_letzte_frage
    {antworten : List AntwortEreignis} {fragen : List FrageEreignis}
    (hlen : fragen.length = antworten.length + 1)
    (hrange : fragen.map (fun q : FrageEreignis => q.questionInstance) = List.range fragen.length)
    (hfwd : List.Forall₂ (fun a q => a.zu q) antworten (fragen.take antworten.length))
    {a : AntwortEreignis} {q0 : FrageEreignis}
    (hq0mem : q0 ∈ fragen) (hzu0 : a.zu q0)
    (hfrisch : ∀ e ∈ antworten, e.questionInstance ≠ a.questionInstance) :
    List.Forall₂ (fun a q => a.zu q) (antworten ++ [a])
      (fragen.take (antworten.length + 1)) := by
  have hans : ∀ (j : Nat) (hj : j < antworten.length),
      (antworten.get ⟨j, hj⟩).questionInstance = j := by
    intro j hj
    have hjtake : j < (fragen.take antworten.length).length := by
      simp only [List.length_take]
      omega
    have hzuj := hfwd.get hj hjtake
    have hget : (fragen.take antworten.length).get ⟨j, hjtake⟩ =
        fragen.get ⟨j, by omega⟩ := by
      exact List.getElem_take (xs := fragen) (j := antworten.length) (i := j) (h := hjtake)
    rw [hget] at hzuj
    have hmap := congrArg (fun l : List Nat => l[j]?) hrange
    have hleft : (fragen.map (fun q : FrageEreignis => q.questionInstance))[j]? =
        some ((fragen.get ⟨j, by omega⟩).questionInstance) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem (by omega)]
      rfl
    have hright : (List.range fragen.length)[j]? = some j := List.getElem?_range (by omega)
    rw [hleft, hright] at hmap
    exact hzuj.2.2.1.symm.trans (Option.some.inj hmap)
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq0mem
  have hi_lt : i < fragen.length := (List.getElem?_eq_some_iff.mp hi).1
  have hi_q0 : fragen.get ⟨i, hi_lt⟩ = q0 := (List.getElem?_eq_some_iff.mp hi).2
  have hqi : q0.questionInstance = i := by
    have hmap := congrArg (fun l : List Nat => l[i]?) hrange
    have hleft : (fragen.map (fun q : FrageEreignis => q.questionInstance))[i]? =
        some q0.questionInstance := by
      rw [List.getElem?_map, hi]
      rfl
    have hright : (List.range fragen.length)[i]? = some i := List.getElem?_range hi_lt
    rw [hleft, hright] at hmap
    exact Option.some.inj hmap
  have haqi : a.questionInstance = i := hzu0.2.2.1.symm.trans hqi
  have hi_eq : i = antworten.length := by
    have hilt : i < antworten.length + 1 := by omega
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hi_lt_n | hi_gt_n
    · have hmem : antworten.get ⟨i, hi_lt_n⟩ ∈ antworten := List.getElem_mem hi_lt_n
      have hne' := hfrisch (antworten.get ⟨i, hi_lt_n⟩) hmem
      exact hne' ((hans i hi_lt_n).trans haqi.symm)
    · omega
  have hgeteq : fragen.get ⟨antworten.length, by omega⟩ = q0 := by
    rw [← hi_q0]
    cases hi_eq
    rfl
  have ha_last : a.zu (fragen.get ⟨antworten.length, by omega⟩) := by
    rw [hgeteq]
    exact hzu0
  rw [List.take_succ_eq_append_getElem (by omega : antworten.length < fragen.length)]
  exact List.rel_append hfwd (List.Forall₂.cons ha_last List.Forall₂.nil)

/-- An interrupt entry changes only cores, status, deliveries and the graph, none of which the
    single-run device invariant constrains. -/
theorem geraete_interrupt_invariant
    {binding : Binding k} {s : State} {kern : Kern} {id : Nat × Nat}
    {c : Kontext} {nmi : Bool} {graph : SpeicherGraph Nat UInt8}
    (inv : GeraeteInvariantAussage binding s) :
    GeraeteInvariantAussage binding
      { Zustandseintritt s kern id c nmi with graph := graph } := by
  simpa only [GeraeteInvariantAussage, Zustandseintritt] using inv

/-- An answer arrival preserves the single-run invariant. Arrival is impossible in a balanced
    pre-state (the matching question already has an answer with the same instance, contradicting
    freshness) and in a post-crash pre-state (the matched question predates the epoch). In the
    one-unmatched shape the fresh answer matches exactly the last question, so the matched prefix
    grows by one and every other clause is unchanged. -/
theorem geraete_ankunft_invariant
    {binding : Binding k} {s : State} {kat : Katalog} {run : HwLauf} {t : Nat}
    {a : AntwortEreignis}
    (inv : GeraeteInvariantAussage binding s)
    (offered : s.AntwortAngeboten kat run t a) :
    GeraeteInvariantAussage binding (s.antwort a) := by
  obtain ⟨hothers, hqctx, hactx, hfwd, hrange, hpre, hpost⟩ := inv
  obtain ⟨hcut, herlaubt, henthaelt, hfrage, hfrisch⟩ := offered
  obtain ⟨q0, hq0mem, hq0cut, hzu0⟩ := hfrage
  have widerlege_ausgeglichen
      (halle : ∀ q ∈ s.fragen, s.epoche ≤ q.cut → ∃ a' ∈ s.antworten, a'.zu q) : False := by
    obtain ⟨a', hamem, hzu'⟩ := halle q0 hq0mem hq0cut
    exact hfrisch a' hamem (hzu'.2.2.1.symm.trans hzu0.2.2.1)
  by_cases hB : s.buchung.geraet = (startBuchung binding.object binding.handle).geraet
  · obtain ⟨hverw, hepoche, hidle, hbusy⟩ := hpre hB
    by_cases hp : (s.lokal entryContext).pending = none
    · obtain ⟨hnm, hverb, halle⟩ := hidle hp
      exact (widerlege_ausgeglichen halle).elim
    · cases hbusy hp with
      | inl hbb =>
        obtain ⟨hnm, hverb, halle⟩ := hbb
        exact (widerlege_ausgeglichen halle).elim
      | inr hub =>
        obtain ⟨hnm, hverb, hex⟩ := hub
        have htakefull : s.fragen.take (s.antworten.length + 1) = s.fragen := by
          rw [← hnm]
          simp only [List.take_length]
        have hneu_fwd : List.Forall₂ (fun a q => a.zu q) (s.antworten ++ [a]) s.fragen := by
          simpa only [htakefull] using
            (geraete_antwort_erklaert_letzte_frage hnm hrange hfwd hq0mem hzu0 hfrisch)
        have hall_NE : ∀ q ∈ s.fragen, s.epoche ≤ q.cut →
            ∃ a' ∈ s.antworten ++ [a], a'.zu q := by
          intro q hq hcutq
          obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
          have hi_lt : i < s.fragen.length := (List.getElem?_eq_some_iff.mp hi).1
          have hi_ans : i < (s.antworten ++ [a]).length := by
            simp only [List.length_append, List.length_singleton]
            omega
          have hzui := hneu_fwd.get hi_ans hi_lt
          have hi_q : s.fragen.get ⟨i, hi_lt⟩ = q := (List.getElem?_eq_some_iff.mp hi).2
          have hmem : (s.antworten ++ [a]).get ⟨i, hi_ans⟩ ∈ s.antworten ++ [a] :=
            List.getElem_mem hi_ans
          exact ⟨(s.antworten ++ [a]).get ⟨i, hi_ans⟩, hmem, by rwa [hi_q] at hzui⟩
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro c hc
          simpa only [Zustand.antwort] using hothers c hc
        · intro q hq
          simpa only [Zustand.antwort] using hqctx q hq
        · intro a' ha'
          have ha'mem : a' ∈ s.antworten ∨ a' = a := by
            simpa only [Zustand.antwort, List.mem_append, List.mem_singleton] using ha'
          cases ha'mem with
          | inl hmem => exact hactx a' hmem
          | inr heq =>
            rw [heq]
            exact hzu0.2.1.symm.trans (hqctx q0 hq0mem)
        · simpa only [Zustand.antwort, List.length_append, List.length_singleton] using
            (geraete_antwort_erklaert_letzte_frage hnm hrange hfwd hq0mem hzu0 hfrisch)
        · simpa only [Zustand.antwort] using hrange
        · intro hpre'
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro c
            simpa only [Zustand.antwort] using hverw c
          · simpa only [Zustand.antwort] using hepoche
          · intro hidle'
            exact (hp (by simpa only [Zustand.antwort] using hidle')).elim
          · intro _hne
            left
            refine ⟨?_, ?_, ?_⟩
            · simp only [Zustand.antwort, List.length_append, List.length_singleton]
              omega
            · simp only [Zustand.antwort, List.length_append, List.length_singleton]
              omega
            · intro q hq hcutq
              have hq0 : q ∈ s.fragen := by simpa only [Zustand.antwort] using hq
              have hcut0 : s.epoche ≤ q.cut := by simpa only [Zustand.antwort] using hcutq
              simpa only [Zustand.antwort] using hall_NE q hq0 hcut0
        · intro hbne
          exact (hbne hB).elim
  · obtain ⟨hbuch, hpending, hcutalt⟩ := hpost hB
    have hqalt := hcutalt q0 hq0mem
    omega

/-- The pinned arrival statement, closed by `geraete_ankunft_invariant`. -/
theorem geraeteAnkunftInvariant : GeraeteAnkunftInvariantAussage (k := k) := by
  intro _ _ _ _ _ _ inv offered
  exact geraete_ankunft_invariant inv offered

/-- The pinned interrupt-entry statement, closed by `geraete_interrupt_invariant`. -/
theorem geraeteInterruptInvariant : GeraeteInterruptInvariantAussage (k := k) := by
  intro _ _ _ _ _ _ _ inv
  exact geraete_interrupt_invariant inv

end Gabbro.Core.Beobachtung
