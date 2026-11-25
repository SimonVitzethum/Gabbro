module

public import Core.Beobachtung.Fluss.Beweise.Geraet.Lockstep
public import Core.Ast.LowLevel.DeviceUnit

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device
open Gabbro.Core.Ast.LowLevel (entryContext)
open Gabbro.Core.Ast

variable {k : Katalog}

/-- The crash preservation statement holds unconditionally: the restart discards the volatile
    frame of every context, so no recovered frame carries a pending question. The remaining
    clauses follow because all ledgers are carried over, the booking is empty, and every
    recorded question predates the new epoch. -/
theorem geraete_absturz_invariant_mit_neustart
    {binding : Binding k} {s : State} {w : Wiederanlauf Nat UInt8 PUnit Frame PUnit}
    {t : Nat} {p : PersistZustand}
    (inv : GeraeteInvariantAussage binding s)
    (cut : ∀ q ∈ s.fragen, q.cut < t) :
    GeraeteInvariantAussage binding (s.wiederanlauf w t p) := by
  obtain ⟨hothers, hqctx, hactx, hfwd, hrange, hpre, hpost⟩ := inv
  have hbuch : (s.wiederanlauf w t p).buchung.geraet =
      (startBuchung binding.object binding.handle).geraet → False := by
    intro hB
    have hfun := congrFun hB binding.object
    simp only [Zustand.wiederanlauf, Zustand.start, Sicherheit.Buchung.leer, startBuchung,
      if_true] at hfun
    cases hfun
  have leer (c : Kontext) : ((s.wiederanlauf w t p).lokal c).pending = none := by
    simp only [Zustand.wiederanlauf, Zustand.start, Fluechtig.verwerfen, fluechtigFrame]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    refine ⟨?_, ?_, ?_⟩
    · exact leer c
    · simpa only [Zustand.wiederanlauf] using (hothers c hc).2.1
    · have hverbraucht : s.verbraucht c = 0 := (hothers c hc).2.1
      have hcnum : c.nummer ≠ entryContext.nummer := by
        intro heq
        exact hc (Kontext.nummer_injektiv heq)
      have hang : s.angekommen c = [] := by
        simp only [Zustand.angekommen]
        suffices h : ∀ l : List AntwortEreignis,
            (∀ a ∈ l, a.context = entryContext.nummer) →
            (l.filter fun e => e.context == c.nummer) = [] from
          h s.antworten hactx
        intro l hall
        induction l with
        | nil => rfl
        | cons a as ih =>
          have hac : a.context = entryContext.nummer := hall a (List.mem_cons_self)
          have hneg : ¬ (a.context == c.nummer) := by
            intro htrue
            have heq : a.context = c.nummer := beq_iff_eq.mp htrue
            exact hcnum (heq.symm.trans hac)
          rw [List.filter_cons_of_neg (p := fun e : AntwortEreignis => e.context == c.nummer)
            (a := a) hneg]
          exact ih (fun b hb => hall b (List.mem_cons_of_mem a hb))
      simp only [Zustand.wiederanlauf, hang, List.length_nil, hverbraucht, Nat.zero_sub]
  · intro qq hqq
    simpa only [Zustand.wiederanlauf] using hqctx qq hqq
  · intro a ha
    simpa only [Zustand.wiederanlauf] using hactx a ha
  · simpa only [Zustand.wiederanlauf] using hfwd
  · simpa only [Zustand.wiederanlauf] using hrange
  · intro hB
    exact (hbuch hB).elim
  · intro hbne
    refine ⟨?_, ?_, ?_⟩
    · simp only [Zustand.wiederanlauf, Zustand.start, Sicherheit.Buchung.leer]
    · intro c
      exact leer c
    · intro qq hqq
      have hqq' : qq ∈ s.fragen := by simpa only [Zustand.wiederanlauf] using hqq
      have hqqcut := cut qq hqq'
      change qq.cut < t + 1
      omega

end Gabbro.Core.Beobachtung
