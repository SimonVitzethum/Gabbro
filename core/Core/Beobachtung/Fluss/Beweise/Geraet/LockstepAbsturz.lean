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

/-- The bare crash statement is false. `Wiederanlauf.daten` is unconstrained, so recovery entry
    data may install a pending frame in every context. Both the general other-context clause and
    the post-crash clause of the invariant then fail on the restarted state, even though the
    cut bound holds and the original state satisfies the invariant. The missing premise is that
    no recovery frame carries a pending question. -/
theorem geraete_absturz_invariant_falsch (binding : Binding k) :
    ¬ GeraeteAbsturzInvariantAussage (k := k) := by
  intro all
  let s : State := Zustand.start (fun _ => ({} : Frame)) (fun _ => .ruht)
    (fun _ => ⟨none, .nutzer, (), fun _ => false, 0, false, []⟩)
    ⟨fun _ => true, fun _ => 0⟩ (fun _ => 0) (.leer (fun _ => 0))
  let p : PersistZustand := .leer (fun _ => 0)
  let q : Frage := binding.question (.read 0x70)
  let daten : (Nat → UInt8) → Startdaten UInt8 PUnit Frame PUnit := fun _ =>
    { lokal := fun _ => { pending := some q }
      status := fun _ => .ruht
      kerne := fun _ => ⟨none, .nutzer, (), fun _ => false, 0, false, []⟩
      rechte := ⟨fun _ => true, fun _ => 0⟩ }
  let w : Wiederanlauf Nat UInt8 PUnit Frame PUnit :=
    { eintritt := entryContext
      kern := 0
      daten := daten
      initial := fun _ _ => 0 }
  have hInv : GeraeteInvariantAussage binding s := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      refine ⟨?_, ?_, ?_⟩ <;> rfl
    · intro qq hqq
      simp only [s, Zustand.start] at hqq
      cases hqq
    · intro a ha
      simp only [s, Zustand.start] at ha
      cases ha
    · change List.Forall₂ (fun a q => a.zu q) ([] : List AntwortEreignis) ([] : List FrageEreignis)
      exact List.Forall₂.nil
    · rfl
    · intro hB
      exfalso
      have hfun := congrFun hB binding.object
      simp only [s, Zustand.start, Sicherheit.Buchung.leer, startBuchung, if_true] at hfun
      cases hfun
    · intro hne
      refine ⟨?_, ?_, ?_⟩
      · rfl
      · intro c
        rfl
      · intro qq hqq
        simp only [s, Zustand.start] at hqq
        cases hqq
  have hcut : ∀ qq ∈ s.fragen, qq.cut < 0 := by
    intro qq hqq
    simp only [s, Zustand.start] at hqq
    cases hqq
  have hinv' : GeraeteInvariantAussage binding (s.wiederanlauf w 0 p) :=
    all binding s w 0 p hInv hcut
  obtain ⟨hothers', _, _, _, _, _, _⟩ := hinv'
  have hne1 : (.faden 1 : Kontext) ≠ entryContext := by
    intro heq
    cases heq
  have hnone := (hothers' (.faden 1) hne1).1
  have hsome : ((s.wiederanlauf w 0 p).lokal (.faden 1)).pending = some q := by
    simp only [Zustand.wiederanlauf, Zustand.start, w, daten]
  rw [hsome] at hnone
  exact (Option.some_ne_none q) hnone

/-- With the missing premise the crash preservation statement holds: no recovered frame has a
    pending question. The remaining clauses follow because all ledgers are carried over, the
    booking is empty, and every recorded question predates the new epoch. -/
theorem geraete_absturz_invariant_mit_neustart
    {binding : Binding k} {s : State} {w : Wiederanlauf Nat UInt8 PUnit Frame PUnit}
    {t : Nat} {p : PersistZustand}
    (inv : GeraeteInvariantAussage binding s)
    (cut : ∀ q ∈ s.fragen, q.cut < t)
    (rein : ∀ c, ((w.daten p.dauerhaft).lokal c).pending = none) :
    GeraeteInvariantAussage binding (s.wiederanlauf w t p) := by
  obtain ⟨hothers, hqctx, hactx, hfwd, hrange, hpre, hpost⟩ := inv
  have hbuch : (s.wiederanlauf w t p).buchung.geraet =
      (startBuchung binding.object binding.handle).geraet → False := by
    intro hB
    have hfun := congrFun hB binding.object
    simp only [Zustand.wiederanlauf, Zustand.start, Sicherheit.Buchung.leer, startBuchung,
      if_true] at hfun
    cases hfun
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Zustand.wiederanlauf, Zustand.start] using rein c
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
      simpa only [Zustand.wiederanlauf, Zustand.start] using rein c
    · intro qq hqq
      have hqq' : qq ∈ s.fragen := by simpa only [Zustand.wiederanlauf] using hqq
      have hqqcut := cut qq hqq'
      change qq.cut < t + 1
      omega

end Gabbro.Core.Beobachtung
