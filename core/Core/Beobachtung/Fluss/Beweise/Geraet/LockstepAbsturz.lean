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

/-- The crash preservation statement holds under the unit's declared clearing: the restart
    applies `w.verwerfen` to every context's entry data, so no recovered frame carries a
    pending question. The remaining clauses follow because all ledgers are carried over, the
    booking is empty, and every recorded question predates the new epoch. -/
theorem geraete_absturz_invariant_mit_neustart
    {binding : Binding k} {s : State} {w : Wiederanlauf Nat UInt8 PUnit Frame PUnit}
    {t : Nat} {p : PersistZustand}
    (leer : ∀ l : Frame, (w.verwerfen l).pending = none)
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
  have leerC (c : Kontext) : ((s.wiederanlauf w t p).lokal c).pending = none :=
    leer _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    refine ⟨?_, ?_, ?_⟩
    · exact leerC c
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
      exact leerC c
    · intro qq hqq
      have hqq' : qq ∈ s.fragen := by simpa only [Zustand.wiederanlauf] using hqq
      have hqqcut := cut qq hqq'
      change qq.cut < t + 1
      omega

/-- A restart on the concrete Frame machine discards every volatile mark: after each crash
    step through the unit's own recovery data, no context carries a pending question and
    both cost-mark stands are empty. The statement is over the real step relation
    (`AbsturzSchritt` with the unit's `Wiederanlauf`, whose clearing is part of the machine
    data), never over a separately chosen clearing instance. -/
def NeustartVerwirftAussage : Prop :=
  ∀ (E : Einheit PUnit Nat UInt8 PUnit Frame PUnit PUnit PUnit PUnit)
    (leer : ∀ l : Frame, (E.einrichtung.wiederanlauf.verwerfen l).pending = none),
    ∀ (region : Strecke) (k : Katalog) (run : HwLauf) (t : Nat)
      (s s' : State) (spur : SchrittSpur Nat UInt8),
      AbsturzSchritt region E.einrichtung.wiederanlauf k run t s spur s' →
      (∀ c, (s'.lokal c).pending = none) ∧
        ∀ c, E.schranken.durchlaufstand (s'.lokal c) = [] ∧
          E.schranken.zeitstand (s'.lokal c) = []

/-- The concrete Frame machine discards its volatile marks on every restart: the pending
    slot is cleared by the unit's restart data, the mark stands by the declared binding. -/
theorem NeustartVerwirft_erfuellbar : NeustartVerwirftAussage := by
  intro E leer region k run t s s' spur step
  obtain ⟨_, rfl⟩ := step.genau
  refine ⟨?_, ?_⟩
  · intro c
    exact leer _
  · intro c
    exact ⟨E.schranken.durchlaufstand_nachVerwerfenLeer _ _,
      E.schranken.zeitstand_nachVerwerfenLeer _ _⟩

/-- The discard is load-bearing: pending questions exist as local state, the device
    clearing discharges the premise, and entry data without clearing can install a pending
    question, so the premise cannot be dropped. -/
theorem NeustartVerwirft_nichtTrivial :
    (∃ l : Frame, l.pending ≠ none) ∧
    (∀ l : Frame, (verwerfen l).pending = none) ∧
      ∃ (w : Wiederanlauf Nat UInt8 PUnit Frame PUnit) (c : Kontext),
        (((w.daten (fun _ => 0)).lokal c).pending ≠ none) := by
  let q : Frage := ⟨.hosted, ⟨0, ⟨⟨.hosted, 0⟩, 0⟩, []⟩, [], .read⟩
  refine ⟨⟨{ pending := some q }, ?_⟩, fun l => rfl, ?_⟩
  · exact Option.some_ne_none q
  · let daten : (Nat → UInt8) → Startdaten UInt8 PUnit Frame PUnit := fun _ =>
      ⟨fun _ => { pending := some q }, fun _ => .ruht,
        fun _ => ⟨none, .nutzer, (), fun _ => false, 0, false, []⟩,
        ⟨fun _ => true, fun _ => 0⟩⟩
    let w : Wiederanlauf Nat UInt8 PUnit Frame PUnit :=
      ⟨entryContext, 0, daten, fun _ _ => 0, id⟩
    exact ⟨w, entryContext, Option.some_ne_none q⟩

/-- The pinned crash statement, closed by the declared-clearing preservation lemma. -/
theorem geraeteAbsturzInvariant : GeraeteAbsturzInvariantAussage (k := k) := by
  intro _ _ _ _ _ leer inv cut
  exact geraete_absturz_invariant_mit_neustart leer inv cut

end Gabbro.Core.Beobachtung
