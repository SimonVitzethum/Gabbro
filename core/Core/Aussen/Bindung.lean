/-
  File:      core/Core/Aussen/Bindung.lean
  Subject:   VALIDITY AT COMMIT (PERFECT-MODEL §4, step M10): every current identity, right,
             generation and precondition an effect uses holds at its COMMIT, across every
             object it touches: established in the same catalogue event through its own handle,
             or by a stability the selected row states. An effect whose authorisation rests only
             on an earlier answer is NOT valid at commit under the arbitrary-change rely
             (`fruehere_antwort_ungueltig`); an atomically revalidated operation is valid even
             when its choice depended on an earlier answer (`revalidiert_gueltig`).
-/
module

public import Core.Katalog.Erfuellbar

@[expose] public section

namespace Gabbro.Core.Aussen

open Gabbro.Core.Katalog

/-- A stability stated by the selected row: the object keeps its generation and liveness
    across all snapshots. No M2 row grants one; the disjunct is the extension point the
    locality rule of M5 uses. -/
def ReihenStabil (p : Plattform) (o : Objekt) : Prop :=
  ∀ s₁ s₂ : AussenSicht, (s₁.objects o).generation = (s₂.objects o).generation ∧
    (s₁.objects o).alive = (s₂.objects o).alive

/-- No row pins an object across snapshots: two snapshots always differ in its generation. -/
theorem reihe_instabil (p : Plattform) (o : Objekt) : ¬ ReihenStabil p o := by
  let s₁ : AussenSicht := ⟨fun _ => ⟨0, true, true, [], fun _ => 0⟩,
    fun _ _ => none, fun _ _ => none⟩
  let s₂ : AussenSicht := ⟨fun _ => ⟨1, true, true, [], fun _ => 0⟩,
    fun _ _ => none, fun _ _ => none⟩
  intro h
  have hgen : (s₁.objects o).generation = (s₂.objects o).generation := (h s₁ s₂).1
  have e₁ : (s₁.objects o).generation = 0 := rfl
  have e₂ : (s₂.objects o).generation = 1 := rfl
  omega

/-- **Validity at commit** of an effect over its touched objects: every identity, right,
    generation and precondition holds at the commit snapshot — established in the same
    catalogue event through the program's own handle, or by a stability the selected
    row states. -/
inductive GueltigBeiCommit (p : Plattform) (s : AussenSicht) (q : Frage) : Prop
  | frisch (alle : q.zugriffe.all (s.gueltig q.endpoint) = true) :
      GueltigBeiCommit p s q
  | stabil (fest : ∀ t ∈ q.zugriffe, ReihenStabil p t.handle.origin.object) :
      GueltigBeiCommit p s q

/-- A dead outside proves nothing: no access through it is valid at commit. -/
theorem tot_gueltig_falsch (s : AussenSicht) (e : Endpunkt) (t : Zugriff)
    (tot : ∀ o, (s.objects o).alive = false) :
    s.gueltig e t = false := by
  have h := tot t.handle.origin.object
  simp only [AussenSicht.gueltig, h, Bool.and_false, Bool.false_and]

/-- **An effect whose authorisation rests only on an earlier answer is NOT valid at commit**
    under the arbitrary-change rely: the outside is constructed explicitly with every
    object dead, so the same-event check fails and no row stability covers the touched
    object. -/
theorem fruehere_antwort_ungueltig (p : Plattform) (s₁ : AussenSicht) (q : Frage)
    (t : Zugriff) (mem : t ∈ q.zugriffe)
    (ninstabil : ¬ ReihenStabil p t.handle.origin.object) :
    ∃ s₂ : AussenSicht, (∀ o, (s₂.objects o).alive = false) ∧
      ¬ GueltigBeiCommit p s₂ q := by
  refine ⟨{ s₁ with objects := fun _ => ⟨0, false, false, [], fun _ => 0⟩ }, ?_, ?_⟩
  · intro o
    rfl
  · intro hval
    cases hval with
    | frisch alle =>
      have htrue := (List.all_eq_true.mp alle) t mem
      have hfalse := tot_gueltig_falsch
        ({ s₁ with objects := fun _ => ⟨0, false, false, [], fun _ => 0⟩ } : AussenSicht)
        q.endpoint t (fun _ => rfl)
      rw [hfalse] at htrue
      exact Bool.false_ne_true htrue
    | stabil fest => exact ninstabil (fest t mem)

/-- **An atomically revalidated operation is valid at commit even when its choice depended
    on an earlier answer**: the commit snapshot establishes every touched identity, right,
    generation and precondition through its own handle. -/
theorem revalidiert_gueltig (p : Plattform) (s : AussenSicht) (q : Frage) (a : Antwort)
    (a₀ : Antwort) (v₀ : AussenWert) (kam : a₀.result = .ok v₀)
    (wahl : AussenWert → Frage) (entschieden : q = wahl v₀)
    (antwort : atomar p s q = .antwort a) (erfolg : a.result.isOk = true) :
    GueltigBeiCommit p s q := by
  subst entschieden
  cases hv : a.result with
  | ok v => exact .frisch (List.all_eq_true.mpr (atomar_aktuell antwort hv).2.2)
  | error e =>
    rw [hv] at erfolg
    simp only [Except.isOk, Except.toBool] at erfolg
    exact False.elim erfolg

/-- Satisfiability: a hosted read is valid at commit. -/
theorem gueltig_erfuellbar (p : Plattform) (bytes : List UInt8) :
    ∃ s q a, GueltigBeiCommit p s q ∧ atomar p s q = .antwort a ∧
      a.result.isOk = true := by
  obtain ⟨s, q, a, _, _, reply, result⟩ := hosted_lesen_erfuellbar p bytes
  have ok : a.result.isOk = true := by simp only [result, Except.isOk, Except.toBool]
  exact ⟨s, q, a,
    .frisch (List.all_eq_true.mpr (atomar_aktuell reply result).2.2), reply, ok⟩

/-- Satisfiability of the negative bundle: an earlier hosted answer succeeds, and a
    changed outside with no row stability kills the same question. -/
theorem ungueltig_erfuellbar (p : Plattform) (bytes : List UInt8) :
    ∃ s₁ q a s₂, atomar p s₁ q = .antwort a ∧ a.result.isOk = true ∧
      (∀ o, (s₂.objects o).alive = false) ∧ ¬ GueltigBeiCommit p s₂ q := by
  obtain ⟨s, q, a, _, _, reply, result⟩ := hosted_lesen_erfuellbar p bytes
  have ok : a.result.isOk = true := by simp only [result, Except.isOk, Except.toBool]
  obtain ⟨s₂, tot, nval⟩ := fruehere_antwort_ungueltig p s q
    ⟨q.handle, q.operation.required⟩ List.mem_cons_self (reihe_instabil p _)
  exact ⟨s, q, a, s₂, reply, ok, tot, nval⟩

end Gabbro.Core.Aussen
