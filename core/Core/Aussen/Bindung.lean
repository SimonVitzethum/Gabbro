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

/-- A stability stated by the selected row: the row declares the object stable as
    pinned catalogue data and its hardware/environment assumption assures it. -/
def ReihenStabil (p : Plattform) (o : Objekt) : Prop :=
  p.stabilGemeldet o ∧ p.stabilZugesichert o

/-- Stability holds exactly when the row declares it and assures it. -/
theorem reihenstabil_iff (p : Plattform) (o : Objekt) :
    ReihenStabil p o ↔ p.stabilGemeldet o ∧ p.stabilZugesichert o :=
  Iff.rfl

/-- The approved rows declare the `cProcess` object 1 stable. -/
theorem reihe_stabil_beispiel : ReihenStabil .x86_64 ⟨.cProcess, 1⟩ :=
  ⟨List.mem_cons_self, List.mem_cons_self⟩

/-- Only the declared object is stable: membership in the singleton list is equality. -/
theorem stabil_nur_deklariert {p : Plattform} {o : Objekt} (h : ReihenStabil p o) :
    o = ⟨.cProcess, 1⟩ := by
  cases p <;>
    simp only [ReihenStabil, Plattform.stabilGemeldet, Plattform.stabileObjekte] at h <;>
    simp only [List.mem_singleton] at h <;>
    exact h.1

/-- No stability without a declaration: every object outside the pinned set is unstable. -/
theorem reihe_instabil_of {p : Plattform} {o : Objekt} (h : o ∉ p.stabileObjekte) :
    ¬ ReihenStabil p o := by
  intro hstab
  have eq := stabil_nur_deklariert hstab
  subst eq
  exact h (by cases p <;> exact List.mem_cons_self)

/-- Every `hosted` object is unstable: the pinned set holds only a `cProcess` object. -/
theorem hosted_nicht_stabil (p : Plattform) (o : Objekt) (hosted : o.endpoint = .hosted) :
    ¬ ReihenStabil p o := by
  intro hstab
  have eq := stabil_nur_deklariert hstab
  rw [eq] at hosted
  exact nomatch hosted

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

/-- The successful catalogue event checks all the touched handles in its commit view. -/
theorem atomar_gueltig {p s q a} (antwort : atomar p s q = .antwort a)
    (erfolg : a.result.isOk = true) : GueltigBeiCommit p s q := by
  cases h : a.result with
  | ok _ => exact .frisch (List.all_eq_true.mpr (atomar_aktuell antwort h).2.2)
  | error _ => rw [h] at erfolg; cases erfolg

/-- **An atomically revalidated operation is valid at commit even when its choice depended
    on an earlier answer**: the commit snapshot establishes every touched identity, right,
    generation and precondition through its own handle. -/
theorem revalidiert_gueltig (p : Plattform) (s : AussenSicht) (q : Frage) (a : Antwort)
    (a₀ : Antwort) (v₀ : AussenWert) (kam : a₀.result = .ok v₀)
    (wahl : AussenWert → Frage) (entschieden : q = wahl v₀)
    (antwort : atomar p s q = .antwort a) (erfolg : a.result.isOk = true) :
    GueltigBeiCommit p s q := by
  exact atomar_gueltig antwort erfolg

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
  let handle : Handle := ⟨0, ⟨⟨.hosted, 0⟩, 0⟩, [.read]⟩
  let q : Frage := ⟨.hosted, handle, [], .read⟩
  let s : AussenSicht :=
    ⟨fun _ => ⟨0, true, true, bytes, fun _ => 0⟩,
      fun e i => if e = .hosted ∧ i = 0 then some handle else none, fun _ _ => none⟩
  have reply : atomar p s q = .antwort ⟨handle.origin, [handle.origin], .ok (.data bytes)⟩ := rfl
  have ok : (⟨handle.origin, [handle.origin], .ok (.data bytes)⟩ : Antwort).result.isOk = true := by
    simp only [Except.isOk, Except.toBool]
  have ninstabil : ¬ ReihenStabil p (⟨q.handle, q.operation.required⟩ : Zugriff).handle.origin.object := by
    show ¬ ReihenStabil p ⟨.hosted, 0⟩
    exact hosted_nicht_stabil p _ rfl
  obtain ⟨s₂, tot, nval⟩ := fruehere_antwort_ungueltig p s q
    ⟨q.handle, q.operation.required⟩ List.mem_cons_self ninstabil
  exact ⟨s, q, _, s₂, reply, ok, tot, nval⟩

/-- Satisfiability of the `stabil` branch: a question touching only the declared
    `cProcess` object is valid at commit on the empty snapshot, where the same-event
    check fails. The `stabil` disjunct is therefore reachable independently. -/
theorem stabil_zweig_erfuellbar :
    ∃ p s q, GueltigBeiCommit p s q ∧ q.zugriffe.all (s.gueltig q.endpoint) = false := by
  let handle : Handle := ⟨0, ⟨⟨.cProcess, 1⟩, 0⟩, [.read]⟩
  let q : Frage := ⟨.cProcess, handle, [], .read⟩
  refine ⟨.x86_64, AussenSicht.leer, q, .stabil ?_, ?_⟩
  · intro t mem
    have singleton : t = (⟨q.handle, q.operation.required⟩ : Zugriff) := by
      have : t ∈ [⟨q.handle, q.operation.required⟩] := mem
      exact List.mem_singleton.mp this
    subst singleton
    show ReihenStabil .x86_64 ⟨.cProcess, 1⟩
    exact reihe_stabil_beispiel
  · rfl

end Gabbro.Core.Aussen
