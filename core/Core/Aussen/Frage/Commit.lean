/-
  File:      core/Core/Aussen/Frage/Commit.lean
  Subject:   THE CONSUME GUARD AT COMMIT (MK-06, `verbrauche` Nacharbeit). A consume step takes the
              next arrived answer only when the answer still carries the revalidation evidence of
              its own commit: the catalogue row's accesses are present in the answer's checked
              objects, or the row declares them stable (`ReihenStabil`). This is the answer-level
              form of `GueltigBeiCommit` over the commit snapshot: an atomic answer obtains it
              from the same snapshot, and an earlier answer on a changed outside loses it unless a
              row states stability. An answer without that evidence is refused by a named halt
              and is not consumed.
-/
module

public import Core.Katalog.Lauf
public import Core.Aussen.Bindung
public import Core.Katalog.Aussen

@[expose] public section

namespace Gabbro.Core.Aussenfrage

open Gabbro.Core.Katalog
open Gabbro.Core.Aussen

/-- **Validity at commit, as carried by the answer.** The first branch is the same-event check at
    the answer's commit snapshot; the second is the stability the selected row states. -/
def Antwort.commitGueltig (p : Plattform) (q : Frage) (a : Antwort) : Prop :=
  (∀ t ∈ q.zugriffe, t.handle.origin ∈ a.checkedObjects) ∨
    ∀ t ∈ q.zugriffe, ReihenStabil p t.handle.origin.object

/-- The guard is decidable: both branches are finite checks over the row's access list. -/
instance (p : Plattform) (q : Frage) (a : Antwort) : Decidable (Antwort.commitGueltig p q a) := by
  unfold Antwort.commitGueltig
  infer_instance

/-- The guard of an arrived answer. -/
def AntwortEreignis.gueltigBeiCommit (p : Plattform) (a : AntwortEreignis) : Prop :=
  Antwort.commitGueltig p a.question a.reply

/-- An atomic ok answer carries the origins of all row accesses from its commit snapshot, so it
    passes the guard. -/
theorem Antwort.commitGueltig_von_atomar {p : Plattform} {s : AussenSicht} {q : Frage} {a : Antwort}
    (antwort : atomar p s q = .antwort a) (erfolg : a.result.isOk = true) :
    Antwort.commitGueltig p q a := by
  cases hres : a.result with
  | error _ =>
    rw [hres] at erfolg
    cases erfolg
  | ok _ =>
    left
    intro t mem
    have checked := (atomar_aktuell antwort hres).2.1
    have gueltig := (atomar_aktuell antwort hres).2.2 t mem
    have originEq : t.handle.origin = s.herkunft t.handle.origin.object := by
      have h := gueltig
      simp only [AussenSicht.gueltig, Bool.and_eq_true] at h
      simpa using h.2.2.2.1
    rw [checked]
    exact List.mem_map.mpr ⟨t, mem, by simpa [originEq]⟩

/-- An answer with no checked origin fails the guard unless every touched object is declared
    stable: an unchanged outside is not assumed by the guard. -/
theorem Antwort.commitGueltig_nicht_leer (p : Plattform) (q : Frage) (a : Antwort)
    (leer : a.checkedObjects = []) (t : Zugriff) (mem : t ∈ q.zugriffe)
    (ninstabil : ¬ ReihenStabil p t.handle.origin.object) :
    ¬ Antwort.commitGueltig p q a := by
  intro hval
  cases hval with
  | inl frisch =>
    exact (by simpa only [leer, List.not_mem_nil] using frisch t mem)
  | inr stabil => exact ninstabil (stabil t mem)

end Gabbro.Core.Aussenfrage
