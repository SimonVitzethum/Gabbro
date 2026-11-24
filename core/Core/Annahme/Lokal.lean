/-
  File:      core/Core/Annahme/Lokal.lean
  Subject:   The local part of acceptance (PERFECT-MODEL §3.2, §4, step M5).

  `Lokal E` is the decidable local rules over the program's syntax interface, generic over the
  program's units and forms as supplied through `Regel`/`System`: typing, authority and
  ownership are per-form obligations (`RegelLokal`) that the M6 constructors discharge, and
  every outside effect is valid at commit (`AussenLokal`, the outside rule of §4). The catalogue
  selection of `E` is well-formed (`KatalogWohlgeformt`). `stale_griff_ungueltig` and the two
  refusal theorems connect M10's outside provenance to validity at commit: a handle that
  records only an earlier answer's generation never establishes validity once the commit
  snapshot moved on.
-/
module

public import Core.Maschine.Start
public import Core.Aussen.Bindung
public import Core.Aussen.Zulassung
public import Core.Aussen.Provenienz

@[expose] public section

namespace Gabbro.Core.Annahme

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type}

/-- **Obligation of a form: its decidable local rules hold** — the typing, authority and
    ownership rules of the form. Fixed here as the interface; the M6 constructors discharge it
    per form when their syntax enters. -/
class RegelLokal {S Ev Wahl : Type} (r : Regel S Ev Wahl) : Prop where

/-- **Obligation of a form: every outside effect it performs is valid at commit** — each
    identity, right, generation and precondition holds at the commit snapshot, established in
    the same catalogue event through its own handle or by a pinned row stability. The M6
    constructors discharge it per form; the refusal theorems below fix what it means. -/
class RegelAussen {S Ev Wahl : Type} (r : Regel S Ev Wahl) : Prop where

/-- **The outside rule of §4 inside `Lokal`**: the selected platform admits only interfaces
    where every query goes through an owned handle with a failure channel (`ZulassungsRegel`),
    and every form's outside effects are valid at commit. -/
def AussenLokal (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) : Prop :=
  Aussen.ZulassungsRegel E.katalog.plattform ∧ ∀ i, RegelAussen (E.system.regel i)

/-- **`Lokal E`: the decidable local rules** — the catalogue selection is well-formed, every
    form meets its local rules, and the outside rule holds. -/
def Lokal (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) : Prop :=
  KatalogWohlgeformt E.katalog ∧ (∀ i, RegelLokal (E.system.regel i)) ∧ AussenLokal E

/-- A handle whose recorded generation is stale at the commit snapshot authorises nothing:
    the same-event validity check fails. -/
theorem stale_griff_ungueltig (s : AussenSicht) (e : Endpunkt) (t : Zugriff)
    (stale : t.handle.origin ≠ s.herkunft t.handle.origin.object) :
    s.gueltig e t = false := by
  have hbeq : (t.handle.origin == s.herkunft t.handle.origin.object) = false :=
    decide_eq_false stale
  simp only [AussenSicht.gueltig, hbeq, Bool.and_false, Bool.false_and]

/-- **An effect whose authorisation rests only on an earlier answer is refused** (§4): the
    handle records the earlier answer's generation, the commit snapshot moved on, and no row
    stability covers the object — so validity at commit fails on both disjuncts. -/
theorem fruehere_provenienz_verweigert (p : Plattform) (s : AussenSicht) (q : Frage)
    (t : Zugriff) (mem : t ∈ q.zugriffe) (frueher : Herkunft)
    (spur : t.handle.origin = frueher)
    (alt : frueher ≠ s.herkunft t.handle.origin.object)
    (ninstabil : ¬ Aussen.ReihenStabil p t.handle.origin.object) :
    ¬ Aussen.GueltigBeiCommit p s q := by
  subst spur
  intro hval
  cases hval with
  | frisch alle =>
    have htrue := (List.all_eq_true.mp alle) t mem
    have hfalse := stale_griff_ungueltig s q.endpoint t alt
    rw [hfalse] at htrue
    exact Bool.false_ne_true htrue
  | stabil fest => exact ninstabil (fest t mem)

/-- **Only earlier-answer provenance never establishes validity at commit**: the value `u`
    derives from the earlier answer `a₀` (M10 `Abgeleitet`, so its label carries that answer's
    origin), the handle the effect uses records that earlier generation, the commit snapshot
    moved on, and no row stability covers the object. -/
theorem fruehere_ableitung_verweigert (p : Plattform) (s : AussenSicht) (q : Frage)
    (t : Zugriff) (mem : t ∈ q.zugriffe) (u : Gabbro.Core.Aussen.Wert Handle)
    (eq : u.inhalt = t.handle) (a₀ : Antwort) (abgel : Aussen.Abgeleitet u a₀)
    (issued : a₀.origin = t.handle.origin)
    (alt : a₀.origin ≠ s.herkunft t.handle.origin.object)
    (ninstabil : ¬ Aussen.ReihenStabil p t.handle.origin.object) :
    ¬ Aussen.GueltigBeiCommit p s q := by
  have _traegt := Aussen.abgeleitet_traegt u a₀ abgel
  have _gleich := eq
  exact fruehere_provenienz_verweigert p s q t mem a₀.origin issued.symm alt ninstabil

end Gabbro.Core.Annahme
