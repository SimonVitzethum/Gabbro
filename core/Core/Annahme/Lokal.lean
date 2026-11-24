/-
  File:      core/Core/Annahme/Lokal.lean
  Subject:   The local part of acceptance (PERFECT-MODEL §3.2, §4, step M5).

  `Lokal E` is the decidable local rules over the program's syntax interface, generic over the
  program's units and forms: the per-form authority obligation (`RegelLokal`, discharged per
  form) and the outside rule of §4 (`AussenLokal` with `AussenGueltig`: every outside effect
  valid at commit), over the catalogue selection (`KatalogWohlgeformt`). `stale_griff_ungueltig`
  and the refusal theorems connect M10's outside provenance to validity at commit: a handle
  that records only an earlier answer's generation never establishes validity once the commit
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

/-- **Authority footprint of one composed plan step** — the generic M5 part of `RegelLokal`:
    every memory location the step touches (every footprint write, every recorded read) is
    covered by the acting context's live authority at the pre-state: the authority state holds
    a live handle. M4's `Rechte` is a global capability state, so per-context and per-location
    attribution is not stated here; form-specific typing (which locations, which values) stays
    M6's additional field, conjoined when each constructor enters. -/
def Befugt (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (s : Zustand L Ort Wert Raum Lok Grund) (c : Kontext)
    (plan : SchrittPlan L Ort Wert Bedingung) : Prop :=
  (plan.fuss ≠ [] ∨ plan.lesen ≠ []) → ∃ g : Griff, s.rechte.Gueltig g

/-- **Obligation of a form: its decidable local rules hold** — the generic authority rule: every
    step of the form's implementation and ideal rules covers its memory footprint by live
    authority at the pre-state. Form-specific typing is M6's additional field. Stated at the
    level of the unit (not over a bare `Regel`): footprints and authority exist only in the
    composed machine. -/
def RegelLokal (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) (i : ι) : Prop :=
  (∀ (c : Kontext) (s u : Zustand L Ort Wert Raum Lok Grund) (plan : SchrittPlan L Ort Wert Bedingung),
    (E.system.regel i).impl c s [plan] u → Befugt E s c plan) ∧
  (∀ (c : Kontext) (s u : Zustand L Ort Wert Raum Lok Grund) (w : Wahl)
    (plan : SchrittPlan L Ort Wert Bedingung),
    (E.system.regel i).ideal c s w [plan] u → Befugt E s c plan)

/-- **Obligation of a unit: every outside effect it performs is valid at commit** — each
    identity, right, generation and precondition holds at the commit snapshot: whenever a
    composed step of either machine emits an outside question, it is valid at the outside view
    of that commit (the policy sight at the commit cut over the committed history),
    established in the same catalogue event through its own handle or by a pinned row
    stability. Under the arbitrary-change rely this pins the `.stabil` disjunct at acceptance
    time; the `.frisch` disjunct is established at commit by the atomic event (admission
    rule). The M6 constructors discharge it per form; the refusal theorems below fix what it
    means. -/
def AussenGueltig [DecidableEq L] (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) :
    Prop :=
  (∀ (run : HwLauf) (t : Nat) (s : Zustand L Ort Wert Raum Lok Grund)
    (spur : SchrittSpur Ort Wert) (s' : Zustand L Ort Wert Raum Lok Grund),
    ImplSchritt E.einrichtung E.system E.katalog run t s spur s' →
    ∀ (ev : FrageEreignis), Ereignis.frage ev ∈ spur.aussen →
      Aussen.GueltigBeiCommit E.katalog.plattform (run.politik.sicht t s'.verlauf) ev.question) ∧
  (∀ (run : HwLauf) (t : Nat) (s : Zustand L Ort Wert Raum Lok Grund)
    (w : I.SchrittWahl Wahl) (spur : SchrittSpur Ort Wert) (s' : Zustand L Ort Wert Raum Lok Grund),
    I.Schritt E.einrichtung E.system E.katalog run t s (w, spur) s' →
    ∀ (ev : FrageEreignis), Ereignis.frage ev ∈ spur.aussen →
      Aussen.GueltigBeiCommit E.katalog.plattform (run.politik.sicht t s'.verlauf) ev.question)

/-- **The outside rule of §4 inside `Lokal`**: the selected platform admits only interfaces
    where every query goes through an owned handle with a failure channel (`ZulassungsRegel`),
    and every outside effect of the unit is valid at commit. -/
def AussenLokal [DecidableEq L] (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) :
    Prop :=
  Aussen.ZulassungsRegel E.katalog.plattform ∧ AussenGueltig E

/-- **`Lokal E`: the decidable local rules** — the catalogue selection is well-formed, every
    form meets its authority obligation, and the outside rule holds. -/
def Lokal [DecidableEq L] (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) : Prop :=
  KatalogWohlgeformt E.katalog ∧ (∀ i, RegelLokal E i) ∧ AussenLokal E

/-- A live handle covers every plan step: the authority obligation holds wherever the
    authority state is alive, for memory-touching steps too. -/
theorem befugt_mit_griff (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (s : Zustand L Ort Wert Raum Lok Grund) (c : Kontext)
    (plan : SchrittPlan L Ort Wert Bedingung) (g : Griff) (hg : s.rechte.Gueltig g) :
    Befugt E s c plan :=
  fun _ => ⟨g, hg⟩

/-- Satisfiability with a touching step: issuing a handle covers an arbitrary plan. -/
theorem befugt_erfuellbar (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (s : Zustand L Ort Wert Raum Lok Grund) (c : Kontext)
    (plan : SchrittPlan L Ort Wert Bedingung) (o : Nat) :
    Befugt E { s with rechte := s.rechte.beleben o } c plan :=
  fun _ => ⟨_, Rechte.ausgeben_gueltig _ _⟩

/-- **A step touching memory without live authority is refused**: where every object is dead,
    no handle is valid, so a plan with a nonempty footprint is not covered. -/
theorem befugt_verweigert (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (s : Zustand L Ort Wert Raum Lok Grund) (c : Kontext)
    (plan : SchrittPlan L Ort Wert Bedingung)
    (tot : ∀ o, s.rechte.lebt o = false)
    (beruehrt : plan.fuss ≠ [] ∨ plan.lesen ≠ []) :
    ¬ Befugt E s c plan := by
  intro h
  obtain ⟨g, hg⟩ := h beruehrt
  have h1 := hg.1
  rw [tot g.objekt] at h1
  exact Bool.false_ne_true h1

/-- A question event is never a member of a singleton of a different event. -/
theorem frage_absurd_mem {C : Prop} {ev : FrageEreignis} {y : Ereignis}
    (mem : Ereignis.frage ev ∈ [y]) (hne : Ereignis.frage ev ≠ y) : C := by
  rcases List.mem_cons.mp mem with h | h
  · exact (hne h).elim
  · cases h

/-- **A unit whose composed steps emit no outside question satisfies the outside rule**:
    both machines only ever produce non-question traces. -/
theorem aussen_gueltig_ohne_fragen [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (impl_stumm : ∀ (run : HwLauf) (t : Nat) (s : Zustand L Ort Wert Raum Lok Grund)
      (spur : SchrittSpur Ort Wert) (s' : Zustand L Ort Wert Raum Lok Grund),
      ImplSchritt E.einrichtung E.system E.katalog run t s spur s' →
      ∀ (ev : FrageEreignis), Ereignis.frage ev ∉ spur.aussen)
    (ideal_stumm : ∀ (run : HwLauf) (t : Nat) (s : Zustand L Ort Wert Raum Lok Grund)
      (w : I.SchrittWahl Wahl) (spur : SchrittSpur Ort Wert) (s' : Zustand L Ort Wert Raum Lok Grund),
      I.Schritt E.einrichtung E.system E.katalog run t s (w, spur) s' →
      ∀ (ev : FrageEreignis), Ereignis.frage ev ∉ spur.aussen) :
    AussenGueltig E := by
  refine ⟨fun run t s spur s' step ev mem => ?_, fun run t s w spur s' step ev mem => ?_⟩
  · exact absurd mem (impl_stumm run t s spur s' step ev)
  · exact absurd mem (ideal_stumm run t s w spur s' step ev)

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
