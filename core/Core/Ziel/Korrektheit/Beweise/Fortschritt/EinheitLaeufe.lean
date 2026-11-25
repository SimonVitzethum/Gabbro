/-
  File:      core/Core/Ziel/Korrektheit/Beweise/Fortschritt/EinheitLaeufe.lean
  Subject:   RUN FACTS OF ELABORATED UNITS for the progress leg — the form-side duties, the
             private-plan discipline of implementation steps, the implementation/ideal state
             agreement on matched runs, and crash-freedom of open suffixes.

  Every instruction step of an elaborated unit is frame-only (the private plan with the
  `intern` action), so context steps and answer arrivals preserve all cores and the status;
  only an interrupt entry or a crash moves dispatch. An open suffix (`BleibtOffen`) hence
  carries no crash offer: a crash would discharge the context. These are properties of the
  elaborated machine, proved once for every elaborated unit; `VerdraengungKonstanz.lean`
  builds the dispatch analysis on them.
-/
module

public import Core.Ziel.Korrektheit.Verfeinerung
public import Core.Verfeinerung.Fortschritt
public import Core.Verfeinerung.Simulation
public import Core.Ast.Semantik.Pflichten
public import Core.Ziel.Korrektheit.Zugriff

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Maschine
open Gabbro.Core.Ideal (RegelFortschritt)

/-- The four form-side fields of `FortschrittsPflichten` hold for the elaborated unit without any
    acceptance or run premise, given the liveness of the memory model for its access heads: a headless
    context is finished, every instruction has its ideal step, every head has a step that composes
    through the shared protocol (an access head the step the memory model offers,
    `ZugriffSchrittExistiertAussage`), and a ready context is neither finished nor blocked. -/
theorem einheit_fortschrittsfelder (existiert : ZugriffSchrittExistiertAussage) (P : Katalog.Plattform)
    (t : Ast.Unit) :
    (∀ s c, (einheitVon P t).system.kopf s c = none → (einheitVon P t).system.fertig s c) ∧
    (∀ f : Ast.Semantik.Befehl, RegelFortschritt (einheitVon P t).system f) ∧
    (∀ i t' s c, (einheitVon P t).system.kopf s c = some i → s.SpeicherGut →
      ∃ w plan u spur s', ((einheitVon P t).system.regel i).ideal c s w [plan] u ∧
        FuehrtSchrittAus (einheitVon P t).einrichtung t' c s u plan spur s') ∧
    (∀ s c, Maschine.I.Bereit (E := einheitVon P t) s c →
      ¬ (einheitVon P t).system.fertig s c ∧ ∀ b, ¬ (einheitVon P t).system.blockiert s c b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Ast.Semantik.Fragment.fertig (Ast.Semantik.fragment Ast.Category.unit t) P
  · intro f
    exact Ast.Semantik.Befehl.regelFortschritt (Ast.Semantik.fragment Ast.Category.unit t) P f
  · exact komponierbar_koepfe existiert (Ast.Semantik.fragment Ast.Category.unit t) P
      (Ast.Semantik.fragment_klassenrein Ast.Category.unit t)
  · intro s c bereit
    rcases bereit with ⟨w, plans, u, step⟩
    exact Ast.Semantik.Fragment.bereit_eindeutig (Ast.Semantik.fragment Ast.Category.unit t) P step

/-- No lock-taking step exists for elaborated units: every plan is the private one. -/
theorem einheitVon_kein_sperre (P : Katalog.Plattform) (t : Ast.Unit)
    {c : Maschine.Kontext} {s u : Ast.Semantik.Zustand} {w : PUnit} {plan : Ast.Semantik.Plan}
    {l : Nat} {a : Maschine.SperrAktion}
    (h : (einheitVon P t).system.ISchritt c s w [plan] u)
    (hsperre : plan.aktion = Aktion.sperre l a) : False := by
  obtain ⟨i, kopf, ideal⟩ := h
  have hpriv : i.Privat :=
    Ast.Semantik.fragment_rein Ast.Category.unit t i (Ast.Semantik.kopf_mem kopf)
  have same := (Ast.Semantik.Befehl.ideal_privat i hpriv c s w [plan] u).mp ideal
  have hplan : plan = Ast.Semantik.plan := (List.cons.inj same.1).1
  subst hplan
  cases hsperre

/-- Every ready context of an elaborated unit offers a complete protocol step. -/
theorem einheitVon_bereit_vollzug (P : Katalog.Plattform) (t : Ast.Unit)
    {c : Maschine.Kontext} {s : Ast.Semantik.Zustand} (tick : Nat)
    (h : Maschine.I.Bereit (E := einheitVon P t) s c) :
    ∃ w plan u spur s', (einheitVon P t).system.ImplSchritt c s w [plan] u ∧
      Maschine.FuehrtSchrittAus (einheitVon P t).einrichtung tick c s u plan spur s' := by
  obtain ⟨w, plans, u, ischritt⟩ := h
  obtain ⟨i, kopf, ideal⟩ := ischritt
  have hpriv : i.Privat :=
    Ast.Semantik.fragment_rein Ast.Category.unit t i (Ast.Semantik.kopf_mem kopf)
  have same := (Ast.Semantik.Befehl.ideal_privat i hpriv c s w plans u).mp ideal
  obtain ⟨rfl, rfl⟩ := same
  refine ⟨w, Ast.Semantik.plan, i.nach c s, ⟨[], []⟩, i.nach c s, ⟨i, kopf, ?_⟩, ?_⟩
  · exact (Ast.Semantik.Befehl.impl_privat i hpriv c s w [Ast.Semantik.plan]
      (i.nach c s)).mpr ⟨rfl, rfl⟩
  · exact Ast.Semantik.Befehl.vollzug _ i tick c s

/-- Every implementation step of an elaborated unit carries the private plan:
    the rule at the head is frame-only, so its step forces `[Semantik.plan]`. -/
theorem einheitVon_plan_privat (P : Katalog.Plattform) (t : Ast.Unit)
    {c : Maschine.Kontext} {s u : Ast.Semantik.Zustand} {w : PUnit}
    {plan : Ast.Semantik.Plan}
    (h : (einheitVon P t).system.ImplSchritt c s w [plan] u) :
    plan = Ast.Semantik.plan := by
  obtain ⟨b, kopfB, implB⟩ := h
  have hpriv : b.Privat :=
    Ast.Semantik.fragment_rein Ast.Category.unit t b (Ast.Semantik.kopf_mem kopfB)
  have hstep := (Ast.Semantik.Befehl.impl_privat b hpriv c s w [plan] u).1 implB
  exact (List.cons.inj hstep.1).1

/-- Every instruction step of an elaborated unit is frame-only: the rule forces
    the private plan, whose action is `intern`, so the post-state agrees with the
    pre-state on cores and status. -/
theorem einheitVon_kontext_erhaelt (P : Katalog.Plattform) (t : Ast.Unit)
    {c : Maschine.Kontext} {s u : Ast.Semantik.Zustand} {w : PUnit}
    {plan : Ast.Semantik.Plan} {spur : Maschine.SchrittSpur Ast.Semantik.Zelle Int}
    {s' : Ast.Semantik.Zustand} {tick : Nat}
    (regel : (einheitVon P t).system.ISchritt c s w [plan] u)
    (aus : Maschine.FuehrtSchrittAus (einheitVon P t).einrichtung tick c s u plan spur s') :
    s'.kerne = s.kerne ∧ s'.status = s.status := by
  obtain ⟨b, kopfB, ideal⟩ := regel
  have hpriv : b.Privat :=
    Ast.Semantik.fragment_rein Ast.Category.unit t b (Ast.Semantik.kopf_mem kopfB)
  have hideal :=
    (Ast.Semantik.Befehl.ideal_privat b hpriv c s w [plan] u).mp ideal
  have planEq : plan = Ast.Semantik.plan := (List.cons.inj hideal.1).1
  have ueq : u = Ast.Semantik.Befehl.nach b c s := hideal.2
  have hakt : plan.aktion = .intern := by rw [planEq]; rfl
  obtain ⟨rahmen, _, _, _, fuaus, _, seq⟩ := aus
  generalize haussen : spur.aussen = aussen at fuaus
  rw [hakt] at fuaus
  cases fuaus with
  | intern =>
    have kerneEq : s'.kerne = s.kerne := by rw [seq]; exact rahmen.kerne
    have statusEq : s'.status = s.status := by rw [seq, ueq]; rfl
    exact ⟨kerneEq, statusEq⟩

/-- Every implementation step of an elaborated unit is frame-only: the rule forces
    the private plan, whose action is `intern`, so the post-state agrees with the
    pre-state on cores and status. -/
theorem einheitVon_kontext_erhaelt_impl (P : Katalog.Plattform) (t : Ast.Unit)
    {c : Maschine.Kontext} {s u : Ast.Semantik.Zustand} {w : PUnit}
    {plan : Ast.Semantik.Plan} {spur : Maschine.SchrittSpur Ast.Semantik.Zelle Int}
    {s' : Ast.Semantik.Zustand} {tick : Nat}
    (regel : (einheitVon P t).system.ImplSchritt c s w [plan] u)
    (aus : Maschine.FuehrtSchrittAus (einheitVon P t).einrichtung tick c s u plan spur s') :
    s'.kerne = s.kerne ∧ s'.status = s.status := by
  obtain ⟨b, kopfB, implB⟩ := regel
  have hpriv : b.Privat :=
    Ast.Semantik.fragment_rein Ast.Category.unit t b (Ast.Semantik.kopf_mem kopfB)
  have hideal :=
    (Ast.Semantik.Befehl.impl_privat b hpriv c s w [plan] u).1 implB
  have planEq : plan = Ast.Semantik.plan := (List.cons.inj hideal.1).1
  have ueq : u = Ast.Semantik.Befehl.nach b c s := hideal.2
  have hakt : plan.aktion = .intern := by rw [planEq]; rfl
  obtain ⟨rahmen, _, _, _, fuaus, _, seq⟩ := aus
  generalize haussen : spur.aussen = aussen at fuaus
  rw [hakt] at fuaus
  cases fuaus with
  | intern =>
    have kerneEq : s'.kerne = s.kerne := by rw [seq]; exact rahmen.kerne
    have statusEq : s'.status = s.status := by rw [seq, ueq]; rfl
    exact ⟨kerneEq, statusEq⟩

/-- An answer arrival touches no core state: neither dispatch nor status moves. -/
theorem einheitVon_antwort_erhaelt {a : Katalog.AntwortEreignis}
    {s s' : Ast.Semantik.Zustand}
    (hstate : s' = {s.antwort a with graph := s'.graph}) :
    s'.kerne = s.kerne ∧ s'.status = s.status := by
  have h1 : s'.kerne = ((s.antwort a).kerne) := by rw [hstate]
  have h2 : ((s.antwort a).kerne) = s.kerne := rfl
  have h3 : s'.status = ((s.antwort a).status) := by rw [hstate]
  have h4 : ((s.antwort a).status) = s.status := rfl
  exact ⟨h1.trans h2, h3.trans h4⟩

/-- The implementation state at a cut of a matched run is the ideal state: the
    protocol agrees on everything but the local frames, and the local relation
    of an elaborated unit is equality. -/
theorem einheitVon_zustand_gleich (P : Katalog.Plattform) (t : Ast.Unit)
    {ρ : Maschine.Lauf (einheitVon P t)}
    {η : Maschine.I.Lauf (einheitVon P t)}
    (matched : Maschine.I.Laufabgleich ρ η)
    (tick : Nat) (s : Ast.Semantik.Zustand)
    (hz : ρ.zeit.zustand tick = some s) :
    s = η.zeit.zustand tick := by
  obtain ⟨x, hx, bezug⟩ := matched.zustand tick
  have xeq : x = s := Option.some.inj (hx.symm.trans hz)
  obtain ⟨proto, lokal⟩ := bezug
  have hlokal : (einheitVon P t).lokalerBezug = Eq := rfl
  rw [hlokal] at lokal
  have hxstate : x = η.zeit.zustand tick := by
    have h2 : ({x with lokal := (η.zeit.zustand tick).lokal} : Ast.Semantik.Zustand) =
        η.zeit.zustand tick := proto
    rw [← lokal] at h2
    exact h2
  rw [← xeq]
  exact hxstate

/-- No crash is offered on an open suffix: a crash would discharge the context. -/
theorem einheitVon_ohne_crash (P : Katalog.Plattform) (t : Ast.Unit)
    {H : Katalog.Umgebung} {ρ : Maschine.Lauf (einheitVon P t)}
    (lauf : Maschine.Laeufe (einheitVon P t) H ρ)
    {η : Maschine.I.Lauf (einheitVon P t)}
    (matched : Maschine.I.Laufabgleich ρ η) (environment : η.umgebung = H)
    {a : Nat} {c : Maschine.Kontext} {f : Ast.Semantik.Befehl}
    (opened : Maschine.I.BleibtOffen η c f a) :
    ∀ t', a ≤ t' → (ρ.hw.angebot t').crash = false := by
  intro t' ht'
  by_cases hc : (ρ.hw.angebot t').crash = false
  · exact hc
  · have htrue : (ρ.hw.angebot t').crash = true := by
      cases hcr : (ρ.hw.angebot t').crash with
      | false => exact (hc hcr).elim
      | true => rfl
    have konform : ρ.hw.konform (einheitVon P t).katalog H := lauf.2.1
    have gueltig := konform.2 t'
    have selected : (einheitVon P t).katalog.enthaelt .persistence :=
      gueltig.2.2.2.2 (Or.inr htrue)
    have offer : Maschine.AbsturzAngeboten (einheitVon P t).katalog ρ.hw t' :=
      ⟨selected, htrue⟩
    have offerη : Maschine.AbsturzAngeboten (einheitVon P t).katalog η.hw t' := by
      rw [matched.hardware]
      exact offer
    have hspurη := (Maschine.I.absturz_am_schnitt (einheitVon P t) η offerη).1
    have herl : Maschine.I.Erledigt η c t' := Or.inr (Or.inl hspurη)
    exact ((opened.2 t' ht').2.2 herl).elim

end Gabbro.Core.Ziel.Korrektheit
