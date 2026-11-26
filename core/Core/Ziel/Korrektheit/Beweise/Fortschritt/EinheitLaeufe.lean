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

/-- The four form-side fields of `FortschrittsPflichten` in the pre-access shape for a frame-only
    fragment: with `Rein` every head is frame-only, so the template step composes
    (`Befehl.komponierbar`) and `RegelKomponierbar` holds for every instruction. For fragments with
    access instructions `RegelKomponierbar` is false (only the memory-accepted step composes), and
    the koepfen shape (`einheit_fortschrittsfelder`) is used instead. -/
theorem einheit_fortschrittsfelder_rein (rein : (Ast.Semantik.fragment Ast.Category.unit t).Rein)
    (P : Katalog.Plattform) (t : Ast.Unit) :
    (∀ s c, (einheitVon P t).system.kopf s c = none → (einheitVon P t).system.fertig s c) ∧
    (∀ f : Ast.Semantik.Befehl, RegelFortschritt (einheitVon P t).system f) ∧
    (∀ f : Ast.Semantik.Befehl,
      Maschine.I.RegelKomponierbar (einheitVon P t).einrichtung (einheitVon P t).system f) ∧
    (∀ s c, Maschine.I.Bereit (E := einheitVon P t) s c →
      ¬ (einheitVon P t).system.fertig s c ∧ ∀ b, ¬ (einheitVon P t).system.blockiert s c b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Ast.Semantik.Fragment.fertig (Ast.Semantik.fragment Ast.Category.unit t) P
  · intro f
    exact Ast.Semantik.Befehl.regelFortschritt (Ast.Semantik.fragment Ast.Category.unit t) P f
  · intro f
    by_cases h : f.Privat
    · exact Ast.Semantik.Befehl.komponierbar (Ast.Semantik.fragment Ast.Category.unit t) P f h
    · intro t' s c w plans u hk _ _
      exact absurd (rein f (Ast.Semantik.kopf_mem hk)) h
  · intro s c bereit
    rcases bereit with ⟨w, plans, u, step⟩
    exact Ast.Semantik.Fragment.bereit_eindeutig (Ast.Semantik.fragment Ast.Category.unit t) P step

/-- No lock-taking step exists for elaborated units: a frame-only head forces the private plan,
    an access head the internal action (`Zugriffsform.ideal_aktion_intern`), so no step plans a lock. -/
theorem einheitVon_kein_sperre (P : Katalog.Plattform) (t : Ast.Unit)
    {c : Maschine.Kontext} {s u : Ast.Semantik.Zustand} {w : PUnit} {plan : Ast.Semantik.Plan}
    {l : Nat} {a : Maschine.SperrAktion}
    (h : (einheitVon P t).system.ISchritt c s w [plan] u)
    (hsperre : plan.aktion = Aktion.sperre l a) : False := by
  obtain ⟨i, kopf, ideal⟩ := h
  rcases (Ast.Semantik.fragment_klassenrein Ast.Category.unit t) i
      (Ast.Semantik.kopf_mem kopf) with hpriv | ⟨z, same⟩
  · have same := (Ast.Semantik.Befehl.ideal_privat i hpriv c s w [plan] u).mp ideal
    have hplan : plan = Ast.Semantik.plan := (List.cons.inj same.1).1
    subst hplan
    cases hsperre
  · subst same
    have hakt := Ast.Semantik.Zugriffsform.ideal_aktion_intern (w := w) z ideal
    rw [hakt] at hsperre
    cases hsperre

/-- Every ready context of an elaborated unit offers a complete protocol step. A frame-only head
    steps by its template (`Befehl.vollzug`); an access head by the step the memory model offers
    (`ZugriffSchrittExistiertAussage`), composed with the protocol (`zugriffKomponierbar`). -/
theorem einheitVon_bereit_vollzug (existiert : ZugriffSchrittExistiertAussage)
    (P : Katalog.Plattform) (t : Ast.Unit)
    {c : Maschine.Kontext} {s : Ast.Semantik.Zustand} (tick : Nat)
    (memory : s.SpeicherGut)
    (h : Maschine.I.Bereit (E := einheitVon P t) s c) :
    ∃ w plan u spur s', (einheitVon P t).system.ImplSchritt c s w [plan] u ∧
      Maschine.FuehrtSchrittAus (einheitVon P t).einrichtung tick c s u plan spur s' := by
  obtain ⟨w, plans, u, ischritt⟩ := h
  obtain ⟨i, kopf, ideal⟩ := ischritt
  rcases (Ast.Semantik.fragment_klassenrein Ast.Category.unit t) i
      (Ast.Semantik.kopf_mem kopf) with hpriv | ⟨z, same⟩
  · have same := (Ast.Semantik.Befehl.ideal_privat i hpriv c s w plans u).mp ideal
    obtain ⟨rfl, rfl⟩ := same
    refine ⟨w, Ast.Semantik.plan, i.nach c s, ⟨[], []⟩, i.nach c s, ⟨i, kopf, ?_⟩, ?_⟩
    · exact (Ast.Semantik.Befehl.impl_privat i hpriv c s w [Ast.Semantik.plan]
        (i.nach c s)).mpr ⟨rfl, rfl⟩
    · exact Ast.Semantik.Befehl.vollzug _ i tick c s
  · subst same
    obtain ⟨w', plan, u', es, g, step, folge⟩ :=
      existiert (Ast.Semantik.fragment Ast.Category.unit t) P z s c kopf memory
    obtain ⟨spur, s', run⟩ :=
      Ast.Semantik.zugriffKomponierbar (Ast.Semantik.fragment Ast.Category.unit t) P z tick s c
        w' plan u' es g kopf step folge
    exact ⟨w', plan, u', spur, s', ⟨Ast.Semantik.Befehl.zugriff z, kopf, step⟩, run⟩

/-- Every instruction step of an elaborated unit plans the internal action — the private plan for a
    frame-only head, the class plan for an access head (`Zugriffsform.ideal_aktion_intern`) — so the
    post-state agrees with the pre-state on cores and status. -/
theorem einheitVon_kontext_erhaelt (P : Katalog.Plattform) (t : Ast.Unit)
    {c : Maschine.Kontext} {s u : Ast.Semantik.Zustand} {w : PUnit}
    {plan : Ast.Semantik.Plan} {spur : Maschine.SchrittSpur Ast.Semantik.Zelle Int}
    {s' : Ast.Semantik.Zustand} {tick : Nat}
    (regel : (einheitVon P t).system.ISchritt c s w [plan] u)
    (aus : Maschine.FuehrtSchrittAus (einheitVon P t).einrichtung tick c s u plan spur s') :
    s'.kerne = s.kerne ∧ s'.status = s.status := by
  obtain ⟨b, kopfB, ideal⟩ := regel
  rcases (Ast.Semantik.fragment_klassenrein Ast.Category.unit t) b
      (Ast.Semantik.kopf_mem kopfB) with hpriv | ⟨z, same⟩
  · have hideal :=
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
  · subst same
    have hschritt : (Ast.Semantik.Befehl.zugriff z).form.zugriffsschritt c s [plan] u :=
      (Ast.Semantik.Zugriffsform.ideal_iff z c s w [plan] u).1 ideal
    have hakt := Ast.Semantik.Zugriffsform.ideal_aktion_intern (w := w) z ideal
    have hstatus : u.status = s.status := by
      rcases hschritt with ⟨_, _, rfl⟩ | ⟨_, v, _, _, rfl⟩ <;> rfl
    obtain ⟨rahmen, _, _, _, fuaus, _, seq⟩ := aus
    generalize haussen : spur.aussen = aussen at fuaus
    rw [hakt] at fuaus
    cases fuaus with
    | intern =>
      have kerneEq : s'.kerne = s.kerne := by rw [seq]; exact rahmen.kerne
      have statusEq : s'.status = s.status := by rw [seq]; exact hstatus
      exact ⟨kerneEq, statusEq⟩

/-- Every implementation step of an elaborated unit plans the internal action — the private plan for a
    frame-only head, the class plan for an access head (`Zugriffsform.ideal_aktion_intern` over the
    ideal the implementation step carries) — so the post-state agrees with the pre-state on cores
    and status. -/
theorem einheitVon_kontext_erhaelt_impl (P : Katalog.Plattform) (t : Ast.Unit)
    {c : Maschine.Kontext} {s u : Ast.Semantik.Zustand} {w : PUnit}
    {plan : Ast.Semantik.Plan} {spur : Maschine.SchrittSpur Ast.Semantik.Zelle Int}
    {s' : Ast.Semantik.Zustand} {tick : Nat}
    (regel : (einheitVon P t).system.ImplSchritt c s w [plan] u)
    (aus : Maschine.FuehrtSchrittAus (einheitVon P t).einrichtung tick c s u plan spur s') :
    s'.kerne = s.kerne ∧ s'.status = s.status := by
  obtain ⟨b, kopfB, implB⟩ := regel
  rcases (Ast.Semantik.fragment_klassenrein Ast.Category.unit t) b
      (Ast.Semantik.kopf_mem kopfB) with hpriv | ⟨z, same⟩
  · have hideal :=
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
  · subst same
    have idealB : (Ast.Semantik.Befehl.zugriff z).ideal c s w [plan] u := implB
    have hschritt : (Ast.Semantik.Befehl.zugriff z).form.zugriffsschritt c s [plan] u :=
      (Ast.Semantik.Zugriffsform.ideal_iff z c s w [plan] u).1 idealB
    have hakt := Ast.Semantik.Zugriffsform.ideal_aktion_intern (w := w) z idealB
    have hstatus : u.status = s.status := by
      rcases hschritt with ⟨_, _, rfl⟩ | ⟨_, v, _, _, rfl⟩ <;> rfl
    obtain ⟨rahmen, _, _, _, fuaus, _, seq⟩ := aus
    generalize haussen : spur.aussen = aussen at fuaus
    rw [hakt] at fuaus
    cases fuaus with
    | intern =>
      have kerneEq : s'.kerne = s.kerne := by rw [seq]; exact rahmen.kerne
      have statusEq : s'.status = s.status := by rw [seq]; exact hstatus
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
