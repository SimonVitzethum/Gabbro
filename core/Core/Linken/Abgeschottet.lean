module

public import Core.Linken.Aussage
public import Core.Annahme.AussenLauf
public import Core.Annahme.Klauseln
public import Core.Annahme.Waechter
public import Core.Annahme.Schranken
public import Core.Beobachtung.Fluss.Quellfragment

@[expose] public section

namespace Gabbro.Core.Linken

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Annahme
open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

/-- No closed waiting set exists for a fragment unit: no context is ever blocked,
    so the deadlock conjunct of `WaechterHalten` holds for every linked whole
    without any seal. -/
theorem fragment_geschlossen_wartend_leer (p : Fragment) (platform : Plattform)
    (s : Zustand) (C : Kontext → Prop) :
    ¬ GeschlossenWartend (p.einheit platform) s C := by
  intro h
  obtain ⟨⟨c, hc⟩, blocked⟩ := h
  obtain ⟨b, hb, _, _, _⟩ := blocked c hc
  exact hb

/-- The holder row is vacuous for a fragment unit: no lock carries a declared hold
    bound, so `SperrHalterHalten` holds for every linked whole without any seal. -/
theorem fragment_sperrhalter_halten (p : Fragment) (platform : Plattform) :
    SperrHalterHalten (p.einheit platform) := by
  intro ρ hρ t l h hbesitz hp
  exact (hp rfl).elim

/-- Every instruction's authority rule holds in every linked unit: the rule is the
    instruction's own, independent of the surrounding code. -/
theorem verknuepfte_regel_lokal (plan : Bauplan) (b : Befehl) :
    RegelLokal ((verknuepfteFragmente plan).einheit plan.plattform) b :=
  b.lokal _ rfl

/-- Entries relocate by concatenation offset: entries of the second fragment shift
    behind the first fragment's instructions; the first fragment's entry wins. -/
theorem anhaengen_eintritte (a b : Fragment) (c : Kontext) :
    (a.anhaengen b).eintritte c = (a.eintritte c).or ((b.eintritte c).map (· + a.code.length)) :=
  rfl

/-- The seal is already implied by a successful link. -/
theorem seal_aus_link {plan : Bauplan} {frag : Fragment} (h : linke plan = some frag) :
    kontrollflussAbgeschottet plan = true := by
  obtain ⟨hok, _⟩ := linke_eq_some h
  simp only [bauplanOk] at hok
  rw [Bool.and_eq_true] at hok
  exact hok.2

/-- Composition from sealed parts up to the guard transfer: with accepted parts and
    every guard use of the linked whole satisfied, the linked whole is accepted.
    The seal is not needed for any conjunct proved here — it is only needed for the
    guard transfer itself, which remains open (the simulation of whole runs by part
    runs). -/
theorem linker_akzeptiert_aus_guard_transfer (plan : Bauplan) (frag : Fragment)
    (hlink : linke plan = some frag)
    (hparts : ∀ m ∈ plan.module, Annahme.Akzeptiert (m.fragment.einheit plan.plattform))
    (hguard : ∀ (ρ : I.Lauf (frag.einheit plan.plattform))
      (hρ : I.Laeufe (frag.einheit plan.plattform) ρ) (t : I.Schnitt _ ρ)
      (op : PartielleOperation) (args : Operanden op),
      (kanonischeVerwendung _).bedarf ρ t op args → waechterBedarf op args) :
    Akzeptiert (frag.einheit plan.plattform) := by
  obtain ⟨hok, rfl⟩ := linke_eq_some hlink
  have hcompat : annahmenKompatibel plan = true := by
    simp only [bauplanOk] at hok
    rw [Bool.and_eq_true] at hok
    rw [Bool.and_eq_true] at hok
    exact hok.1.2
  have hklauseln : (verknuepfteFragmente plan).klauseln = .leer :=
    verknuepfte_klauseln_leer hcompat
  let E := (verknuepfteFragmente plan).einheit plan.plattform
  refine ⟨⟨Plattform.katalog_wohlgeformt plan.plattform, fun b => Befehl.regelLokal _ _ b,
    ⟨Aussen.zulassung_m2 _, ?_⟩, Beobachtung.fragment_fluss_lokal _ _
      (fun b _ => b.klasse_privat), ?_⟩, ?_, ?_⟩
  · apply aussen_gueltig_aus_kontext
    intro run t s c w spur next step
    cases step with
    | kontext _ _ rule execute =>
      obtain ⟨b, _, transfer⟩ := rule
      obtain ⟨rfl, rfl⟩ := b.vollzug_genau (w := w) transfer execute b.klasse_privat
      exact ⟨⟨fun _ mem => (List.not_mem_nil mem).elim, [],
        (List.append_nil _).symm, fun _ mem => (List.not_mem_nil mem).elim⟩, fun h => h⟩
  · exact schrankenLokal_leer (E := (verknuepfteFragmente plan).einheit plan.plattform) rfl rfl rfl
  · intro run conforms
    change (∀ pred ∈ (verknuepfteFragmente plan).klauseln.voraus, _) ∧
      (∀ _ : I.Schnitt E run, ∀ pred ∈ (verknuepfteFragmente plan).klauseln.invariant, _) ∧
      ∀ _ : I.Schnitt E run, _ → ∀ pred ∈ (verknuepfteFragmente plan).klauseln.sicher, _
    rw [hklauseln]
    exact ⟨fun _ h => (List.not_mem_nil h).elim, fun _ _ h => (List.not_mem_nil h).elim,
      fun _ _ _ h => (List.not_mem_nil h).elim⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro run conforms t op args need
      exact hguard run conforms t op args need
    · intro run conforms t waiting
      obtain ⟨contexts, ⟨c, member⟩, blocked⟩ := waiting
      obtain ⟨_, impossible, _⟩ := blocked c member
      exact impossible
    · intro run conforms t l h _ hne
      exact (hne rfl).elim

end Gabbro.Core.Linken
