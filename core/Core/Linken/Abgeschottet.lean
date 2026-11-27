module

public import Core.Linken.Aussage
public import Core.Annahme.AussenLauf
public import Core.Annahme.Klauseln
public import Core.Annahme.Waechter
public import Core.Annahme.Schranken
public import Core.Beobachtung.Fluss.Quellfragment
public import Core.Ast.Semantik.Runtime.Mehrkontext.System

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
  Befehl.regelLokal _ _ b

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

/-- Binding keeps the layout used by the static seal and the relocation of context entries. -/
theorem bindefragment_laenge (m : Modul) (weiter : Bool) :
    (m.bindefragment weiter).code.length = m.fragment.code.length := by
  cases m with
  | mk name inhalt exporte importe =>
    cases inhalt <;> cases weiter <;> (
      first | rfl | simp only [Modul.bindefragment, Modul.fragment, Fragment.anhaengen,
        Fragment.einzel, List.length_append, List.length_cons, List.length_nil])

/-- The bound layout preserves each instruction except for the generated library transfer. -/
theorem bindefragment_befehl (m : Modul) (rest : List Modul) (pos : Nat) (b : Befehl)
    (atPos : (m.bindefragment (hatFortsetzung rest)).code[pos]? = some b) :
    m.fragment.code[pos]? = some b ∨
      (b = .springe 1 ∧ pos + 1 = m.fragment.code.length ∧
        ∃ tree next tail, m.inhalt = .bibliothek tree ∧ rest = next :: tail ∧
          next.fragment.code.isEmpty = false) := by
  cases hnext : hatFortsetzung rest with
  | false =>
    rw [hnext] at atPos
    exact Or.inl atPos
  | true =>
    cases hm : m.inhalt with
    | roh p | quelle _ _ | mitInvarianten _ =>
      apply Or.inl
      simpa only [Modul.fragment, Modul.bindefragment, hm] using atPos
    | bibliothek tree =>
      let code := (unitBody tree.2).code
      have original : m.fragment.code = code ++ [.ende] := by
        simp only [Modul.fragment, Modul.bindefragment, hm]
        rfl
      have emitted : (m.bindefragment (hatFortsetzung rest)).code = code ++ [.springe 1] := by
        simp only [Modul.bindefragment, hm, hnext, if_true]
        rfl
      rw [emitted] at atPos
      by_cases inside : pos < code.length
      · apply Or.inl
        rw [original, List.getElem?_append_left inside]
        exact (List.getElem?_append_left inside).symm.trans atPos
      · have bound := (List.getElem?_eq_some_iff.mp atPos).1
        simp only [List.length_append, List.length_cons, List.length_nil] at bound
        have posEq : pos = code.length := by omega
        subst pos
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at atPos
        have bEq : b = .springe 1 := (Option.some.inj atPos).symm
        refine Or.inr ⟨bEq, ?_, ?_⟩
        · simp only [original, List.length_append, List.length_cons, List.length_nil]
        · cases rest with
          | nil => cases hnext
          | cons next tail =>
            refine ⟨tree, next, tail, rfl, rfl, ?_⟩
            change !next.fragment.code.isEmpty = true at hnext
            cases hempty : next.fragment.code.isEmpty with
            | false => rfl
            | true => rw [hempty] at hnext
                      cases hnext

/-- Every emitted static target stays in its module, except for the library terminator
    synthesized at the last slot. That instruction can only enter an immediate successor
    with a first instruction. The input seal still applies to all input targets. -/
theorem bindefragment_sprungziel (m : Modul) (rest : List Modul) (letzter : Bool)
    (sealed : modulAbgeschottet m letzter = true) (pos : Nat) (b : Befehl)
    (atPos : (m.bindefragment (hatFortsetzung rest)).code[pos]? = some b) :
    sprungZielInnen pos m.fragment.code.length b = true ∨
      (b = .springe 1 ∧ pos + 1 = m.fragment.code.length ∧
        ∃ tree next tail, m.inhalt = .bibliothek tree ∧ rest = next :: tail ∧
          next.fragment.code.isEmpty = false) := by
  rcases bindefragment_befehl m rest pos b atPos with input | bridge
  · apply Or.inl
    unfold modulAbgeschottet at sealed
    rw [Bool.and_eq_true] at sealed
    have ht := (List.all_eq_true.mp sealed.1) pos
      (List.mem_range.mpr (List.getElem?_eq_some_iff.mp input).1)
    simpa only [input] using ht
  · exact Or.inr bridge

/-- Composition from sealed parts up to the guard transfer: with accepted parts, a
    frame-only linked program and every guard use of the linked whole satisfied, the
    linked whole is accepted. The seal is not needed for any conjunct proved here; it
    is only needed for the guard transfer itself, which remains open (the simulation
    of whole runs by part runs). -/
theorem linker_akzeptiert_aus_guard_transfer (plan : Bauplan) (frag : Fragment)
    (hlink : linke plan = some frag)
    (hparts : ∀ m ∈ plan.module, Annahme.Akzeptiert (m.fragment.einheit plan.plattform))
    (hpriv : ∀ b ∈ (verknuepfteFragmente plan).code, b.Privat)
    (hguard : ∀ (ρ : I.Lauf (frag.einheit plan.plattform)) (hρ : I.Laeufe _ ρ)
      (t : I.Schnitt _ ρ) (op : PartielleOperation) (args : Operanden op),
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
  have hdom : DomaenenLokal E := by
    refine ⟨eineTabelle_akzeptiert,
      fun s c i hkopf _ _ _ _ _ w _ spur himpl haus => ?_⟩
    have head' : kopf (verknuepfteFragmente plan).code s c = some i := hkopf
    have hpriv_i := hpriv i (kopf_mem head')
    obtain ⟨rfl, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := i.vollzug_genau_privat hpriv_i (w := w) himpl haus
    exact spurRespektiert_leer _ _ _
  refine ⟨⟨Plattform.katalog_wohlgeformt plan.plattform, fun b => Befehl.regelLokal _ _ b,
    ⟨Aussen.zulassung_m2 _, ?_⟩, Beobachtung.fragment_fluss_lokal _ _ hpriv,
    schrankenLokal_leer (E := E) rfl rfl rfl,
    abschnittWartefrei_ohne_blockade E (fun _ _ _ hb => hb), hdom⟩, ?_, ?_⟩
  · apply aussen_gueltig_aus_kontext
    intro run t s c w spur next step
    cases step with
    | kontext _ _ rule execute =>
      obtain ⟨b, head, transfer⟩ := rule
      have head' : kopf (verknuepfteFragmente plan).code s c = some b := head
      obtain ⟨rfl, _, _, hfragen, hantworten, _, _, _, _, hbuchung, _, _, _, hepoch, _, _⟩ := b.vollzug_genau_privat (hpriv b (kopf_mem head')) (w := w) transfer execute
      obtain ⟨_, hnach⟩ := (b.impl_privat (hpriv b (kopf_mem head')) c s w _ _).1 transfer
      have hb : next.buchung = s.buchung := by simp only [hbuchung, hnach, Befehl.nach]
      refine ⟨⟨fun _ mem => (List.not_mem_nil mem).elim, [], ?_, fun _ mem => (List.not_mem_nil mem).elim⟩, ?_⟩
      · rw [hb]
        exact (List.append_nil _).symm
      · intro h
        have e1 : next.fragen = s.fragen := by simp only [hfragen, hnach, Befehl.nach]
        have e2 : next.antworten = s.antworten := by simp only [hantworten, hnach, Befehl.nach]
        have e3 : next.epoche = s.epoche := by simp only [hepoch, hnach, Befehl.nach]
        simp only [OffeneGriffeEigen, e1, e2, e3, hb, AussengriffeEigen] at h ⊢
        exact h
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
