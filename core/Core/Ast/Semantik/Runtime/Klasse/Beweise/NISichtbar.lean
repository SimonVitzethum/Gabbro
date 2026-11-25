/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Beweise/NISichtbar.lean
  Subject:   WHAT THE FLOW PREMISES OF THE NON-READING CLASSES ACTUALLY GIVE (MK-03). The pinned
             `KlassenNIAussage` asks for `RegelNIPflicht` from three premises: the unit's flow rule for
             the one form `f`, visibility of the form's operands, and the class not reading. This file
             proves the part that follows from those premises alone: the public-state comparison is
             symmetric and transitive, two steps of the SAME form from public-equal states end in
             public-equal states with the same plan view and the same public output, and the operands
             of a form are equal on public-equal states.

             It also proves that the premises do NOT determine the form at the head of the second run:
             a unit can satisfy them and still have `system.kopf` return different forms on two
             publicly equal states. The remaining step of `KlassenNIAussage` -- that the second run
             takes the same form, plus the coupled graph step that matches the low events -- is
             therefore not a consequence of the pinned premises. The pinned statements are unchanged.
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Pflichten

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Beobachtung
open Gabbro.Core.Speicher (Modus)

/-! ### What follows from the flow premises -/

/-- The public state comparison is symmetric: every component is an equality of a projection. -/
theorem Beobachtung.QuellzustandGleich.symm
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type}
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {v u : Maschine.Zustand L Ort Wert Raum Lok Grund}
    (h : Beobachtung.QuellzustandGleich E v u) :
    Beobachtung.QuellzustandGleich E u v := by
  refine ⟨?_, ?_, ?_, h.2.2.2.1.symm, h.2.2.2.2.1.symm, ?_⟩
  · intro c p hp
    exact (h.1 c p hp).symm
  · intro c
    exact (h.2.1 c).symm
  · intro x
    exact (h.2.2.1 x).symm
  · intro c
    exact (h.2.2.2.2.2 c).symm

/-- The public state comparison is transitive. -/
theorem Beobachtung.QuellzustandGleich.trans
    {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type}
    {E : Maschine.Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    {v u n : Maschine.Zustand L Ort Wert Raum Lok Grund}
    (h₁ : Beobachtung.QuellzustandGleich E v u) (h₂ : Beobachtung.QuellzustandGleich E u n) :
    Beobachtung.QuellzustandGleich E v n := by
  refine ⟨?_, ?_, ?_, h₁.2.2.2.1.trans h₂.2.2.2.1, h₁.2.2.2.2.1.trans h₂.2.2.2.2.1, ?_⟩
  · intro c p hp
    exact (h₁.1 c p hp).trans (h₂.1 c p hp)
  · intro c
    exact (h₁.2.1 c).trans (h₂.2.1 c)
  · intro x
    exact (h₁.2.2.1 x).trans (h₂.2.2.1 x)
  · intro c
    exact (h₁.2.2.2.2.2 c).trans (h₂.2.2.2.2.2 c)

/-- Visibility of a form's operands, specialised to two public-equal states at one context. -/
theorem Schrittform.operand_gleich {ι : Type} {E : Klasseneinheit ι} {F : Schrittform}
    (sicht : F.Operandensicht E) {c : Kontext} {v₁ v₂ : Zustand}
    (gleich : Beobachtung.QuellzustandGleich E v₁ v₂) :
    F.operand (v₁.lokal c) = F.operand (v₂.lokal c) :=
  sicht c v₁ v₂ gleich

/-- **Two steps of the same form from public-equal states stay public-equal.** This is the whole
    content of `RegelFluss` for a pair of steps: for a public control form the rule states the
    agreement directly; for a private control form each step preserves the public state and has an
    empty plan/output view, and symmetry plus transitivity complete the claim. -/
theorem Beobachtung.RegelFluss.schrittpaar_gleich
    {ι : Type} {E : Klasseneinheit ι} {f : ι} (fl : Beobachtung.RegelFluss E f)
    {c : Kontext} {v₁ w₁ p₁ u₁ v₂ w₂ p₂ u₂}
    (gleich : Beobachtung.QuellzustandGleich E v₁ v₂)
    (s₁ : Beobachtung.FormSchritt E f c v₁ w₁ p₁ u₁)
    (s₂ : Beobachtung.FormSchritt E f c v₂ w₂ p₂ u₂) :
    Beobachtung.QuellzustandGleich E u₁ u₂ ∧ PlanSicht E p₁ = PlanSicht E p₂ ∧
      AusgabeSicht E c v₁ u₁ = AusgabeSicht E c v₂ u₂ := by
  by_cases pub : oeffentlich (E.fluss.kontrolle f) = true
  · exact fl.2 pub c v₁ w₁ p₁ u₁ v₂ w₂ p₂ u₂ gleich s₁ s₂
  · have pubf : oeffentlich (E.fluss.kontrolle f) = false := by
      cases hb : oeffentlich (E.fluss.kontrolle f) <;> simp_all
    have o₁ := (fl.1 c v₁ w₁ p₁ u₁ s₁).2 pubf
    have o₂ := (fl.1 c v₂ w₂ p₂ u₂ s₂).2 pubf
    have hquel : Beobachtung.QuellzustandGleich E u₁ u₂ :=
      Beobachtung.QuellzustandGleich.trans (v := u₁) (u := v₁) (n := u₂)
        (Beobachtung.QuellzustandGleich.symm (v := v₁) (u := u₁) o₁.1)
        (Beobachtung.QuellzustandGleich.trans (v := v₁) (u := v₂) (n := u₂) gleich o₂.1)
    exact ⟨hquel, o₁.2.1.trans o₂.2.1.symm, o₁.2.2.trans o₂.2.2.symm⟩

/-! ### The missing premise: the head of the second run is not determined -/

/-- A secret compartment, as in the other flow countermodels. -/
def NISichtbar.geheim : Beobachtung.Etikett := {0}

theorem NISichtbar.geheim_verborgen : oeffentlich NISichtbar.geheim = false := by
  apply decide_eq_false
  intro eq
  have mem : 0 ∈ NISichtbar.geheim := Finset.mem_singleton_self _
  rw [eq] at mem
  exact Finset.notMem_empty _ mem

/-- All locations and control labels are secret in the countermodel. -/
def NISichtbar.etikettOrt (_ : Zelle) : Beobachtung.Etikett := NISichtbar.geheim
def NISichtbar.etikettBoot (_ : Nat) : Beobachtung.Etikett := NISichtbar.geheim
def NISichtbar.lokalEtikett (_ : Kontext) : Beobachtung.LokaleEtiketten Rahmen :=
  Beobachtung.LokaleEtiketten.ganz NISichtbar.geheim
def NISichtbar.kontrollEtikett (_ : Bool) : Beobachtung.Etikett := NISichtbar.geheim

/-- A writing form that names no particular cell. -/
def NISichtbar.schreibform (m : Modus) : Schrittform :=
  ⟨.schreiben m, fun _ => Operand.keiner, fun r _ _ => r⟩

/-- A unit embedding the writing form at `true`. Its head function reads the discarded-answer
    counter, which is NOT part of the public state comparison: two publicly equal states carry
    different forms, while the flow and visibility premises for `true` are satisfied. -/
def NISichtbar.einheit (m : Modus) : Klasseneinheit Bool :=
  let F := NISichtbar.schreibform m
  { katalog := (Plattform.x86_64).katalog,
    bild := bild,
    einrichtung := einrichtung Fragment.leer.eingang Fragment.leer.eintritte Fragment.leer.speicher,
    system := ⟨(fun _ => F.regel),
      (fun s _c => if s.verworfen eintritt = 0 then some true else some false),
      (fun _ _ => False), (fun _ _ _ => False)⟩,
    startdaten := fun start =>
      startdaten Fragment.leer.eingang Fragment.leer.eintritte (start.assignment 0) .x86_64 [],
    startmedium := startmedium,
    laden := laden Fragment.leer.eingang Fragment.leer.eintritte Fragment.leer.speicher .x86_64,
    lokalerBezug := Eq,
    stotterLaenge := fun _ => 0,
    quelltabellen := Fragment.leer.tabellen,
    etiketten := { ort := NISichtbar.etikettOrt, bootByte := NISichtbar.etikettBoot },
    fluss := { lokal := NISichtbar.lokalEtikett, kontrolle := NISichtbar.kontrollEtikett } }

/-- A start whose bytes are absent; it only supplies a machine state to place frames in. -/
def NISichtbar.start : AussenStart :=
  ⟨0, fun _ => some 0, [], fun _ => none, .leer⟩

/-- The state of the unit with the hidden discarded-answer counter set to `b`. -/
def NISichtbar.zustand (m : Modus) (b : Nat) : Zustand :=
  let v := (I.start (NISichtbar.einheit m) NISichtbar.start).2
  { v with verworfen := fun _ => b }

/-- Changing the hidden counter preserves the public state. -/
theorem NISichtbar.quellzustand_gleich (m : Modus) :
    Beobachtung.QuellzustandGleich (NISichtbar.einheit m)
      (NISichtbar.zustand m 0) (NISichtbar.zustand m 1) := by
  refine ⟨?_, ?_, ?_, rfl, rfl, ?_⟩
  · intro c p hp
    rfl
  · intro c
    rfl
  · intro x
    rfl
  · intro c
    rfl

/-- The embedded form, its visibility premise and `liest = false` all hold. -/
theorem NISichtbar.premissen (m : Modus) :
    (NISichtbar.schreibform m).klasse = .schreiben m ∧
      (NISichtbar.schreibform m).Eingebettet (NISichtbar.einheit m) true ∧
      (.schreiben m : Wirkungsklasse).liest = false ∧
      (NISichtbar.schreibform m).Operandensicht (NISichtbar.einheit m) := by
  refine ⟨rfl, ⟨rfl, rfl, rfl⟩, rfl, ?_⟩
  intro c v₁ v₂ gleich
  rfl

/-- Yet the two publicly equal states carry different forms at the head. -/
theorem NISichtbar.kopf_nicht_offenbar (m : Modus) :
    (NISichtbar.einheit m).system.kopf (NISichtbar.zustand m 0) eintritt ≠
      (NISichtbar.einheit m).system.kopf (NISichtbar.zustand m 1) eintritt := by
  intro h
  have h0 : (NISichtbar.einheit m).system.kopf (NISichtbar.zustand m 0) eintritt = some true := by
    change (if (NISichtbar.zustand m 0).verworfen eintritt = 0 then some true else some false) = some true
    rfl
  have h1 : (NISichtbar.einheit m).system.kopf (NISichtbar.zustand m 1) eintritt = some false := by
    change (if (NISichtbar.zustand m 1).verworfen eintritt = 0 then some true else some false) = some false
    rfl
  rw [h0, h1] at h
  cases h

end Gabbro.Core.Ast.Semantik
