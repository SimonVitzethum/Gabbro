/-
  File:      core/Core/Annahme/Annahme.lean
  Subject:   Acceptance and its satisfiability (PERFECT-MODEL §3.2, step M5).

  `Akzeptiert E := Lokal E ∧ KlauselnWahr E ∧ WaechterHalten E`: the perfect checker over the
  syntax, `I` and the catalogue only. `akzeptiert_erfuellbar` proves the three conjuncts hold
  jointly for a concrete trivial-syntax system, and `geschlossen_nicht_akzeptiert` with
  `geschlossen_erfuellbar` proves acceptance is not vacuous in the refusal direction: a system
  with a closed waiting set at an `I` cut is not accepted, and such a set exists.
-/
module

public import Core.Annahme.Lokal
public import Core.Annahme.Klauseln
public import Core.Annahme.Waechter

@[expose] public section

namespace Gabbro.Core.Annahme

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type}

/-- **`Akzeptiert E := Lokal E ∧ KlauselnWahr E ∧ WaechterHalten E`** (§3.2): the perfect
    checker. It may use only the syntax, `I` and the catalogue — never the implementation
    machine, images, runs or an error notion. `I` never mentions `Akzeptiert`. -/
def Akzeptiert [DecidableEq L] (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    [KlauselTabelle E] [GuardVerwendung E] : Prop :=
  Lokal E ∧ KlauselnWahr E ∧ WaechterHalten E

/-- Acceptance implies a well-formed catalogue selection — the `Akzeptiert`-conjunct of
    `NichtLeer` (§2.1), from `Lokal`. -/
theorem akzeptiert_katalog [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    [KlauselTabelle E] [GuardVerwendung E]
    (h : Akzeptiert E) : KatalogWohlgeformt E.katalog :=
  h.1.1

/-- The trivial rule: no implementation step, no `I` step. -/
def trivialesRegel
    : Regel (Zustand Unit Unit Unit Unit Unit Unit) (SchrittPlan Unit Unit Unit Unit) Unit :=
  ⟨fun _ _ _ _ => False, fun _ _ _ _ _ => False⟩

instance trivialeRegelLokal : RegelLokal trivialesRegel := ⟨⟩

instance trivialeRegelAussen : RegelAussen trivialesRegel := ⟨⟩

/-- The trivial system: one form with no steps, no head anywhere, nothing finished, never
    blocked. -/
def trivialesSystem : MaschinenSystem Unit Unit Unit Unit Unit Unit Unit Unit Unit :=
  ⟨fun _ => trivialesRegel, fun _ _ => none, fun _ _ => False, fun _ _ _ => False⟩

/-- The trivial unit on the approved x86-64 rows. -/
def trivialeEinheit : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit where
  katalog := Plattform.x86_64.katalog
  bild := ⟨Bildformat.elf, fun _ => none, []⟩
  einrichtung := ⟨fun _ => (), fun _ => (), fun _ => (), fun _ => (),
    fun _ _ _ => False, fun _ _ => True⟩
  system := trivialesSystem
  startdaten := fun _ => ⟨fun _ => (), fun _ => .ruht,
    fun _ => ⟨none, .nutzer, (), fun _ => true, 0, false, []⟩,
    ⟨fun _ => true, fun _ => 0⟩⟩
  laden := fun _ _ => none

instance trivialeKlauseln : KlauselTabelle trivialeEinheit where
  voraus := fun _ => True
  sicher := fun _ => True
  invariant := fun _ => True

instance trivialeVerwendung : GuardVerwendung trivialeEinheit where
  bedarf := fun _ _ _ _ => False

/-- **Satisfiability of acceptance**: a concrete (trivial-syntax) system where all three
    conjuncts hold jointly — no uses to guard, nothing written to violate, never blocked. -/
theorem akzeptiert_erfuellbar
    : ∃ E : Einheit Unit Unit Unit Unit Unit Unit Unit Unit Unit, Akzeptiert E := by
  have hL : Lokal trivialeEinheit :=
    ⟨Plattform.katalog_wohlgeformt .x86_64, fun i => ?_, Aussen.zulassung_m2 .x86_64,
      fun i => ?_⟩
  · show RegelLokal trivialesRegel
    exact inferInstance
  · show RegelAussen trivialesRegel
    exact inferInstance
  have hK : KlauselnWahr trivialeEinheit := by
    intro ρ _
    exact ⟨trivial, fun _ => trivial, fun _ _ => trivial⟩
  have hW : WaechterHalten trivialeEinheit := by
    refine ⟨fun ρ _ t op args need => False.elim need, fun ρ _ t => ?_⟩
    intro h
    obtain ⟨C, hC⟩ := h
    obtain ⟨hex, hall⟩ := hC
    obtain ⟨c, hc⟩ := hex
    obtain ⟨b, hb, _⟩ := hall c hc
    exact False.elim hb
  exact ⟨trivialeEinheit, hL, hK, hW⟩

/-- **A system with a closed waiting set at an `I` cut is not accepted.** -/
theorem geschlossen_nicht_akzeptiert [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    [KlauselTabelle E] [GuardVerwendung E]
    (ρ : I.Lauf E) (hρ : I.Laeufe E ρ) (t : I.Schnitt E ρ)
    (C : Kontext → Prop) (h : GeschlossenWartend E (ρ.zeit.zustand t.val) C) :
    ¬ Akzeptiert E := by
  intro ha
  exact ha.2.2.2 ρ hρ t ⟨C, h⟩

/-- Two locks held cross-wise: each holder waits on the lock the other holds. -/
def kreuzSperren : Bool → SperrZustand
  | false => ⟨some (.faden 1), []⟩
  | true => ⟨some (.faden 0), []⟩

/-- Both contexts wait on the lock the other holds. -/
def kreuzBlockiert : Zustand Bool Unit Unit Unit Unit Unit → Kontext → Blockade Bool Unit → Prop
  | _, .faden 0, .sperre false => True
  | _, .faden 1, .sperre true => True
  | _, _, _ => False

/-- The cross-waiting rule: silent in both machines. -/
def kreuzRegel
    : Regel (Zustand Bool Unit Unit Unit Unit Unit) (SchrittPlan Bool Unit Unit Unit) Unit :=
  ⟨fun _ _ _ _ => False, fun _ _ _ _ _ => False⟩

/-- The cross-waiting system: one silent form, heads nowhere, nothing finished. -/
def kreuzSystem : MaschinenSystem Bool Unit Unit Unit Unit Unit Unit Unit Unit :=
  ⟨fun _ => kreuzRegel, fun _ _ => none, fun _ _ => False, kreuzBlockiert⟩

/-- The cross-waiting unit on the approved x86-64 rows. -/
def kreuzEinheit : Einheit Bool Unit Unit Unit Unit Unit Unit Unit Unit where
  katalog := Plattform.x86_64.katalog
  bild := ⟨Bildformat.elf, fun _ => none, []⟩
  einrichtung := ⟨fun _ => (), fun _ => (), fun _ => (), fun _ => (),
    fun _ _ _ => False, fun _ _ => True⟩
  system := kreuzSystem
  startdaten := fun _ => ⟨fun _ => (), fun _ => .ruht,
    fun _ => ⟨none, .nutzer, (), fun _ => true, 0, false, []⟩,
    ⟨fun _ => true, fun _ => 0⟩⟩
  laden := fun _ _ => none

/-- The cross-waiting state: free memory, no traffic, locks held cross-wise. -/
def kreuzZustand : Zustand Bool Unit Unit Unit Unit Unit :=
  { (Zustand.start (L := Bool) (Ort := Unit) (Wert := Unit) (Raum := Unit) (Lok := Unit)
      (Grund := Unit) (fun _ => ()) (fun _ => .ruht)
      (fun _ => ⟨none, .nutzer, (), fun _ => true, 0, false, []⟩)
      ⟨fun _ => true, fun _ => 0⟩) with sperren := kreuzSperren }

/-- **The closed waiting set exists**: both contexts wait on the lock the other holds. -/
theorem geschlossen_erfuellbar :
    ∃ (E : Einheit Bool Unit Unit Unit Unit Unit Unit Unit Unit)
      (s : Zustand Bool Unit Unit Unit Unit Unit) (C : Kontext → Prop),
      GeschlossenWartend E s C := by
  refine ⟨kreuzEinheit, kreuzZustand, fun c => c = .faden 0 ∨ c = .faden 1, ?_, ?_⟩
  · exact ⟨.faden 0, Or.inl rfl⟩
  · intro c hc
    cases hc with
    | inl h =>
      subst h
      refine ⟨.sperre false, True.intro, True.intro, ?_, ?_⟩
      · intro l hl
        cases hl
        exact ⟨.faden 1, Or.inr rfl, rfl⟩
      · intro k hk
        cases hk
    | inr h =>
      subst h
      refine ⟨.sperre true, True.intro, True.intro, ?_, ?_⟩
      · intro l hl
        cases hl
        exact ⟨.faden 0, Or.inl rfl, rfl⟩
      · intro k hk
        cases hk

end Gabbro.Core.Annahme
