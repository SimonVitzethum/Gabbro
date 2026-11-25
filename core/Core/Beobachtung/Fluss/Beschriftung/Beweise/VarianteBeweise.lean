module

public import Core.Ast.Aggregate.Runtime
public import Core.Beobachtung.Fluss.Beschriftung.Variante
public import Core.Beobachtung.Fluss.Beschriftung.AufgabenBeweise

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung Katalog

theorem schreibform_baueVariante (ziel : Nat) (name : List Char)
    (labels : List Identifier) (cases : List (Option (Ty .value)))
    (index : Fin cases.length) :
    (Befehl.baueVariante ziel name labels cases index).Schreibform ziel [.temp ziel] :=
  ⟨fun r => do
      let value ← variantActual (cases.get index) (r.temp ziel)
      pure ⟨variantValueType name labels cases, variantInject cases index value⟩,
    fun _ _ => rfl,
    fun r₁ r₂ h => by
      have h0 : r₁.temp ziel = r₂.temp ziel :=
        h (.temp ziel) (List.mem_singleton_self _)
      simp only [h0]⟩

theorem baueVarianteSicht (β : Beschriftung) (pc ziel : Nat) (name : List Char)
    (labels : List Identifier) (cases : List (Option (Ty .value)))
    (index : Fin cases.length) (regel : β.SchreibRegel pc ziel [.temp ziel]) :
    (Befehl.baueVariante ziel name labels cases index).SichtErhaltendBei β pc :=
  Befehl.sichtErhaltend_schreibform
    (schreibform_baueVariante ziel name labels cases index) regel

theorem schreibform_optionIstBesetzt (ziel count : Nat) :
    (Befehl.optionIstBesetzt ziel count).Schreibform ziel [.temp ziel] :=
  ⟨fun r => do
      let value ← (r.temp ziel).bind (wertAls (indexOptionType count))
      pure ⟨.bool, indexOptionPresent value⟩,
    fun _ _ => rfl,
    fun r₁ r₂ h => by
      have h0 : r₁.temp ziel = r₂.temp ziel :=
        h (.temp ziel) (List.mem_singleton_self _)
      simp only [h0]⟩

theorem optionIstBesetztSicht (β : Beschriftung) (pc ziel count : Nat)
    (regel : β.SchreibRegel pc ziel [.temp ziel]) :
    (Befehl.optionIstBesetzt ziel count).SichtErhaltendBei β pc :=
  Befehl.sichtErhaltend_schreibform (schreibform_optionIstBesetzt ziel count) regel

theorem definiereVarianteSicht : DefiniereVarianteSichtAussage := by
  intro β pc name labels cases hT hL r₁ r₂ live hpc h
  have e₁ : (Befehl.definiereVariante name labels cases).auswerten r₁ live =
      r₁.installSchema ⟨variantSchemaType name labels cases, PUnit.unit⟩ := rfl
  have e₂ : (Befehl.definiereVariante name labels cases).auswerten r₂ live =
      r₂.installSchema ⟨variantSchemaType name labels cases, PUnit.unit⟩ := rfl
  rw [e₁, e₂]
  exact installSchemaSicht β pc _ hT hL r₁ r₂ live hpc h

theorem definiereTraegerSicht : DefiniereTraegerSichtAussage := by
  intro β pc count labels layout exported hT hL r₁ r₂ live hpc h
  have e₁ : (Befehl.definiereTraeger count labels layout exported).auswerten r₁ live =
      r₁.installSchema ⟨.carrierSchema count labels layout exported, PUnit.unit⟩ := rfl
  have e₂ : (Befehl.definiereTraeger count labels layout exported).auswerten r₂ live =
      r₂.installSchema ⟨.carrierSchema count labels layout exported, PUnit.unit⟩ := rfl
  rw [e₁, e₂]
  exact installSchemaSicht β pc _ hT hL r₁ r₂ live hpc h

theorem definiereEffektgruppeSicht : DefiniereEffektgruppeSichtAussage := by
  intro β pc effects hT hL r₁ r₂ live hpc h
  have e₁ : (Befehl.definiereEffektgruppe effects).auswerten r₁ live =
      r₁.installSchema ⟨.effectGroupSchema effects, PUnit.unit⟩ := rfl
  have e₂ : (Befehl.definiereEffektgruppe effects).auswerten r₂ live =
      r₂.installSchema ⟨.effectGroupSchema effects, PUnit.unit⟩ := rfl
  rw [e₁, e₂]
  exact installSchemaSicht β pc _ hT hL r₁ r₂ live hpc h

/-- The view after choosing an environment: one static entry is pushed onto the
    always-visible environment. -/
theorem sicht_waehleUmgebung (β : Beschriftung) (r : Rahmen) (live : Nat → Bool)
    (name : Identifier) (abi : Katalog.DienstAbi) (row : Katalog.FirmwareZeile) :
    ((Befehl.waehleUmgebung name abi row).auswerten r live).sicht β =
      { r.sicht β with
        pc := r.pc + 1
        temp := fun s => if oeffentlich (β.temp (r.pc + 1) s) = true then r.temp s else none
        lokale := maskiereLokal (β.lokal (r.pc + 1)) 0 r.lokale
        environment := (name, abi, row) :: r.environment } := rfl

theorem waehleUmgebungSicht : WaehleUmgebungSichtAussage := by
  intro β pc name abi row hT hL r₁ r₂ live hpc h
  subst hpc
  obtain ⟨pcEq, tempPub, lokEq⟩ := sicht_oeffentliche_teile h
  have hTe : (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₁.temp s else none) =
      (fun s => if oeffentlich (β.temp (r₁.pc + 1) s) = true then r₂.temp s else none) := by
    funext s
    by_cases hp : oeffentlich (β.temp (r₁.pc + 1) s) = true
    · simp only [hp, if_true]
      exact tempPub s (hT s hp)
    · simp only [if_neg hp]
  have hLe : maskiereLokal (β.lokal (r₁.pc + 1)) 0 r₁.lokale =
      maskiereLokal (β.lokal (r₁.pc + 1)) 0 r₂.lokale :=
    maskiereLokal_gleich_mono hL 0 _ _ lokEq
  have hEnv : ((name, abi, row) :: r₁.environment) =
      ((name, abi, row) :: r₂.environment) := by
    have e : r₁.environment = r₂.environment := by
      simpa only [Rahmen.sicht] using
        congrArg (fun r : Rahmen => (r.sicht β).environment) h
    rw [e]
  rw [sicht_waehleUmgebung, sicht_waehleUmgebung, h, pcEq, hTe, hLe, hEnv]

end Gabbro.Core.Ast.Semantik
