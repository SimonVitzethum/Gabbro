module

public import Core.Ast.Aggregate.Runtime
public import Core.Beobachtung.Fluss.Beschriftung.Aggregat
public import Core.Beobachtung.Fluss.Beschriftung.AufgabenBeweise

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung Katalog

theorem schreibform_liesArray (basis : Nat) (element : Ty .value) (count : Nat) :
    (Befehl.liesArray basis element count).Schreibform basis
      [.temp basis, .temp (basis + 1)] :=
  ⟨fun r => do
      let values : Vector (Wert element) count ←
        (r.temp basis).bind (wertAls (.array element count))
      let index ← r.zahl (basis + 1)
      if index.zahl.wert < 0 then none else
        if bound : index.zahl.wert.toNat < count then
          some ⟨element, values[index.zahl.wert.toNat]'bound⟩
        else none,
    fun _ _ => rfl,
    fun r₁ r₂ h => by
      have h0 : r₁.temp basis = r₂.temp basis := h (.temp basis) (List.mem_cons_self _)
      have h1 : r₁.temp (basis + 1) = r₂.temp (basis + 1) :=
        h (.temp (basis + 1)) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
      simp only [Rahmen.zahl, h0, h1]⟩

theorem liesArraySicht (β : Beschriftung) (pc basis : Nat) (element : Ty .value)
    (count : Nat)
    (regel : β.SchreibRegel pc basis [.temp basis, .temp (basis + 1)]) :
    (Befehl.liesArray basis element count).SichtErhaltendBei β pc :=
  Befehl.sichtErhaltend_schreibform (schreibform_liesArray basis element count) regel

theorem schreibform_liesTupelfeld (basis : Nat) (types : List (Ty .value))
    (index : Fin types.length) :
    (Befehl.liesTupelfeld basis types index).Schreibform basis [.temp basis] :=
  ⟨fun r => do
      let values ← (r.temp basis).bind (wertAls (tupleType types))
      pure ⟨types.get index, tupleGet types index values⟩,
    fun _ _ => rfl,
    fun r₁ r₂ h => by
      have h0 : r₁.temp basis = r₂.temp basis :=
        h (.temp basis) (List.mem_singleton_self _)
      simp only [h0]⟩

theorem liesTupelfeldSicht (β : Beschriftung) (pc basis : Nat)
    (types : List (Ty .value)) (index : Fin types.length)
    (regel : β.SchreibRegel pc basis [.temp basis]) :
    (Befehl.liesTupelfeld basis types index).SichtErhaltendBei β pc :=
  Befehl.sichtErhaltend_schreibform (schreibform_liesTupelfeld basis types index) regel

theorem schreibform_liesRecordFeld (basis : Nat) (name : List Char)
    (labels : List Identifier) (types : List (Ty .value)) (index : Fin types.length) :
    (Befehl.liesRecordFeld basis name labels types index).Schreibform basis
      [.temp basis] :=
  ⟨fun r => do
      let record ← (r.temp basis).bind (wertAls (recordValueType name labels types))
      pure ⟨types.get index, tupleGet types index record⟩,
    fun _ _ => rfl,
    fun r₁ r₂ h => by
      have h0 : r₁.temp basis = r₂.temp basis :=
        h (.temp basis) (List.mem_singleton_self _)
      simp only [h0]⟩

theorem liesRecordFeldSicht (β : Beschriftung) (pc basis : Nat) (name : List Char)
    (labels : List Identifier) (types : List (Ty .value)) (index : Fin types.length)
    (regel : β.SchreibRegel pc basis [.temp basis]) :
    (Befehl.liesRecordFeld basis name labels types index).SichtErhaltendBei β pc :=
  Befehl.sichtErhaltend_schreibform
    (schreibform_liesRecordFeld basis name labels types index) regel

theorem definiereRecordSicht : DefiniereRecordSichtAussage := by
  intro β pc name labels types hT hL r₁ r₂ live hpc h
  have e₁ : (Befehl.definiereRecord name labels types).auswerten r₁ live =
      r₁.installSchema ⟨recordSchemaType name labels types, PUnit.unit⟩ := rfl
  have e₂ : (Befehl.definiereRecord name labels types).auswerten r₂ live =
      r₂.installSchema ⟨recordSchemaType name labels types, PUnit.unit⟩ := rfl
  rw [e₁, e₂]
  exact installSchemaSicht β pc _ hT hL r₁ r₂ live hpc h

end Gabbro.Core.Ast.Semantik
