module

public import Core.Ast.Aggregate.Runtime
public import Core.Ast.TextValue.Bytes
public import Core.Beobachtung.Fluss.Beschriftung.Text
public import Core.Beobachtung.Fluss.Beschriftung.AufgabenBeweise

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung Katalog

theorem schreibform_textLiteral (ziel : Nat) (decoded : List Char) :
    (Befehl.textLiteral ziel decoded).Schreibform ziel [] :=
  ⟨fun _ => some ⟨.text (sourceUtf8 decoded).size, TextValue.literal decoded⟩,
    fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem textLiteralSicht (β : Beschriftung) (pc ziel : Nat) (decoded : List Char)
    (regel : β.SchreibRegel pc ziel []) :
    (Befehl.textLiteral ziel decoded).SichtErhaltendBei β pc :=
  Befehl.sichtErhaltend_schreibform (schreibform_textLiteral ziel decoded) regel

theorem schreibform_textConcat (basis a b : Nat) :
    (Befehl.textConcat basis a b).Schreibform basis [.temp basis, .temp (basis + 1)] :=
  ⟨fun r => do
      let left ← (r.temp basis).bind (wertAls (.text a))
      let right ← (r.temp (basis + 1)).bind (wertAls (.text b))
      pure ⟨.text (a + b), left.concat right⟩,
    fun _ _ => rfl,
    fun r₁ r₂ h => by
      have h0 : r₁.temp basis = r₂.temp basis :=
        h (.temp basis) (List.mem_cons_self ..)
      have h1 : r₁.temp (basis + 1) = r₂.temp (basis + 1) :=
        h (.temp (basis + 1)) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
      simp only [h0, h1]⟩

theorem textConcatSicht (β : Beschriftung) (pc basis a b : Nat)
    (regel : β.SchreibRegel pc basis [.temp basis, .temp (basis + 1)]) :
    (Befehl.textConcat basis a b).SichtErhaltendBei β pc :=
  Befehl.sichtErhaltend_schreibform (schreibform_textConcat basis a b) regel

theorem schreibform_textLength (basis capacity : Nat) :
    (Befehl.textLength basis capacity).Schreibform basis [.temp basis] :=
  ⟨fun r => (r.temp basis).bind (wertAls (.text capacity)) |>.map
      fun text => ⟨.text capacity, text.lengthValue⟩,
    fun _ _ => rfl,
    fun r₁ r₂ h => by
      have h0 : r₁.temp basis = r₂.temp basis :=
        h (.temp basis) (List.mem_singleton_self _)
      simp only [h0]⟩

theorem textLengthSicht (β : Beschriftung) (pc basis capacity : Nat)
    (regel : β.SchreibRegel pc basis [.temp basis]) :
    (Befehl.textLength basis capacity).SichtErhaltendBei β pc :=
  Befehl.sichtErhaltend_schreibform (schreibform_textLength basis capacity) regel

end Gabbro.Core.Ast.Semantik
