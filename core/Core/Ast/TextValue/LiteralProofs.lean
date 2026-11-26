module

public import Core.Ast.TextValue.Literal
public import Core.Ast.Semantik.Formbeweise

/-!
# TextLiteral

Prove the pinned statements in this file.

- `TextLiteralInversionAussage`
- `TextLiteralDerivationAussage`
- `TextLiteralBytesAussage`
- `TextLiteralParseAussage`
- `TextLiteralElaboriertAussage`
- `TextLiteralRealisiertAussage`
- `TextLiteralAnnahmeAussage`
- `TextLiteralIdealAussage`
- `TextLiteralEinheitAussage`
- `TextLiteralImplAussage`
- `TextLiteralErhaltungAussage`
- `TextLiteralKernOrtAussage`
- `TextLiteralRegelSicherAussage`
- `TextLiteralRegelAntwortSicherAussage`
- `TextLiteralKostenUndSpurAussage`
- `TextLiteralErfuellbarAmAussage`
-/

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter
open Gabbro.Core.Text

private theorem textLiteral_am_ort (scope : Scope) : (textLiteralForm scope).RegelAmOrt :=
  fun _ => rfl

private theorem textLiteral_keine_invarianten (scope : Scope) (args : List Char) :
    ((textLiteralForm scope).fragment args).klauseln.invariant = [] := by
  rfl

theorem textLiteralInversion : TextLiteralInversionAussage := by
  intro scope decoded input type tree rest read
  cases read
  exact ⟨rfl, rfl⟩

theorem textLiteralDerivation : TextLiteralDerivationAussage := by
  intro scope
  refine ⟨?_, ?_, ?_⟩
  · intro decoded tokens production
    change tokens = [.string decoded] at production
    subst tokens
    exact .atom .textLiteral (.stop noOperatorAtEnd)
  · intro decoded
    rfl
  · exact Surface.Rule.satisfiableOfPrint (rule := Surface.textLiteral scope) [] (by rfl)

theorem textLiteralBytes : TextLiteralBytesAussage := by
  intro decoded frame
  dsimp only
  constructor
  · simp only [Befehl.auswerten, Rahmen.schreibe, Function.update_self]
  constructor
  · change (String.ofList decoded).toByteArray = decoded.utf8Encode
    rw [← String.utf8Encode_toList, String.toList_ofList]
  · rfl

theorem textLiteralParse : TextLiteralParseAussage := by
  intro scope args text pieces lexed production
  exact (textLiteralDerivation scope).parse lexed production

theorem textLiteralElaboriert : TextLiteralElaboriertAussage := by
  intro scope platform args
  rfl

theorem textLiteralRealisiert : TextLiteralRealisiertAussage := by
  intro scope platform args s running active live atPc
  exact (textLiteralForm scope).realisiert (textLiteral_am_ort scope) platform args s running active live atPc

theorem textLiteralAnnahme : TextLiteralAnnahmeAussage := by
  intro scope
  exact Quellform.annahme (textLiteralForm scope)

theorem textLiteralIdeal : TextLiteralIdealAussage := by
  intro scope
  refine ⟨textLiteral_am_ort scope, ?_⟩
  intro args
  refine ⟨Befehl.bestimmt _, ?_⟩
  intro c s w plans u
  rfl

theorem textLiteralEinheit : TextLiteralEinheitAussage := by
  intro scope platform args
  exact ⟨rfl, ((textLiteralForm scope).befehl args).kommutation⟩

theorem textLiteralImpl : TextLiteralImplAussage := by
  intro scope args c s w plans u
  rfl

theorem textLiteralErhaltung : TextLiteralErhaltungAussage := by
  intro scope
  apply Quellform.erhaltung
  intro args
  exact textLiteral_keine_invarianten scope args

theorem textLiteralRegelSicher : TextLiteralRegelSicherAussage := by
  intro scope platform args
  exact Befehl.sicher ((textLiteralForm scope).fragment args) platform [] (tabLeer _ (textLiteral_keine_invarianten scope args)) (fun b _ => rfl) ((textLiteralForm scope).befehl args)

theorem textLiteralKernOrt : TextLiteralKernOrtAussage := by
  intro scope
  exact textLiteral_am_ort scope

theorem textLiteralRegelAntwortSicher : TextLiteralRegelAntwortSicherAussage := by
  intro scope platform args
  dsimp only
  let form := textLiteralForm scope
  let b := form.befehl args
  intro t c s choice stepPlan u spur next head impl execute
  have hspur := b.vollzug_genau (h := Or.inl rfl) (w := choice) impl execute
  have hplan : stepPlan = plan := (List.cons.inj impl.1).1
  constructor
  · intro answer eq
    rw [hplan] at eq
    simp only [plan] at eq
    cases eq
  · intro answer
    rw [hspur.1]
    intro mem
    cases mem

theorem textLiteralKostenUndSpur : TextLiteralKostenUndSpurAussage := by
  intro scope platform args
  dsimp only
  let form := textLiteralForm scope
  let b := form.befehl args
  intro t c s choice stepPlan u spur next head impl execute
  have hspur := b.vollzug_genau (h := Or.inl rfl) (w := choice) impl execute
  rw [hspur.1]
  constructor
  · rfl
  constructor
  · rfl
  · change 0 + [stepPlan].length = 1
    rfl

theorem textLiteralErfuellbarAm : TextLiteralErfuellbarAmAussage := by
  intro platform start
  let decoded : List Char := []
  refine ⟨decoded, ?_⟩
  let form := textLiteralForm []
  let E := form.einheit platform decoded
  let s := (I.start E start).2
  refine ⟨Ast.print (category := .expression []) (form.produktion.tree decoded), s, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Ast.parse_print _
  · rfl
  · exact .start
  · exact form.realisiert (textLiteral_am_ort []) platform decoded s rfl rfl rfl rfl
  · intro g guard
    change (Befehl.textLiteral 0 decoded).guard (s.lokal eintritt) = some g at guard
    simp only [Befehl.guard] at guard
    cases guard
  · dsimp only
    constructor
    · change (s.lokal eintritt).stopp = none
      rfl
    · simp only [textLiteralForm, Befehl.nach, Befehl.auswerten, Rahmen.schreibe, Function.update_self]
      rfl

end Gabbro.Core.Ast.Semantik
