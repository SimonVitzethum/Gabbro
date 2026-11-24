module

public import Core.Ast.TextValue.Length
public import Core.Ast.Surface
public import Core.Ast.Grammar
public import Core.Ast.Semantik.Formbeweise
public import Core.Ast.Semantik.Pflichten
public import Core.Ast.Semantik.Sicherheit

/-!
# TextLength

Prove the pinned statements in this file.

- `TextLengthInversionAussage`
- `TextLengthDerivationAussage`
- `TextLengthBytesAussage`
- `TextLengthParseAussage`
- `TextLengthElaboriertAussage`
- `TextLengthRealisiertAussage`
- `TextLengthAnnahmeAussage`
- `TextLengthIdealAussage`
- `TextLengthEinheitAussage`
- `TextLengthImplAussage`
- `TextLengthErhaltungAussage`
- `TextLengthKernOrtAussage`
- `TextLengthRegelSicherAussage`
- `TextLengthRegelAntwortSicherAussage`
- `TextLengthKostenUndSpurAussage`
- `TextLengthErfuellbarAmAussage`
-/

namespace Gabbro.Core.Ast.Surface

open Gabbro.Core.Text
open Gabbro.Core.Ast

theorem textLength_print (scope : Scope) (args : TextLengthArgs scope) :
    (textLength scope).production args
      (((Category.expression scope).printPieces ((Expr.textLength args.base).typed)).map
        PrintedToken.value) := by
  refine ⟨args.base.printTokens ++ [closeParen], ?_, ?_⟩
  · rfl
  · exact Expr.printReads args.base noOperatorAtClose

end Gabbro.Core.Ast.Surface

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter
open Gabbro.Core.Text

theorem textLength_derivation : TextLengthDerivationAussage := by
  intro scope
  refine ⟨?_, Surface.textLength_print scope, ?_⟩
  · intro args tokens production
    rcases production with ⟨input, rfl, read⟩
    change ExprReads scope 0 (lenofKeyword :: openParen :: input)
      ((Surface.textLength scope).tree args).2 []
    exact .atom (AtomReads.textLength read) (.stop noOperatorAtEnd)
  · let args : Surface.TextLengthArgs [] := ⟨_, .textLiteral []⟩
    exact Rule.satisfiableOfPrint args (Surface.textLength_print [] args)

theorem textLength_inversion : TextLengthInversionAussage := by
  intro scope type input rest tree read
  cases read with
  | textLength baseRead =>
      rename_i capacity base
      exact ⟨capacity, base, baseRead, rfl⟩

theorem textLength_bytes : TextLengthBytesAussage := by
  intro capacity text frame h
  cases text with
  | mk bytes bound =>
      simp [Befehl.auswerten, Rahmen.schreibe, h, wertAls, bound]

private theorem textLength_amOrt (scope : Scope) : (textLengthForm scope).RegelAmOrt := by
  intro args
  change ((expr 0 args.base).code ++ [Befehl.textLength 0 args.capacity])[
    (expr 0 args.base).code.length]? = some (.textLength 0 args.capacity)
  simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

theorem textLength_parse : TextLengthParseAussage := by
  intro scope args text pieces lexed production
  exact (textLength_derivation scope).parse lexed production

theorem textLength_elaboriert : TextLengthElaboriertAussage := by
  intro scope platform args
  rfl

theorem textLength_realisiert : TextLengthRealisiertAussage := by
  intro scope platform args s running active live atPc
  exact (textLengthForm scope).realisiert (textLength_amOrt scope) platform args s
    running active live atPc

theorem textLength_annahme : TextLengthAnnahmeAussage := by
  intro scope
  exact Quellform.annahme (textLengthForm scope)

theorem textLength_ideal : TextLengthIdealAussage := by
  intro scope
  refine ⟨textLength_amOrt scope, ?_⟩
  intro args
  exact ⟨((textLengthForm scope).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

theorem textLength_einheit : TextLengthEinheitAussage := by
  intro scope platform args
  exact ⟨rfl, ((textLengthForm scope).befehl args).kommutation⟩

theorem textLength_impl : TextLengthImplAussage := by
  intro scope args c s w plans u
  rfl

theorem textLength_erhaltung : TextLengthErhaltungAussage := by
  intro scope
  exact Quellform.erhaltung (textLengthForm scope) (fun args =>
    expr_keine_invarianten 0 ((Surface.textLength scope).tree args).2)

theorem textLength_kernOrt : TextLengthKernOrtAussage := by
  intro scope
  exact textLength_amOrt scope

theorem textLength_regelSicher : TextLengthRegelSicherAussage := by
  intro scope platform args
  exact (Quellform.erhaltung (textLengthForm scope) (fun a =>
    expr_keine_invarianten 0 ((Surface.textLength scope).tree a).2) platform args).2.2.2

theorem textLength_regelAntwortSicher : TextLengthRegelAntwortSicherAussage := by
  intro scope platform args
  dsimp
  intro t c s choice stepPlan u spur next head impl execute
  let form := textLengthForm scope
  let b := form.befehl args
  obtain ⟨spurEq, _⟩ := Befehl.vollzug_genau b (w := choice) impl execute
  subst spur
  obtain ⟨same, _⟩ := impl
  cases (List.cons.inj same).1
  refine ⟨?_, ?_⟩
  · intro answer h
    cases h
  · intro answer
    simp

theorem textLength_kostenUndSpur : TextLengthKostenUndSpurAussage := by
  intro scope platform args
  dsimp
  intro t c s choice stepPlan u spur next head impl execute
  let form := textLengthForm scope
  let b := form.befehl args
  obtain ⟨spurEq, _⟩ := Befehl.vollzug_genau b (w := choice) impl execute
  cases spurEq
  refine ⟨rfl, rfl, ?_⟩
  have hst : (form.einheit platform args).stotterLaenge b = 0 := rfl
  simp [hst]

theorem textLength_erfuellbarAm : TextLengthErfuellbarAmAussage := by
  intro platform start
  let args : Surface.TextLengthArgs [] := ⟨_, .textLiteral []⟩
  let form := textLengthForm []
  let E := form.einheit platform args
  let b := form.befehl args
  let b0 : Befehl := .textLiteral 0 []
  let s0 := (I.start E start).2
  let s := b0.nach eintritt s0
  refine ⟨args, Ast.print (category := .expression []) (form.produktion.tree args), s,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Ast.parse_print _
  · rfl
  · apply System.IErreichbar.schritt eintritt () [plan] System.IErreichbar.start
    refine ⟨b0, ?_, rfl⟩
    simp [E, form, s0, b0, I.start, Zustand.start, startdaten, Rahmen.start, kopf,
      Quellform.einheit, Quellform.fragment, fragment, Fragment.einheit, expr,
      Fragment.anhaengen, Fragment.einzel, textLengthForm]
  · apply form.realisiert (textLength_amOrt []) platform args s
    · rfl
    · rfl
    · rfl
    · rfl
  · intro g guard
    simp [b, Befehl.guard] at guard
  · dsimp
    constructor
    · rfl
    · simp [b, s, s0, b0, Befehl.nach, Befehl.auswerten, Rahmen.schreibe,
        Rahmen.start, wertAls, TextValue.literal, I.start, Zustand.start, startdaten]

end Gabbro.Core.Ast.Semantik
