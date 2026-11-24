module

public import Core.Ast.TextValue.Index
public import Core.Ast.Semantik.Formbeweise

import Init.Omega

/-!
# TextIndex

Prove the pinned statements in this file.

- `TextIndexDerivationAussage`
- `TextIndexSuffixAussage`
- `TextIndexBytesAussage`
- `TextIndexParseAussage`
- `TextIndexElaboriertAussage`
- `TextIndexRealisiertAussage`
- `TextIndexAnnahmeAussage`
- `TextIndexIdealAussage`
- `TextIndexEinheitAussage`
- `TextIndexImplAussage`
- `TextIndexErhaltungAussage`
- `TextIndexKernOrtAussage`
- `TextIndexRegelSicherAussage`
- `TextIndexRegelAntwortSicherAussage`
- `TextIndexKostenUndSpurAussage`
- `TextIndexErfuellbarAmAussage`
-/

@[expose] public section

open Gabbro.Core.Text
open Gabbro.Core.Ast

namespace Gabbro.Core.Ast.Surface

private theorem textIndexInfixPrecLe7 (op : Infix) : op.precedence ≤ 7 := by
  cases op with
  | arith a => cases a <;> simp only [Infix.precedence, Arith.precedence] <;> omega
  | div => simp only [Infix.precedence] <;> omega
  | compare c => simp only [Infix.precedence] <;> omega
  | logic l => cases l <;> simp only [Infix.precedence] <;> omega
  | index => simp only [Infix.precedence] <;> omega
  | projection => simp only [Infix.precedence] <;> omega

private theorem textIndexPrint (scope : Scope) (args : TextIndexArgs scope) :
    (textIndex scope).production args
      (((Category.expression scope).printPieces ((textIndex scope).tree args)).map PrintedToken.value) := by
  change postfixProduction (fun input rest =>
    ∃ offsetInput, ExprReads scope 8 input args.base (openBracket :: offsetInput) ∧
      ExprReads scope 0 offsetInput args.offset (closeBracket :: rest))
    ((Expr.textIndex args.base args.offset).printTokens)
  refine Or.inr ⟨args.base.printTokens ++ [openBracket] ++ args.offset.printTokens ++
    [closeBracket, closeParen], ?_, ?_⟩
  · simp only [Expr.printTokens, Expr.printPieces, List.map_append, List.map_cons,
      List.map_nil, List.singleton_append, List.append_assoc, printOpen, printClose,
      printOpenBracket, printCloseBracket, printPunctuation, PrintedToken.unquoted,
      (show (Token.punctuation "(".toList : Token) = openParen by rfl),
      (show (Token.punctuation "[".toList : Token) = openBracket by rfl),
      (show (Token.punctuation "]".toList : Token) = closeBracket by rfl),
      (show (Token.punctuation ")".toList : Token) = closeParen by rfl)]
    rfl
  refine ⟨args.offset.printTokens ++ [closeBracket, closeParen], ?_, ?_⟩
  · simpa only [List.singleton_append, List.cons_append, List.append_assoc, List.nil_append] using
      (Expr.printReads (minimum := 8)
        (rest := openBracket :: (args.offset.printTokens ++ [closeBracket, closeParen]))
        args.base (by
          intro cont
          obtain ⟨op, more, same, allowed⟩ := cont
          have prec := textIndexInfixPrecLe7 op
          omega))
  · exact Expr.printReads (rest := [closeBracket, closeParen]) args.offset noOperatorAtCloseBracket

theorem textIndexDerivation : Gabbro.Core.Ast.Semantik.TextIndexDerivationAussage := by
  intro scope
  refine ⟨?_, ?_, ?_⟩
  · intro args tokens production
    change ExprReads scope 0 tokens
      (Expr.textIndex args.base args.offset) []
    rcases production with plain | grouped
    · rcases plain with ⟨offsetInput, baseRead, offsetRead⟩
      cases baseRead with
      | atom atomRead highTail =>
          cases highTail with
          | stop =>
              exact .atom atomRead
                (.textIndex args.base args.offset (by omega) offsetRead
                  (.stop noOperatorAtEnd))
          | binary op allowed _ _ =>
              have prec : op.precedence ≤ 7 := by
                simpa [Infix.precedence] using textIndexInfixPrecLe7 (.arith op)
              omega
          | div allowed _ _ _ =>
              have prec := textIndexInfixPrecLe7 .div; omega
          | compare op allowed _ _ =>
              have prec := textIndexInfixPrecLe7 (.compare op); omega
          | logic op allowed _ _ =>
              have prec := textIndexInfixPrecLe7 (.logic op); omega
          | arrayIndex _ _ _ allowed _ _ =>
              have prec := textIndexInfixPrecLe7 .index; omega
          | tupleField _ _ allowed _ =>
              have prec := textIndexInfixPrecLe7 .projection; omega
          | recordField _ _ _ _ allowed _ =>
              have prec := textIndexInfixPrecLe7 .projection; omega
          | textConcat _ _ allowed _ _ =>
              have prec : Arith.add.precedence ≤ 7 := by
                simpa [Infix.precedence] using textIndexInfixPrecLe7 (.arith Arith.add)
              omega
          | textIndex _ _ allowed _ _ =>
              have prec := textIndexInfixPrecLe7 .index; omega
          | substring _ _ _ allowed _ _ _ =>
              have prec := textIndexInfixPrecLe7 .index; omega
          | optionIsSome _ _ _ allowed _ =>
              have prec := textIndexInfixPrecLe7 .projection; omega
    · rcases grouped with ⟨inside, rfl, offsetInput, baseRead, offsetRead⟩
      cases baseRead with
      | atom atomRead highTail =>
          cases highTail with
          | stop =>
              have inner : ExprReads scope 0 inside
                  (Expr.textIndex args.base args.offset) [closeParen] :=
                .atom atomRead
                  (.textIndex args.base args.offset (by omega) offsetRead
                    (.stop noOperatorAtClose))
              exact .atom (.grouped inner) (.stop noOperatorAtEnd)
          | binary op allowed _ _ =>
              have prec : op.precedence ≤ 7 := by
                simpa [Infix.precedence] using textIndexInfixPrecLe7 (.arith op)
              omega
          | div allowed _ _ _ =>
              have prec := textIndexInfixPrecLe7 .div; omega
          | compare op allowed _ _ =>
              have prec := textIndexInfixPrecLe7 (.compare op); omega
          | logic op allowed _ _ =>
              have prec := textIndexInfixPrecLe7 (.logic op); omega
          | arrayIndex _ _ _ allowed _ _ =>
              have prec := textIndexInfixPrecLe7 .index; omega
          | tupleField _ _ allowed _ =>
              have prec := textIndexInfixPrecLe7 .projection; omega
          | recordField _ _ _ _ allowed _ =>
              have prec := textIndexInfixPrecLe7 .projection; omega
          | textConcat _ _ allowed _ _ =>
              have prec : Arith.add.precedence ≤ 7 := by
                simpa [Infix.precedence] using textIndexInfixPrecLe7 (.arith Arith.add)
              omega
          | textIndex _ _ allowed _ _ =>
              have prec := textIndexInfixPrecLe7 .index; omega
          | substring _ _ _ allowed _ _ _ =>
              have prec := textIndexInfixPrecLe7 .index; omega
          | optionIsSome _ _ _ allowed _ =>
              have prec := textIndexInfixPrecLe7 .projection; omega
  · exact textIndexPrint scope
  · let base : Expr scope (.text (sourceUtf8 ['x']).size) := .textLiteral ['x']
    let args : TextIndexArgs scope := ⟨(sourceUtf8 ['x']).size, 0, 0, base, .lit 0⟩
    exact Rule.satisfiableOfPrint args (textIndexPrint scope args)

end Gabbro.Core.Ast.Surface

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter

private theorem textIndexRootLookup (p : Fragment) (b : Befehl) :
    (p.anhaengen (.einzel b)).code[p.code.length]? = some b := by
  simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self, List.getElem?_cons_zero]

private theorem textIndex_am_ort (scope : Scope) : (textIndexForm scope).RegelAmOrt := by
  intro args
  let p := (expr 0 args.base).anhaengen (expr 1 args.offset)
  let b : Befehl := .textIndex 0 args.capacity
  change (p.anhaengen (.einzel b)).code[(expr 0 args.base).code.length + (expr 1 args.offset).code.length]? = some b
  have hpos : (expr 0 args.base).code.length + (expr 1 args.offset).code.length = p.code.length := by
    simp only [p, Fragment.anhaengen, List.length_append]
  rw [hpos]
  exact textIndexRootLookup p b

private theorem textIndex_keine_invarianten (scope : Scope) (args : Surface.TextIndexArgs scope) :
    ((textIndexForm scope).fragment args).klauseln.invariant = [] := by
  change (expr 0 (Surface.TextIndexArgs.expression args)).klauseln.invariant = []
  exact expr_keine_invarianten 0 _

theorem textIndexSuffix : TextIndexSuffixAussage := by
  intro scope capacity type minimum first rest base tree allowed read
  cases read with
  | stop blocked =>
      exact (blocked ⟨.index, first, rfl, allowed⟩).elim
  | textIndex _ _ _ offsetRead tailRead =>
      have closeSuffix := ExprReads.consumes offsetRead
      have moreSuffix := (List.suffix_cons closeBracket _).trans closeSuffix
      exact (ExprTail.consumes tailRead).trans moreSuffix
  | substring _ _ _ _ firstRead lastRead tailRead =>
      have lastCloseSuffix := ExprReads.consumes lastRead
      have lastMoreSuffix := (List.suffix_cons closeBracket _).trans lastCloseSuffix
      have firstCloseSuffix := ExprReads.consumes firstRead
      have firstMoreSuffix := (List.suffix_cons sliceRange _).trans firstCloseSuffix
      exact (ExprTail.consumes tailRead).trans (lastMoreSuffix.trans firstMoreSuffix)

private theorem textWertAls (capacity : Nat) (text : TextValue capacity) :
    wertAls (.text capacity) (Sigma.mk (.text capacity) text) = some text := by
  change (if fits : text.bytes.size ≤ capacity then some (⟨text.bytes, fits⟩ : TextValue capacity) else none) = some text
  rw [dif_pos text.bound]

theorem textIndexBytes : TextIndexBytesAussage := by
  intro capacity text index frame htemp hzahl
  dsimp only
  have htext : (frame.temp 0).bind (wertAls (.text capacity)) = some text := by
    rw [htemp]
    exact textWertAls capacity text
  refine ⟨?_, ?_, ?_⟩
  · rw [Befehl.guard]
    rw [htext, hzahl]
    rfl
  · intro byte nonneg hbyte
    have hnonneg' : ¬ index.zahl.wert < 0 := not_lt_of_ge nonneg
    simp only [Befehl.auswerten, htext, hzahl, hnonneg', hbyte, Rahmen.schreibe,
      Function.update_self, if_false, Id.run]
    constructor <;> rfl
  · intro hfail
    rcases hfail with hneg | hge
    · simp only [Befehl.auswerten, htext, hzahl, hneg, Rahmen.halt, if_true, Id.run]
      rfl
    · have hnonneg : 0 ≤ index.zahl.wert := by omega
      have hge' : (text.bytes.size : Int) ≤ (index.zahl.wert.toNat : Int) := by
        rw [Int.toNat_of_nonneg hnonneg]
        exact hge
      have hnat : text.bytes.size ≤ index.zahl.wert.toNat := Int.ofNat_le.mp hge'
      have hout : text.bytes[index.zahl.wert.toNat]? = none := by
        simp only [getElem?_eq_none_iff]
        exact not_lt_of_ge hnat
      have hnonneg' : ¬ index.zahl.wert < 0 := not_lt_of_ge hnonneg
      simp only [Befehl.auswerten, htext, hzahl, hnonneg', hout, Rahmen.halt, if_false, Id.run]
      rfl

theorem textIndexParse : TextIndexParseAussage := by
  intro scope args text pieces lexed production
  exact (Surface.textIndexDerivation scope).parse lexed production

theorem textIndexElaboriert : TextIndexElaboriertAussage := by
  intro scope platform args
  rfl

theorem textIndexRealisiert : TextIndexRealisiertAussage := by
  intro scope platform args s running active live atPc
  exact (textIndexForm scope).realisiert (textIndex_am_ort scope) platform args s running active live atPc

theorem textIndexAnnahme : TextIndexAnnahmeAussage := by
  intro scope
  exact Quellform.annahme (textIndexForm scope)

theorem textIndexIdeal : TextIndexIdealAussage := by
  intro scope
  refine ⟨textIndex_am_ort scope, ?_⟩
  intro args
  refine ⟨Befehl.bestimmt _, ?_⟩
  intro c s w plans u
  rfl

theorem textIndexEinheit : TextIndexEinheitAussage := by
  intro scope platform args
  exact ⟨rfl, ((textIndexForm scope).befehl args).kommutation⟩

theorem textIndexImpl : TextIndexImplAussage := by
  intro scope args c s w plans u
  rfl

theorem textIndexErhaltung : TextIndexErhaltungAussage := by
  intro scope
  apply Quellform.erhaltung
  intro args
  exact textIndex_keine_invarianten scope args

theorem textIndexKernOrt : TextIndexKernOrtAussage := by
  intro scope
  exact textIndex_am_ort scope

theorem textIndexRegelSicher : TextIndexRegelSicherAussage := by
  intro scope platform args
  exact Befehl.sicher ((textIndexForm scope).fragment args) platform
    (textIndex_keine_invarianten scope args) ((textIndexForm scope).befehl args)

theorem textIndexRegelAntwortSicher : TextIndexRegelAntwortSicherAussage := by
  intro scope platform args form t c s choice stepPlan u spur next head impl execute
  obtain ⟨rfl, rfl⟩ := ((textIndexForm scope).befehl args).vollzug_genau (w := choice) impl execute
  have same : [stepPlan] = [plan] := impl.1
  have eqPlan : stepPlan = plan := (List.cons.inj same).1
  subst stepPlan
  constructor
  · intro answer
    intro equal
    cases equal
  · intro answer
    change Ereignis.antwort answer ∉ ([] : List Ereignis)
    intro mem
    cases mem

theorem textIndexKostenUndSpur : TextIndexKostenUndSpurAussage := by
  intro scope platform args form t c s choice stepPlan u spur next head impl execute
  obtain ⟨rfl, rfl⟩ := ((textIndexForm scope).befehl args).vollzug_genau (w := choice) impl execute
  have same : [stepPlan] = [plan] := impl.1
  have eqPlan : stepPlan = plan := (List.cons.inj same).1
  subst stepPlan
  refine ⟨rfl, rfl, ?_⟩
  simp only [Fragment.einheit, List.length_cons, List.length_nil, Nat.zero_add]

theorem textIndexErfuellbarAm : TextIndexErfuellbarAmAussage := by
  intro platform start
  let decoded : List Char := ['x']
  let capacity : Nat := (sourceUtf8 decoded).size
  let text : TextValue capacity := TextValue.literal decoded
  let args : Surface.TextIndexArgs [] := ⟨capacity, 0, 0, .textLiteral decoded, .lit 0⟩
  let form := textIndexForm []
  let E := form.einheit platform args
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.textLiteral 0 decoded).nach eintritt s₀
  let s₂ := (Befehl.literal 1 0).nach eintritt s₁
  let frame₂ := s₂.lokal eintritt
  have first : E.system.ISchritt eintritt s₀ () [plan] s₁ := ⟨.textLiteral 0 decoded, rfl, rfl, rfl⟩
  have second : E.system.ISchritt eintritt s₁ () [plan] s₂ := ⟨.literal 1 0, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₂ :=
    .schritt eintritt () [plan] (.schritt eintritt () [plan] .start first) second
  have htemp : frame₂.temp 0 = some ⟨.text capacity, text⟩ := by rfl
  have hzahl : frame₂.zahl 1 = some (⟨0, 0, Zahl.literal 0⟩ : Ganzzahl) := by rfl
  have htext : (frame₂.temp 0).bind (wertAls (.text capacity)) = some text := by
    rw [htemp]
    exact textWertAls capacity text
  have hcapPos : 0 < capacity := Nat.zero_lt_succ _
  have hlt : (0 : Int).toNat < text.bytes.size := by
    dsimp [text, TextValue.literal, capacity]
    exact hcapPos
  let byte : UInt8 := text.bytes[0]'(by simpa using hlt)
  have hbyte : text.bytes[(0 : Int).toNat]? = some byte := by
    rw [getElem?_eq_some_iff]
    have heq : text.bytes[(0 : Int).toNat] = text.bytes[0] := by rfl
    exact ⟨by simpa using hlt, by simpa only [byte] using heq⟩
  have hbyte0 : text.bytes[0]? = some byte := by simpa using hbyte
  have heval : (Befehl.textIndex 0 capacity).auswerten frame₂ =
      frame₂.schreibe 0 (some ⟨.int 0 255, byteValue byte⟩) := by
    have hnonneg' : ¬ (0 : Int) < 0 := by omega
    simp only [Befehl.auswerten, htext, hzahl, hnonneg', hbyte, Zahl.literal, if_false, Id.run]
    rfl
  have hstop₂ : (s₂.lokal eintritt).stopp = none := by
    simp only [s₂, s₁, s₀, E, form, I.start, Zustand.start, Quellform.einheit, Fragment.einheit,
      startdaten, Rahmen.start, Befehl.nach, Rahmen.schreibe, Befehl.auswerten,
      Function.update_self, Nat.zero_add]
  refine ⟨args, ?_⟩
  refine ⟨Ast.print (category := .expression []) (form.produktion.tree args), s₂, ?_, ?_, reached, ?_, ?_, ?_, ?_⟩
  · exact Ast.parse_print _
  · rfl
  · exact form.realisiert (textIndex_am_ort []) platform args s₂ rfl rfl rfl rfl
  · intro g hg
    have hguard : (form.befehl args).guard (s₂.lokal eintritt) = some (⟨.index, (0, capacity)⟩ : Bedarf) := by
      dsimp [form, textIndexForm, frame₂]
      simp only [Befehl.guard, htext, hzahl, lt_irrefl]
      rfl
    rw [hguard] at hg
    simp at hg
    subst g
    exact hcapPos
  · simp only [form, textIndexForm, args, Befehl.nach, Function.update_self]
    change (((Befehl.textIndex 0 capacity).auswerten frame₂).temp 0).isSome = true
    rw [heval]
    simp only [Rahmen.schreibe, Function.update_self, Option.isSome_some]
  · simp only [form, textIndexForm, args, Befehl.nach, Function.update_self]
    change ((Befehl.textIndex 0 capacity).auswerten frame₂).stopp = none
    rw [heval]
    exact hstop₂

end Gabbro.Core.Ast.Semantik
