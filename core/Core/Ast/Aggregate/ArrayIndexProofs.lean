module

public import Core.Ast.Aggregate.Arrays
public import Core.Ast.Semantik.Formbeweise

import Init.Omega

/-!
# ArrayIndex

Prove the pinned statements in this file.

- `Surface.ArrayIndexInversionAussage`
- `Surface.ArrayIndexSuffixAussage`
- `Surface.ArrayIndexDerivationAussage`
- `ArrayIndexParseAussage`
- `ArrayIndexElaboriertAussage`
- `ArrayIndexRealisiertAussage`
- `ArrayIndexAnnahmeAussage`
- `ArrayIndexIdealAussage`
- `ArrayIndexEinheitAussage`
- `ArrayIndexImplAussage`
- `ArrayIndexErhaltungAussage`
- `ArrayIndexRegelSicherAussage`
- `ArrayIndexErfuellbarAmAussage`
- `ArrayIndexGuardAussage`
-/

@[expose] public section

open Gabbro.Core.Text
open Gabbro.Core.Ast

namespace Gabbro.Core.Ast.Surface

private theorem infixPrecLe7 (op : Infix) : op.precedence ≤ 7 := by
  cases op with
  | arith a => cases a <;> simp only [Infix.precedence, Arith.precedence] <;> omega
  | div => simp only [Infix.precedence] <;> omega
  | compare c => simp only [Infix.precedence] <;> omega
  | logic l => cases l <;> simp only [Infix.precedence] <;> omega
  | index => simp only [Infix.precedence] <;> omega
  | projection => simp only [Infix.precedence] <;> omega

theorem arrayIndexInversion : ArrayIndexInversionAussage := by
  intro scope element count minimum input type base tree rest allowed read
  cases read with
  | stop blocked =>
      exact (blocked ⟨.index, input, rfl, allowed⟩).elim
  | arrayIndex _ lower upper _ indexRead tailRead =>
      exact ⟨_, _, _, _, lower, upper, indexRead, tailRead⟩

theorem arrayIndexSuffix : ArrayIndexSuffixAussage := by
  intro scope element count minimum input type base tree rest allowed read
  obtain ⟨lo, hi, i, more, lower, upper, indexRead, tailRead⟩ :=
    arrayIndexInversion allowed read
  have closeSuffix : closeBracket :: more <:+ input := ExprReads.consumes indexRead
  have moreSuffix : more <:+ input := (List.suffix_cons closeBracket more).trans closeSuffix
  have restSuffix : rest <:+ more := ExprTail.consumes tailRead
  exact restSuffix.trans moreSuffix

private theorem arrayIndexPrint (scope : Scope) (args : ArrayIndexArgs scope) :
    (arrayIndex scope).production args
      (((Category.expression scope).printPieces ((arrayIndex scope).tree args)).map PrintedToken.value) := by
  change postfixProduction (fun input rest =>
    ∃ indexInput, ExprReads scope 8 input args.base (openBracket :: indexInput) ∧
      ExprReads scope 0 indexInput args.offset (closeBracket :: rest))
    ((Expr.arrayIndex args.base args.offset args.lower args.upper).printTokens)
  refine Or.inr ⟨args.base.printTokens ++ [openBracket] ++ args.offset.printTokens ++
    [closeBracket, closeParen], ?_, ?_⟩
  · simp only [Expr.printTokens, Expr.printPieces, List.map_append, List.map_cons,
      List.map_nil, List.singleton_append, List.append_assoc, printOpen, printClose,
      printOpenBracket, printCloseBracket, printPunctuation, PrintedToken.unquoted,
      (show (Token.punctuation "(".toList : Token) = openParen by decide),
      (show (Token.punctuation "[".toList : Token) = openBracket by decide),
      (show (Token.punctuation "]".toList : Token) = closeBracket by decide),
      (show (Token.punctuation ")".toList : Token) = closeParen by decide)]
    rfl
  refine ⟨args.offset.printTokens ++ [closeBracket, closeParen], ?_, ?_⟩
  · simpa only [List.singleton_append, List.cons_append, List.append_assoc, List.nil_append] using
      (Expr.printReads (minimum := 8)
        (rest := openBracket :: (args.offset.printTokens ++ [closeBracket, closeParen]))
        args.base (by
          intro cont
          obtain ⟨op, more, same, allowed⟩ := cont
          have prec := infixPrecLe7 op
          omega))
  · exact Expr.printReads (rest := [closeBracket, closeParen]) args.offset noOperatorAtCloseBracket

theorem arrayIndexDerivation : ArrayIndexDerivationAussage := by
  intro scope
  refine ⟨?_, ?_, ?_⟩
  · intro args tokens production
    change ExprReads scope 0 tokens
      (Expr.arrayIndex args.base args.offset args.lower args.upper) []
    rcases production with plain | grouped
    · rcases plain with ⟨indexInput, baseRead, offsetRead⟩
      cases baseRead with
      | atom atomRead highTail =>
          cases highTail with
          | stop =>
              exact .atom atomRead
                (.arrayIndex args.base args.lower args.upper (by omega) offsetRead
                  (.stop noOperatorAtEnd))
          | binary op allowed _ _ =>
              have prec : op.precedence ≤ 7 := by
                simpa [Infix.precedence] using infixPrecLe7 (.arith op)
              omega
          | div allowed _ _ _ =>
              have prec := infixPrecLe7 .div; omega
          | compare op allowed _ _ =>
              have prec := infixPrecLe7 (.compare op); omega
          | logic op allowed _ _ =>
              have prec := infixPrecLe7 (.logic op); omega
          | arrayIndex _ _ _ allowed _ _ =>
              have prec := infixPrecLe7 .index; omega
          | tupleField _ _ allowed _ =>
              have prec := infixPrecLe7 .projection; omega
          | recordField _ _ _ _ allowed _ =>
              have prec := infixPrecLe7 .projection; omega
          | textConcat _ _ allowed _ _ =>
              have prec := infixPrecLe7 (.arith .add)
              simp only [Infix.precedence] at prec
              omega
          | textIndex _ _ allowed _ _ | substring _ _ _ allowed _ _ _ =>
              have prec := infixPrecLe7 .index; omega
          | optionIsSome _ _ _ allowed _ =>
              have prec := infixPrecLe7 .projection; omega
    · rcases grouped with ⟨inside, rfl, indexInput, baseRead, offsetRead⟩
      cases baseRead with
      | atom atomRead highTail =>
          cases highTail with
          | stop =>
              have inner : ExprReads scope 0 inside
                  (Expr.arrayIndex args.base args.offset args.lower args.upper) [closeParen] :=
                .atom atomRead
                  (.arrayIndex args.base args.lower args.upper (by omega) offsetRead
                    (.stop noOperatorAtClose))
              exact .atom (.grouped inner) (.stop noOperatorAtEnd)
          | binary op allowed _ _ =>
              have prec : op.precedence ≤ 7 := by
                simpa [Infix.precedence] using infixPrecLe7 (.arith op)
              omega
          | div allowed _ _ _ =>
              have prec := infixPrecLe7 .div; omega
          | compare op allowed _ _ =>
              have prec := infixPrecLe7 (.compare op); omega
          | logic op allowed _ _ =>
              have prec := infixPrecLe7 (.logic op); omega
          | arrayIndex _ _ _ allowed _ _ =>
              have prec := infixPrecLe7 .index; omega
          | tupleField _ _ allowed _ =>
              have prec := infixPrecLe7 .projection; omega
          | recordField _ _ _ _ allowed _ =>
              have prec := infixPrecLe7 .projection; omega
          | textConcat _ _ allowed _ _ =>
              have prec := infixPrecLe7 (.arith .add)
              simp only [Infix.precedence] at prec
              omega
          | textIndex _ _ allowed _ _ | substring _ _ _ allowed _ _ _ =>
              have prec := infixPrecLe7 .index; omega
          | optionIsSome _ _ _ allowed _ =>
              have prec := infixPrecLe7 .projection; omega
  · exact arrayIndexPrint scope
  · let base : Expr scope (.array (.int 0 0) 1) :=
      .arrayValue (.next (.lit 0) .empty) rfl (fun i => by
        have bound : i.val < 1 := by simpa using i.isLt
        have ival : i.val = 0 := by omega
        cases i with
        | mk val isLt =>
            simp only at ival
            subst val
            change Fits (.int 0 0) (.int 0 0)
            exact ⟨le_rfl, le_rfl⟩)
    let args : ArrayIndexArgs scope :=
      ⟨.int 0 0, 1, 0, 0, base, .lit 0, le_rfl, by omega⟩
    exact Rule.satisfiableOfPrint args (arrayIndexPrint scope args)

end Gabbro.Core.Ast.Surface

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter

private theorem arrayIndexRootLookup (p : Fragment) (b : Befehl) :
    (p.anhaengen (.einzel b)).code[p.code.length]? = some b := by
  simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self, List.getElem?_cons_zero]

private theorem arrayIndex_am_ort (scope : Scope) : (arrayIndexForm scope).RegelAmOrt := by
  intro args
  let p := (expr 0 args.base).anhaengen (expr 1 args.offset)
  let b : Befehl := .liesArray 0 args.element args.count
  change (p.anhaengen (.einzel b)).code[p.code.length]? = some b
  exact arrayIndexRootLookup p b

private theorem arrayIndex_keine_invarianten (scope : Scope) (args : Surface.ArrayIndexArgs scope) :
    ((arrayIndexForm scope).fragment args).klauseln.invariant = [] := by
  change (expr 0 (Surface.ArrayIndexArgs.expression args)).klauseln.invariant = []
  exact expr_keine_invarianten 0 _

theorem arrayIndexParse : ArrayIndexParseAussage := by
  intro scope args text pieces lexed production
  exact (Surface.arrayIndexDerivation scope).parse lexed production

theorem arrayIndexElaboriert : ArrayIndexElaboriertAussage := by
  intro scope platform args
  rfl

theorem arrayIndexRealisiert : ArrayIndexRealisiertAussage := by
  intro scope platform args s running active live atPc
  exact (arrayIndexForm scope).realisiert (arrayIndex_am_ort scope) platform args s running active live atPc

theorem arrayIndexAnnahme : ArrayIndexAnnahmeAussage := by
  intro scope
  exact Quellform.annahme (arrayIndexForm scope)

theorem arrayIndexIdeal : ArrayIndexIdealAussage := by
  intro scope
  refine ⟨arrayIndex_am_ort scope, ?_⟩
  intro args
  refine ⟨Befehl.bestimmt _, ?_⟩
  intro c s w plans u
  rfl

theorem arrayIndexEinheit : ArrayIndexEinheitAussage := by
  intro scope platform args
  exact ⟨rfl, ((arrayIndexForm scope).befehl args).kommutation⟩

theorem arrayIndexImpl : ArrayIndexImplAussage := by
  intro scope args c s w plans u
  rfl

theorem arrayIndexErhaltung : ArrayIndexErhaltungAussage := by
  intro scope
  apply Quellform.erhaltung
  intro args
  exact arrayIndex_keine_invarianten scope args

theorem arrayIndexRegelSicher : ArrayIndexRegelSicherAussage := by
  intro scope platform args
  exact Befehl.sicher ((arrayIndexForm scope).fragment args) platform
    (arrayIndex_keine_invarianten scope args) ((arrayIndexForm scope).befehl args)

theorem arrayIndexErfuellbarAm : ArrayIndexErfuellbarAmAussage := by
  intro platform start
  let base : Expr [] (.array (.int 0 0) 1) :=
    .arrayValue (.next (.lit 0) .empty) rfl (fun i => by
      have bound : i.val < 1 := by simpa using i.isLt
      have ival : i.val = 0 := by omega
      cases i with
      | mk val isLt =>
          simp only at ival
          subst val
          change Fits (.int 0 0) (.int 0 0)
          exact ⟨le_rfl, le_rfl⟩)
  let args : Surface.ArrayIndexArgs [] :=
    ⟨.int 0 0, 1, 0, 0, base, .lit 0, le_rfl, by omega⟩
  let form := arrayIndexForm []
  let E := form.einheit platform args
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.literal 0 0).nach eintritt s₀
  let s₂ := (Befehl.baueArray 0 (.int 0 0) 1).nach eintritt s₁
  let s₃ := (Befehl.literal 1 0).nach eintritt s₂
  have first : E.system.ISchritt eintritt s₀ () [plan] s₁ :=
    ⟨.literal 0 0, rfl, rfl, rfl⟩
  have second : E.system.ISchritt eintritt s₁ () [plan] s₂ :=
    ⟨.baueArray 0 (.int 0 0) 1, rfl, rfl, rfl⟩
  have third : E.system.ISchritt eintritt s₂ () [plan] s₃ :=
    ⟨.literal 1 0, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₃ :=
    .schritt eintritt () [plan]
      (.schritt eintritt () [plan] (.schritt eintritt () [plan] .start first) second) third
  refine ⟨args, form.erfuellbar_aus_erreichbar platform start args s₃ reached
    (form.realisiert (arrayIndex_am_ort []) platform args s₃ rfl rfl rfl rfl) ?_⟩
  intro g guard
  change (Befehl.liesArray 0 (.int 0 0) 1).guard (s₃.lokal eintritt) = some g at guard
  simp only [Befehl.guard, Rahmen.zahl, alsGanzzahl, Option.bind] at guard
  cases guard
  change (0 : Nat) < 1
  omega

theorem arrayIndexGuard : ArrayIndexGuardAussage := by
  intro frame slot element count values lo hi offset lower upper harr hoff
  dsimp only
  have nonneg : 0 ≤ offset.wert := Int.le_trans lower offset.unten
  have posval : (indexPosition offset lower upper).val = offset.wert.toNat := rfl
  cases count with
  | zero =>
      have above : offset.wert < (0 : Int) := Int.lt_of_le_of_lt offset.oben upper
      omega
  | succ count =>
      have boundProof : offset.wert.toNat < Nat.succ count :=
        (indexPosition offset lower upper).isLt
      constructor
      · change (do
            let i ← frame.zahl (slot + 1)
            pure (⟨PartielleOperation.index,
              (if i.zahl.wert < 0 then count + 1 else i.zahl.wert.toNat, count + 1)⟩ : Bedarf)) =
          some (⟨PartielleOperation.index, (offset.wert.toNat, count + 1)⟩ : Bedarf)
        rw [show frame.zahl (slot + 1) = some ⟨lo, hi, offset⟩ by
          change (frame.temp (slot + 1)).bind alsGanzzahl = some ⟨lo, hi, offset⟩
          rw [hoff]
          rfl]
        change some (⟨PartielleOperation.index,
            (if offset.wert < 0 then count + 1 else offset.wert.toNat, count + 1)⟩ : Bedarf) =
          some (⟨PartielleOperation.index, (offset.wert.toNat, count + 1)⟩ : Bedarf)
        rw [if_neg (not_lt_of_ge nonneg)]
      constructor
      · change (indexPosition offset lower upper).val < Nat.succ count
        exact (indexPosition offset lower upper).isLt
      ·
        let val : Wert (.array element (count + 1)) := by
          change Vector (Wert element) (count + 1)
          exact values
        have wert : wertAls (.array element (count + 1))
            (Sigma.mk (.array element (count + 1)) val) = some val := by
          change (if same : (element.array (count + 1) : Ty .value) = element.array (count + 1) then
            some (same ▸ val) else none) = some val
          rw [dif_pos rfl]
        have harr' : frame.temp slot = some (Sigma.mk (.array element (count + 1)) val) := by
          rw [harr]
          rfl
        have leCount : offset.wert ≤ (count : Int) := by omega
        rw [Befehl.auswerten, Rahmen.schreibe]
        simp only [Function.update_self]
        rw [harr']
        rw [show frame.zahl (slot + 1) = some ⟨lo, hi, offset⟩ by
          change (frame.temp (slot + 1)).bind alsGanzzahl = some ⟨lo, hi, offset⟩
          rw [hoff]
          rfl]
        dsimp
        change ((wertAls (.array element (count + 1))
            (Sigma.mk (.array element (count + 1)) val)).bind fun values =>
          if offset.wert < 0 then none else
            if bound : offset.wert.toNat < count + 1 then
              some (⟨element,
                (show Vector (Wert element) (count + 1) from values)[offset.wert.toNat]'bound⟩ :
                Dynamisch) else none) =
          some (⟨element,
            (show Vector (Wert element) (count + 1) from values)[offset.wert.toNat]'boundProof⟩ :
            Dynamisch)
        rw [wert]
        change (if offset.wert < 0 then none else
          if bound : offset.wert.toNat < count + 1 then
            some (⟨element,
              (show Vector (Wert element) (count + 1) from val)[offset.wert.toNat]'bound⟩ :
              Dynamisch) else none) =
          some (⟨element,
            (show Vector (Wert element) (count + 1) from val)[offset.wert.toNat]'boundProof⟩ :
            Dynamisch)
        rw [if_neg (not_lt_of_ge nonneg)]
        rw [dif_pos boundProof]

end Gabbro.Core.Ast.Semantik
