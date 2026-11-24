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
  | arith a => cases a <;> simp [Infix.precedence, Arith.precedence]
  | div => simp [Infix.precedence]
  | compare c => simp [Infix.precedence]
  | logic l => cases l <;> simp [Infix.precedence]
  | index => simp [Infix.precedence]
  | projection => simp [Infix.precedence]

theorem arrayIndexInversion : ArrayIndexInversionAussage := by
  intro scope element count minimum input type base tree rest allowed read
  cases read with
  | stop blocked =>
      exact (blocked ⟨.index, input, rfl, allowed⟩).elim
  | arrayIndex baseArg lower upper _ indexRead tailRead =>
      exact ⟨_, _, baseArg, _, lower, upper, indexRead, tailRead⟩

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
  refine Or.inr ⟨args.base.printTokens ++ [openBracket] ++ args.offset.printTokens ++ [closeBracket],
    rfl, ?_⟩
  refine ⟨args.offset.printTokens ++ [closeBracket], ?_, ?_⟩
  · simpa only [List.append_assoc] using
      (Expr.printReads (minimum := 8) args.base (by
        intro cont
        obtain ⟨op, more, same, allowed⟩ := cont
        have prec := infixPrecLe7 op
        omega))
  · exact Expr.printReads args.offset noOperatorAtCloseBracket

private theorem oneBoolArrayFits {scope : Scope} (i : Fin 1) : Fits (.int 0 0) (.int 0 0) := by
  have bound : i.val < 1 := by simpa using i.isLt
  have ival : i.val = 0 := by omega
  cases i with
  | mk val isLt =>
      simp only at ival
      subst val
      exact ⟨le_rfl, le_rfl⟩

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
              have prec := infixPrecLe7 (.arith op); omega
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
              have prec := infixPrecLe7 (.arith op); omega
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
  · exact arrayIndexPrint scope
  · let base : Expr scope (.array (.int 0 0) 1) :=
      .arrayValue (.next (.lit 0) .empty) rfl oneBoolArrayFits
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
    .arrayValue (.next (.lit 0) .empty) rfl Surface.oneBoolArrayFits
  let args : Surface.ArrayIndexArgs [] :=
    ⟨.int 0 0, 1, 0, 0, base, .lit 0, le_rfl, by omega⟩
  let form := arrayIndexForm []
  let E := form.einheit platform args
  let s₀ := (I.start E start).2
  let s₁ := (Befehl.baueArray 0 (.int 0 0) 1).nach eintritt s₀
  let s₂ := (Befehl.literal 1 0).nach eintritt s₁
  have first : E.system.ISchritt eintritt s₀ () [plan] s₁ :=
    ⟨.baueArray 0 (.int 0 0) 1, rfl, rfl, rfl⟩
  have second : E.system.ISchritt eintritt s₁ () [plan] s₂ :=
    ⟨.literal 1 0, rfl, rfl, rfl⟩
  have reached : E.system.IErreichbar s₀ s₂ :=
    .schritt eintritt () [plan] (.schritt eintritt () [plan] .start first) second
  refine ⟨args, form.erfuellbar_aus_erreichbar platform start args s₂ reached
    (form.realisiert (arrayIndex_am_ort []) platform args s₂ rfl rfl rfl rfl) ?_⟩
  intro g guard
  change (Befehl.liesArray 0 (.int 0 0) 1).guard (s₂.lokal eintritt) = some g at guard
  simp [Befehl.guard, Rahmen.zahl, alsGanzzahl] at guard
  cases guard
  decide

theorem arrayIndexGuard : ArrayIndexGuardAussage := by
  intro frame slot element count values lo hi offset lower upper harr hoff
  dsimp only
  have nonneg : 0 ≤ offset.wert := Int.le_trans lower offset.unten
  have posval : (indexPosition offset lower upper).val = offset.wert.toNat := rfl
  constructor
  · simp [Befehl.guard, Rahmen.zahl, hoff, alsGanzzahl,
      if_neg (not_lt_of_ge nonneg), posval]
  constructor
  · change (indexPosition offset lower upper).val < count
    exact (indexPosition offset lower upper).isLt
  · have arr : wertAls (.array element count) ⟨.array element count, values⟩ = some values := by
      cases count with
      | zero =>
          cases values
          simp_all [wertAls]
      | succ n =>
          rfl
    simp only [Befehl.auswerten, Rahmen.schreibe, Function.update_self]
    rw [harr]
    simp only [Option.bind]
    rw [arr]
    simp only [Option.bind]
    simp only [Rahmen.zahl]
    rw [hoff]
    simp only [Option.bind, alsGanzzahl]
    rw [if_neg (not_lt_of_ge nonneg)]
    have boundProof : offset.wert.toNat < count := (indexPosition offset lower upper).isLt
    rw [dif_pos boundProof]
    rfl

end Gabbro.Core.Ast.Semantik
