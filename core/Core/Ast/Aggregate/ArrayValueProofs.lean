module

public import Core.Ast.Aggregate.Arrays
public import Core.Ast.Semantik.Formbeweise

import Init.Omega

/-!
# ArrayValue

Prove the pinned statements in this file.

- `Surface.ArrayValueInversionAussage`
- `Surface.ArrayValueSuffixAussage`
- `Surface.ArrayValueDerivationAussage`
- `Surface.ArrayValueElementSoundAussage`
- `ArrayValueParseAussage`
- `ArrayValueElaboriertAussage`
- `ArrayValueRealisiertAussage`
- `ArrayValueAnnahmeAussage`
- `ArrayValueIdealAussage`
- `ArrayValueEinheitAussage`
- `ArrayValueImplAussage`
- `ArrayValueErhaltungAussage`
- `ArrayValueRegelSicherAussage`
- `ArrayValueErfuellbarAmAussage`
-/

@[expose] public section

open Gabbro.Core.Text
open Gabbro.Core.Ast

namespace Gabbro.Core.Ast.Surface

private theorem itemsSuffix {scope close input types} {items : ExprItems scope types} {rest}
    (read : ItemsRead scope close input items rest ∨ ItemsTail scope close input items rest) :
    rest <:+ input := by
  cases read with
  | inl read =>
      cases read with
      | close => exact List.suffix_cons _ _
      | next headRead tailRead =>
          exact (itemsSuffix (Or.inr tailRead)).trans (ExprReads.consumes headRead)
  | inr read =>
      cases read with
      | close => exact List.suffix_cons _ _
      | comma _ tailRead =>
          exact (itemsSuffix (Or.inl tailRead)).trans (List.suffix_cons _ _)

private theorem fitsSelf (type : Ty .value) : Fits type type := by
  cases type with
  | int lo hi => exact ⟨le_rfl, le_rfl⟩
  | bool => trivial
  | array element count =>
      cases count with
      | zero => simp only [Fits]
      | succ n => simp only [Fits]
  | productEnd => rfl
  | product head tail => rfl
  | record name labels layout => rfl
  | recordSchema name labels layout => rfl
  | sumEnd => rfl
  | sum head tail => rfl
  | variant name labels hasPayload layout => rfl
  | variantSchema name labels hasPayload layout => rfl
  | text capacity => exact Nat.le_refl _
  | carrierSchema _ _ _ _ => rfl
  | effectGroupSchema _ => rfl

private theorem fitsArrayJoin (head principal : Ty .value) {element : Ty .value}
    (join : arrayJoin head principal = some element) : Fits head element := by
  unfold arrayJoin at join
  split at join
  · cases join
    simp only [Fits]
    exact ⟨min_le_left _ _, le_max_left _ _⟩
  · split at join
    · rename_i same
      cases join
      subst principal
      exact fitsSelf head
    · cases join

private theorem fitsThroughJoin (head principal : Ty .value) {element target : Ty .value}
    (fit : Fits target principal) (join : arrayJoin head principal = some element) :
    Fits target element := by
  unfold arrayJoin at join
  split at join
  · cases join
    by_cases ht : ∃ l u : Int, target = .int l u
    · obtain ⟨l, u, rfl⟩ := ht
      simp only [Fits] at fit ⊢
      exact ⟨le_trans (min_le_right _ _) fit.1, le_trans fit.2 (le_max_right _ _)⟩
    · cases target with
      | int l u => exact False.elim (ht ⟨l, u, rfl⟩)
      | _ =>
          simp only [Fits] at fit
          exact False.elim (ht ⟨_, _, fit⟩)
  · split at join
    · rename_i same
      cases join
      subst principal
      exact fit
    · cases join

theorem arrayValueInversion : ArrayValueInversionAussage := by
  intro scope input type tree rest read
  cases read with
  | arrayValue principal fits itemsRead =>
      exact ⟨⟨_, _, _, principal, fits⟩, itemsRead, rfl⟩

theorem arrayValueSuffix : ArrayValueSuffixAussage := by
  intro scope input type tree rest read
  obtain ⟨args, itemsRead, _⟩ := arrayValueInversion read
  exact itemsSuffix (Or.inl itemsRead)

private theorem itemsPrintRead {scope : Scope} {types : List (Ty .value)}
    (items : ExprItems scope types) :
    ItemsRead scope closeBracket
      (items.printPieces.map PrintedToken.value ++ [closeBracket]) items [] := by
  cases items with
  | empty => exact .close
  | next head tail =>
      have headRead (more : List Token) (blocked : ¬ Continues 0 more) :
          ExprReads scope 0 (head.printTokens ++ more) head more :=
        Expr.printReads (rest := more) head blocked
      cases tail with
      | empty =>
          simpa only [ExprItems.printPieces, ExprItems.printTail, List.map_append, List.map_nil,
            List.singleton_append, List.append_nil] using
            (.next (headRead [closeBracket] noOperatorAtCloseBracket)
              (ItemsTail.close : ItemsTail scope closeBracket [closeBracket] ExprItems.empty []))
      | next second rest =>
          simp only [ExprItems.printPieces, ExprItems.printTail, Expr.printTokens,
            List.map_append, List.map_cons, List.map_nil, List.singleton_append, List.append_assoc,
            printComma, printPunctuation, PrintedToken.unquoted,
            (show (Token.punctuation ",".toList : Token) = comma by decide)]
          change ItemsRead scope closeBracket
            (head.printPieces.map PrintedToken.value ++
              (comma :: (second.printPieces.map PrintedToken.value ++
                (rest.printTail.map PrintedToken.value ++ [closeBracket]))))
            (.next head (.next second rest)) []
          exact .next
            (Expr.printReads (rest := comma ::
              (second.printPieces.map PrintedToken.value ++
                (rest.printTail.map PrintedToken.value ++ [closeBracket])))
              head noOperatorAtComma)
            (.comma (Or.inr rfl) (by
              simpa only [ExprItems.printPieces, List.map_append, List.append_assoc] using
                (itemsPrintRead (ExprItems.next second rest))))

private theorem arrayValuePrint (scope : Scope) (args : ArrayValueArgs scope) :
    (arrayValue scope).production args
      (((Category.expression scope).printPieces ((arrayValue scope).tree args)).map PrintedToken.value) := by
  change ∃ input, (Expr.arrayValue args.items args.principal args.fits).printTokens =
      openBracket :: input ∧ ItemsRead scope closeBracket input args.items []
  refine ⟨args.items.printPieces.map PrintedToken.value ++ [closeBracket], ?_, ?_⟩
  · simp only [Expr.printTokens, Expr.printPieces, List.map_append, List.map_cons,
      List.map_nil, List.singleton_append, printOpenBracket, printCloseBracket,
      printPunctuation, PrintedToken.unquoted,
      (show (Token.punctuation "[".toList : Token) = openBracket by decide),
      (show (Token.punctuation "]".toList : Token) = closeBracket by decide)]
    rfl
  exact itemsPrintRead args.items

theorem arrayValueDerivation : ArrayValueDerivationAussage := by
  intro scope
  refine ⟨?_, ?_, ?_⟩
  · intro args tokens production
    rcases production with ⟨input, rfl, itemsRead⟩
    change ExprReads scope 0 (openBracket :: input)
      (Expr.arrayValue args.items args.principal args.fits) []
    exact .atom (.arrayValue args.principal args.fits itemsRead) (.stop noOperatorAtEnd)
  · exact arrayValuePrint scope
  · let args : ArrayValueArgs scope := ⟨[], .productEnd, .empty, rfl, fun i => Fin.elim0 i⟩
    exact Rule.satisfiableOfPrint args (arrayValuePrint scope args)

theorem arrayValueElementSound : ArrayValueElementSoundAussage := by
  intro types element principal i
  induction types generalizing element with
  | nil => exact Fin.elim0 i
  | cons head tail ih =>
      cases tail with
      | nil =>
          change arrayElement [head] = some element at principal
          simp only [arrayElement] at principal
          cases principal
          have bound : i.val < 1 := by simpa using i.isLt
          have ival : i.val = 0 := by omega
          cases i with
          | mk val isLt =>
              simp only at ival
              subst val
              change Fits head head
              exact fitsSelf head
      | cons next rest =>
          change (arrayElement (next :: rest)).bind (arrayJoin head) = some element at principal
          cases hTail : arrayElement (next :: rest) with
          | none =>
              simp only [hTail] at principal
              cases principal
          | some principalElement =>
              simp only [hTail, Option.bind] at principal
              cases i using Fin.cases with
              | zero =>
                  change Fits head element
                  exact fitsArrayJoin head principalElement principal
              | succ j =>
                  change Fits ((next :: rest).get j) element
                  exact fitsThroughJoin head principalElement (ih hTail j) principal

end Gabbro.Core.Ast.Surface

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog Waechter

private theorem arrayValueRootLookup (p : Fragment) (b : Befehl) :
    (p.anhaengen (.einzel b)).code[p.code.length]? = some b := by
  simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self, List.getElem?_cons_zero]

private theorem arrayValue_am_ort (scope : Scope) : (arrayValueForm scope).RegelAmOrt := by
  intro args
  change (((itemCode 0 args.items).anhaengen
    (.einzel (.baueArray 0 args.element args.types.length))).code)[(itemCode 0 args.items).code.length]? =
      some (.baueArray 0 args.element args.types.length)
  exact arrayValueRootLookup _ _

private theorem arrayValue_keine_invarianten (scope : Scope) (args : Surface.ArrayValueArgs scope) :
    ((arrayValueForm scope).fragment args).klauseln.invariant = [] := by
  change (expr 0 (Surface.ArrayValueArgs.expression args)).klauseln.invariant = []
  exact expr_keine_invarianten 0 _

theorem arrayValueParse : ArrayValueParseAussage := by
  intro scope args text pieces lexed production
  exact (Surface.arrayValueDerivation scope).parse lexed production

theorem arrayValueElaboriert : ArrayValueElaboriertAussage := by
  intro scope platform args
  rfl

theorem arrayValueRealisiert : ArrayValueRealisiertAussage := by
  intro scope platform args s running active live atPc
  exact (arrayValueForm scope).realisiert (arrayValue_am_ort scope) platform args s running active live atPc

theorem arrayValueAnnahme : ArrayValueAnnahmeAussage := by
  intro scope
  exact Quellform.annahme (arrayValueForm scope)

theorem arrayValueIdeal : ArrayValueIdealAussage := by
  intro scope
  refine ⟨arrayValue_am_ort scope, ?_⟩
  intro args
  refine ⟨Befehl.bestimmt _, ?_⟩
  intro c s w plans u
  rfl

theorem arrayValueEinheit : ArrayValueEinheitAussage := by
  intro scope platform args
  exact ⟨rfl, ((arrayValueForm scope).befehl args).kommutation⟩

theorem arrayValueImpl : ArrayValueImplAussage := by
  intro scope args c s w plans u
  rfl

theorem arrayValueErhaltung : ArrayValueErhaltungAussage := by
  intro scope
  apply Quellform.erhaltung
  intro args
  exact arrayValue_keine_invarianten scope args

theorem arrayValueRegelSicher : ArrayValueRegelSicherAussage := by
  intro scope platform args
  exact Befehl.sicher ((arrayValueForm scope).fragment args) platform
    (arrayValue_keine_invarianten scope args) ((arrayValueForm scope).befehl args)

theorem arrayValueErfuellbarAm : ArrayValueErfuellbarAmAussage := by
  intro platform start
  let form := arrayValueForm []
  let args : Surface.ArrayValueArgs [] := ⟨[], .productEnd, .empty, rfl, fun i => Fin.elim0 i⟩
  let E := form.einheit platform args
  let s := (I.start E start).2
  refine ⟨args, form.erfuellbar_aus_erreichbar platform start args s .start
    (form.realisiert (arrayValue_am_ort []) platform args s rfl rfl rfl rfl) ?_⟩
  intro g guard
  cases guard

end Gabbro.Core.Ast.Semantik
