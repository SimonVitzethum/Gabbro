module

public import Core.Ast.Aggregate.Pattern

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

private theorem patternName_printReads (name : Option Identifier) (rest : List Token)
    (use : ∀ id, name = some id → id.val ≠ ['_']) :
    PatternNameReads ((patternNamePieces name).map PrintedToken.value ++ rest) name rest := by
  cases name with
  | none => exact .discard
  | some id => exact .name id (use id rfl)

private def patternTailTokens : List (Option Identifier) → List Token → List Token
  | [], rest => closeParen :: rest
  | name :: names, rest =>
      comma :: (commaSeparated ((name :: names).map patternNamePieces) ++ [printClose]).map PrintedToken.value ++ rest

private theorem patternTail_printReads : (names : List (Option Identifier)) → (rest : List Token) →
    (∀ nm, nm ∈ names.filterMap (fun x => x) → nm.val ≠ ['_']) →
    PatternTailReads (patternTailTokens names rest) names rest
  | [], rest, use => .close
  | name :: names, rest, use => by
      have closeTok : printClose.value = closeParen := by rfl
      have commaTok : printComma.value = comma := by rfl
      have htokens : patternTailTokens (name :: names) rest =
          comma :: (patternNamePieces name).map PrintedToken.value ++ patternTailTokens names rest := by
        cases names <;> rfl
      rw [htokens]
      apply PatternTailReads.next
      · exact patternName_printReads name (patternTailTokens names rest) (fun nm h => use nm (by simp_all [TuplePattern.names]))
      · exact patternTail_printReads names rest (fun nm h => use nm (by simp_all [TuplePattern.names]))

theorem TuplePattern.printReads (pattern : TuplePattern) (rest : List Token)
    (use : ∀ nm, nm ∈ pattern.names.filterMap (fun x => x) → nm.val ≠ ['_']) :
    TuplePatternReads (pattern.printPieces.map PrintedToken.value ++ rest) pattern rest := by
  have openTok : printOpen.value = openParen := by rfl
  have closeTok : printClose.value = closeParen := by rfl
  have commaTok : printComma.value = comma := by rfl
  unfold TuplePattern.printPieces
  cases pattern with
  | mk first second tail =>
      simp only [TuplePattern.names, List.map_cons, List.map_append, List.map_nil, openTok, closeTok]
      cases tail with
      | nil =>
          simp only [commaSeparated, List.intersperse, List.flatten, List.map_append,
            List.map_cons, List.map_nil, commaTok]
          apply TuplePatternReads.tuple
          · exact patternName_printReads first
              (comma :: (patternNamePieces second).map PrintedToken.value ++ closeParen :: rest)
              (fun nm h => use nm (by simp_all [TuplePattern.names]))
          · exact patternName_printReads second (closeParen :: rest) (fun nm h => use nm (by simp_all [TuplePattern.names]))
          · exact .close
      | cons c cs =>
          have hcs : (commaSeparated (patternNamePieces first :: patternNamePieces second :: (c :: cs).map patternNamePieces)).map PrintedToken.value =
              (patternNamePieces first).map PrintedToken.value ++ comma ::
                (patternNamePieces second).map PrintedToken.value ++ comma ::
                  (commaSeparated ((c :: cs).map patternNamePieces)).map PrintedToken.value := by
            rfl
          rw [hcs]
          apply TuplePatternReads.tuple
          · simpa only [patternTailTokens, closeTok, commaTok, List.append_assoc] using
              (patternName_printReads first
                (comma :: (patternNamePieces second).map PrintedToken.value ++ patternTailTokens (c :: cs) rest)
                (fun nm h => use nm (by simp_all [TuplePattern.names])))
          · simpa only [patternTailTokens, closeTok, commaTok, List.append_assoc] using
              (patternName_printReads second (patternTailTokens (c :: cs) rest)
                (fun nm h => use nm (by simp_all [TuplePattern.names])))
          · simpa only [patternTailTokens, closeTok, commaTok, List.append_assoc] using
              (patternTail_printReads (c :: cs) rest (fun nm h => use nm (by simp_all [TuplePattern.names])))

theorem TupleAnnotationReads.printReads (annotation : Option WrittenType) (valueRest : List Token)
    (valid : ∀ written ∈ annotation.toList, written.valid scope) :
    TupleAnnotationReads scope ((tupleAnnotationPieces annotation).map PrintedToken.value ++ assignment :: valueRest)
      annotation valueRest := by
  cases annotation with
  | none => exact .absent
  | some written =>
      have colonTok : printColon.value = colon := by rfl
      simp only [tupleAnnotationPieces, List.map_cons, colonTok]
      apply TupleAnnotationReads.written
      exact WrittenType.printReads written (valid written List.mem_cons_self) (by
        intro more h
        have eq : assignment = keyword "in" := (List.cons.inj h).1
        unfold assignment keyword at eq
        cases eq)

private end Gabbro.Core.Ast
