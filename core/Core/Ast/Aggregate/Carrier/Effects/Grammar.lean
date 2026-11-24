module

public import Core.Ast.Aggregate.Records.RecordGrammar

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

def printEffects : PrintedToken :=
  printProgramWord 'e' ['f', 'f', 'e', 'c', 't', 's'] (by decide) (by
    intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

def printReads : PrintedToken :=
  printProgramWord 'r' ['e', 'a', 'd', 's'] (by decide) (by
    intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide)

def printWrites : PrintedToken :=
  printProgramWord 'w' ['r', 'i', 't', 'e', 's'] (by decide) (by
    intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide)

def printSlots : PrintedToken :=
  printProgramWord 's' ['l', 'o', 't', 's'] (by decide) (by
    intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide)

def printPure : PrintedToken :=
  printProgramWord 'p' ['u', 'r', 'e'] (by decide) (by
    intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide)

def CarrierAccess.print : CarrierAccess → PrintedToken
  | .read => printReads
  | .write => printWrites

def WrittenCarrierEffect.printPieces (effect : WrittenCarrierEffect) : List PrintedToken :=
  [effect.access.print, effect.carrier.print] ++ (if effect.slots then [printDot, printSlots] else [])

def EffectTerm.printPieces : EffectTerm → List PrintedToken
  | .carrier effect => effect.printPieces
  | .group name => [name.print]
  | .pure => [printPure]

def EffectGroupDeclaration.header (item : EffectGroupDeclaration before) : List PrintedToken :=
  (if item.exported then [printPub] else []) ++ [printEffects, item.name.print, printOpenBrace]

def effectClausePieces : Option (EffectClause scope ps) → List PrintedToken
  | none => []
  | some clause => [printEffects, printOpenBrace] ++
      commaSeparated (clause.written.map EffectTerm.printPieces) ++ [printCloseBrace]

inductive CarrierEffectReads : List Token → WrittenCarrierEffect → List Token → Prop where
  | bare (access : CarrierAccess) (name : Identifier) :
      CarrierEffectReads (access.print.value :: .word name.val :: rest) ⟨access, name, false⟩ rest
  | slots (access : CarrierAccess) (name : Identifier) :
      CarrierEffectReads (access.print.value :: .word name.val :: dot :: keyword "slots" :: rest)
        ⟨access, name, true⟩ rest

inductive EffectTermReads : List Token → EffectTerm → List Token → Prop where
  | carrier : CarrierEffectReads input effect rest → EffectTermReads input (.carrier effect) rest
  | group (name : Identifier) (ordinary : name.val ≠ "pure".toList) :
      EffectTermReads (.word name.val :: rest) (.group name) rest
  | pure : EffectTermReads (keyword "pure" :: rest) .pure rest

/-- Read a list without consuming the token following its closing brace. -/
inductive EffectListReads (read : List Token → α → List Token → Prop) :
    List Token → List α → List Token → Prop where
  | close : EffectListReads read (closeBrace :: rest) [] rest
  | last : read input head (closeBrace :: rest) → EffectListReads read input [head] rest
  | next : read input head (comma :: more) → EffectListReads read more (next :: tail) rest →
      EffectListReads read input (head :: next :: tail) rest

inductive EffectClauseReads (scope : Scope) (ps : List (Parameter scope)) :
    List Token → Option (EffectClause scope ps) → List Token → Prop where
  | absent (closed : ∀ tail, rest ≠ keyword "effects" :: tail) :
      EffectClauseReads scope ps rest none rest
  | present (clause : EffectClause scope ps) : EffectListReads EffectTermReads input clause.written rest →
      EffectClauseReads scope ps (keyword "effects" :: openBrace :: input) (some clause) rest

end Gabbro.Core.Ast
