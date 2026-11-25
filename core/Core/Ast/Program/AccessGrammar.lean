/-
  File:      core/Core/Ast/Program/AccessGrammar.lean
  Subject:   THE PRODUCTIONS OF THE ACCESS STATEMENTS (MK-04b). An access statement is the head word `mem` and one access
             form. Surface syntax (SYNTAX.md, "Memory access statements"):

                 statement += "mem" ( load | store ) ;
                 load       = "load" ident ":" type "=" region "," index "," mode ";" ;
                 store      = "store" region "," index "," value "," mode ";" ;
                 mode       = "na" | "rlx" | "ra" | "sc" ;

             `region` is the name of an owned-region local, `index` and `value` are integer expressions. The head
             word `mem` is reserved (`directName`), so no call statement starts with it; the forms after it are
             unreserved words, so a later form (an exchange, a compare-and-swap, a fetch-and-add, the confirming
             observation, the publication) adds a production here and a constructor to `Access`, and reserves nothing
             more. The modes are the four of the memory model (`Speicher.Modus`).
-/
module

public import Core.Ast.Program.WrittenTypeGrammar
public import Core.Ast.Program.HeaderTokens

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

def printMem : PrintedToken := printProgramWord 'm' ['e', 'm'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide)
def printLoadWord : PrintedToken := printProgramWord 'l' ['o', 'a', 'd'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> decide)
def printStoreWord : PrintedToken := printProgramWord 's' ['t', 'o', 'r', 'e'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide)
def printModeNa : PrintedToken := printProgramWord 'n' ['a'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl <;> decide)
def printModeRlx : PrintedToken := printProgramWord 'r' ['l', 'x'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide)
def printModeRa : PrintedToken := printProgramWord 'r' ['a'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl <;> decide)
def printModeSc : PrintedToken := printProgramWord 's' ['c'] (by decide) (by
  intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl <;> decide)

/-- The word of a memory order. -/
def AccessMode.print : AccessMode → PrintedToken
  | .na => printModeNa
  | .rlx => printModeRlx
  | .ra => printModeRa
  | .sc => printModeSc

/-- The memory-order word of an access. -/
inductive ModeReads : List Token → AccessMode → List Token → Prop where
  | na : ModeReads (keyword "na" :: rest) .na rest
  | rlx : ModeReads (keyword "rlx" :: rest) .rlx rest
  | ra : ModeReads (keyword "ra" :: rest) .ra rest
  | sc : ModeReads (keyword "sc" :: rest) .sc rest

theorem ModeReads.deterministic (left : ModeReads input a rest) (right : ModeReads input b rest') :
    a = b ∧ rest = rest' := by
  cases left <;> cases right <;> exact ⟨rfl, rfl⟩

theorem ModeReads.consumes (read : ModeReads input mode rest) : rest <:+ input := by
  cases read <;> exact List.suffix_cons _ _

/-- The access forms with the scope they leave. -/
abbrev AccessStatement (scope : Scope) := (after : Scope) × Access scope after

/-- The productions of the access forms, after the head word `mem`. -/
inductive AccessReads (scope : Scope) : List Token → AccessStatement scope → List Token → Prop where
  | load (name : Identifier) (ordinary : name.val ≠ "mut".toList ∧ ordinaryLocal name)
      (written : WrittenType) (valid : written.valid scope)
      (region : Local scope .ownedRegion) (visible : region.nameVisible)
      (receiverOrdinary : ordinaryLocal region.binding.name) :
      TypeReads scope typeInput written (assignment :: .word region.binding.name.val :: comma :: indexInput) →
      ExprReads scope 0 indexInput (index : Expr scope (.int lo hi)) (comma :: modeInput) →
      ModeReads modeInput mode (semicolon :: rest) →
      AccessReads scope (keyword "load" :: .word name.val :: colon :: typeInput)
        ⟨_, .load name ordinary written valid region visible receiverOrdinary index mode⟩ rest
  | store (region : Local scope .ownedRegion) (visible : region.nameVisible)
      (receiverOrdinary : ordinaryLocal region.binding.name) :
      ExprReads scope 0 indexInput (index : Expr scope (.int lo hi)) (comma :: valueInput) →
      ExprReads scope 0 valueInput (value : Expr scope (.int valueLo valueHi)) (comma :: modeInput) →
      ModeReads modeInput mode (semicolon :: rest) →
      AccessReads scope (keyword "store" :: .word region.binding.name.val :: comma :: indexInput)
        ⟨_, .store region visible receiverOrdinary index value mode⟩ rest

end Gabbro.Core.Ast
