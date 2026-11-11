/-
  The `touches` header of an ordinary traversal, bound to the enclosing function's effects.

  `Stmt.traverse` has no component for the header, so the elaborator drops it. The gate may
  admit it only when the claim follows from something the checker verifies: the function's
  declared effects bound every effect of its body, hence of the loop. If every declared effect
  is listed in the header, the header's claim "the loop touches at most these" is implied.
-/
module
public import Grammatik.Parser.Item.ElementTief
import all Init.Data.String.Basic
import all Init.Data.String.Defs
@[expose] public section

namespace Gabbro.Grammatik.Parser.ExportMetadata

/-- The effects a `touches …` header lists; any other or trailing clause is refused. -/
def touchesHeader (raw : String) : Except String (List SEffekt) := do
  let tokens ← match lex raw with
    | .ok ts => pure ts
    | .error _ => throw "traversal header does not lex"
  let rest ← match tokens with
    | .wort "touches" :: rest => pure rest
    | _ => throw "traversal header is not a touches clause"
  let (effects, rest) ← parseEffektListe 10000 rest
  match rest with
  | [.ende] => pure effects
  | _ => throw "traversal header has an unsupported or duplicate clause"

/-- The declared effects the contract tracks. `pure` declares none, and a read is no right of
    the signature (`Signatur` records writes, held locks and marks only), so a header owes
    nothing for it. -/
def declaredEffects (clauses : List SKlausel) : List SEffekt :=
  (clauses.flatMap fun | .effs effects => effects | _ => []).filter fun
    | .pure | .reads _ => false
    | _ => true

/-- An empty header claims nothing. A written header is covered when it lists every effect
    the function declares. -/
def touchesCovered (clauses : List SKlausel) (raw : String) : Bool :=
  raw == "" || match touchesHeader raw with
    | .ok listed => (declaredEffects clauses).all fun e => listed.any (beqSEffekt e)
    | .error _ => false

/-- An empty header is covered by every function. -/
theorem touchesCovered_empty (clauses : List SKlausel) : touchesCovered clauses "" = true := rfl

/-- A covered written header lists every declared effect. -/
theorem touchesCovered_sound (clauses : List SKlausel) (raw : String) (written : raw ≠ "")
    (covered : touchesCovered clauses raw = true) :
    ∃ listed, touchesHeader raw = .ok listed ∧
      ∀ e ∈ declaredEffects clauses, ∃ l ∈ listed, beqSEffekt e l = true := by
  unfold touchesCovered at covered
  have notEmpty : (raw == "") = false := by simpa using written
  rw [notEmpty, Bool.false_or] at covered
  cases parsed : touchesHeader raw with
  | error e => rw [parsed] at covered; cases covered
  | ok listed =>
    rw [parsed] at covered
    refine ⟨listed, rfl, fun e member => ?_⟩
    exact List.any_eq_true.mp (List.all_eq_true.mp covered e member)

/-- The header of the corpus loops is covered by the same declared effect, an unlisted declared
    effect is not, and a header with a second clause is refused. -/
theorem touchesCovered_zeuge :
    touchesCovered [.effs [.reads (.field (.variable "t") "slots"), .writes (.field (.variable "t") "slots")]]
      "touches writes t.slots" = true ∧
    touchesCovered [.effs [.reads (.field (.variable "t") "slots"), .writes (.variable "g")]]
      "touches reads t.slots" = false ∧
    touchesCovered [] "touches reads t.slots decreases n" = false := by
  decide +kernel

/-- Erase every covered `touches` header of an ordinary traversal, in every position the gate
    inspects; a header that is not covered stays and is refused by the gate. -/
def eraseCovered (covered : String → Bool) : Nat → SAnw → SAnw
  | 0, s => s
  | n + 1, .block ss e => .block (ss.map (eraseCovered covered n)) e
  | n + 1, .bindElse a ty c d b => .bindElse a ty c d (eraseCovered covered n b)
  | n + 1, .bindAxiomOptElse a ty c d b => .bindAxiomOptElse a ty c d (eraseCovered covered n b)
  | n + 1, .callIndElse a b c body => .callIndElse a b c (eraseCovered covered n body)
  | n + 1, .callElse a b c body => .callElse a b c (eraseCovered covered n body)
  | n + 1, .waive a b => .waive a (eraseCovered covered n b)
  | n + 1, .locks a b c => .locks a b (eraseCovered covered n c)
  | n + 1, .watch a b => .watch a (eraseCovered covered n b)
  | n + 1, .trim a b c => .trim a b (eraseCovered covered n c)
  | n + 1, .cond c a bs b => .cond c (eraseCovered covered n a) (bs.map (eraseCovered covered n))
      (b.map (eraseCovered covered n))
  | n + 1, .elsif c b => .elsif c (eraseCovered covered n b)
  | n + 1, .arm a b c => .arm a b (eraseCovered covered n c)
  | n + 1, .cases a arms => .cases a (arms.map (eraseCovered covered n))
  | n + 1, .each a b c d mode raw inv body =>
    .each a b c d mode (if mode == "unvisited" && covered raw then "" else raw) inv
      (eraseCovered covered n body)
  | n + 1, .alloc m x ty an v (some body) => .alloc m x ty an v (some (eraseCovered covered n body))
  | _ + 1, s => s

/-- A covered header of an ordinary traversal is erased, an uncovered one and a consuming header stay. -/
theorem eraseCovered_zeuge (body : SAnw) :
    eraseCovered (fun raw => raw == "h") 2 (.each "i" none "slots" (.variable "t") "unvisited" "h" none body) =
      .each "i" none "slots" (.variable "t") "unvisited" "" none (eraseCovered (fun raw => raw == "h") 1 body) ∧
    eraseCovered (fun raw => raw == "h") 2 (.each "i" none "slots" (.variable "t") "unvisited" "x" none body) =
      .each "i" none "slots" (.variable "t") "unvisited" "x" none (eraseCovered (fun raw => raw == "h") 1 body) ∧
    eraseCovered (fun raw => raw == "h") 2 (.each "i" none "slots" (.variable "t") "consuming" "h" none body) =
      .each "i" none "slots" (.variable "t") "consuming" "h" none (eraseCovered (fun raw => raw == "h") 1 body) :=
  ⟨rfl, rfl, rfl⟩

end Gabbro.Grammatik.Parser.ExportMetadata
