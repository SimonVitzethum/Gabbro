module

public import Grammatik.Parser.Item.ElementTief.Defs7

@[expose] public section

namespace Gabbro.Grammatik.Parser

/-- The three boundaries of an item list. The enclosing production decides
    whether it expects the closing brace or the end marker. -/
def ItemsEnde (tokens : List Token) : Prop :=
  tokens = [] ∨ (∃ rest, tokens = .zeichen "}" :: rest) ∨ (∃ rest, tokens = .ende :: rest)

/-- The sequence production with the item reader as its leaf rule. Each AST
    node records an item read from the exact remainder of the previous one. -/
inductive ItemSequence : Nat → List Token → List SItemTief → List Token → Prop where
  | done {fuel tokens} : ItemsEnde tokens → ItemSequence (fuel + 1) tokens [] tokens
  | item {fuel tokens rest closing node nodes} :
      ¬ ItemsEnde tokens → parseItemTief fuel tokens = .ok (node, rest) →
      ItemSequence fuel rest nodes closing → ItemSequence (fuel + 1) tokens (node :: nodes) closing

private theorem parseItemsTief_succ (fuel : Nat) (tokens : List Token) :
    parseItemsTief (fuel + 1) tokens = @ite _ (ItemsEnde tokens) (Classical.propDecidable _)
      (.ok ([], tokens)) (match parseItemTief fuel tokens with
      | .error e => .error e
      | .ok (node, rest) => match parseItemsTief fuel rest with
        | .error e => .error e
        | .ok (nodes, closing) => .ok (node :: nodes, closing)) := by
  classical
  conv_lhs => unfold parseItemsTief
  split <;> simp_all [ItemsEnde] <;> rfl

/-- At a fixed fuel bound the concrete reader recognizes exactly the item
    sequence production, with the same AST order and closing tokens. -/
theorem parseItemsTief_iff {fuel : Nat} {tokens closing : List Token} {nodes : List SItemTief} :
    parseItemsTief fuel tokens = .ok (nodes, closing) ↔ ItemSequence fuel tokens nodes closing := by
  classical
  constructor
  · intro parsed
    induction fuel generalizing tokens nodes closing with
    | zero => simp only [parseItemsTief, reduceCtorEq] at parsed
    | succ fuel ih =>
      rw [parseItemsTief_succ] at parsed
      split at parsed
      · rename_i boundary
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj parsed)
        exact .done boundary
      · rename_i continues
        cases head : parseItemTief fuel tokens with
        | error e => simp only [head, reduceCtorEq] at parsed
        | ok current =>
          obtain ⟨node, rest⟩ := current
          cases tail : parseItemsTief fuel rest with
          | error e => simp only [head, tail, reduceCtorEq] at parsed
          | ok remaining =>
            obtain ⟨following, ending⟩ := remaining
            simp only [head, tail] at parsed
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj parsed)
            exact .item continues head (ih tail)
  · intro derivation
    induction derivation with
    | done boundary => rw [parseItemsTief_succ, ite_eq_left boundary]
    | item continues head _ tail => simp only [parseItemsTief_succ, ite_eq_right continues, head, tail]

theorem ItemSequence.length_lt {fuel : Nat} {tokens closing : List Token} {nodes : List SItemTief}
    (read : ItemSequence fuel tokens nodes closing) : nodes.length < fuel := by
  induction read with
  | done => exact Nat.zero_lt_succ _
  | item _ _ _ shorter => exact Nat.succ_lt_succ shorter

/-- A compilation unit consumes the entire sequence up to its sole final
    marker. A closing brace or trailing tokens cannot end this production. -/
theorem parseTopTief_iff {tokens : List Token} {nodes : List SItemTief} :
    parseTopTief tokens = .ok nodes ↔ ItemSequence (tokens.length * 8 + 32) tokens nodes [.ende] := by
  constructor
  · intro parsed
    unfold parseTopTief at parsed
    split at parsed
    · rename_i read
      cases Except.ok.inj parsed
      exact parseItemsTief_iff.mp read
    · cases parsed
    · cases parsed
  · intro read
    unfold parseTopTief
    rw [parseItemsTief_iff.mpr read]

end Gabbro.Grammatik.Parser
