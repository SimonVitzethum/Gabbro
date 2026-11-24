module

public import Core.Ast.Expression.Grammar

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

theorem Local.binding_mem (ref : Local scope type) : ref.binding ∈ scope := by
  induction ref with
  | here => exact List.mem_cons_self
  | there _ ih => exact List.mem_cons_of_mem _ ih

theorem Local.nameVisible_unique (a : Local scope type) (b : Local scope type')
    (visibleA : a.nameVisible) (visibleB : b.nameVisible)
    (same : a.binding.name.val = b.binding.name.val) :
    (⟨type, a⟩ : (t : Ty .value) × Local scope t) = ⟨type', b⟩ := by
  induction a with
  | here =>
    cases b with
    | here => rfl
    | there b' => exact (visibleB.1 same).elim
  | there a' ih =>
    cases b with
    | here => exact (visibleA.1 same.symm).elim
    | there b' =>
      have eq := ih b' visibleA.2 visibleB.2 same
      cases eq
      rfl

/-- Inverting the atom production recovers both the literal and its complete suffix. -/
theorem AtomReads.lit_inversion
    (read : AtomReads scope (.natural value :: rest) tree suffix) :
    tree.typed = (Expr.lit (scope := scope) value).typed ∧ suffix = rest := by
  cases read
  exact ⟨rfl, rfl⟩

-- Mirror AtomReads.lit_inversion and eliminate the ordinaryLocal exclusion.
theorem AtomReads.true_inversion (read : AtomReads scope (trueKeyword :: rest) tree suffix) :
    tree.typed = (Expr.trueLit (scope := scope)).typed ∧ suffix = rest := by
  change AtomReads scope (.word "true".toList :: rest) tree suffix at read
  generalize hs : "true".toList = word at read
  cases read with
  | trueLit => exact ⟨rfl, rfl⟩
  | falseLit => exfalso; cases hs
  | «variable» ref visible ordinary => exact (ordinary.1 hs.symm).elim
  | recordValue ref fields fits read => exact (ref.ordinary.1 hs.symm).elim
  | variantValue ref label index written ordinary available payload read =>
    exact (ordinary.1 hs.symm).elim
  | textLength _ => cases hs

-- Mirror AtomReads.true_inversion.
theorem AtomReads.false_inversion (read : AtomReads scope (falseKeyword :: rest) tree suffix) :
    tree.typed = (Expr.falseLit (scope := scope)).typed ∧ suffix = rest := by
  change AtomReads scope (.word "false".toList :: rest) tree suffix at read
  generalize hs : "false".toList = word at read
  cases read with
  | falseLit => exact ⟨rfl, rfl⟩
  | trueLit => exfalso; cases hs
  | «variable» ref visible ordinary => exact (ordinary.2.1 hs.symm).elim
  | recordValue ref fields fits read => exact (ref.ordinary.2.1 hs.symm).elim
  | variantValue ref label index written ordinary available payload read =>
    exact (ordinary.2.1 hs.symm).elim
  | textLength _ => cases hs

-- Mirror AtomReads.lit_inversion, leaving the lookup evidence existential.
theorem AtomReads.variable_inversion (ordinary : ordinaryAtomWord word)
    (bound : ∃ (type : Ty .value) (ref : Local scope type), ref.visible ∧ ref.binding.name.val = word)
    (read : AtomReads scope (.word word :: rest) tree suffix) :
    ∃ (type : Ty .value) (ref : Local scope type) (visible : ref.visible)
      (ordinary : ordinaryLocal ref.binding.name),
      ref.binding.name.val = word ∧ tree.typed = (Expr.variable ref visible ordinary).typed ∧ suffix = rest := by
  obtain ⟨_, localRef, localVisible, localSpelling⟩ := bound
  generalize head : Token.word word = token at read
  cases read with
  | trueLit =>
    injection head with spelling
    exact (ordinary.1 spelling).elim
  | falseLit =>
    injection head with spelling
    exact (ordinary.2.1 spelling).elim
  | «variable» ref visible nameOrdinary =>
    injection head with spelling
    exact ⟨_, ref, visible, nameOrdinary, spelling.symm, rfl, rfl⟩
  | recordValue ref _ _ _ =>
    injection head with spelling
    have same := Local.nameVisible_unique localRef ref.schema localVisible.2 ref.visible
      (localSpelling.trans (spelling.trans ref.spelled.symm))
    exact (Eq.mp (congrArg Ty.valueBinding (congrArg Sigma.fst same)) localVisible.1 : False).elim
  | variantValue ref label index written nameOrdinary available payload payloadRead =>
    injection head with spelling
    exact (available.2 _ (Local.binding_mem localRef) (localSpelling.trans spelling)).elim
  | textLength _ =>
    have spelling : word = "lenof".toList := Token.word.inj head
    exact (ordinary.2.2.1 spelling).elim
  | _ => cases head

theorem AtomReads.negative_inversion
    (read : AtomReads scope (minus :: .natural value :: rest) tree suffix) :
    tree.typed = (Expr.negativeLit (scope := scope) value).typed ∧ suffix = rest := by
  cases read with
  | negativeLit => exact ⟨rfl, rfl⟩
  | _ =>
      exfalso
      rename_i start child
      exact start.2 _ _ rfl

-- Mirror AtomReads.lit_inversion, retaining the operand derivation.
theorem AtomReads.neg_inversion (start : NegationStart input)
    (read : AtomReads scope (minus :: input) tree rest) :
    ∃ (lo hi : Int) (operand : Expr scope (.int lo hi)),
      AtomReads scope input operand rest ∧ tree.typed = (Expr.neg operand).typed := by
  cases read with
  | neg start' child => exact ⟨_, _, _, child, rfl⟩
  | _ =>
      exfalso
      exact start.2 _ _ rfl

-- Mirror AtomReads.neg_inversion and keep the Boolean type.
theorem AtomReads.not_inversion (read : AtomReads scope (bang :: input) tree rest) :
    ∃ operand : Expr scope .bool, PrimaryStart input ∧
      AtomReads scope input operand rest ∧ tree.typed = (Expr.not operand).typed := by
  cases read with
  | not primary child => exact ⟨_, primary, child, rfl⟩

-- Mirror Arith.token_injective by inducting on the two typed indices.
theorem Local.visible_unique (a : Local scope type) (b : Local scope type')
    (visibleA : a.visible) (visibleB : b.visible) (same : a.binding.name.val = b.binding.name.val) :
    (⟨type, a⟩ : (t : Ty .value) × Local scope t) = ⟨type', b⟩ := by
  exact Local.nameVisible_unique a b visibleA.2 visibleB.2 same

end Gabbro.Core.Ast
