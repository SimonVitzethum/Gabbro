module

public import Core.Ast.Aggregate.Carrier.Effects.Grammar

@[expose] public section

namespace Gabbro.Core.Ast

open Gabbro.Core.Text

/-- Effect items are compared at the list boundary. A bare access can leave
    a suffix that still contains its optional slot qualifier. -/
inductive EffectItemEnd : List Token → Prop where
  | comma : EffectItemEnd (comma :: rest)
  | close : EffectItemEnd (closeBrace :: rest)

private theorem CarrierAccess.token_injective (same : a.print.value = b.print.value) : a = b := by
  cases a <;> cases b <;> first | rfl | cases same

private theorem CarrierEffectReads.prefix (read : CarrierEffectReads input effect rest) :
    ∃ tail, input = effect.access.print.value :: .word effect.carrier.val :: tail := by
  cases read <;> exact ⟨_, rfl⟩

theorem CarrierEffectReads.deterministic (left : CarrierEffectReads input a rest)
    (right : CarrierEffectReads input b more) (leftEnd : EffectItemEnd rest) (rightEnd : EffectItemEnd more) :
    a = b ∧ rest = more := by
  cases left with
  | bare access name =>
    generalize same : (access.print.value :: Token.word name.val :: rest) = tokens at right
    cases right with
    | bare otherAccess otherName =>
      cases CarrierAccess.token_injective (List.cons.inj same).1
      have tail := List.cons.inj (List.cons.inj same).2
      cases Subtype.ext (Token.word.inj tail.1)
      exact ⟨rfl, tail.2⟩
    | slots _ _ =>
      have tail := (List.cons.inj (List.cons.inj same).2).2
      rw [tail] at leftEnd
      cases leftEnd
  | slots access name =>
    generalize same : (access.print.value :: Token.word name.val :: dot :: keyword "slots" :: rest) = tokens at right
    cases right with
    | bare _ _ =>
      have tail := (List.cons.inj (List.cons.inj same).2).2
      rw [← tail] at rightEnd
      cases rightEnd
    | slots otherAccess otherName =>
      cases CarrierAccess.token_injective (List.cons.inj same).1
      have tail := List.cons.inj (List.cons.inj same).2
      cases Subtype.ext (Token.word.inj tail.1)
      exact ⟨rfl, (List.cons.inj (List.cons.inj tail.2).2).2⟩

private theorem CarrierEffectReads.disjoint_wordEnd
    (read : CarrierEffectReads (.word word :: input) effect rest) (ending : EffectItemEnd input) : False := by
  obtain ⟨_, head⟩ := read.prefix
  rw [(List.cons.inj head).2] at ending
  cases ending

private theorem CarrierEffectReads.disjoint_pure
    (read : CarrierEffectReads (keyword "pure" :: input) effect rest) : False := by
  obtain ⟨_, head⟩ := read.prefix
  have same := (List.cons.inj head).1
  cases effect.access <;> cases same

theorem EffectTermReads.deterministic (left : EffectTermReads input a rest)
    (right : EffectTermReads input b more) (leftEnd : EffectItemEnd rest) (rightEnd : EffectItemEnd more) :
    a = b ∧ rest = more := by
  cases left with
  | carrier read =>
    cases right with
    | carrier other =>
      obtain ⟨rfl, rfl⟩ := read.deterministic other leftEnd rightEnd
      exact ⟨rfl, rfl⟩
    | group name _ => exact (read.disjoint_wordEnd (word := name.val) rightEnd).elim
    | pure => exact read.disjoint_pure.elim
  | group name ordinary =>
    generalize same : name.val = text at right
    cases right with
    | carrier read =>
      cases same
      exact (read.disjoint_wordEnd leftEnd).elim
    | group other _ =>
      cases Subtype.ext same
      exact ⟨rfl, rfl⟩
    | pure => exact (ordinary same).elim
  | pure =>
    generalize same : "pure".toList = text at right
    cases right with
    | carrier read =>
      cases same
      exact read.disjoint_pure.elim
    | group name ordinary => exact (ordinary same.symm).elim
    | pure => exact ⟨rfl, rfl⟩

theorem CarrierEffectReads.consumes (read : CarrierEffectReads input effect rest) : rest <:+ input := by
  cases read with
  | bare _ _ => exact (List.suffix_cons _ _).trans (List.suffix_cons _ _)
  | slots _ _ =>
    exact (((List.suffix_cons _ _).trans (List.suffix_cons _ _)).trans
      (List.suffix_cons _ _)).trans (List.suffix_cons _ _)

theorem EffectTermReads.consumes (read : EffectTermReads input effect rest) : rest <:+ input := by
  cases read with
  | carrier read => exact read.consumes
  | group _ _ => exact List.suffix_cons _ _
  | pure => exact List.suffix_cons _ _

theorem CarrierEffectReads.not_closeBrace (read : CarrierEffectReads (closeBrace :: input) effect rest) : False := by
  obtain ⟨_, head⟩ := read.prefix
  have same := (List.cons.inj head).1
  cases effect.access <;> cases same

theorem EffectTermReads.not_closeBrace (read : EffectTermReads (closeBrace :: input) effect rest) : False := by
  cases read with
  | carrier read => exact read.not_closeBrace

theorem EffectListReads.deterministic
    (itemDet : ∀ {input a b rest more}, read input a rest → read input b more →
      EffectItemEnd rest → EffectItemEnd more → a = b ∧ rest = more)
    (itemClose : ∀ {input a rest}, read (closeBrace :: input) a rest → False)
    (left : EffectListReads read input a rest) (right : EffectListReads read input b more) :
    a = b ∧ rest = more := by
  induction left generalizing b more with
  | close =>
    cases right with
    | close => exact ⟨rfl, rfl⟩
    | last item => exact (itemClose item).elim
    | next item _ => exact (itemClose item).elim
  | last item =>
    cases right with
    | close => exact (itemClose item).elim
    | last other =>
      obtain ⟨rfl, hs⟩ := itemDet item other .close .close
      exact ⟨rfl, (List.cons.inj hs).2⟩
    | next other _ =>
      have hs := (itemDet item other .close .comma).2
      cases hs
  | next item tail ih =>
    cases right with
    | close => exact (itemClose item).elim
    | last other =>
      have hs := (itemDet item other .comma .close).2
      cases hs
    | next other otherTail =>
      obtain ⟨rfl, hs⟩ := itemDet item other .comma .comma
      cases (List.cons.inj hs).2
      obtain ⟨same, rfl⟩ := ih otherTail
      cases same
      exact ⟨rfl, rfl⟩

theorem EffectListReads.consumes
    (itemConsumes : ∀ {input item rest}, read input item rest → rest <:+ input)
    (items : EffectListReads read input effects rest) : rest <:+ input := by
  induction items with
  | close => exact List.suffix_cons _ _
  | last item => exact (List.suffix_cons _ _).trans (itemConsumes item)
  | next item _ ih => exact (ih.trans (List.suffix_cons _ _)).trans (itemConsumes item)

theorem EffectClauseReads.deterministic
    (left : EffectClauseReads scope ps input a rest) (right : EffectClauseReads scope ps input b more) :
    a = b ∧ rest = more := by
  cases left with
  | absent closed =>
    cases right with
    | absent _ => exact ⟨rfl, rfl⟩
    | present _ _ => exact (closed _ rfl).elim
  | present clause terms =>
    cases right with
    | absent closed => exact (closed _ rfl).elim
    | present other otherTerms =>
      obtain ⟨same, rfl⟩ := EffectListReads.deterministic EffectTermReads.deterministic
        EffectTermReads.not_closeBrace terms otherTerms
      cases clause with
      | mk written expanded checked =>
        cases other with
        | mk otherWritten otherExpanded otherChecked =>
          cases same
          cases Option.some.inj (checked.symm.trans otherChecked)
          exact ⟨rfl, rfl⟩

theorem EffectClauseReads.consumes (read : EffectClauseReads scope ps input effects rest) : rest <:+ input := by
  cases read with
  | absent _ => exact List.suffix_refl _
  | present _ terms =>
    exact ((EffectListReads.consumes EffectTermReads.consumes terms).trans (List.suffix_cons _ _)).trans
      (List.suffix_cons _ _)

end Gabbro.Core.Ast
