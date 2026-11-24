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

private theorem CarrierAccess.token_injective {a b : CarrierAccess} (same : a.print.value = b.print.value) : a = b := by
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
  cases effect with
  | mk access _ _ => cases access <;> cases same

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
    | carrier read => exact (read.disjoint_wordEnd leftEnd).elim
    | group other _ =>
      cases Subtype.ext same
      exact ⟨rfl, rfl⟩
    | pure => exact (ordinary same).elim
  | pure =>
    change EffectTermReads (Token.word "pure".toList :: rest) _ _ at right
    generalize same : "pure".toList = text at right
    cases right with
    | carrier read =>
      rw [← same] at read
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
  cases effect with
  | mk access _ _ => cases access <;> cases same

theorem EffectTermReads.not_closeBrace (read : EffectTermReads (closeBrace :: input) effect rest) : False := by
  cases read with
  | carrier read => exact read.not_closeBrace

theorem EffectListReads.deterministic {read : List Token → α → List Token → Prop}
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

theorem EffectListReads.consumes {read : List Token → α → List Token → Prop}
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
      obtain ⟨same, rfl⟩ := EffectListReads.deterministic (read := EffectTermReads) EffectTermReads.deterministic
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

theorem CarrierEffectReads.printReads (effect : WrittenCarrierEffect) (rest : List Token) :
    CarrierEffectReads (effect.printPieces.map PrintedToken.value ++ rest) effect rest := by
  rcases effect with ⟨access, name, slots⟩
  cases slots
  · exact .bare access name
  · exact .slots access name

private def EffectTerm.printable : EffectTerm → Prop
  | .group name => name.val ≠ "pure".toList
  | _ => True

private theorem EffectTermReads.printReads (term : EffectTerm) (rest : List Token)
    (valid : term.printable) :
    EffectTermReads (term.printPieces.map PrintedToken.value ++ rest) term rest := by
  cases term with
  | carrier effect => exact .carrier (CarrierEffectReads.printReads effect rest)
  | group name => exact .group name valid
  | pure => exact .pure

theorem EffectListReads.printReads {read : List Token → α → List Token → Prop}
    (items : List α) (printItem : α → List PrintedToken)
    (itemRead : ∀ item ∈ items, ∀ suffix, read ((printItem item).map PrintedToken.value ++ suffix) item suffix) :
    EffectListReads read ((commaSeparated (items.map printItem) ++ [printCloseBrace]).map PrintedToken.value ++ rest)
      items rest := by
  have hpClose : printCloseBrace.value = closeBrace := rfl
  have hpComma : printComma.value = comma := rfl
  induction items with
  | nil => exact .close
  | cons head tail ih =>
    cases tail with
    | nil =>
      simpa only [List.map_cons, List.map_nil, commaSeparated, List.intersperse_singleton,
        List.flatten_cons, List.flatten_nil, List.append_nil, List.map_append, List.cons_append,
        List.nil_append, List.append_assoc, hpClose] using
        (EffectListReads.last (itemRead head List.mem_cons_self (closeBrace :: rest)))
    | cons next tail =>
      let tailTokens := (commaSeparated ((next :: tail).map printItem) ++ [printCloseBrace]).map
        PrintedToken.value ++ rest
      have first := itemRead head List.mem_cons_self (comma :: tailTokens)
      have more := ih (fun item member => itemRead item (List.mem_cons_of_mem _ member))
      have tokens : commaSeparated ((head :: next :: tail).map printItem) =
          printItem head ++ [printComma] ++ commaSeparated ((next :: tail).map printItem) := by
        simp only [commaSeparated, List.map_cons, List.intersperse_cons_cons, List.flatten_cons,
          List.append_assoc, List.cons_append, List.nil_append]
      rw [tokens]
      simpa only [tailTokens, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.cons_append, List.nil_append, hpComma] using (EffectListReads.next first more)

private theorem mapM_member (f : α → Option β) {items : List α}
    (mapped : ∃ values, items.mapM f = some values) (member : item ∈ items) :
    ∃ value, f item = some value := by
  induction items with
  | nil => cases member
  | cons head tail ih =>
    obtain ⟨values, mapped⟩ := mapped
    rw [List.mapM_cons] at mapped
    cases hhead : f head with
    | none => simp only [hhead, bind, Option.bind, reduceCtorEq] at mapped
    | some first =>
      rcases List.mem_cons.mp member with eq | member
      · cases eq
        exact ⟨first, hhead⟩
      · cases htail : tail.mapM f with
        | none => simp only [hhead, htail, bind, Option.bind, reduceCtorEq] at mapped
        | some tailValues => exact ih ⟨tailValues, htail⟩ member

private theorem EffectClause.term_printable (clause : EffectClause scope ps)
    (member : term ∈ clause.written) : term.printable := by
  have mapped : ∃ values,
      clause.written.mapM (EffectTerm.resolve scope (ps.map (fun p => p.name.val))) = some values := by
    cases found : clause.written.mapM (EffectTerm.resolve scope (ps.map (fun p => p.name.val))) with
    | none =>
      have checked := clause.checked
      simp only [expandEffects, found, Option.map_none, reduceCtorEq] at checked
    | some values => exact ⟨values, rfl⟩
  obtain ⟨value, resolved⟩ := mapM_member _ mapped member
  cases term with
  | carrier _ => trivial
  | pure => trivial
  | group name =>
    intro reserved
    simp only [EffectTerm.resolve, reserved, true_or, if_true, reduceCtorEq] at resolved

theorem EffectClauseReads.printReads (clause : Option (EffectClause scope ps))
    (closed : ∀ tail, rest ≠ keyword "effects" :: tail) :
    EffectClauseReads scope ps ((effectClausePieces clause).map PrintedToken.value ++ rest) clause rest := by
  cases clause with
  | none => exact .absent closed
  | some clause =>
    have hpEffects : printEffects.value = keyword "effects" := rfl
    have hpOpen : printOpenBrace.value = openBrace := rfl
    have items := EffectListReads.printReads (rest := rest) clause.written EffectTerm.printPieces
      (fun item member suffix => EffectTermReads.printReads item suffix (clause.term_printable member))
    simpa only [effectClausePieces, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.append_assoc, hpEffects, hpOpen] using
      (EffectClauseReads.present clause items)

end Gabbro.Core.Ast
