module

public import Grammatik.Parser.Elab.Export.ExportControl
public import Grammatik.Parser.Elab.UebersetzeSum
public import Grammatik.Bausteine.Arena.ArenaZucker
public import Grammatik.Parser.Namen.Oeffentlich
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.UebersetzeAllg3.Rest2

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg2

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000

/-! ## The expansion certificate of a lowered program

For every function of a successfully lowered unit that a transition declaration
generated, the lowered requires, ensures and body ARE the expansion of the
declaration (`TransitionExpansion` / `TransitionShiftExpansion`), so the generic
call theorems apply to every successful call of it. An ordinary caller reaches
the function only through its real requires, which the lowering built from the
declaration's source-stage equalities and clause. -/

/-- The lowered pair at an index known good. -/
theorem lowerAtPair_of_ok (u : UProg) (f : Fin u.fns.length) (hw : ∃ v, lowerFnAt u f = .ok v)
    {v : EnsTy u f × RumpTy u f × ReqTy u f} (hv : lowerFnAt u f = .ok v) :
    lowerAtPair u f hw = v := by
  unfold lowerAtPair
  split
  · rename_i v' hv'
    rw [hv] at hv'
    cases hv'
    rfl
  · rename_i e he
    rw [hv] at he
    cases he

/-- What the assembled program holds at a function of a successful lowering. -/
theorem lowerAllg_fields (u : UProg) (P : Programm (declOf u)) (fs : List (declOf u).Fn)
    (h : lowerAllg u = .ok (P, fs)) (c : Fin u.fns.length) :
    ∃ v, lowerFnAt u c = .ok v ∧ P.ensures c = v.1 ∧ P.rumpf c = v.2.1 ∧
      ((fnAt u c).needs ≠ [] → P.requires c = v.2.2) := by
  unfold lowerAllg at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · obtain ⟨rfl, -⟩ := Gabbro.Grammatik.Parser.Measures.checkedProgram_eq h
        obtain ⟨v, hv⟩ := lowerEach_all_ok u (List.finRange u.fns.length) c (List.mem_finRange c)
          ‹lowerEach u (List.finRange u.fns.length) = .ok ()›
        refine ⟨v, hv, ?_, ?_, ?_⟩
        · exact congrArg Prod.fst (lowerAtPair_of_ok u c _ hv)
        · exact congrArg (fun p => p.2.1) (lowerAtPair_of_ok u c _ hv)
        · intro hne
          simp only [progOfFn, reqOf, hne, ↓reduceIte]
          exact congrArg (fun p => p.2.2) (lowerAtPair_of_ok u c _ hv)
      · cases h

/-- The pieces of a lowered transition of stores. -/
theorem lowerStoresAt_spec (u : UProg) (c : Fin u.fns.length) (tr : UTransition)
    {v : EnsTy u c × RumpTy u c × ReqTy u c} (h : lowerStoresAt u c tr = .ok v) :
    ∃ (ws : List (TransitionWrite (declOf u) (ctxOf u c) (resOf u c)))
      (clause : Expr (declOf u) (ctxOf u c) (resOf u c) .bool)
      (frozen : ∀ w ∈ ws, w.Frozen)
      (rights : ∀ w ∈ ws, w.Permitted (vertragVon (declOf u) c))
      (hn : (declOf u).erg c = none),
      HEq v.2.2 (transitionRequires ws clause) ∧ HEq v.1 (transitionEnsures ws) ∧
      HEq v.2.1 (transitionEnd (vertragVon (declOf u) c) ws rights
        (transitionReturn (vertragVon (declOf u) c) hn (transitionResPerm u c))) := by
  unfold lowerStoresAt at h
  split at h
  · cases h
  · rename_i ws _
    split at h
    · cases h
    · rename_i clause _
      split at h
      · rename_i hn
        cases h
        exact ⟨ws.1, clause, ws.2.1, ws.2.2, hn, transCast_heq _ _, transCast_heq _ _,
          transCast_heq _ _⟩
      · cases h

/-- The pieces of a lowered constant-edge transition. -/
theorem lowerShiftAt_spec (u : UProg) (c : Fin u.fns.length) (tr : UTransition)
    {v : EnsTy u c × RumpTy u c × ReqTy u c} (h : lowerShiftAt u c tr = .ok v) :
    ∃ (edge : ConstEdge (declOf u) (vertragVon (declOf u) c) (ctxOf u c) (resOf u c))
      (clause : Expr (declOf u) (ctxOf u c) (resOf u c) .bool)
      (hn : (declOf u).erg c = none),
      HEq v.2.2 (transitionRequires [edge.write] clause) ∧
      HEq v.1 (transitionEnsures [edge.write]) ∧
      HEq v.2.1 (Endblock.cons edge.statement
        (transitionReturn (vertragVon (declOf u) c) hn (transitionResPerm u c))) := by
  unfold lowerShiftAt at h
  split at h
  · rename_i w
    split at h
    · cases h
    · rename_i edge _
      split at h
      · cases h
      · rename_i clause _
        split at h
        · rename_i hn
          cases h
          exact ⟨edge, clause, hn, transCast_heq _ _, transCast_heq _ _, transCast_heq _ _⟩
        · cases h
  · cases h

/-- A generated function is admitted only as its declaration's expansion, with a requires. -/
theorem lowerTransitionAt_stores_spec (u : UProg) (c : Fin u.fns.length) (state : UZustand)
    (tr : UTransition) (hs : uTransitionShift tr = false)
    {v : EnsTy u c × RumpTy u c × ReqTy u c} (h : lowerTransitionAt u c state tr = .ok v) :
    (fnAt u c).needs ≠ [] ∧
    ∃ (ws : List (TransitionWrite (declOf u) (ctxOf u c) (resOf u c)))
      (clause : Expr (declOf u) (ctxOf u c) (resOf u c) .bool)
      (frozen : ∀ w ∈ ws, w.Frozen)
      (rights : ∀ w ∈ ws, w.Permitted (vertragVon (declOf u) c))
      (hn : (declOf u).erg c = none),
      HEq v.2.2 (transitionRequires ws clause) ∧ HEq v.1 (transitionEnsures ws) ∧
      HEq v.2.1 (transitionEnd (vertragVon (declOf u) c) ws rights
        (transitionReturn (vertragVon (declOf u) c) hn (transitionResPerm u c))) := by
  unfold lowerTransitionAt at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · rename_i hne
        split at h
        · rename_i hshift
          rw [hs] at hshift
          exact absurd hshift (by decide)
        · exact ⟨hne, lowerStoresAt_spec u c tr h⟩
    · cases h

theorem lowerTransitionAt_shift_spec (u : UProg) (c : Fin u.fns.length) (state : UZustand)
    (tr : UTransition) (hs : uTransitionShift tr = true)
    {v : EnsTy u c × RumpTy u c × ReqTy u c} (h : lowerTransitionAt u c state tr = .ok v) :
    (fnAt u c).needs ≠ [] ∧
    ∃ (edge : ConstEdge (declOf u) (vertragVon (declOf u) c) (ctxOf u c) (resOf u c))
      (clause : Expr (declOf u) (ctxOf u c) (resOf u c) .bool)
      (hn : (declOf u).erg c = none),
      HEq v.2.2 (transitionRequires [edge.write] clause) ∧
      HEq v.1 (transitionEnsures [edge.write]) ∧
      HEq v.2.1 (Endblock.cons edge.statement
        (transitionReturn (vertragVon (declOf u) c) hn (transitionResPerm u c))) := by
  unfold lowerTransitionAt at h
  simp only [hs, ↓reduceIte] at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · rename_i hne
        exact ⟨hne, lowerShiftAt_spec u c tr h⟩
    · cases h

/-- **Expansion certificate (stores).** In a successful lowering, the function
    generated for a declaration of stores IS its expansion: the generic call theorem
    (`TransitionExpansion.call_correct`) relates every successful call to the
    declaration's full pre/post relation and frame. -/
theorem lowerAllg_transition_stores (u : UProg) (P : Programm (declOf u))
    (fs : List (declOf u).Fn) (h : lowerAllg u = .ok (P, fs)) (c : Fin u.fns.length)
    (state : UZustand) (tr : UTransition) (hc : transitionOfFn u c = some (state, tr))
    (hs : uTransitionShift tr = false) : Nonempty (TransitionExpansion P c) := by
  obtain ⟨v, hv, hens, hrump, hreq⟩ := lowerAllg_fields u P fs h c
  have hlow : lowerFnAt u c = lowerTransitionAt u c state tr := by
    simp only [lowerFnAt, hc]
  rw [hlow] at hv
  obtain ⟨hne, ws, clause, frozen, rights, hn, hR, hE, hB⟩ :=
    lowerTransitionAt_stores_spec u c state tr hs hv
  exact ⟨TransitionExpansion.ofHEq (ctxParams_eq u c) (anfangRes_eq u c) ws clause frozen
    rights hn (endeRes_eq u c)
    (HEq.trans (heq_of_eq (hreq hne)) hR) (HEq.trans (heq_of_eq hens) hE)
    (HEq.trans (heq_of_eq hrump) hB)⟩

/-- **Expansion certificate (constant edge).** The generated function ends in the
    primitive `Stmt.shift`; the certificate relates it to the same declaration
    relation under the legal entry its requires establishes. -/
theorem lowerAllg_transition_shift (u : UProg) (P : Programm (declOf u))
    (fs : List (declOf u).Fn) (h : lowerAllg u = .ok (P, fs)) (c : Fin u.fns.length)
    (state : UZustand) (tr : UTransition) (hc : transitionOfFn u c = some (state, tr))
    (hs : uTransitionShift tr = true) : Nonempty (TransitionShiftExpansion P c) := by
  obtain ⟨v, hv, hens, hrump, hreq⟩ := lowerAllg_fields u P fs h c
  have hlow : lowerFnAt u c = lowerTransitionAt u c state tr := by
    simp only [lowerFnAt, hc]
  rw [hlow] at hv
  obtain ⟨hne, edge, clause, hn, hR, hE, hB⟩ := lowerTransitionAt_shift_spec u c state tr hs hv
  exact ⟨TransitionShiftExpansion.ofHEq (ctxParams_eq u c) (anfangRes_eq u c) edge clause hn
    (endeRes_eq u c)
    (HEq.trans (heq_of_eq (hreq hne)) hR) (HEq.trans (heq_of_eq hens) hE)
    (HEq.trans (heq_of_eq hrump) hB)⟩

/-- **Every generated function is certified.** A function of the generated name
    range in a successfully lowered unit belongs to a declaration and carries its
    expansion certificate; there is no ordinary-function lowering of such a name. -/
theorem lowerAllg_transition_certified (u : UProg) (P : Programm (declOf u))
    (fs : List (declOf u).Fn) (h : lowerAllg u = .ok (P, fs)) (c : Fin u.fns.length)
    (hname : (fnAt u c).name.startsWith "#transition#" = true) :
    ∃ (state : UZustand) (tr : UTransition), transitionOfFn u c = some (state, tr) ∧
      (Nonempty (TransitionExpansion P c) ∨ Nonempty (TransitionShiftExpansion P c)) := by
  obtain ⟨v, hv, -, -, -⟩ := lowerAllg_fields u P fs h c
  cases hc : transitionOfFn u c with
  | none =>
    exfalso
    simp only [lowerFnAt, hc, hname, ↓reduceIte, reduceCtorEq] at hv
  | some pair =>
    obtain ⟨state, tr⟩ := pair
    refine ⟨state, tr, rfl, ?_⟩
    cases hs : uTransitionShift tr with
    | false => exact Or.inl (lowerAllg_transition_stores u P fs h c state tr hc hs)
    | true => exact Or.inr (lowerAllg_transition_shift u P fs h c state tr hc hs)

end Gabbro.Grammatik.Parser.UebersetzeAllg2
