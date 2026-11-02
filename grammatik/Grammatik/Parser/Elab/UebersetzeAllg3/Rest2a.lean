module
public import Grammatik.Parser.Elab.Export.ExportControl
public import Grammatik.Parser.Elab.UebersetzeSum
public import Grammatik.Bausteine.Arena.ArenaZucker
public import Grammatik.Parser.Namen.Oeffentlich
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
public import Grammatik.Parser.Elab.UebersetzeAllg3.Stufe
public import Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
public import Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Export
@[expose] public section
namespace Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
set_option maxRecDepth 100000
/-- What `lowerEach` checks, per function. -/
theorem lowerEach_all_ok (u : UProg) (fs : List (Fin u.fns.length))
    (f : Fin u.fns.length) (hm : f ∈ fs)
    (h : lowerEach u fs = .ok ()) :
    ∃ v, lowerFnAt u f = .ok v := by
  induction fs with
  | nil =>
    simp only [List.not_mem_nil] at hm
  | cons g gs ih =>
    simp only [List.mem_cons] at hm
    cases hg : lowerFnAt u g with
    | error e =>
      have hE : lowerEach u (g :: gs) = .error e := by
        simp only [lowerEach, hg]
      rw [hE] at h
      simp only [reduceCtorEq] at h
    | ok v =>
      have hO : lowerEach u (g :: gs) = lowerEach u gs := by
        simp only [lowerEach, hg]
      cases hm with
      | inl he =>
        subst he
        exact ⟨v, hg⟩
      | inr hm' =>
        rw [hO] at h
        exact ih hm' h
/-- The lowered pair at an index known good. -/
def lowerAtPair (u : UProg) (f : Fin u.fns.length)
    (h : ∃ v, lowerFnAt u f = .ok v) :
    EnsTy u f × RumpTy u f × ReqTy u f :=
  match hm : lowerFnAt u f with
  | .ok v => v
  | .error e => by
    exfalso
    obtain ⟨v, hv⟩ := h
    rw [hv] at hm
    simp only [reduceCtorEq] at hm
/-- The type of a lowered invariant: a predicate over no parameter, under the guards of its carriers. -/
abbrev InvTy (u : UProg) (i : Fin u.invs.length) := Expr (declOf u) [] (invSicht (declOf u) i) .bool
/-- The requires of a function: `.tru` without a `requires` predicate (what the conjunction of none is),
    else the lowered conjunction. -/
def reqOf (u : UProg) (R : ∀ f : Fin u.fns.length, ReqTy u f) (f : Fin u.fns.length) : ReqTy u f :=
  if (fnAt u f).needs = [] then Expr.tru else R f

theorem reqOf_leer (u : UProg) (R : ∀ f : Fin u.fns.length, ReqTy u f) (f : Fin u.fns.length)
    (h : (fnAt u f).needs = []) : reqOf u R f = Expr.tru := by
  unfold reqOf
  rw [if_pos h]

/-- Assemble lowered functions to a program (no contract
    content in `requires`, per-function `ensures` and bodies). -/
def progOfFn (u : UProg) (E : ∀ f : Fin u.fns.length, EnsTy u f)
    (B : ∀ f : Fin u.fns.length, RumpTy u f) (R : ∀ f : Fin u.fns.length, ReqTy u f)
    (I : ∀ i : Fin u.invs.length, InvTy u i) :
    Programm (declOf u) where
  invariante := I
  requires := fun f => reqOf u R f
  ensures := fun f => E f
  rumpf := fun f => B f
  unterbricht := fun f => u.hands.any (fun n => strEq n (fnAt u f).name)

/-- The function of no parameter in whose scope an invariant is read. -/
def leerFn : UFn :=
  { name := "", params := [], kinds := [], res := none, held := [], puts := [], gives := [], body := [], ret := .empty }

/-- A lowered invariant reads only its declared carriers: every carrier its predicate reads is one of the
    invariant's carriers (tables and statics, C05) -- `InvTraeger` of the exported unit, decided. -/
def invReadsOk (u : UProg) (i : Fin u.invs.length) (e : InvTy u i) : Bool :=
  e.orte.all fun (c : Fin u.tabs.length ⊕ Fin u.globs.length) => decide (c ∈ invTraeger u i)

/-- One invariant, lowered. It is REFUSED -- never lowered over a shortened carrier list -- where a writer of a
    carrier does not hold every guard lock of the carriers (`U003`, `invOkB`; `traegerD` would fall back to
    no carriers there), and where the predicate reads a carrier the invariant does not declare. -/
def lowerInvAt (u : UProg) (i : Fin u.invs.length) : Except String (InvTy u i) :=
  if invOkB u i then
    match lowEns u [] (invSicht (declOf u) i) leerFn none (u.invs.get i).pred with
    | .error e => .error e
    | .ok e =>
      if invReadsOk u i e then .ok e else .error "an invariant reads a carrier it does not declare"
  else .error "a writer of an invariant's carrier does not hold all its locks"

/-- What a lowered invariant guarantees: `U003` holds and the predicate reads only declared carriers. -/
theorem lowerInvAt_facts (u : UProg) (i : Fin u.invs.length) (v : InvTy u i)
    (h : lowerInvAt u i = .ok v) : invOkB u i = true ∧ invReadsOk u i v = true := by
  unfold lowerInvAt at h
  by_cases hok : invOkB u i = true
  · rw [if_pos hok] at h
    refine ⟨hok, ?_⟩
    cases hl : lowEns u [] (invSicht (declOf u) i) leerFn none (u.invs.get i).pred with
    | error e => simp only [hl, reduceCtorEq] at h
    | ok e =>
      simp only [hl] at h
      by_cases hr : invReadsOk u i e = true
      · rw [if_pos hr] at h
        cases h
        exact hr
      · rw [if_neg hr] at h
        cases h
  · rw [if_neg hok] at h
    cases h

/-- Every invariant lowers. -/
def lowerInvs (u : UProg) : List (Fin u.invs.length) → Except String Unit
  | [] => .ok ()
  | i :: is =>
    match lowerInvAt u i with
    | .error e => .error e
    | .ok _ => lowerInvs u is

theorem lowerInvs_all_ok (u : UProg) (is : List (Fin u.invs.length)) (i : Fin u.invs.length) (hm : i ∈ is)
    (h : lowerInvs u is = .ok ()) : ∃ v, lowerInvAt u i = .ok v := by
  induction is with
  | nil => simp only [List.not_mem_nil] at hm
  | cons j js ih =>
    simp only [List.mem_cons] at hm
    cases hj : lowerInvAt u j with
    | error e =>
      have hE : lowerInvs u (j :: js) = .error e := by simp only [lowerInvs, hj]
      rw [hE] at h
      simp only [reduceCtorEq] at h
    | ok v =>
      have hO : lowerInvs u (j :: js) = lowerInvs u js := by simp only [lowerInvs, hj]
      cases hm with
      | inl he => subst he; exact ⟨v, hj⟩
      | inr hm' => rw [hO] at h; exact ih hm' h

/-- The lowered invariant at an index known good. -/
def lowerInvGut (u : UProg) (i : Fin u.invs.length) (h : ∃ v, lowerInvAt u i = .ok v) : InvTy u i :=
  match hm : lowerInvAt u i with
  | .ok v => v
  | .error _ => by
    exfalso
    obtain ⟨v, hv⟩ := h
    rw [hv] at hm
    simp only [reduceCtorEq] at hm

/-- Pointer interfaces carry no lowered contract until the full O43 duty is
    bound (candidate table, structural `SigPasst`, interface caller duty and
    `PtrVerfeinert` in `LogikPflicht`). A nontrivial `needs`/`gives` on a
    pointer type is an explicit refusal here, never a silent `trivial`: the
    export admits the target only where the full duty is proved. -/
def ptrVertragGebunden (u : UProg) : Bool :=
  u.ptrs.all fun p => p.needs.isEmpty && p.gives.isEmpty

/-- The generically lowered program: every function of the
    elaborated program over the declaration built from it. -/
def lowerAllg (u : UProg) :
    Except String (Programm (declOf u) × List (declOf u).Fn) :=
  match hI : lowerInvs u (List.finRange u.invs.length) with
  | .error e => .error e
  | .ok _ =>
  have wI : ∀ i : Fin u.invs.length, ∃ v, lowerInvAt u i = .ok v := fun i =>
    lowerInvs_all_ok u (List.finRange u.invs.length) i (List.mem_finRange i) hI
  match h : lowerEach u (List.finRange u.fns.length) with
  | .error e => .error e
  | .ok _ =>
    if ptrVertragGebunden u then
    have w : ∀ f : Fin u.fns.length,
        ∃ v, lowerFnAt u f = .ok v := fun f =>
      lowerEach_all_ok u (List.finRange u.fns.length) f
        (List.mem_finRange f) h
    Measures.checkedProgram u (progOfFn u (fun f => (lowerAtPair u f (w f)).1)
      (fun f => (lowerAtPair u f (w f)).2.1) (fun f => (lowerAtPair u f (w f)).2.2)
      (fun i => lowerInvGut u i (wI i)))
    else .error "contract on a function-pointer type without bound O43 duty"

/-- The lowered invariant at an index known good: `U003` holds and it reads only declared carriers. -/
theorem lowerInvGut_facts (u : UProg) (i : Fin u.invs.length) (h : ∃ v, lowerInvAt u i = .ok v) :
    invOkB u i = true ∧ invReadsOk u i (lowerInvGut u i h) = true := by
  unfold lowerInvGut
  split
  next v hm => exact lowerInvAt_facts u i v hm
  next e hm =>
    exfalso
    obtain ⟨v, hv⟩ := h
    rw [hv] at hm
    cases hm

/-- A lowered invariant reads only carriers in the declaration's carrier list (`InvTraeger`). -/
theorem lowerInvGut_orte (u : UProg) (i : Fin u.invs.length) (h : ∃ v, lowerInvAt u i = .ok v) :
    ∀ c ∈ (lowerInvGut u i h).orte, c ∈ (declOf u).traeger i := by
  intro c hc
  obtain ⟨hok, hr⟩ := lowerInvGut_facts u i h
  unfold invReadsOk at hr
  have hc' : c ∈ invTraeger u i := by
    have := List.all_eq_true.mp hr c hc
    simp only [decide_eq_true_eq] at this
    exact this
  show c ∈ traegerD u i
  rw [traegerD_of_ok u i hok]
  exact hc'

/-- **The exported unit keeps its whole declared carrier list and reads only it.** A unit that lowers has `U003`
    at every invariant, so the declaration's carriers of each invariant are ALL its carriers, tables and statics
    (never the empty fallback of `traegerD`), and the lowered predicate reads no other carrier. -/
theorem lowerAllg_traeger (u : UProg) (P : Programm (declOf u)) (fs : List (declOf u).Fn)
    (h : lowerAllg u = .ok (P, fs)) (i : Fin u.invs.length) :
    (declOf u).traeger i = invTraeger u i ∧
      ∀ c ∈ (P.invariante i).orte, c ∈ (declOf u).traeger i := by
  unfold lowerAllg at h
  split at h
  next e hI => cases h
  next x hI =>
    split at h
    · cases h
    · split at h
      · obtain ⟨rfl, -⟩ := Measures.checkedProgram_eq h
        have wI : ∀ j : Fin u.invs.length, ∃ v, lowerInvAt u j = .ok v := fun j =>
          lowerInvs_all_ok u (List.finRange u.invs.length) j (List.mem_finRange j) hI
        dsimp only [progOfFn]
        exact ⟨traegerD_of_ok u i (lowerInvGut_facts u i (wI i)).1,
          fun c hc => lowerInvGut_orte u i (wI i) c hc⟩
      · cases h

end Gabbro.Grammatik.Parser.UebersetzeAllg2
