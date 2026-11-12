module
public import Grammatik.Parser.Elab.Export.ExportControl
public import Grammatik.Parser.Elab.UebersetzeAllg3.Memo
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
public import Grammatik.Parser.Elab.Generic.Signatures
public import Grammatik.Parser.Elab.UebersetzeAllg3.Guest.Contracts
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

/-! ## Pointer-interface contracts (C06, O43)

  `lowerPtrAt` mirrors `lowerFnPlain`'s contract part in the head's own
  context: the `needs` as the pre, the `gives` as the post (with the result
  context), so the lowered `CallContract` states exactly what the source
  type wrote. Out-of-range numbers carry the trivial contract (like
  `dummySig`, whose head has empty `needs`/`gives`). -/

/-- The parameter context of the head behind signature number `n`. -/
def ptrCtxOf (u : UProg) (n : Nat) : Ctx :=
  (sigAt u n).params

/-- The held resources of a pointer interface: the signature beginning. -/
def ptrResOf (u : UProg) (n : Nat) : List (Res (declOf u)) :=
  Signatur.anfang (declOf u) (sigAt u n)

/-- The result type behind `n` read off the head: for a live number the
    head's `ergTy`, else `none` (like `dummySig`). -/
theorem ptrErg_eq (u : UProg) (n : Nat) :
    (sigFnAt u n).ergTy = (sigAt u n).erg := by
  unfold sigFnAt sigAt
  by_cases h : n < (sigFns u).length
  · simp only [dite_eq_left h, mkSig]
  · simp only [dite_eq_right h, dummySig, UFn.ergTy] <;> rfl

/-- One pointer interface, lowered: its `needs` as the pre, its `gives` as
    the post, mirroring `lowerFnPlain`'s contract part. -/
def lowerPtrAt (u : UProg) (n : Nat) :
    Except String (CallContract (declOf u) ((declOf u).sigNr n)) :=
  match lowEnsList u (ptrCtxOf u n) (ptrResOf u n) (sigFnAt u n) none
      (sigFnAt u n).needs with
  | .error e => .error e
  | .ok r0 =>
  match lowEnsList u (ErgCtx (ptrCtxOf u n) ((sigAt u n).erg)) (Vertrag.vonSig (declOf u) ((declOf u).sigNr n)).ende
      (sigFnAt u n) ((sigFnAt u n).ergTy) (sigFnAt u n).gives with
  | .error e => .error e
  | .ok e0 =>
    have r1 : Expr (declOf u) ((declOf u).sigNr n).params
        (Signatur.anfang (declOf u) ((declOf u).sigNr n)) .bool := r0
    have e1 : Expr (declOf u)
        (ErgCtx ((declOf u).sigNr n).params ((declOf u).sigNr n).erg)
        (Vertrag.vonSig (declOf u) ((declOf u).sigNr n)).ende .bool := e0
    .ok { pre := r1, post := e1 }

/-- Per-pair conformance gate (C06, O43): every admitted function-to-signature
    pair also passes contract inclusion. Since `passtAt` conjoins
    `vertragPasstAt`, this holds wherever `passtAt` holds; it replaces the
    former whole-unit `ptrVertragGebunden` refusal below: a nontrivial pointer
    contract is lowered, and only a non-conforming pair is refused, at its
    value site (`bindFnref`). -/
def ptrPaarGate (u : UProg) : Bool :=
  (List.finRange u.fns.length).all fun f =>
    (List.range (sigFns u).length).all fun n =>
      !(passtAt u f n) || vertragPasstAt u f n

/-- **The pair gate never refuses**: conformance (`passtAt`) already contains the contract part. -/
theorem ptrPaarGate_wahr (u : UProg) : ptrPaarGate u = true := by
  apply List.all_eq_true.mpr
  intro f _
  apply List.all_eq_true.mpr
  intro n _
  unfold passtAt
  cases vertragPasstAt u f n with
  | false => simp only [Bool.and_false, Bool.not_false, Bool.or_false]
  | true => simp only [Bool.or_true]

/-- The constant answer of the pair gate, for compiled code. -/
def ptrPaarGateSchnell (_ : UProg) : Bool := true

/-- Compiled code does not walk the pairs. -/
@[csimp] theorem ptrPaarGate_eq_schnell : @ptrPaarGate = @ptrPaarGateSchnell := by
  funext u
  exact ptrPaarGate_wahr u

/-- Every pointer contract lowers (no silent `trivial`). -/
def ptrLowerOk (u : UProg) : Bool :=
  (List.range (sigFns u).length).all fun n => (lowerPtrAt u n).isOk

/-- The shared contract gate: pointer conformance and exact lowering of all pointer and foreign contracts. -/
def contractGate (u : UProg) : Bool :=
  ptrPaarGate u && ptrLowerOk u && axContractsB u

/-- The lowered pointer contract, or `trivial` where lowering failed (the
    gate `contractGate` refuses such units, so the fallback never silences a bad
    contract). -/
def ptrVertragOf (u : UProg) (n : Nat) :
    CallContract (declOf u) ((declOf u).sigNr n) :=
  (lowerPtrAt u n).toOption.getD (CallContract.trivial (declOf u) ((declOf u).sigNr n))

/-- Assemble functions with their lowered pre/postconditions and both interface contract families. -/
def progOfFn (u : UProg) (E : ∀ f : Fin u.fns.length, EnsTy u f)
    (B : ∀ f : Fin u.fns.length, RumpTy u f) (R : ∀ f : Fin u.fns.length, ReqTy u f)
    (I : ∀ i : Fin u.invs.length, InvTy u i)
    (Pt : ∀ n, CallContract (declOf u) ((declOf u).sigNr n))
    (Ax : ∀ a, CallContract (declOf u) ((declOf u).asignatur a)) :
    Programm (declOf u) where
  invariante := I
  requires := fun f => reqOf u R f
  ensures := fun f => E f
  rumpf := fun f => B f
  unterbricht := fun f => u.hands.any (fun n => strEq n (fnAt u f).name)
  ptrVertrag := Pt
  axVertrag := Ax

/-- The same program with each function's postcondition, body and precondition evaluated once
    into a table: every later access reads the table instead of elaborating the function again. -/
def progOfFnSchnell (u : UProg) (E : ∀ f : Fin u.fns.length, EnsTy u f)
    (B : ∀ f : Fin u.fns.length, RumpTy u f) (R : ∀ f : Fin u.fns.length, ReqTy u f)
    (I : ∀ i : Fin u.invs.length, InvTy u i)
    (Pt : ∀ n, CallContract (declOf u) ((declOf u).sigNr n))
    (Ax : ∀ a, CallContract (declOf u) ((declOf u).asignatur a)) :
    Programm (declOf u) :=
  let table := Memo.build (T := fun f : Fin u.fns.length => EnsTy u f × RumpTy u f × ReqTy u f)
    fun f => (E f, B f, R f)
  progOfFn u (fun f => (table.get f).1) (fun f => (table.get f).2.1) (fun f => (table.get f).2.2) I Pt Ax

/-- **The table changes no program.** -/
@[csimp] theorem progOfFn_eq_schnell : @progOfFn = @progOfFnSchnell := by
  funext u E B R I Pt Ax
  simp only [progOfFnSchnell, Memo.build_get]

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
    `PtrVerfeinert` in `LogikPflicht`). SUPERSEDED (C06, O43): `lowerAllg`
    now lowers every pointer contract (`lowerPtrAt`) under the per-pair gate
    `contractGate`; this whole-unit emptiness check is kept only for reference and
    is no longer consulted. -/
def ptrVertragGebunden (u : UProg) : Bool :=
  u.ptrs.all fun p => p.needs.isEmpty && p.gives.isEmpty

/-- The generically lowered program: every function of the
    elaborated program over the declaration built from it, with every
    pointer-interface contract lowered (`lowerPtrAt`) under the per-pair gate
    `contractGate` (a non-conforming pair is refused at its value site). -/
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
    if hC : contractGate u then
    have hAx : axContractsB u = true := (Bool.and_eq_true_iff.mp hC).2
    have w : ∀ f : Fin u.fns.length,
        ∃ v, lowerFnAt u f = .ok v := fun f =>
      lowerEach_all_ok u (List.finRange u.fns.length) f
        (List.mem_finRange f) h
    Measures.checkedProgram u (progOfFn u (fun f => (lowerAtPair u f (w f)).1)
      (fun f => (lowerAtPair u f (w f)).2.1) (fun f => (lowerAtPair u f (w f)).2.2)
      (fun i => lowerInvGut u i (wI i)) (fun n => ptrVertragOf u n) (fun a => axVertragOf u a hAx))
    else .error "function does not conform to the pointer type"

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
