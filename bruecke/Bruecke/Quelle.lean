module
public import Grammatik.Parser.Elab.UebersetzePipeline
public import Bruecke.Pruefung
public import Bruecke.Start
public import Grammatik.Zielsatz.Atomar.BeweisAtomar
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
@[expose] public section


/-!
# Source elaboration and the initial unit

`uOf` ties a duty to the Lean front end's actual output. `einheitAllg` equips that output
with the empty lock invariant, trivial hardware contract, declared entry roots and checked
initial memory. The consolidated source endpoints live in `Kette/Quelle.lean`.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

instance (u : UProg) : DecidableEq (declOf u).Fn := inferInstanceAs (DecidableEq (Fin u.fns.length))

/-- A unit without statics has no atomic global. -/
theorem declOf_kein_atomar (u : UProg) (h : u.globs = []) :
    ∀ g : (declOf u).Glob, (declOf u).atomar g = false := fun g => by
  have h1 : g.val < u.globs.length := g.isLt
  have h2 : u.globs.length = 0 := by rw [h] <;> rfl
  omega

/-- The elaborated program of a source text, if the Lean front end accepts it. -/
def uOf (src : String) : Option UProg :=
  match uebersetzeAllg src with
  | .ok ⟨u, _, _⟩ => some u
  | .error _ => none

/-- Initial values are validated even for a hand-built UProg, independently of elaboration. -/
def initialStaticsB (u : UProg) : Bool := u.globs.all fun g =>
  match g.ty with
  | .int lo hi => decide (lo ≤ g.init ∧ g.init ≤ hi)
  | .bool | .wert _ => false

/-- Zero-initialized numeric table fields and valid, non-atomic numeric static initializers. -/
def nullB (u : UProg) : Bool :=
  (staticsB u && initialStaticsB u) && u.tabs.all fun t => t.opts.isEmpty && t.werte.isEmpty &&
    t.cols.all fun f => decide (f.2.1 ≤ 0) && decide (0 ≤ f.2.2)

theorem nullB_statics {u : UProg} (h : nullB u = true) : NumericStatics u :=
  staticsB_ok (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1

theorem initial_bereich {u : UProg} (h : nullB u = true) (g : Fin u.globs.length)
    (lo hi : Int) (ht : (globAt u g).ty = .int lo hi) :
    lo ≤ (globAt u g).init ∧ (globAt u g).init ≤ hi := by
  have hb : initialStaticsB u = true := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
  have hg := List.all_eq_true.mp hb (globAt u g) (List.get_mem _ _)
  simp only [ht, decide_eq_true_eq] at hg
  exact hg

/-- Numeric statics admitted by this bridge are ordinary world state, never atomics. -/
theorem declOf_numeric_kein_atomar (u : UProg) (h : NumericStatics u) :
    ∀ g : (declOf u).Glob, (declOf u).atomar g = false := by
  intro g
  obtain ⟨_, _, _, ha⟩ := h g
  exact ha

theorem nullB_tab {u : UProg} (h : nullB u = true) (t : Fin u.tabs.length) :
    (tabAt u t).opts = [] ∧ (tabAt u t).werte = [] := by
  simp only [nullB, Bool.and_eq_true, List.all_eq_true] at h
  have := (h.2 _ (List.get_mem _ _ : tabAt u t ∈ u.tabs)).1
  exact ⟨List.isEmpty_iff.mp this.1, List.isEmpty_iff.mp this.2⟩

theorem null_bereich {u : UProg} (h : nullB u = true) (t : Fin u.tabs.length)
    (f : Fin (fieldCount u t)) (w : Int × Int) (hw : fieldRangeO u t f = some w) :
    w.1 ≤ 0 ∧ 0 ≤ w.2 := by
  unfold fieldRangeO at hw
  cases hf : (tabAt u t).cols[f.val]? with
  | none => rw [hf] at hw; simp at hw
  | some e =>
    rw [hf] at hw
    simp only [Option.map_some, Option.some.injEq] at hw
    subst hw
    have hte : tabAt u t ∈ u.tabs := List.get_mem _ _
    have hfe : e ∈ (tabAt u t).cols := List.mem_of_getElem? hf
    simp only [nullB, Bool.and_eq_true, List.all_eq_true] at h
    have h2 := (h.2 _ hte).2 _ hfe
    simpa using h2

/-- The declaration's initial memory: zero table fields and the recorded static initializers. -/
def nullSp (u : UProg) (h : nullB u = true) : Speicher (declOf u) where
  slots := fun t _ f => by
    show Wert (declOf u) (typAt u t f)
    unfold typAt
    by_cases hbf : boolFeldAt u t f = true
    · rw [if_pos hbf]
      exact (false : Bool)
    · rw [if_neg hbf]
      have hp := nullB_tab h t
      have ho : optFeldAt u t f = none := by
        unfold optFeldAt optNumAt; rw [hp.1]; split <;> rfl
      have hw' : wertFeldAt u t f = none := by
        unfold wertFeldAt; rw [hp.2]; split <;> rfl
      rw [ho, hw']
      cases hw : fieldRangeO u t f with
      | none => exact (⟨0, Int.le_refl _, Int.le_refl _⟩ : Zahl 0 0)
      | some w =>
        have := null_bereich h t f w hw
        exact (⟨0, this.1, this.2⟩ : Zahl w.1 w.2)
  globs := fun g => by
    change Wert (declOf u) (globAt u g).ty.toTy
    cases ht : (globAt u g).ty with
    | int lo hi =>
      exact (⟨(globAt u g).init, (initial_bereich h g lo hi ht).1,
        (initial_bereich h g lo hi ht).2⟩ : Zahl lo hi)
    | bool =>
      exfalso
      obtain ⟨_, _, hn, _⟩ := nullB_statics h g
      rw [ht] at hn
      cases hn
    | wert ty =>
      exfalso
      obtain ⟨_, _, hn, _⟩ := nullB_statics h g
      rw [ht] at hn
      cases hn

/-- The declared thread roots of a unit: the dispatch targets of its `entry` items, each a
    parameterless function (the front end refuses any other), started with the empty environment. -/
def startsAllg (u : UProg) : List (Σ w : (declOf u).Fn, Env (declOf u) ((declOf u).params w)) :=
  u.roots.filterMap fun n =>
    match fnIdx u.fns n with
    | .error _ => none
    | .ok i =>
      if h : (declOf u).params i = [] then some ⟨i, by rw [h]; exact Env.nil⟩ else none

/-- The unit of a source the front end accepts: the parsed program, no lock invariant, the
    trivial axiom ensures, the starts of its `entry` items and the declared initial memory. -/
def einheitAllg (u : UProg) (P : Programm (declOf u)) (h : nullB u = true) : Zielsatz.Einheit (declOf u) where
  P := P
  S := SperrInv.leer (declOf u)
  Q := axWahr (declOf u)
  starts := startsAllg u
  sp0 := nullSp u h

/-- The lowering is the last stage of the front end. -/
theorem lower_of_uebersetze {src : String} {u : UProg} {P : Programm (declOf u)}
    {fs : List (declOf u).Fn} (h : uebersetzeAllg src = .ok ⟨u, P, fs⟩) :
    lowerAllg u = .ok (P, fs) := by
  unfold uebersetzeAllg at h
  cases hl : Parser.lex src with
  | error e => simp [hl] at h
  | ok toks =>
    simp only [hl] at h
    cases hp : Parser.parseTopTief toks with
    | error e => simp [hp] at h
    | ok items =>
      simp only [hp] at h
      cases he : elabU (pre108 items) with
      | error e => simp [he] at h
      | ok u' =>
        simp only [he] at h
        cases hw : lowerAllg u' with
        | error e => simp [hw] at h
        | ok r =>
          obtain ⟨P', fs'⟩ := r
          simp only [hw, Except.ok.injEq] at h
          injection h with h1 h2
          subst h1
          have h3 := eq_of_heq h2
          injection h3 with h4 h5
          subst h4 h5
          exact hw

theorem uOf_eq {src : String} {u : UProg} {P : Programm (declOf u)} {fs : List (declOf u).Fn}
    (h : uebersetzeAllg src = .ok ⟨u, P, fs⟩) : uOf src = some u := by
  unfold uOf
  rw [h]


/-- The enumeration of the functions of a generically lowered unit. -/
def aufzFn (u : UProg) : Zielsatz.Aufzaehlung (declOf u).Fn := ⟨List.finRange u.fns.length, List.mem_finRange⟩

/-- The enumeration of the locks. -/
def aufzLock (u : UProg) : Zielsatz.Aufzaehlung (declOf u).Lock := ⟨List.finRange u.locks.length, List.mem_finRange⟩

/-- The enumeration of the carriers of a unit with no tables and no globals: none. -/
def aufzTraegerLeer (u : UProg) (ht : u.tabs = []) (hg : u.globs = []) :
    Zielsatz.Aufzaehlung ((declOf u).Tab ⊕ (declOf u).Glob) :=
  ⟨[], fun c => match c with
    | .inl t => absurd (t : Fin u.tabs.length).isLt (by simp [ht])
    | .inr g => absurd (g : Fin u.globs.length).isLt (by simp [hg])⟩

end Gabbro.Bruecke
