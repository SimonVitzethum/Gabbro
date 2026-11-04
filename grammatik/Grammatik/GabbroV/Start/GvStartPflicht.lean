module

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
public import Grammatik.GabbroV.Start.GvStartPflichta
import all Init.Data.Repr
@[expose] public section


namespace Gabbro.Grammatik.GabbroV

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Grammatik.Parser.UebersetzeAllg2
  Gabbro.Grammatik.Zielsatz
/-- **The per-field test is sound** (`sp0FeldOkB_klingt`): from
    `sp0FeldOkB u t f = true` the field is a `bool` field or carries a range
    holding `0`. The goal is a `Prop`, so the `Bool` tests split without any
    large elimination. -/
theorem sp0FeldOkB_klingt (u : UProg) (t : Fin u.tabs.length)
    (f : Fin (fieldCount u t)) (h : sp0FeldOkB u t f = true) :
    boolFeldAt u t f = true ∨
      ∃ w, fieldRangeO u t f = some w ∧ w.1 ≤ 0 ∧ 0 ≤ w.2 := by
  unfold sp0FeldOkB at h
  cases hqe : (tabAt u t).cols[f.val]? with
  | none =>
    simp only [hqe, Bool.false_eq_true] at h
  | some q =>
    rw [hqe] at h
    change ((tabAt u t).bools.contains q.1 ||
      decide (q.2.1 ≤ 0 ∧ 0 ≤ q.2.2)) = true at h
    rw [Bool.or_eq_true] at h
    cases h with
    | inl hc => exact Or.inl (by unfold boolFeldAt; rw [hqe]; exact hc)
    | inr hd =>
      have hbd := of_decide_eq_true hd
      exact Or.inr ⟨q.2, by unfold fieldRangeO; rw [hqe]; rfl, hbd.1, hbd.2⟩

/-- **The decider is sound** (`sp0OkB_klingt`): from `sp0OkB u = true` every
    field is a `bool` field or carries a range holding `0`. Assembly only over
    the accepted lookups; every premise is used. -/
theorem sp0OkB_klingt (u : UProg) (h : sp0OkB u = true) : Sp0Ok u := by
  intro t f
  have h := sp0OkB_tab u h
  unfold sp0TabOkB at h
  have ht := (List.all_eq_true.mp h) t (List.mem_finRange t)
  have hf := (List.all_eq_true.mp ht) f (List.mem_finRange f)
  exact sp0FeldOkB_klingt u t f ((Bool.and_eq_true _ _).mp hf).1

/-- **Per-field evidence from the decider** (`sp0FeldOkB_of`): `sp0OkB u = true`
    gives every field test. Assembly only; every premise is used. -/
theorem sp0FeldOkB_of (u : UProg) (h : sp0OkB u = true) (t : Fin u.tabs.length)
    (f : Fin (fieldCount u t)) : sp0FeldOkB u t f = true := by
  have h := sp0OkB_tab u h
  unfold sp0TabOkB at h
  have ht := (List.all_eq_true.mp h) t (List.mem_finRange t)
  exact ((Bool.and_eq_true _ _).mp ((List.all_eq_true.mp ht) f (List.mem_finRange f))).1

/-- **The aggregate test from the decider** (`sp0WertOkB_of`). -/
theorem sp0WertOkB_of (u : UProg) (h : sp0OkB u = true) (t : Fin u.tabs.length)
    (f : Fin (fieldCount u t)) : sp0WertOkB u t f = true := by
  have h := sp0OkB_tab u h
  unfold sp0TabOkB at h
  have ht := (List.all_eq_true.mp h) t (List.mem_finRange t)
  exact ((Bool.and_eq_true _ _).mp ((List.all_eq_true.mp ht) f (List.mem_finRange f))).2

/-- **The computed initial memory** (`sp0Of`): slots at zero through `sp0FeldWert`, statics at their
    initialisers through `sp0GlobWert`. This is the Lean side of the exporter's `gSp0`: the loader
    establishes exactly this memory (`Laufzeit.lader`). -/
def sp0Of (u : UProg) (h : sp0OkB u = true) : Speicher (declOf u) where
  slots := fun t _ f => sp0FeldWert u t f (sp0FeldOkB_of u h t f) (sp0WertOkB_of u h t f)
  globs := fun g => sp0GlobWert u g (sp0OkB_glob u h g)

/-- **No zero memory where a range misses zero** (`sp0_luecke`): a non-`bool`
    field whose recorded range holds no `0` refutes `Sp0Ok` -- the Lean side of
    the exporter's `check_sp0` refusal (`LG003`: "has no `sp0` form",
    `crates/gabbro-check/src/lean_g.rs` line 3727). Every premise is used:
    `hb` kills the `bool` case, `hr` fixes the range, `hmiss` with the bounds
    closes by `omega`. -/
theorem sp0_luecke (u : UProg) (t : Fin u.tabs.length) (f : Fin (fieldCount u t))
    (hb : boolFeldAt u t f = false) (w : Int × Int) (hr : fieldRangeO u t f = some w)
    (hmiss : w.1 > 0 ∨ 0 > w.2) : ¬ Sp0Ok u := by
  intro h
  cases h t f with
  | inl hbT =>
    rw [hbT] at hb
    cases hb
  | inr hw =>
    obtain ⟨w', hr', h1, h2⟩ := hw
    rw [hr] at hr'
    cases hr'
    cases hmiss with
    | inl hm => omega
    | inr hm => omega

/-- **The decider refuses where no zero memory exists** (`sp0_lueckeB`): the
    checkable form of `sp0_luecke` -- where a recorded range misses zero the
    decider answers `false` (contrapositive of `sp0OkB_klingt`). Every premise
    is used through `sp0_luecke`. -/
theorem sp0_lueckeB (u : UProg) (t : Fin u.tabs.length) (f : Fin (fieldCount u t))
    (hb : boolFeldAt u t f = false) (w : Int × Int) (hr : fieldRangeO u t f = some w)
    (hmiss : w.1 > 0 ∨ 0 > w.2) : sp0OkB u = false := by
  by_cases hok : sp0OkB u = true
  · exact absurd (sp0OkB_klingt u hok) (sp0_luecke u t f hb w hr hmiss)
  · exact Bool.eq_false_iff.mpr hok

/-- **A static starts at its initialiser** (`sp0Of_glob`): by definition of the computed memory. -/
theorem sp0Of_glob (u : UProg) (h : sp0OkB u = true) (g : Fin u.globs.length) :
    (sp0Of u h).globs g = sp0GlobWert u g (sp0OkB_glob u h g) := by rfl

/-! ## Static initialisers -/

/-- **An out-of-range initialiser has no initial memory** (`sp0_glob_luecke`): the `LG003` arm of the
    exporter (`lean_g.rs` `read_static`), the Lean side of the refusal. Every premise is used: `hty` fixes
    the range, `hmiss` with the bounds closes by `omega`. -/
theorem sp0_glob_luecke (u : UProg) (g : Fin u.globs.length) (lo hi : Int)
    (hty : (globAt u g).ty = .int lo hi)
    (hmiss : (globAt u g).init < lo ∨ hi < (globAt u g).init) : sp0OkB u = false := by
  by_cases hok : sp0OkB u = true
  · have hg := sp0OkB_glob u hok g
    unfold sp0GlobOkB at hg
    rw [hty] at hg
    have hb := of_decide_eq_true hg
    cases hmiss with
    | inl hm => omega
    | inr hm => omega
  · exact Bool.eq_false_iff.mpr hok

/-! ## The bridge: `StartPflicht` from lowering plus zero memory -/

/-- **Without `requires` predicates the parser's lowering writes no `requires`** (`gv_lowerAllg_requires`):
    `progOfFn` sets `requires f := .tru` for every function whose `needs` is empty (`reqOf_leer`) --
    mirror of the accepted `bruecke` S4 lemma over the same definition (no
    interpreter duplicated). -/
theorem gv_lowerAllg_requires (u : UProg) (P : Programm (declOf u))
    (fs : List (declOf u).Fn) (h : lowerAllg u = .ok (P, fs)) (hn : ∀ g ∈ u.fns, g.needs = []) :
    ∀ f, P.requires f = .tru := by
  unfold lowerAllg at h
  split at h
  · cases h
  split at h
  · cases h
  · split at h
    · obtain ⟨rfl, -⟩ := Gabbro.Grammatik.Parser.Measures.checkedProgram_eq h
      intro f
      dsimp only [progOfFn]
      exact reqOf_leer u _ f (hn _ (List.get_mem u.fns f))
    · cases h

/-- **The start duty without `Initially`** (`gv_startPflicht`): for every
    declaration of the parser fragment, lowering-ok plus the decided
    zero-initialisation give `StartPflicht` over the computed memory `sp0Of` --
    no well-typedness assumption is taken. `hSp0` is statement-load-bearing
    (without it `sp0Of` cannot even be formed; `sp0_lueckeB` shows where it
    fails), `hsp0` pins the unit's declared memory to the computed one, and
    every other premise is rewritten in the proof. -/
theorem gv_startPflicht (u : UProg) (P : Programm (declOf u))
    (fs : List (declOf u).Fn) (hlow : lowerAllg u = .ok (P, fs))
    (hSp0 : sp0OkB u = true) (E : Einheit (declOf u))
    (hP : E.P = P) (hS : E.S = SperrInv.leer _) (hsp0 : E.sp0 = sp0Of u hSp0)
    (hn : ∀ g ∈ u.fns, g.needs = []) :
    StartPflicht E := by
  constructor
  · intro L
    rw [hS, hsp0]
    rfl
  · intro a _
    unfold ReqAmEintritt
    rw [hP, gv_lowerAllg_requires u P fs hlow hn]
    rfl

/-! ## The joint witness -/

/-- **A unit with a static** (`beispiele/187`): `static mut ANHALTEN : bool = false;`, a writer and a reader. -/
def uStatik : UProg :=
  { tabs := [], locks := [],
    fns := [{ name := "halte", params := [], kinds := [], res := none, held := [], puts := [],
              gputs := ["ANHALTEN"], gives := [], body := [.assignGlobB "ANHALTEN" .tru], ret := .empty },
            { name := "gehalten", params := [], kinds := [], res := none, resBool := true, held := [],
              puts := [], gives := [], body := [], ret := .bool (.globB "ANHALTEN") }],
    globs := [{ name := "ANHALTEN", ty := .bool, init := 0, var := true }] }

/-- The lowering accepts the unit. -/
def lowOk (u : UProg) : Bool :=
  match lowerAllg u with
  | .ok _ => true
  | .error _ => false

/-- **Joint witness for the bridge** (`gv_startPflicht_zeuge`): all premises jointly on non-degenerate
    fixtures -- the decider accepts the array unit `uExp104` (`Konto` count 2, `stand` in `0 .. 100`,
    `einzahlen` writes `Konto`) and the static unit `uStatik` (its `bool` static starts at `false`, the
    lowering accepts the writer and the reader), and an initialiser outside its range has no memory. -/
theorem gv_startPflicht_zeuge :
    sp0OkB uExp104 = true ∧
    (declOf uExp104).count ⟨0, by decide⟩ = 2 ∧
    writesAt uExp104 (fnAt uExp104 ⟨0, by decide⟩) ⟨0, by decide⟩ = true ∧
    sp0OkB uStatik = true ∧
    lowOk uStatik = true ∧
    (sp0Of uStatik (by decide)).globs ⟨0, by decide⟩ = (false : Wert (declOf uStatik) Ty.bool) ∧
    sp0OkB { uStatik with globs := [{ name := "N", ty := .int 0 9, init := 10 }] } = false :=
  ⟨by decide, by decide, by decide, by decide, by decide +kernel, rfl, by decide⟩

end Gabbro.Grammatik.GabbroV
/- CUTS: PROVED here -- `Sp0Ok` with its decider (`sp0OkB` over the per-field
    test `sp0FeldOkB`, sound by `sp0OkB_klingt`/`sp0FeldOkB_klingt`); the computed
    zero memory (`sp0FeldWert` from the very `Bool` tests, `sp0FeldOkB_of`,
    `sp0Of`); the obstructions (`sp0_luecke`, checkable as `sp0_lueckeB`);
    the static memory (`sp0GlobWert`, `sp0Of_glob`, refusal `sp0_glob_luecke`); the bridge (`gv_lowerAllg_requires`,
    `gv_startPflicht`: `StartPflicht` from lowering plus `sp0OkB`, no
    `Initially`); the joint non-degenerate witness (`gv_startPflicht_zeuge`
    on `uExp104` and the static unit `uStatik`).
    NOT covered: `tagged` (`Sum`) statics (exporter `read_static`'s third arm); the `Body`-side
    `Initially` (`WF shapeOf`) transfer, which needs `programmlogik/` compiled
    in context (the `bruecke/` project, out of this file's scope -- its S4
    already closes the shape half for 104/108). Full `./lean-bau`: exit 0,
    0 errors, 723 jobs, module built. -/
#print axioms Gabbro.Grammatik.GabbroV.Sp0Ok
#print axioms Gabbro.Grammatik.GabbroV.sp0_luecke
#print axioms Gabbro.Grammatik.GabbroV.sp0FeldOkB_klingt
#print axioms Gabbro.Grammatik.GabbroV.sp0OkB_klingt
#print axioms Gabbro.Grammatik.GabbroV.sp0FeldWert
#print axioms Gabbro.Grammatik.GabbroV.sp0FeldOkB_of
#print axioms Gabbro.Grammatik.GabbroV.sp0Of
#print axioms Gabbro.Grammatik.GabbroV.sp0_lueckeB
#print axioms Gabbro.Grammatik.GabbroV.sp0_glob_luecke
#print axioms Gabbro.Grammatik.GabbroV.gv_lowerAllg_requires
#print axioms Gabbro.Grammatik.GabbroV.gv_startPflicht
#print axioms Gabbro.Grammatik.GabbroV.gv_startPflicht_zeuge
