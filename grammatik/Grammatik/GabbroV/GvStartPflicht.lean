/-
  File:      Grammatik/GabbroV/GvStartPflicht.lean
  Subject:   GabbroV bridge: `StartPflicht` without the `Initially` assumption (lane 1387).

  GabbroV duty files assume `Initially s0` (well-typed initial world, every
  invariant holds; `programmlogik/Duty/Duty104Referenz.lean`), while the goal
  theorem's premise (b) `StartPflicht E` is a duty of the user over the
  DECLARED initial memory `E.sp0`. This module computes that memory from the
  SOURCE in Lean and discharges the assumption by the declarations:
  * fragment slots are zero-initialised (`sp0Of`, the Lean side of the
    exporter's `gSp0` slot half, `crates/gabbro-check/src/lean_g.rs`);
    `Sp0Ok` (decided by `sp0OkB`) says every range holds zero;
  * a declared `static` starts at its initialiser (`sp0GlobWert`, the Lean
    side of `GInit`); an initialiser outside its type has no value (the
    `check_sp0` refusal, `sp0GlobOkB`).
  The exact classes where no initial memory exists are proved (`sp0_luecke`),
  not just stated. Reuses the accepted
  definitions of `Zielsatz/`, `Semantik` and `Parser/` unchanged; no new
  interpreter, no import from `programmlogik/`.
-/
import Grammatik.Parser.Elab.Uebersetze
import Grammatik.Parser.Elab.UebersetzeAllg
import Grammatik.Parser.Elab.UebersetzeAllg3
import Grammatik.Kern.Syntax.Typen
import Grammatik.Kern.Syntax.Syntax
import Grammatik.Kern.Semantik.Semantik
import Grammatik.Kern.Semantik.Maschine
import Grammatik.Logik.Vertraege.VertragOrtB
import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem
import Grammatik.Zielsatz.Kern.Spec
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmenBeweis

namespace Gabbro.Grammatik.GabbroV

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
  Gabbro.Grammatik.Zielsatz

/-- **Zero holds at every slot** (`Sp0Ok`): every field of every table of the
    elaborated unit is a `bool` field (zero is `false`) or an integer field
    whose recorded range holds `0`. This is the Lean side of the exporter's
    `check_sp0` (`crates/gabbro-check/src/lean_g.rs`): a range holding no
    zero has no `sp0` value and is refused BY NAME. -/
def Sp0Ok (u : UProg) : Prop :=
  ∀ (t : Fin u.tabs.length) (f : Fin (fieldCount u t)),
    boolFeldAt u t f = true ∨
      ∃ w, fieldRangeO u t f = some w ∧ w.1 ≤ 0 ∧ 0 ≤ w.2

/-- **The per-field `Sp0Ok` test** (`sp0FeldOkB`): the field entry is present and
    is a `bool` field or its recorded range holds `0` (the `none` arm is
    unreachable through a live index, kept for totality). Values (`sp0FeldWert`)
    match on these very `Bool` tests, so the `Prop` evidence is only rewritten,
    never eliminated into a value (large elimination from `Or`/`Exists` into
    `Type` is refused by the kernel: `propRecLargeElim`). -/
def sp0FeldOkB (u : UProg) (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) : Bool :=
  match (tabAt u t).cols[f.val]? with
  | some q => (tabAt u t).bools.contains q.1 || decide (q.2.1 ≤ 0 ∧ 0 ≤ q.2.2)
  | none => false

/-- **The tables of the decider** (`sp0TabOkB`): the per-field test over every table and every field index
    (`List.finRange`, like `lowerAllg`'s own coverage). -/
def sp0TabOkB (u : UProg) : Bool :=
  (List.finRange u.tabs.length).all fun t =>
    (List.finRange (fieldCount u t)).all fun f => sp0FeldOkB u t f

/-- **A static holds its initialiser** (`sp0GlobOkB`): an integer static starts inside its range, a `bool`
    static at `0` or `1`. -/
def sp0GlobOkB (u : UProg) (g : Fin u.globs.length) : Bool :=
  match (globAt u g).ty with
  | .int lo hi => decide (lo ≤ (globAt u g).init ∧ (globAt u g).init ≤ hi)
  | .bool => (globAt u g).init == 0 || (globAt u g).init == 1

/-- **The `Sp0Ok` decider** (`sp0OkB`): every slot starts at zero and every static at its initialiser. -/
def sp0OkB (u : UProg) : Bool :=
  sp0TabOkB u && (List.finRange u.globs.length).all fun g => sp0GlobOkB u g

/-- The table half of the decider. -/
theorem sp0OkB_tab (u : UProg) (h : sp0OkB u = true) : sp0TabOkB u = true :=
  ((Bool.and_eq_true _ _).mp h).1

/-- The static half of the decider, at one static. -/
theorem sp0OkB_glob (u : UProg) (h : sp0OkB u = true) (g : Fin u.globs.length) :
    sp0GlobOkB u g = true :=
  (List.all_eq_true.mp ((Bool.and_eq_true _ _).mp h).2) g (List.mem_finRange g)

/-- **The initial value of a static** (`sp0GlobWert`): the declared numeral (inside its range by
    `sp0GlobOkB`), or the truth value `init = 1`. -/
def sp0GlobWert (u : UProg) (g : Fin u.globs.length) (h : sp0GlobOkB u g = true) :
    Wert (declOf u) ((declOf u).gtyp g) :=
  match hq : (globAt u g).ty with
  | .int lo hi => by
      have hg : (declOf u).gtyp g = .int lo hi := by
        show (globAt u g).ty.toTy = _
        rw [hq]
        rfl
      rw [hg]
      have hc : decide (lo ≤ (globAt u g).init ∧ (globAt u g).init ≤ hi) = true := by
        unfold sp0GlobOkB at h
        rw [hq] at h
        exact h
      have hb := of_decide_eq_true hc
      exact ⟨(globAt u g).init, hb.1, hb.2⟩
  | .bool => by
      have hg : (declOf u).gtyp g = .bool := by
        show (globAt u g).ty.toTy = _
        rw [hq]
        rfl
      rw [hg]
      exact decide ((globAt u g).init = 1)

/-- **The zero value at one field** (`sp0FeldWert`): `false` at a `bool` field,
    `⟨0, _, _⟩` at an integer field whose range holds `0` -- the Lean side of
    the exporter's `gSp0` slot half (`crates/gabbro-check/src/lean_g.rs`
    lines 456-466: a slot starts at zero because no surface form names a slot
    initialiser). -/
def sp0FeldWert (u : UProg) (t : Fin u.tabs.length) (f : Fin (fieldCount u t))
    (h : sp0FeldOkB u t f = true) :
    Wert (declOf u) ((declOf u).typ t f) :=
  match hq : (tabAt u t).cols[f.val]? with
  | some q =>
    match hb : (tabAt u t).bools.contains q.1 with
    | true => by
        have ht : (declOf u).typ t f = .bool := by
          show typAt u t f = .bool
          exact typAt_bool u t f (by unfold boolFeldAt; rw [hq]; exact hb)
        rw [ht]
        exact false
    | false =>
      match hO : optFeldAt u t f with
      | some n => by
          have hbf : boolFeldAt u t f = false := by unfold boolFeldAt; rw [hq]; exact hb
          have ht : (declOf u).typ t f = .opt n := by
            show typAt u t f = .opt n
            exact typAt_opt u t f n hbf hO
          rw [ht]
          exact (none : Option (Zahl 0 (n - 1)))
      | none =>
        match hd : decide (q.2.1 ≤ 0 ∧ 0 ≤ q.2.2) with
        | true => by
            have hbd := of_decide_eq_true hd
            have ht : (declOf u).typ t f = .int q.2.1 q.2.2 := by
              show typAt u t f = .int q.2.1 q.2.2
              have hfr : fieldRangeO u t f = some q.2 := by unfold fieldRangeO; rw [hq]; rfl
              have hbf : boolFeldAt u t f = false := by unfold boolFeldAt; rw [hq]; exact hb
              exact typAt_of u t f q.2 hfr hbf hO
            rw [ht]
            exact ⟨0, hbd.1, hbd.2⟩
        | false => by
            have hcon : sp0FeldOkB u t f = false := by
              unfold sp0FeldOkB
              rw [hq]
              change ((tabAt u t).bools.contains q.1 ||
                decide (q.2.1 ≤ 0 ∧ 0 ≤ q.2.2)) = false
              rw [hb, hd]
              rfl
            rw [hcon] at h
            exact nomatch h
  | none => by
      have hcon : sp0FeldOkB u t f = false := by unfold sp0FeldOkB; rw [hq]
      rw [hcon] at h
      exact nomatch h

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
    simp [hqe] at h
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
  exact sp0FeldOkB_klingt u t f hf

/-- **Per-field evidence from the decider** (`sp0FeldOkB_of`): `sp0OkB u = true`
    gives every field test. Assembly only; every premise is used. -/
theorem sp0FeldOkB_of (u : UProg) (h : sp0OkB u = true) (t : Fin u.tabs.length)
    (f : Fin (fieldCount u t)) : sp0FeldOkB u t f = true := by
  have h := sp0OkB_tab u h
  unfold sp0TabOkB at h
  have ht := (List.all_eq_true.mp h) t (List.mem_finRange t)
  exact (List.all_eq_true.mp ht) f (List.mem_finRange f)

/-- **The computed initial memory** (`sp0Of`): slots at zero through `sp0FeldWert`, statics at their
    initialisers through `sp0GlobWert`. This is the Lean side of the exporter's `gSp0`: the loader
    establishes exactly this memory (`Laufzeit.lader`). -/
def sp0Of (u : UProg) (h : sp0OkB u = true) : Speicher (declOf u) where
  slots := fun t _ f => sp0FeldWert u t f (sp0FeldOkB_of u h t f)
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
    (sp0Of u h).globs g = sp0GlobWert u g (sp0OkB_glob u h g) := rfl

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
  · injection h with h1
    injection h1 with h2 h3
    subst h2
    intro f
    dsimp only [progOfFn]
    exact reqOf_leer u _ f (hn _ (List.get_mem u.fns f))

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
