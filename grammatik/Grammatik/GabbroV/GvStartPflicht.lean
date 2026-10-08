/-
  File:      Grammatik/X86/GvStartPflicht.lean
  Subject:   GabbroV bridge: `StartPflicht` without the `Initially` assumption (lane 1387).

  GabbroV duty files assume `Initially s0` (well-typed initial world, every
  invariant holds; `programmlogik/Duty/Duty104Referenz.lean`), while the goal
  theorem's premise (b) `StartPflicht E` is a duty of the user over the
  DECLARED initial memory `E.sp0`. This module computes that memory from the
  SOURCE in Lean and discharges the assumption by the declarations:
  * fragment slots are zero-initialised (`sp0Of`, the Lean side of the
    exporter's `gSp0` slot half, `crates/gabbro-check/src/lean_g.rs`);
    `Sp0Ok` (decided by `sp0OkB`) says every range holds zero;
  * declared `static` initialisers travel through `gvInitWert` (the Lean
    side of `GInit`); out-of-range has no value (the `check_sp0` refusal).
  The exact classes where no initial memory exists are proved (`sp0_luecke`,
  `gv_fragment_kein_static`), not just stated. Reuses the accepted
  definitions of `Zielsatz/`, `Semantik` and `Parser/` unchanged; no new
  interpreter, no import from `programmlogik/`.
-/
import Grammatik.Parser.Uebersetze
import Grammatik.Parser.UebersetzeAllg
import Grammatik.Parser.UebersetzeAllg2
import Grammatik.Kern.Syntax.Typen
import Grammatik.Kern.Syntax.Syntax
import Grammatik.Kern.Semantik.Semantik
import Grammatik.Kern.Semantik.Maschine
import Grammatik.Logik.Vertraege.VertragOrtB
import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem
import Grammatik.Zielsatz.Kern.Spec
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmenBeweis

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
  Gabbro.Grammatik.Zielsatz

/-- **Zero holds at every slot** (`Sp0Ok`): every field of every table of the
    elaborated unit is a `bool` field (zero is `false`) or an integer field
    whose recorded range holds `0`. This is the Lean side of the exporter's
    `check_sp0` (`crates/gabbro-check/src/lean_g.rs`): a range holding no
    zero has no `sp0` value and is refused BY NAME. -/
def Sp0Ok (u : UProg) : Prop :=
  ∀ (t : Fin u.tabellen.length) (f : Fin (fieldCount u t)),
    boolFeldAt u t f = true ∨
      ∃ w, fieldRangeO u t f = some w ∧ w.1 ≤ 0 ∧ 0 ≤ w.2

/-- **The per-field `Sp0Ok` test** (`sp0FeldOkB`): the field entry is present and
    is a `bool` field or its recorded range holds `0` (the `none` arm is
    unreachable through a live index, kept for totality). Values (`sp0FeldWert`)
    match on these very `Bool` tests, so the `Prop` evidence is only rewritten,
    never eliminated into a value (large elimination from `Or`/`Exists` into
    `Type` is refused by the kernel: `propRecLargeElim`). -/
def sp0FeldOkB (u : UProg) (t : Fin u.tabellen.length) (f : Fin (fieldCount u t)) : Bool :=
  match (tabAt u t).felder[f.val]? with
  | some q => (tabAt u t).bools.contains q.1 || decide (q.2.1 ≤ 0 ∧ 0 ≤ q.2.2)
  | none => false

/-- **The `Sp0Ok` decider** (`sp0OkB`): the per-field test over every table and
    every field index (`List.finRange`, like `lowerAllg`'s own coverage). -/
def sp0OkB (u : UProg) : Bool :=
  (List.finRange u.tabellen.length).all fun t =>
    (List.finRange (fieldCount u t)).all fun f => sp0FeldOkB u t f

/-- **The zero value at one field** (`sp0FeldWert`): `false` at a `bool` field,
    `⟨0, _, _⟩` at an integer field whose range holds `0` -- the Lean side of
    the exporter's `gSp0` slot half (`crates/gabbro-check/src/lean_g.rs`
    lines 456-466: a slot starts at zero because no surface form names a slot
    initialiser). -/
def sp0FeldWert (u : UProg) (t : Fin u.tabellen.length) (f : Fin (fieldCount u t))
    (h : sp0FeldOkB u t f = true) :
    Wert (declOf u) ((declOf u).typ t f) :=
  match hq : (tabAt u t).felder[f.val]? with
  | some q =>
    match hb : (tabAt u t).bools.contains q.1 with
    | true => by
        have ht : (declOf u).typ t f = .bool := by
          show typAt u t f = .bool
          exact typAt_bool u t f (by unfold boolFeldAt; rw [hq]; exact hb)
        rw [ht]
        exact false
    | false =>
      match hd : decide (q.2.1 ≤ 0 ∧ 0 ≤ q.2.2) with
      | true => by
          have hbd := of_decide_eq_true hd
          have ht : (declOf u).typ t f = .int q.2.1 q.2.2 := by
            show typAt u t f = .int q.2.1 q.2.2
            have hfr : fieldRangeO u t f = some q.2 := by unfold fieldRangeO; rw [hq]; rfl
            have hbf : boolFeldAt u t f = false := by unfold boolFeldAt; rw [hq]; exact hb
            exact typAt_of u t f q.2 hfr hbf
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
theorem sp0FeldOkB_klingt (u : UProg) (t : Fin u.tabellen.length)
    (f : Fin (fieldCount u t)) (h : sp0FeldOkB u t f = true) :
    boolFeldAt u t f = true ∨
      ∃ w, fieldRangeO u t f = some w ∧ w.1 ≤ 0 ∧ 0 ≤ w.2 := by
  unfold sp0FeldOkB at h
  cases hqe : (tabAt u t).felder[f.val]? with
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
  unfold sp0OkB at h
  have ht := (List.all_eq_true.mp h) t (List.mem_finRange t)
  have hf := (List.all_eq_true.mp ht) f (List.mem_finRange f)
  exact sp0FeldOkB_klingt u t f hf

/-- **Per-field evidence from the decider** (`sp0FeldOkB_of`): `sp0OkB u = true`
    gives every field test. Assembly only; every premise is used. -/
theorem sp0FeldOkB_of (u : UProg) (h : sp0OkB u = true) (t : Fin u.tabellen.length)
    (f : Fin (fieldCount u t)) : sp0FeldOkB u t f = true := by
  unfold sp0OkB at h
  have ht := (List.all_eq_true.mp h) t (List.mem_finRange t)
  exact (List.all_eq_true.mp ht) f (List.mem_finRange f)

/-- **The computed initial memory** (`sp0Of`): slots at zero through
    `sp0FeldWert`, no globals (`Glob = Empty`, so `nomatch`). This is the Lean
    side of the exporter's `gSp0`: the loader establishes exactly this memory
    (`Laufzeit.lader`). -/
def sp0Of (u : UProg) (h : sp0OkB u = true) : Speicher (declOf u) where
  slots := fun t _ f => sp0FeldWert u t f (sp0FeldOkB_of u h t f)
  globs := fun e => nomatch e

/-- **No zero memory where a range misses zero** (`sp0_luecke`): a non-`bool`
    field whose recorded range holds no `0` refutes `Sp0Ok` -- the Lean side of
    the exporter's `check_sp0` refusal (`LG003`: "has no `sp0` form",
    `crates/gabbro-check/src/lean_g.rs` line 3727). Every premise is used:
    `hb` kills the `bool` case, `hr` fixes the range, `hmiss` with the bounds
    closes by `omega`. -/
theorem sp0_luecke (u : UProg) (t : Fin u.tabellen.length) (f : Fin (fieldCount u t))
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
theorem sp0_lueckeB (u : UProg) (t : Fin u.tabellen.length) (f : Fin (fieldCount u t))
    (hb : boolFeldAt u t f = false) (w : Int × Int) (hr : fieldRangeO u t f = some w)
    (hmiss : w.1 > 0 ∨ 0 > w.2) : sp0OkB u = false := by
  by_cases hok : sp0OkB u = true
  · exact absurd (sp0OkB_klingt u hok) (sp0_luecke u t f hb w hr hmiss)
  · exact Bool.eq_false_iff.mpr hok

/-- **The parser's fragment elaborates no statics** (`gv_fragment_kein_static`):
    `declOf` sets `Glob := Empty`
    (`grammatik/Grammatik/Parser/UebersetzeAllg.lean` line 156). Measured fact:
    a `static` (with its declared initialiser) never reaches the fragment, so
    the fragment's whole initial memory is the zero memory `sp0Of`; static
    initialisers live exporter-side (`gvInitWert`). Agent 02 may widen what is
    elaborated; `Parser/` is untouched. -/
theorem gv_fragment_kein_static (u : UProg) : (declOf u).Glob = Empty := rfl

/-! ## Static initialisers: the Lean side of `GInit` -/

/-- **Declared initialiser forms** (`GvInit`): a numeral or `true`/`false` -- the
    two spellings `read_static` accepts (`crates/gabbro-check/src/lean_g.rs`
    lines 1988-2014: `Bool` takes `Wahr`/`Falsch`, `Int` takes a numeral in
    range, anything else is `LG003`). `tagged` (`Sum`) initialisers are NOT
    modelled here (open, see CUTS). -/
inductive GvInit : Type
  | int : Int → GvInit
  | bool : Bool → GvInit

/-- **The initialiser travels** (`gvInitWert`): the Lean side of `GInit`
    (`lean_g.rs` lines 460-466). An in-range numeral becomes the value, a
    `bool` spelling becomes itself; a mismatch or an out-of-range numeral has
    no value (`none`: the `LG003` refusal). -/
def gvInitWert {F : Type} {sig : F → Nat} : (ty : Ty) → GvInit → Option (Val F sig ty)
  | .int lo hi, .int n =>
    if h : lo ≤ n ∧ n ≤ hi then some ⟨n, h.1, h.2⟩ else none
  | .bool, .bool b => some b
  | _, _ => none

/-- **A `bool` initialiser travels** (`gvInitWert_bool`). -/
theorem gvInitWert_bool {F : Type} {sig : F → Nat} (b : Bool) :
    gvInitWert (F := F) (sig := sig) .bool (.bool b) = some b := rfl

/-- **A `bool` spelling at an integer type is refused** (`gvInitWert_int_bool_none`). -/
theorem gvInitWert_int_bool_none {F : Type} {sig : F → Nat} (lo hi : Int) (b : Bool) :
    gvInitWert (F := F) (sig := sig) (.int lo hi) (.bool b) = none := rfl

/-- **An in-range numeral travels** (`gvInitWert_int_ok`): the value is the
    numeral (`read_static`'s `GInit::Int(n)`, `lean_g.rs` lines 1997-2014).
    Every premise is used. -/
theorem gvInitWert_int_ok {F : Type} {sig : F → Nat} (lo hi n : Int)
    (h1 : lo ≤ n) (h2 : n ≤ hi) :
    ∃ v : Zahl lo hi,
      gvInitWert (F := F) (sig := sig) (.int lo hi) (.int n) = some v ∧ v.n = n :=
  ⟨⟨n, h1, h2⟩, by simp only [gvInitWert]; rw [dif_pos ⟨h1, h2⟩]; rfl, rfl⟩

/-- **An out-of-range numeral is refused** (`gvInitWert_int_none`): the `LG003`
    arm (`lean_g.rs` lines 2004-2012). Every premise is used. -/
theorem gvInitWert_int_none {F : Type} {sig : F → Nat} (lo hi n : Int)
    (hmiss : n < lo ∨ hi < n) :
    gvInitWert (F := F) (sig := sig) (.int lo hi) (.int n) = none := by
  have hneg : ¬(lo ≤ n ∧ n ≤ hi) := by
    cases hmiss with
    | inl hm => omega
    | inr hm => omega
  simp only [gvInitWert]
  rw [dif_neg hneg]

/-! ## The bridge: `StartPflicht` from lowering plus zero memory -/

/-- **The parser's lowering writes no `requires`** (`gv_lowerAllg_requires`):
    `progOfFn` sets `requires := fun _ => .wahr` for every accepted program --
    mirror of the accepted `bruecke` S4 lemma over the same definition (no
    interpreter duplicated). -/
theorem gv_lowerAllg_requires (u : UProg) (P : Programm (declOf u))
    (fs : List (declOf u).Fn) (h : lowerAllg u = .ok (P, fs)) :
    ∀ f, P.requires f = .wahr := by
  unfold lowerAllg at h
  split at h
  · cases h
  · injection h with h1
    injection h1 with h2 h3
    subst h2
    intro f
    rfl

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
    (hP : E.P = P) (hS : E.S = SperrInv.leer _) (hsp0 : E.sp0 = sp0Of u hSp0) :
    StartPflicht E := by
  constructor
  · intro L
    rw [hS, hsp0]
    rfl
  · intro a _
    unfold ReqAmEintritt
    rw [hP, gv_lowerAllg_requires u P fs hlow]
    rfl

/-! ## The joint witness -/

/-- **Joint witness for the bridge** (`gv_startPflicht_zeuge`): all premises
    jointly on the non-degenerate fixture `uExp104` -- the decider accepts the
    array unit (`Konto` count 2, `stand` in `0 .. 100`), `einzahlen` writes
    `Konto`, a NON-ZERO static initialiser (`64`) travels through `gvInitWert`
    in the fragment's own declaration context, and the fragment has no statics.
    No single fragment unit carries both an array and a static (`Glob` is
    empty), so the witness pairs them: this is the task-shape finding, not a
    weakening. -/
theorem gv_startPflicht_zeuge :
    sp0OkB uExp104 = true ∧
    (declOf uExp104).count ⟨0, by decide⟩ = 2 ∧
    writesAt uExp104 (fnAt uExp104 ⟨0, by decide⟩) ⟨0, by decide⟩ = true ∧
    (∃ v : Zahl 0 100,
      gvInitWert (F := (declOf uExp104).Fn) (sig := (declOf uExp104).sig)
        (.int 0 100) (.int 64) = some v ∧ v.n = 64) ∧
    (declOf uExp104).Glob = Empty :=
  ⟨by decide, by decide, by decide,
    gvInitWert_int_ok 0 100 64 (by decide) (by decide),
    gv_fragment_kein_static uExp104⟩

end Gabbro.Grammatik.X86
/- CUTS: PROVED here -- `Sp0Ok` with its decider (`sp0OkB` over the per-field
    test `sp0FeldOkB`, sound by `sp0OkB_klingt`/`sp0FeldOkB_klingt`); the computed
    zero memory (`sp0FeldWert` from the very `Bool` tests, `sp0FeldOkB_of`,
    `sp0Of`); the obstructions (`sp0_luecke`, checkable as `sp0_lueckeB`);
    the fragment-shape fact (`gv_fragment_kein_static`: `Glob = Empty`); the
    static-initialiser model (`GvInit`/`gvInitWert` for `int`/`bool` with
    travel/refusal lemmas); the bridge (`gv_lowerAllg_requires`,
    `gv_startPflicht`: `StartPflicht` from lowering plus `sp0OkB`, no
    `Initially`); the joint non-degenerate witness (`gv_startPflicht_zeuge`
    on `uExp104` plus a non-zero `gvInitWert` initialiser).
    NOT covered: `tagged` (`Sum`) initialisers in `gvInitWert` (exporter
    `read_static`'s third arm, `lean_g.rs` lines 2020-2079); the `Body`-side
    `Initially` (`WF shapeOf`) transfer, which needs `programmlogik/` compiled
    in context (the `bruecke/` project, out of this file's scope -- its S4
    already closes the shape half for 104/108). Full `./lean-bau`: exit 0,
    0 errors, 723 jobs, module built. -/
#print axioms Gabbro.Grammatik.X86.Sp0Ok
#print axioms Gabbro.Grammatik.X86.sp0_luecke
#print axioms Gabbro.Grammatik.X86.sp0FeldOkB_klingt
#print axioms Gabbro.Grammatik.X86.sp0OkB_klingt
#print axioms Gabbro.Grammatik.X86.sp0FeldWert
#print axioms Gabbro.Grammatik.X86.sp0FeldOkB_of
#print axioms Gabbro.Grammatik.X86.sp0Of
#print axioms Gabbro.Grammatik.X86.sp0_lueckeB
#print axioms Gabbro.Grammatik.X86.gv_fragment_kein_static
#print axioms Gabbro.Grammatik.X86.gvInitWert_bool
#print axioms Gabbro.Grammatik.X86.gvInitWert_int_bool_none
#print axioms Gabbro.Grammatik.X86.gvInitWert_int_ok
#print axioms Gabbro.Grammatik.X86.gvInitWert_int_none
#print axioms Gabbro.Grammatik.X86.gv_lowerAllg_requires
#print axioms Gabbro.Grammatik.X86.gv_startPflicht
#print axioms Gabbro.Grammatik.X86.gv_startPflicht_zeuge
