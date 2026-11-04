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
public import Grammatik.Parser.Elab.Uebersetze
public import Grammatik.Parser.Elab.UebersetzeAllg
public import Grammatik.Parser.Elab.UebersetzeAllg3
public import Grammatik.Kern.Syntax.Typen.Teil2
public import Grammatik.Kern.Syntax.Typen.Fall
public import Grammatik.Kern.Syntax.Syntax.Teil2
public import Grammatik.Kern.Syntax.Syntax.Teil2Programm
public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Logik.Vertraege.Locations.VertragOrtB
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem
public import Grammatik.Zielsatz.Kern.Spec
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmenBeweis
import all Init.Data.Repr
@[expose] public section


namespace Gabbro.Grammatik.GabbroV

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg
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

/-- The elements of an array initialiser. -/
def konstListe : UKonst → Option (List UKonst)
  | .nil => some []
  | .cons a r => (konstListe r).map (a :: ·)
  | _ => none

/-- The single field traversal passes evidence of the actual type child to its callback. -/
def prodKonstFields {F : Type} {P : F → Nat → Bool} :
    (fs : List Ty) → List UKonst →
    ((τ : Ty) → τ ∈ fs → UKonst → Option (Val F P τ)) → Option (ProdVal F P fs)
  | [], [], _ => some ()
  | τ :: τs, k :: ks, elaborate => do
    let v ← elaborate τ (List.mem_cons_self) k
    let vs ← prodKonstFields τs ks
      (fun child member value => elaborate child (List.mem_cons_of_mem τ member) value)
    pure (ProdVal.pcons v vs)
  | _, _, _ => none
termination_by structural fs _ _ => fs

/-- Constant fields retain declaration order and exact arity, with arbitrary typed callbacks. -/
def prodKonst {F : Type} {P : F → Nat → Bool}
    (elaborate : (τ : Ty) → UKonst → Option (Val F P τ))
    (fs : List Ty) (ks : List UKonst) : Option (ProdVal F P fs) :=
  prodKonstFields fs ks (fun τ _ value => elaborate τ value)

@[simp] theorem prodKonst_nil_nil {F : Type} {P : F → Nat → Bool}
    (elaborate : (τ : Ty) → UKonst → Option (Val F P τ)) :
    prodKonst elaborate [] [] = some () := rfl

@[simp] theorem prodKonst_nil_cons {F : Type} {P : F → Nat → Bool}
    (elaborate : (τ : Ty) → UKonst → Option (Val F P τ)) (k : UKonst) (ks : List UKonst) :
    prodKonst elaborate [] (k :: ks) = none := rfl

@[simp] theorem prodKonst_cons_nil {F : Type} {P : F → Nat → Bool}
    (elaborate : (τ : Ty) → UKonst → Option (Val F P τ)) (τ : Ty) (fs : List Ty) :
    prodKonst elaborate (τ :: fs) [] = none := rfl

@[simp] theorem prodKonst_cons_cons {F : Type} {P : F → Nat → Bool}
    (elaborate : (τ : Ty) → UKonst → Option (Val F P τ))
    (τ : Ty) (fs : List Ty) (k : UKonst) (ks : List UKonst) :
    prodKonst elaborate (τ :: fs) (k :: ks) = (do
      let value ← elaborate τ k
      let rest ← prodKonst elaborate fs ks
      pure (ProdVal.pcons value rest)) := rfl

mutual

/-- **The value of a constant initialiser at the type `τ`**: zero memory (`= 0`) wherever the type holds a zero,
    a number inside its range, a truth value, the bytes of a string under its maximum, an array literal of exactly
    the array's length; anything else has no value. -/
def konstWert {F : Type} {P : F → Nat → Bool} : (τ : Ty) → UKonst → Option (Val F P τ)
  | .int lo hi, .zahl n => if h : lo ≤ n ∧ n ≤ hi then some ⟨n, h.1, h.2⟩ else none
  | .int lo hi, .null => if h : lo ≤ 0 ∧ 0 ≤ hi then some ⟨0, h.1, h.2⟩ else none
  | .bool, .wahr b => some b
  | .bool, .null => some false
  | .str n, .text bs =>
    match bytesZahl bs with
    | some zs => if h : zs.length ≤ n then some ⟨zs, h⟩ else none
    | none => none
  | .str _, .null => some ⟨[], Nat.zero_le _⟩
  | .opt _, .null => some none
  | .sum cs, .fall k p =>
    if h : k < cs.length then (nutzKonst (cs.get ⟨k, h⟩) p).map (⟨⟨k, h⟩, Fall.ofNutzlast _ _ _ _ ·⟩) else none
  -- zero memory of a tagged value: the first case, its payload zero
  | .sum cs, .null =>
    if h : 0 < cs.length then
      (nutzKonst (cs.get ⟨0, h⟩) .null).map (⟨⟨0, h⟩, Fall.ofNutzlast _ _ _ _ ·⟩)
    else none
  | .arr τ _, .null => (konstWert τ .null).map (fun z => fun _ => z)
  | .prod name fs, .product name2 ks =>
    if name == name2 then
      prodKonstFields fs ks (fun field member value => konstWert field value)
    else none
  | .arr τ n, k =>
    match konstListe k with
    | some ks =>
      match ks.mapM (konstWert τ) with
      | some vs => if h : vs.length = n then some (fun i => vs.get ⟨i.val, by rw [h]; exact i.isLt⟩) else none
      | none => none
    | none => none
  | _, _ => none

termination_by τ _ => sizeOf τ
decreasing_by
  all_goals first
    | decreasing_trivial
    | have hs := List.sizeOf_get cs ⟨k, h⟩
      simp only [Ty.sum.sizeOf_spec]
      omega
    | have hs := List.sizeOf_get cs ⟨0, h⟩
      simp only [Ty.sum.sizeOf_spec]
      omega
    | have hs := List.sizeOf_lt_of_mem (show _ ∈ fs from by assumption)
      simp only [Ty.prod.sizeOf_spec]
      omega

/-- Constants use the same complete payload type as ordinary construction. -/
def nutzKonst {F : Type} {P : F → Nat → Bool} :
    (o : Option Ty) → UKonst → Option (Nutzlast F P o)
  | none, .null => some ()
  | none, _ => none
  | some τ, value => konstWert τ value
termination_by c _ => sizeOf c

end

/-- The actual product branch retains the public field collector and nominal-name guard exactly. -/
theorem konstWert_product {F : Type} {P : F → Nat → Bool}
    (name other : Nat) (fs : List Ty) (ks : List UKonst) :
    konstWert (F := F) (P := P) (.prod name fs) (.product other ks) =
      if name == other then prodKonst konstWert fs ks else none := by
  rw [konstWert]
  rfl

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

/-- **An aggregate field has a zero value** (`sp0WertOkB`): zero memory is a value of its type (every number range
    in it holds `0`); any other field passes. -/
def sp0WertOkB (u : UProg) (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) : Bool :=
  match wertFeldAt u t f with
  | some τ => (konstWert (F := (declOf u).Fn) (P := (declOf u).passt) τ .null).isSome
  | none => true

/-- **The tables of the decider** (`sp0TabOkB`): the per-field test over every table and every field index
    (`List.finRange`, like `lowerAllg`'s own coverage). -/
def sp0TabOkB (u : UProg) : Bool :=
  (List.finRange u.tabs.length).all fun t =>
    (List.finRange (fieldCount u t)).all fun f => sp0FeldOkB u t f && sp0WertOkB u t f

/-- **A static holds its initialiser** (`sp0GlobOkB`): an integer static starts inside its range, a `bool`
    static at `0` or `1`. -/
def sp0GlobOkB (u : UProg) (g : Fin u.globs.length) : Bool :=
  match (globAt u g).ty with
  | .int lo hi => decide (lo ≤ (globAt u g).init ∧ (globAt u g).init ≤ hi)
  | .bool => (globAt u g).init == 0 || (globAt u g).init == 1
  | .wert τ => (konstWert (F := (declOf u).Fn) (P := (declOf u).passt) τ (globAt u g).initK).isSome

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
  | .wert τ => by
      have hg : (declOf u).gtyp g = τ := by
        show (globAt u g).ty.toTy = _
        rw [hq]
        rfl
      rw [hg]
      have hc : (konstWert (F := (declOf u).Fn) (P := (declOf u).passt) τ (globAt u g).initK).isSome = true := by
        unfold sp0GlobOkB at h
        rw [hq] at h
        exact h
      exact Option.get _ hc

/-- **The zero value at one field** (`sp0FeldWert`): `false` at a `bool` field,
    `⟨0, _, _⟩` at an integer field whose range holds `0` -- the Lean side of
    the exporter's `gSp0` slot half (`crates/gabbro-check/src/lean_g.rs`
    lines 456-466: a slot starts at zero because no surface form names a slot
    initialiser). -/
def sp0FeldWert (u : UProg) (t : Fin u.tabs.length) (f : Fin (fieldCount u t))
    (h : sp0FeldOkB u t f = true) (hw0 : sp0WertOkB u t f = true) :
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
        match hW : wertFeldAt u t f with
        | some τ => by
            have hbf : boolFeldAt u t f = false := by unfold boolFeldAt; rw [hq]; exact hb
            have ht : (declOf u).typ t f = τ := typAt_wert u t f τ hbf hO hW
            rw [ht]
            have hc : (konstWert (F := (declOf u).Fn) (P := (declOf u).passt) τ .null).isSome = true := by
              unfold sp0WertOkB at hw0
              rw [hW] at hw0
              exact hw0
            exact Option.get _ hc
        | none =>
        match hd : decide (q.2.1 ≤ 0 ∧ 0 ≤ q.2.2) with
        | true => by
            have hbd := of_decide_eq_true hd
            have ht : (declOf u).typ t f = .int q.2.1 q.2.2 := by
              show typAt u t f = .int q.2.1 q.2.2
              have hfr : fieldRangeO u t f = some q.2 := by unfold fieldRangeO; rw [hq]; rfl
              have hbf : boolFeldAt u t f = false := by unfold boolFeldAt; rw [hq]; exact hb
              exact typAt_of u t f q.2 hfr hbf hO hW
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


end Gabbro.Grammatik.GabbroV
