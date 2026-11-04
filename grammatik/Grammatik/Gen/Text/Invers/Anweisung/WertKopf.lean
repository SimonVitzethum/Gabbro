module

public import Grammatik.Gen.Text.Invers.Ausdruck
public import Grammatik.Gen.Text.Invers.Anweisung.Kontext
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

namespace Gabbro.Grammatik.Gen.Text
open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
variable (z : Spez)
variable (V : Vertrag z.deklaration) (gNr : Nat → Nat)
variable {z V}

theorem wert_fehler_blatt {ctx : UCtx} (s : SExpr) (hz : ∃ e, uZugriff ctx s = .error e) (hg : uGrenzwort ctx s = none)
    (h1 : ∀ v, s ≠ .lit v) (h2 : ∀ p, s ≠ .variable p) (h3 : ∀ r f, s ≠ .arrow (.variable r) f) :
    ∃ e, uWertBlatt ctx s = .error e := by
  obtain ⟨e, he⟩ := hz
  cases s with
  | lit v => exact absurd rfl (h1 v)
  | «variable» p => exact absurd rfl (h2 p)
  | arrow a f =>
    cases a with
    | «variable» r => exact absurd rfl (h3 r f)
    | _ => simp only [uWertBlatt, hg, he]; exact ⟨_, rfl⟩
  | _ => simp only [uWertBlatt, hg, he]; exact ⟨_, rfl⟩

theorem wert_bin_fehler (ctx : UCtx) (op : String) (a b : SExpr)
    (hop : op = "<" ∨ op = "<=" ∨ op = "==" ∨ op = "&&" ∨ op = "||") : ∃ e, uWertBody ctx (.bin op a b) = .error e := by
  rcases hop with rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, by simp only [uWertBody, uRechne, strEq_eq, String.reduceEq, decide_false, Bool.or_self, Bool.false_eq_true,
  ↓reduceIte, uWertBlatt, uGrenzwort, uZugriff, Except.error.injEq]; rfl⟩

/-- **A printed truth value is no number**: `uWertBody` refuses it (so `let x = p;` binds a truth value). -/
theorem wert_bool_fehler {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : EInv z ctx Γ Λ art) {τ : Ty} (e : Expr z.deklaration Γ Λ τ) (s : SExpr) (u : UEns)
    (hd : delabE z none e = .ok s) (hu : uOfB z art none e = some u) : ∃ err, uWertBody ctx s = .error err := by
  cases e with
  | tru =>
    simp only [delabE, Except.ok.injEq] at hd; subst hd
    simp only [uWertBody, uRechne, uWertBlatt, uGrenzwort, uZugriff, Except.error.injEq, exists_eq']
  | fls =>
    simp only [delabE, Except.ok.injEq] at hd; subst hd
    simp only [uWertBody, uRechne, uWertBlatt, uGrenzwort, uZugriff, Except.error.injEq, exists_eq']
  | var x =>
    simp only [delabE, Except.ok.injEq] at hd; subst hd
    simp only [uOfB] at hu
    split at hu
    · rename_i h; simp only [reduceCtorEq] at h
    · rename_i hk
      obtain ⟨j, hj, ha⟩ := H.var (tiefe x) (tiefe_lt x) (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
      split at hu
      · rename_i hb
        simp only [uWertBody, hk, ↓reduceIte, uRechne, uWertBlatt, hj, ha, hb, Except.error.injEq, exists_eq']
      · simp only [reduceCtorEq] at hu
  | glob g hL =>
    simp only [delabE, Except.ok.injEq] at hd; subst hd
    simp only [uOfB] at hu
    split at hu
    · rename_i hg
      obtain ⟨err, he⟩ := H.param_fremd (nGlob (gN z g)) (fun n hn => strEq_rumpf_nGlob hn _)
      obtain ⟨gl, hf, hb⟩ := H.glob g
      have : gl.ty = .bool := hb.2 hg
      simp only [uWertBody, uRechne, uWertBlatt, he, H.lits, List.find?_nil, H.arrKonst, uGlobLies, hf, this,
  Except.error.injEq, exists_eq']
    · simp only [reduceCtorEq] at hu
  | slot t f i hL =>
    simp only [delabE] at hd
    cases hi : delabE z none i with
    | error _ => simp only [hi] at hd; cases hd
    | ok i' =>
      simp only [hi, bind, Except.bind, Except.ok.injEq] at hd
      subst hd
      simp only [uOfB] at hu
      split at hu
      · rename_i hb
        cases hx : uOfIdx z art none (tN z t) (z.deklaration.count t) i with
        | none => simp only [hx, Option.map_none, reduceCtorEq] at hu
        | some ix =>
          have hz := zugriff_slot H t f i' ix (idx_ok H t (sizeOf i + 1) i (by omega) i' ix hi hx) hL
          simp only [slotS] at hz
          have leaf : uWertBlatt ctx (slotS (nTab (tN z t)) (nFeld (show Fin _ from f).val) i') =
              .error "bool field as a number" := by
            simp only [slotS, uWertBlatt, uGrenzwort, hz, H.boolFeld t f, hb, decide_true, ↓reduceIte]
          have base : uRechne ctx (uWertBlatt ctx)
              (.index (.field (.variable (nTab (tN z t))) "slots") i') =
              .error "value without G form" := by
            simp only [uRechne, uTraegerIndex, strEq_eq, String.reduceEq, decide_true, ↓reduceIte,
              uWertBlatt, uGrenzwort, uZugriff, uPraemisse, decide_false, Bool.or_self,
              Bool.false_eq_true]
          refine ⟨"bool field as a number", ?_⟩
          change uRechne ctx (uWertBlatt ctx)
            (slotS (nTab (tN z t)) (nFeld (show Fin _ from f).val) i') = _
          dsimp only [slotS] at leaf ⊢
          rw [uRechne, leaf, base]
      · simp only [reduceCtorEq] at hu
  | lt a b =>
    simp only [delabE] at hd
    cases ha : delabE z none a <;> cases hb : delabE z none b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd
    exact wert_bin_fehler ctx _ _ _ (by simp only [String.reduceEq, or_self, or_false])
  | le a b =>
    simp only [delabE] at hd
    cases ha : delabE z none a <;> cases hb : delabE z none b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd
    exact wert_bin_fehler ctx _ _ _ (by simp only [String.reduceEq, or_self, or_false, or_true])
  | eq a b =>
    simp only [delabE] at hd
    cases ha : delabE z none a <;> cases hb : delabE z none b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd
    exact wert_bin_fehler ctx _ _ _ (by simp only [String.reduceEq, or_self, or_false, or_true])
  | and a b =>
    simp only [delabE] at hd
    cases ha : delabE z none a <;> cases hb : delabE z none b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd
    exact wert_bin_fehler ctx _ _ _ (by simp only [String.reduceEq, or_false, or_true])
  | or a b =>
    simp only [delabE] at hd
    cases ha : delabE z none a <;> cases hb : delabE z none b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd
    exact wert_bin_fehler ctx _ _ _ (by simp only [String.reduceEq, or_true])
  | not a =>
    simp only [delabE] at hd
    cases ha : delabE z none a <;>
      simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd
    exact ⟨_, by simp only [uWertBody, SExpr.un.injEq, String.reduceEq, false_and, imp_self, implies_true, uRechne, uWertBlatt,
  uGrenzwort, uZugriff, Except.error.injEq]; rfl⟩
  | forallSlots t body hL | existsSlots t body hL =>
    simp only [delabE] at hd
    cases ha : delabE z none body <;>
      simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd
    exact ⟨_, by simp only [uWertBody, uRechne, uWertBlatt, uGrenzwort, uZugriff, Except.error.injEq]; rfl⟩
  | _ => simp only [uOfB, reduceCtorEq] at hu

/-- The head of a printed value: no register place, no function reference, no call. -/
def kopfOk : SExpr → Bool
  | .float _ | .un "-" (.float _) | .un "-()" (.float _) => false
  | .field (.variable _) _ => false
  | .field (.field _ _) _ => false
  | .fnref _ => false
  | .call _ _ => false
  | .why _ _ => false
  | _ => true

theorem kopfOk_delab {Γ : Ctx} {Λ : List (Res z.deklaration)} (art : Nat → UParamArt) (k : Option Nat) (n : Nat) :
    ∀ {τ : Ty} (e : Expr z.deklaration Γ Λ τ), sizeOf e < n → ∀ (s : SExpr), delabE z k e = .ok s →
      ((uOfS z art k e).isSome = true ∨ (uOfB z art k e).isSome = true) → kopfOk s = true := by
  induction n with
  | zero => intro _ _ h; omega
  | succ n ih =>
  intro τ e hn s hd hf
  cases e with
  | lit n => simp only [delabE, Except.ok.injEq] at hd; subst hd; simp only [zahlE]; split <;> rfl
  | tru | fls => simp only [delabE, Except.ok.injEq] at hd; subst hd; rfl
  | var x => simp only [delabE, Except.ok.injEq] at hd; subst hd; split <;> rfl
  | glob g hL => simp only [delabE, Except.ok.injEq] at hd; subst hd; rfl
  | slot t f i hL =>
    simp only [delabE] at hd
    cases hi : delabE z k i <;> simp only [hi, bind, Except.bind, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; rfl
  | fnref f m h => simp only [uOfS, Option.isSome_none, Bool.false_eq_true, uOfB, or_self] at hf
  | widen h1 h2 e =>
    simp only [delabE] at hd
    simp only [uOfS, uOfB] at hf
    exact ih e (by simp only [Expr.widen.sizeOf_spec, sizeOf_default, add_zero] at hn; omega) s hd (Or.inl (by simpa using hf))
  | add a b =>
    simp only [delabE] at hd
    cases ha : delabE z k a <;> cases hb : delabE z k b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; rfl
  | sub a b =>
    simp only [delabE] at hd
    cases ha : delabE z k a <;> cases hb : delabE z k b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; rfl
  | mul a b =>
    simp only [delabE] at hd
    cases ha : delabE z k a <;> cases hb : delabE z k b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; rfl
  | lt a b =>
    simp only [delabE] at hd
    cases ha : delabE z k a <;> cases hb : delabE z k b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; rfl
  | le a b =>
    simp only [delabE] at hd
    cases ha : delabE z k a <;> cases hb : delabE z k b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; rfl
  | eq a b =>
    simp only [delabE] at hd
    cases ha : delabE z k a <;> cases hb : delabE z k b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; rfl
  | and a b =>
    simp only [delabE] at hd
    cases ha : delabE z k a <;> cases hb : delabE z k b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; rfl
  | or a b =>
    simp only [delabE] at hd
    cases ha : delabE z k a <;> cases hb : delabE z k b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; rfl
  | neg a =>
    simp only [uOfS, uOfB] at hf
    cases hu : uOfS z art k a with
    | none => simp only [hu, Option.bind_eq_bind, Option.bind_none, Option.isSome_none,
        Bool.false_eq_true, or_self] at hf
    | some u =>
      have haOk : ∀ s', delabE z k a = .ok s' → kopfOk s' = true :=
        fun s' hd' => ih a (by simp only [Expr.neg.sizeOf_spec] at hn; omega) s' hd'
          (Or.inl (by simp only [hu, Option.isSome_some]))
      simp only [delabE] at hd
      cases ha : delabE z k a <;>
        simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
      rename_i source
      have hk := haOk source ha
      subst hd
      cases source <;> simp only [kopfOk, Bool.false_eq_true] at hk ⊢ <;> rfl
  | not a =>
    simp only [delabE] at hd
    cases ha : delabE z k a <;> simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; (try split) <;> rfl
  | forallSlots t body hL | existsSlots t body hL =>
    simp only [delabE] at hd
    cases ha : delabE z k body <;> simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; rfl
  | why m r => simp only [uOfS, Option.isSome_none, Bool.false_eq_true, uOfB, or_self] at hf
  | div _ _ a b | rem _ _ a b | sdiv _ a b | srem _ a b | band _ _ a b | bor _ _ _ _ _ a b | bxor _ _ _ _ _ a b
  | shl _ _ _ _ _ a b | shr _ _ _ _ _ a b =>
    simp only [delabE] at hd
    cases ha : delabE z k a <;> cases hb : delabE z k b <;>
      simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; rfl
  | oldG g hL => simp only [delabE, Except.ok.injEq] at hd; subst hd; rfl
  | oldS t f i hL =>
    simp only [delabE] at hd
    cases hi : delabE z k i <;> simp only [hi, bind, Except.bind, Except.ok.injEq, reduceCtorEq] at hd
    subst hd; rfl
  | none m => simp only [uOfS, Option.isSome_none, Bool.false_eq_true, uOfB, or_self] at hf
  | some e => simp only [uOfS, Option.isSome_none, Bool.false_eq_true, uOfB, or_self] at hf
  | istSome e => simp only [uOfS, Option.isSome_none, Bool.false_eq_true, uOfB, or_self] at hf
  | _ => simp only [delabE, reduceCtorEq] at hd

theorem regOrt_kopfOk (ctx : UCtx) (s : SExpr) (h : kopfOk s = true) : uRegOrt ctx s = none := by
  cases s with
  | field a r =>
    cases a with
    | «variable» _ => simp only [kopfOk, Bool.false_eq_true] at h
    | field _ _ => simp only [kopfOk, Bool.false_eq_true] at h
    | _ => simp only [uRegOrt]
  | _ => simp only [uRegOrt]

/-- A scalar reader's metadata does not select an aggregate or IEEE introduction. -/
def ScalarType : Option Ty → Prop
  | some (.fl ..) | some (.prod ..) | some (.arr ..) | some (.str ..) => False
  | _ => True

theorem ScalarMeta.scalarType {a : UParamArt} {ty : Ty} (h : ScalarMeta a ty) : ScalarType (some ty) := by
  cases a <;> cases ty <;> simp_all only [ScalarMeta, ScalarType]

private theorem paramNr_find : ∀ (names : List String) (k : Nat) (name : String) (j : Nat),
    uParamNrAux names k name = .ok j → List.findIdx?.go (strEq · name) names k = some j
  | [], _, _, _, h => by cases h
  | first :: rest, k, name, j, h => by
      by_cases he : strEq first name = true
      · simpa only [uParamNrAux, List.findIdx?.go, he, ↓reduceIte, Except.ok.injEq, Option.some.injEq] using h
      · simp only [uParamNrAux, he, Bool.false_eq_true, ↓reduceIte] at h
        simpa only [List.findIdx?.go, he, Bool.false_eq_true, ↓reduceIte] using paramNr_find rest (k + 1) name j h

/-- The existing side classifier and the actual context rows certify the complete type probe. -/
theorem scalar_type {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (n : Nat) :
    ∀ {τ : Ty} (e : Expr z.deklaration Γ Λ τ), sizeOf e < n → ∀ u,
      uOfS z art none e = some u → ScalarType (uValueType ctx u) := by
  induction n with
  | zero => intro _ _ hn; omega
  | succ n ih =>
    intro τ e hn u hu
    cases e with
    | lit value => simp only [uOfS, Option.some.injEq] at hu; subst hu; trivial
    | var x =>
      obtain ⟨j, hj, _⟩ := H.var (tiefe x) (tiefe_lt x)
      obtain ⟨ty, hty, hm⟩ := H.meta (tiefe x) (tiefe_lt x) j hj
      have hf : ctx.names.findIdx? (strEq · (nVar (Γ.length - 1 - tiefe x))) = some j := paramNr_find _ 0 _ j hj
      cases ha : art (tiefe x) <;>
        simp only [uOfS, ha, reduceCtorEq, ↓reduceIte, Option.some.injEq] at hu
      all_goals subst hu; simpa only [uValueType, hf, Option.bind_some, hty] using hm.scalarType
    | glob g _ =>
      obtain ⟨gl, hf, _, _, _, _, hscalar, _⟩ := H.glob g
      cases ht : gl.ty with
      | wert ty => exact (hscalar ty ht).elim
      | bool | int lo hi =>
        simp only [uOfS] at hu
        split at hu
        · simp only [reduceCtorEq] at hu
        · simp only [Option.some.injEq] at hu
          subst hu
          simp only [uValueType, hf, Option.map_some, ht, GTy.toTy, ScalarType]
    | slot t field index _ =>
      simp only [uOfS] at hu
      split at hu
      · cases hu
      · cases hx : uOfIdx z art none (tN z t) (z.deklaration.count t) index <;>
          simp only [hx, Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] at hu
        subst hu; trivial
    | widen _ _ value => exact ih value (by simp only [Expr.widen.sizeOf_spec, sizeOf_default, add_zero] at hn; omega) u hu
    | add a b | sub a b | mul a b =>
      simp only [uOfS] at hu
      cases ha : uOfS z art none a <;> cases hb : uOfS z art none b <;>
        simp only [ha, hb, Option.bind_eq_bind, Option.bind_none, Option.bind_some, Option.some.injEq, reduceCtorEq] at hu
      subst hu; trivial
    | neg a =>
      simp only [uOfS] at hu
      cases ha : uOfS z art none a <;>
        simp only [ha, Option.bind_eq_bind, Option.bind_none, Option.bind_some, Option.some.injEq, reduceCtorEq] at hu
      subst hu; trivial
    | _ => simp only [uOfS, reduceCtorEq] at hu

/-- A printed binary head retains the actual left operand's scalar type probe. -/
theorem printed_left_scalar {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (n : Nat) :
    ∀ {τ : Ty} (e : Expr z.deklaration Γ Λ τ), sizeOf e < n → ∀ s,
      delabE z none e = .ok s →
      ((uOfS z art none e).isSome = true ∨ (uOfB z art none e).isSome = true) →
      ∀ op a b, s = .bin op a b → ∀ u, uWertBody ctx a = .ok u → ScalarType (uValueType ctx u) := by
  induction n with
  | zero => intro _ _ hn; omega
  | succ n ih =>
    intro τ e hn s hd hf op a b hbin u hu
    cases e with
    | widen _ _ value =>
      have accepted : (uOfS z art none value).isSome = true := by
        simpa only [uOfS, uOfB, Option.isSome_none, Bool.false_eq_true, or_false] using hf
      exact ih value (by simp only [Expr.widen.sizeOf_spec, sizeOf_default, add_zero] at hn; omega)
        s hd (Or.inl accepted) op a b hbin u hu
    | add left right | sub left right | mul left right | lt left right | le left right | eq left right =>
      simp only [delabE] at hd
      cases hl : delabE z none left <;> cases hr : delabE z none right <;>
        simp only [hl, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
      subst hd
      cases hbin
      cases hs : uOfS z art none left <;> cases ht : uOfS z art none right <;>
        simp only [uOfS, uOfB, hs, ht, Option.bind_eq_bind, Option.bind_none, Option.bind_some,
          Option.isSome_none, Option.isSome_some, Bool.false_eq_true, or_self, or_false, false_or, true_or, or_true] at hf
      rename_i leftSide rightSide
      have read := wert_ok H.einv left _ leftSide hl hs
      have same : u = leftSide := Except.ok.inj (hu.symm.trans read)
      subst u
      exact scalar_type H (sizeOf left + 1) left (by omega) leftSide hs
    | and left right | or left right =>
      simp only [delabE] at hd
      cases hl : delabE z none left <;> cases hr : delabE z none right <;>
        simp only [hl, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
      subst hd
      cases hbin
      cases hs : uOfB z art none left <;> cases ht : uOfB z art none right <;>
        simp only [uOfS, uOfB, hs, ht, Option.bind_eq_bind, Option.bind_none, Option.bind_some,
          Option.isSome_none, Option.isSome_some, Bool.false_eq_true, or_self, or_false, false_or, true_or, or_true] at hf
      obtain ⟨err, he⟩ := wert_bool_fehler H.einv left _ _ hl hs
      rw [he] at hu
      cases hu
    | lit value =>
      simp only [delabE, Except.ok.injEq] at hd
      subst hd
      simp only [zahlE] at hbin
      split at hbin <;> cases hbin
    | tru | fls | var _ | glob _ _ =>
      simp only [delabE, reduceCtorEq, ↓reduceIte, Except.ok.injEq] at hd
      subst hd
      cases hbin
    | slot _ _ index _ =>
      simp only [delabE] at hd
      cases hi : delabE z none index <;>
        simp only [hi, bind, Except.bind, Except.ok.injEq, reduceCtorEq] at hd
      subst hd
      cases hbin
    | neg value =>
      simp only [delabE] at hd
      cases hv : delabE z none value <;>
        simp only [hv, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
      subst hd
      split at hbin <;> cases hbin
    | not value | forallSlots _ value _ | existsSlots _ value _ =>
      simp only [delabE] at hd
      cases hv : delabE z none value <;>
        simp only [hv, bind, Except.bind, pure, Except.pure, Except.ok.injEq, reduceCtorEq] at hd
      subst hd
      cases hbin
    | _ => simp only [uOfS, uOfB, Option.isSome_none, Bool.false_eq_true, or_self] at hf


end Gabbro.Grammatik.Gen.Text
