module

public import Grammatik.Gen.Text.Invers.Anweisung.Teil1
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
variable {z : Spez} {V : Vertrag z.deklaration}

theorem ScalarMeta.of_artErg {τ : Ty} {a : UParamArt} (h : artErg τ = some a) : ScalarMeta a τ := by
  cases τ <;> simp_all only [artErg, Option.some.injEq, reduceCtorEq, ScalarMeta]

/-- Parameter metadata comes from the existing scalar parameter classification. -/
theorem ScalarMeta.of_params : ∀ (tys : List Ty) (ks : List UParamArt),
    tys.mapM artErg = some ks → ∀ d, d < tys.length →
      ∃ ty, tys[d]? = some ty ∧ ScalarMeta (ks.getD d .int) ty
  | [], _, _, _, hd => by simp only [List.length_nil] at hd; omega
  | ty :: tys, ks, h, d, hd => by
      cases ha : artErg ty with
      | none => simp only [List.mapM_cons, ha, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at h
      | some a =>
        cases ht : tys.mapM artErg with
        | none => simp only [List.mapM_cons, ha, Option.bind_eq_bind, Option.bind_some, ht, Option.bind_none, reduceCtorEq] at h
        | some rest =>
          simp only [List.mapM_cons, ha, Option.bind_eq_bind, Option.bind_some, ht, Option.pure_def, Option.some.injEq] at h
          subst h
          cases d with
          | zero => exact ⟨ty, rfl, ScalarMeta.of_artErg ha⟩
          | succ d => exact ScalarMeta.of_params tys rest ht d (by simp only [List.length_cons] at hd; omega)

/-! ### The context under a binder and under a lock -/

/-- The scope after a binder `x` of kind `a` (the shape every binding of the elaborator has). -/
def ctxMit (ctx : UCtx) (x : String) (a : UParamArt) (ty : Ty) (b : Nat) (ms ls : List String) : UCtx :=
  { ctx with names := x :: ctx.names, kinds := a :: ctx.kinds, types := ty :: ctx.types, bits := b :: ctx.bits,
             muts := ms, loops := ls }

theorem SInv.push {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (τ : Ty) (a : UParamArt) (ty : Ty) (b : Nat) (ms ls : List String) (hms : ms = [])
    (hmeta : ScalarMeta a ty) :
    SInv z V (ctxMit ctx (nVar Γ.length) a ty b ms ls) (τ :: Γ) Λ (artAuf a art) where
  var d hd := by
    cases d with
    | zero =>
      refine ⟨0, ?_, rfl⟩
      simp only [uParamNr, ctxMit, List.length_cons, Nat.add_one_sub_one, Nat.sub_zero, uParamNrAux, strEq_nVar,
  BEq.rfl, ↓reduceIte]
    | succ d =>
      simp only [List.length_cons] at hd
      obtain ⟨j, hj, ha⟩ := H.var d (by omega)
      refine ⟨j + 1, ?_, ha⟩
      have hne : strEq (nVar Γ.length) (nVar (Γ.length + 1 - 1 - (d + 1))) = false := by
        simp only [strEq_nVar, beq_eq_false_iff_ne]; omega
      simp only [uParamNr, ctxMit, List.length_cons, uParamNrAux, hne, Bool.false_eq_true, ite_false]
      have : Γ.length + 1 - 1 - (d + 1) = Γ.length - 1 - d := by omega
      rw [this]
      exact uParamNrAux_succ _ 0 _ j hj
  «meta» d hd j hj := by
    cases d with
    | zero =>
      have here : uParamNr (ctxMit ctx (nVar Γ.length) a ty b ms ls) (nVar Γ.length) = .ok 0 := by
        simp only [uParamNr, ctxMit, uParamNrAux, strEq_nVar, BEq.rfl, ↓reduceIte]
      have : j = 0 := Except.ok.inj (hj.symm.trans (by simpa only [List.length_cons,
        Nat.add_one_sub_one, Nat.sub_zero] using here))
      subst j
      exact ⟨ty, rfl, hmeta⟩
    | succ d =>
      have hd' : d < Γ.length := by simp only [List.length_cons] at hd; omega
      obtain ⟨k, hk, _⟩ := H.var d hd'
      obtain ⟨oldTy, hty, hm⟩ := H.meta d hd' k hk
      have here : uParamNr (ctxMit ctx (nVar Γ.length) a ty b ms ls)
          (nVar ((τ :: Γ).length - 1 - (d + 1))) = .ok (k + 1) := by
        have ne : strEq (nVar Γ.length) (nVar ((τ :: Γ).length - 1 - (d + 1))) = false := by
          simp only [strEq_nVar, beq_eq_false_iff_ne, List.length_cons]; omega
        simp only [uParamNr, ctxMit, uParamNrAux, ne, Bool.false_eq_true, ↓reduceIte]
        have index : (τ :: Γ).length - 1 - (d + 1) = Γ.length - 1 - d := by
          simp only [List.length_cons]; omega
        rw [index]
        exact uParamNrAux_succ _ 0 _ k hk
      have : j = k + 1 := Except.ok.inj (hj.symm.trans here)
      subst j
      exact ⟨oldTy, hty, hm⟩
  namen n hn := by
    simp only [ctxMit, List.mem_cons] at hn
    rcases hn with rfl | hn
    · exact Or.inl ⟨_, rfl⟩
    · exact H.namen n hn
  lits := H.lits
  arrKonst := H.arrKonst
  glob := H.glob
  tab := H.tab
  wrapsLeer := H.wrapsLeer
  tabNr := H.tabNr
  tabIdx := H.tabIdx
  tabNamen := H.tabNamen
  lockFind := H.lockFind
  lockGuard := H.lockGuard
  held := H.held
  muts := hms
  sums := H.sums
  resOpt := H.resOpt
  resSum := H.resSum
  resWhy := H.resWhy
  resTy := H.resTy
  ergNone := H.ergNone
  ergBool := H.ergBool
  ergInt := H.ergInt
  kanal0 := H.kanal0
  griff := H.griff
  reg := H.reg
  kanal := H.kanal
  zb := H.zb
  transFrei := H.transFrei

theorem SInv.lock {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (L : z.deklaration.Lock) :
    SInv z V { ctx with held := nLock (lN z L) :: ctx.held } Γ (.held L :: Λ) art where
  var := H.var
  «meta» := H.meta
  namen := H.namen
  lits := H.lits
  arrKonst := H.arrKonst
  glob := H.glob
  tab := H.tab
  wrapsLeer := H.wrapsLeer
  tabNr := H.tabNr
  tabIdx := H.tabIdx
  tabNamen := H.tabNamen
  lockFind := H.lockFind
  lockGuard := H.lockGuard
  held M hM := by
    simp only [List.mem_cons] at hM
    rcases hM with hM | hM
    · cases hM; simp only [List.any_cons, strEq_nLock, BEq.rfl, Bool.true_or]
    · simp only [List.any_cons, H.held M hM, Bool.or_true]
  muts := H.muts
  sums := H.sums
  resOpt := H.resOpt
  resSum := H.resSum
  resWhy := H.resWhy
  resTy := H.resTy
  ergNone := H.ergNone
  ergBool := H.ergBool
  ergInt := H.ergInt
  kanal0 := H.kanal0
  griff := H.griff
  reg := H.reg
  kanal := H.kanal
  zb := H.zb
  transFrei := H.transFrei

/-! ### Values of a `let`: a truth value is never read as a number -/

end Gabbro.Grammatik.Gen.Text
