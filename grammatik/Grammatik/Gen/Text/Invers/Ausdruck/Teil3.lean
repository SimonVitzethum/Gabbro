module

public import Grammatik.Gen.Text.Invers.Namen
public import Grammatik.Gen.Text.Invers.Ausdruck.Teil2
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
variable {z}

/-- **A truth value in an `ensures`/`requires`**. -/
theorem sichert_ok (kopf : Option Nat) (n : Nat) :
    ∀ {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt},
    EInvK z ctx Γ Λ art kopf → ErgOk ctx Γ kopf →
    ∀ {τ : Ty} (e : Expr z.deklaration Γ Λ τ), sizeOf e < n → ∀ (s : SExpr) (u : UEns),
      delabE z kopf e = .ok s → uOfB z art kopf e = some u → uSichert ctx s = .ok u := by
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ h; omega
  | succ n ih =>
  intro ctx Γ Λ art H hr τ e hn s u hd hu
  cases e with
  | tru =>
    simp only [delabE, Except.ok.injEq] at hd; subst hd
    simp only [uOfB, Option.some.injEq] at hu; subst hu
    simp only [uSichert]
  | fls =>
    simp only [delabE, Except.ok.injEq] at hd; subst hd
    simp only [uOfB, Option.some.injEq] at hu; subst hu
    simp only [uSichert]
  | var x =>
    simp only [delabE, Except.ok.injEq] at hd; subst hd
    simp only [uOfB] at hu
    split at hu
    · rename_i hk
      split at hu
      · rename_i hτ
        simp only [Option.some.injEq] at hu; subst hu
        subst hτ
        have hx := var_typ x
        have := (hr _ hk).2.2 hx
        simp only [hk, ↓reduceIte, uSichert, this]
      · simp only [reduceCtorEq] at hu
    · rename_i hk
      simp only [hk, ite_false]
      obtain ⟨j, hj, ha⟩ := H.var (tiefe x) (tiefe_lt x) hk
      split at hu
      · rename_i hb
        simp only [Option.some.injEq] at hu; subst hu
        simp only [uSichert, hj, ha, hb]
      · simp only [reduceCtorEq] at hu
  | glob g hL =>
    simp only [delabE, Except.ok.injEq] at hd; subst hd
    simp only [uOfB] at hu
    split at hu
    · rename_i hg
      simp only [Option.some.injEq] at hu; subst hu
      obtain ⟨e, he⟩ := H.param_fremd (nGlob (gN z g)) (fun n hn => strEq_rumpf_nGlob hn _)
      obtain ⟨gl, hf, hb⟩ := H.glob g
      have hgl : gl.ty = .bool := hb.2 hg
      simp only [uSichert, he, hf, hgl]
    · simp only [reduceCtorEq] at hu
  | slot t f i hL =>
    simp only [delabE] at hd
    cases hi : delabE z kopf i with
    | error _ => simp only [hi] at hd; cases hd
    | ok i' =>
      simp only [hi, bind, Except.bind, Except.ok.injEq] at hd
      subst hd
      simp only [uOfB] at hu
      split at hu
      · rename_i hb
        cases hx : uOfIdx z art kopf (tN z t) (z.deklaration.count t) i with
        | none => simp only [hx, Option.map_none, reduceCtorEq] at hu
        | some ix =>
          simp only [hx, Option.map_some, Option.some.injEq] at hu
          subst hu
          have hz := zugriff_slot H t f i' ix (idx_ok H t (sizeOf i + 1) i (by omega) i' ix hi hx) hL
          simp only [slotS] at hz
          simp only [uSichert, hz, H.boolFeld t f, hb, decide_true, ite_true]
      · simp only [reduceCtorEq] at hu
  | lt a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok sa =>
    cases hb : delabE z kopf b with
    | error _ => simp only [bind, Except.bind, ha, hb, reduceCtorEq] at hd
    | ok sb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfB] at hu
    cases xa : uOfS z art kopf a with
    | none => simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some x =>
    cases xb : uOfS z art kopf b with
    | none => simp only [xa, xb, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
    | some y =>
    simp only [xa, xb, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    exact rechne_vgl ctx "<" sa sb x y (seite_ok H hr a sa x ha xa) (seite_ok H hr b sb y hb xb) (by simp only [String.reduceEq, or_self, or_false])
  | le a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok sa =>
    cases hb : delabE z kopf b with
    | error _ => simp only [bind, Except.bind, ha, hb, reduceCtorEq] at hd
    | ok sb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfB] at hu
    cases xa : uOfS z art kopf a with
    | none => simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some x =>
    cases xb : uOfS z art kopf b with
    | none => simp only [xa, xb, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
    | some y =>
    simp only [xa, xb, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    exact rechne_vgl ctx "<=" sa sb x y (seite_ok H hr a sa x ha xa) (seite_ok H hr b sb y hb xb) (by simp only [String.reduceEq, or_false, or_true])
  | eq a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok sa =>
    cases hb : delabE z kopf b with
    | error _ => simp only [bind, Except.bind, ha, hb, reduceCtorEq] at hd
    | ok sb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfB] at hu
    cases xa : uOfS z art kopf a with
    | none => simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some x =>
    cases xb : uOfS z art kopf b with
    | none => simp only [xa, xb, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
    | some y =>
    simp only [xa, xb, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    exact rechne_vgl ctx "==" sa sb x y (seite_ok H hr a sa x ha xa) (seite_ok H hr b sb y hb xb) (by simp only [String.reduceEq, or_true])
  | and a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok sa =>
    cases hb : delabE z kopf b with
    | error _ => simp only [bind, Except.bind, ha, hb, reduceCtorEq] at hd
    | ok sb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfB] at hu
    cases xa : uOfB z art kopf a with
    | none => simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some x =>
    cases xb : uOfB z art kopf b with
    | none => simp only [xa, xb, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
    | some y =>
    simp only [xa, xb, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [Expr.and.sizeOf_spec] at hn
    have h1 := ih H hr a (by omega) sa x ha xa
    have h2 := ih H hr b (by omega) sb y hb xb
    simp only [uSichert, uIstVgl, String.reduceEq, imp_self, Bool.false_eq_true, ↓reduceIte, strEq_eq,
  decide_true, h1, h2]
  | or a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok sa =>
    cases hb : delabE z kopf b with
    | error _ => simp only [bind, Except.bind, ha, hb, reduceCtorEq] at hd
    | ok sb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfB] at hu
    cases xa : uOfB z art kopf a with
    | none => simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some x =>
    cases xb : uOfB z art kopf b with
    | none => simp only [xa, xb, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
    | some y =>
    simp only [xa, xb, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [Expr.or.sizeOf_spec] at hn
    have h1 := ih H hr a (by omega) sa x ha xa
    have h2 := ih H hr b (by omega) sb y hb xb
    simp only [uSichert, uIstVgl, String.reduceEq, imp_self, Bool.false_eq_true, ↓reduceIte, strEq_eq,
  decide_false, decide_true, h1, h2]
  | not a =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok sa =>
    simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfB] at hu
    cases xa : uOfB z art kopf a with
    | none => simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some x =>
    simp only [xa, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [Expr.not.sizeOf_spec] at hn
    have h1 := ih H hr a (by omega) sa x ha xa
    simp only [uSichert, h1]
  | forallSlots t body hL =>
    simp only [delabE] at hd
    cases ha : delabE z kopf body with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok sa =>
    simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfB] at hu
    cases xa : uOfB z (artAuf (.index (tN z t)) art) kopf body with
    | none => simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some x =>
    simp only [xa, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [Expr.forallSlots.sizeOf_spec, sizeOf_default, add_zero] at hn
    have h1 := ih (H.auf t) (hr.auf rfl rfl _) body (by omega) sa x ha xa
    simp only [ctxAuf] at h1
    simp only [(show ("slots" == "elems") = false from rfl),
      (show (("slots" == "descendants") || ("slots" == "ancestors")) = false from rfl), uSichert, BEq.rfl, Bool.true_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte, strEq_eq,
  decide_true, uTabNr, H.tabNr t, h1]
  | existsSlots t body hL =>
    simp only [delabE] at hd
    cases ha : delabE z kopf body with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok sa =>
    simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfB] at hu
    cases xa : uOfB z (artAuf (.index (tN z t)) art) kopf body with
    | none => simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some x =>
    simp only [xa, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [Expr.existsSlots.sizeOf_spec, sizeOf_default, add_zero] at hn
    have h1 := ih (H.auf t) (hr.auf rfl rfl _) body (by omega) sa x ha xa
    simp only [ctxAuf] at h1
    simp only [(show ("slots" == "elems") = false from rfl),
      (show (("slots" == "descendants") || ("slots" == "ancestors")) = false from rfl), uSichert, BEq.rfl, Bool.or_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, strEq_eq,
  decide_true, uTabNr, H.tabNr t, h1, beq_iff_eq, reduceCtorEq]
  | _ => simp only [uOfB, reduceCtorEq] at hu

/-- Without a result, a read-back side holds no `old` and no `result`. -/
theorem seite_ohne_erg (art : Nat → UParamArt) (n : Nat) :
    ∀ {Γ : Ctx} {Λ : List (Res z.deklaration)} {τ : Ty} (e : Expr z.deklaration Γ Λ τ), sizeOf e < n →
      ∀ u, uOfS z art none e = some u → seiteAltErg u = false := by
  induction n with
  | zero => intro _ _ _ _ h; omega
  | succ n ih =>
  intro Γ Λ τ e hn u hu
  cases e with
  | lit m =>
    simp only [uOfS, Option.some.injEq] at hu; subst hu
    simp only [seiteAltErg]
  | var x =>
    simp only [uOfS] at hu
    split at hu
    · rename_i h; simp only [reduceCtorEq] at h
    · split at hu <;> simp only [reduceCtorEq, Option.some.injEq] at hu; subst hu
      simp only [seiteAltErg]
  | glob g hL =>
    simp only [uOfS] at hu
    split at hu <;> simp only [reduceCtorEq, Option.some.injEq] at hu; subst hu
    simp only [seiteAltErg]
  | slot t f i hL =>
    simp only [uOfS] at hu
    split at hu
    · simp only [reduceCtorEq] at hu
    · cases hx : uOfIdx z art none (tN z t) (z.deklaration.count t) i <;> simp only [hx, Option.map_none, reduceCtorEq, Option.map_some, Option.some.injEq] at hu; subst hu
      simp only [seiteAltErg]
  | widen h1 h2 e =>
    simp only [uOfS] at hu
    exact ih e (by simp only [Expr.widen.sizeOf_spec, sizeOf_default, add_zero] at hn; omega) u hu
  | add a b | sub a b | mul a b =>
    simp only [uOfS] at hu
    simp only [Expr.add.sizeOf_spec, Expr.sub.sizeOf_spec, Expr.mul.sizeOf_spec] at hn
    cases xa : uOfS z art none a <;> cases xb : uOfS z art none b <;> simp only [xa, xb, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [seiteAltErg, ih a (by omega) _ xa, ih b (by omega) _ xb, Bool.or_self]
  | neg a =>
    simp only [uOfS] at hu
    simp only [Expr.neg.sizeOf_spec] at hn
    cases xa : uOfS z art none a <;> simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [seiteAltErg, ih a (by omega) _ xa]
  | _ => simp only [uOfS, reduceCtorEq] at hu

theorem ens_ohne_erg (n : Nat) :
    ∀ {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt} {τ : Ty} (e : Expr z.deklaration Γ Λ τ),
      sizeOf e < n → ∀ u, uOfB z art none e = some u → ensAltErg u = false := by
  induction n with
  | zero => intro _ _ _ _ _ h; omega
  | succ n ih =>
  intro Γ Λ art τ e hn u hu
  cases e with
  | tru | fls =>
    simp only [uOfB, Option.some.injEq] at hu; subst hu
    simp only [ensAltErg]
  | var x =>
    simp only [uOfB] at hu
    split at hu
    · rename_i h; simp only [reduceCtorEq] at h
    · split at hu <;> simp only [Option.some.injEq, reduceCtorEq] at hu; subst hu
      simp only [ensAltErg]
  | glob g hL =>
    simp only [uOfB] at hu
    split at hu <;> simp only [Option.some.injEq, reduceCtorEq] at hu; subst hu
    simp only [ensAltErg]
  | slot t f i hL =>
    simp only [uOfB] at hu
    split at hu
    · cases hx : uOfIdx z art none (tN z t) (z.deklaration.count t) i <;> simp only [hx, Option.map_none, reduceCtorEq, Option.map_some, Option.some.injEq] at hu; subst hu
      simp only [ensAltErg]
    · simp only [reduceCtorEq] at hu
  | lt a b | le a b | eq a b =>
    simp only [uOfB] at hu
    cases xa : uOfS z art none a <;> cases xb : uOfS z art none b <;> simp only [xa, xb, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [ensAltErg, seite_ohne_erg art (sizeOf a + 1) a (by omega) _ xa,
  seite_ohne_erg art (sizeOf b + 1) b (by omega) _ xb, Bool.or_self]
  | and a b | or a b =>
    simp only [uOfB] at hu
    simp only [Expr.and.sizeOf_spec, Expr.or.sizeOf_spec] at hn
    cases xa : uOfB z art none a <;> cases xb : uOfB z art none b <;> simp only [xa, xb, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [ensAltErg, ih a (by omega) _ xa, ih b (by omega) _ xb, Bool.or_self]
  | not a =>
    simp only [uOfB] at hu
    simp only [Expr.not.sizeOf_spec] at hn
    cases xa : uOfB z art none a <;> simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [ensAltErg, ih a (by omega) _ xa]
  | forallSlots t body hL | existsSlots t body hL =>
    simp only [uOfB] at hu
    simp only [Expr.forallSlots.sizeOf_spec, sizeOf_default, add_zero, Expr.existsSlots.sizeOf_spec] at hn
    cases xa : uOfB z (artAuf (.index (tN z t)) art) none body <;> simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [ensAltErg, ih body (by omega) _ xa]
  | _ => simp only [uOfB, reduceCtorEq] at hu

/-- **A truth value in a body** (`uBool`: the predicate reader without `old`/`result`). -/
theorem bool_ok {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : EInv z ctx Γ Λ art) {τ : Ty} (e : Expr z.deklaration Γ Λ τ) (s : SExpr) (u : UEns)
    (hd : delabE z none e = .ok s) (hu : uOfB z art none e = some u) : uBool ctx s = .ok u := by
  have H' : EInv z { ctx with res := none, resBool := false } Γ Λ art :=
    { var := H.var, namen := H.namen, lits := H.lits, arrKonst := H.arrKonst, wrapsLeer := H.wrapsLeer, glob := H.glob, tab := H.tab, tabNr := H.tabNr,
      waechter := H.waechter }
  have h := sichert_ok none (sizeOf e + 1) H' (ergOk_none _ _) e (by omega) s u hd hu
  simp only [uBool, h, ens_ohne_erg (sizeOf e + 1) e (by omega) u hu, Bool.false_eq_true, ite_false]

end Gabbro.Grammatik.Gen.Text
