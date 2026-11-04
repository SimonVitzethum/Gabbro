module

public import Grammatik.Gen.Text.Invers.Namen
public import Grammatik.Gen.Text.Invers.Ausdruck.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Gen.Text
open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
variable (z : Spez)
variable {z}

/-- **The side**: the arithmetic layer over a leaf reader that answers the printed leaves reads every printed
    number back. -/
theorem rechne_ok {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    {kopf : Option Nat} (H : EInvK z ctx Γ Λ art kopf) (bl : SExpr → Except String USide)
    (hB : Blatt (z := z) ctx Γ Λ art kopf bl) (n : Nat) :
    ∀ {τ : Ty} (e : Expr z.deklaration Γ Λ τ), sizeOf e < n → ∀ (s : SExpr) (u : USide),
      delabE z kopf e = .ok s → uOfS z art kopf e = some u → uRechne ctx bl s = .ok u := by
  induction n with
  | zero => intro _ _ h; omega
  | succ n ih =>
  intro τ e hn s u hd hu
  cases e with
  | lit m =>
    simp only [delabE, Except.ok.injEq] at hd
    subst hd
    simp only [uOfS, Option.some.injEq] at hu
    subst hu
    by_cases h : 0 ≤ m
    · simp only [zahlE, h, ite_true]
      simp only [uRechne, hB.lit]
      simp only [Int.ofNat_eq_natCast, Int.toNat_of_nonneg h]
    · simp only [zahlE, h, ite_false]
      simp only [uRechne]
      simp only [Int.ofNat_eq_natCast, Int.toNat_of_nonneg (show 0 ≤ -m by omega), neg_neg]
  | var x =>
    simp only [delabE, Except.ok.injEq] at hd
    subst hd
    simp only [uOfS] at hu
    split at hu
    · rename_i hk
      split at hu
      · rename_i hτ
        simp only [Option.some.injEq] at hu
        subst hu
        simp only [hk, ite_true, uRechne]
        exact hB.res x hτ hk
      · simp only [reduceCtorEq] at hu
    · rename_i hk
      simp only [hk, ite_false, uRechne]
      split at hu
      · simp only [reduceCtorEq] at hu
      · simp only [reduceCtorEq] at hu
      · simp only [reduceCtorEq] at hu
      · rename_i hp hb hr
        simp only [Option.some.injEq] at hu
        subst hu
        exact hB.var (tiefe x) (tiefe_lt x) hk hp hb (fun n h => hr n h)
  | glob g hL =>
    simp only [delabE, Except.ok.injEq] at hd
    subst hd
    simp only [uOfS] at hu
    split at hu
    · simp only [reduceCtorEq] at hu
    · rename_i hg
      simp only [Option.some.injEq] at hu
      subst hu
      simp only [uRechne]
      exact hB.glob g hg
  | slot t f i hL =>
    simp only [delabE] at hd
    cases hi : delabE z kopf i with
    | error _ => simp only [hi] at hd; cases hd
    | ok i' =>
      simp only [hi, bind, Except.bind, Except.ok.injEq] at hd
      subst hd
      simp only [uOfS] at hu
      split at hu
      · simp only [reduceCtorEq] at hu
      · rename_i hb
        cases hx : uOfIdx z art kopf (tN z t) (z.deklaration.count t) i with
        | none => simp only [hx, Option.map_none, reduceCtorEq] at hu
        | some ix =>
          simp only [hx, Option.map_some, Option.some.injEq] at hu
          subst hu
          have := hB.slot t f i' ix (idx_ok H t (sizeOf i + 1) i (by omega) i' ix hi hx) hL hb
          simp only [slotS] at this
          simp only [uRechne, this]
  | widen h1 h2 e =>
    simp only [delabE] at hd
    simp only [uOfS] at hu
    exact ih e (by simp only [Expr.widen.sizeOf_spec, sizeOf_default, add_zero] at hn; omega) s u hd hu
  | add a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok sa =>
    cases hb : delabE z kopf b with
    | error _ => simp only [bind, Except.bind, ha, hb, reduceCtorEq] at hd
    | ok sb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfS] at hu
    cases xa : uOfS z art kopf a with
    | none => simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some x =>
    cases xb : uOfS z art kopf b with
    | none => simp only [xa, xb, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
    | some y =>
    simp only [xa, xb, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [Expr.add.sizeOf_spec] at hn
    exact (rechne_bin ctx bl "+" sa sb x y (ih a (by omega) sa x ha xa) (ih b (by omega) sb y hb xb)).1 rfl
  | sub a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok sa =>
    cases hb : delabE z kopf b with
    | error _ => simp only [bind, Except.bind, ha, hb, reduceCtorEq] at hd
    | ok sb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfS] at hu
    cases xa : uOfS z art kopf a with
    | none => simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some x =>
    cases xb : uOfS z art kopf b with
    | none => simp only [xa, xb, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
    | some y =>
    simp only [xa, xb, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [Expr.sub.sizeOf_spec] at hn
    exact (rechne_bin ctx bl "-" sa sb x y (ih a (by omega) sa x ha xa) (ih b (by omega) sb y hb xb)).2.1 rfl
  | mul a b =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok sa =>
    cases hb : delabE z kopf b with
    | error _ => simp only [bind, Except.bind, ha, hb, reduceCtorEq] at hd
    | ok sb =>
    simp only [ha, hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfS] at hu
    cases xa : uOfS z art kopf a with
    | none => simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some x =>
    cases xb : uOfS z art kopf b with
    | none => simp only [xa, xb, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
    | some y =>
    simp only [xa, xb, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [Expr.mul.sizeOf_spec] at hn
    exact (rechne_bin ctx bl "*" sa sb x y (ih a (by omega) sa x ha xa) (ih b (by omega) sb y hb xb)).2.2 rfl
  | neg a =>
    simp only [delabE] at hd
    cases ha : delabE z kopf a with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok sa =>
    simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfS] at hu
    cases xa : uOfS z art kopf a with
    | none => simp only [xa, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some x =>
    simp only [xa, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [Expr.neg.sizeOf_spec] at hn
    have hx := ih a (by omega) sa x ha xa
    cases sa with
    | lit m => simp only [uRechne] at hx ⊢; simp only [hx]
    | _ => simp only [uRechne] at hx ⊢ <;> simp only [hx]
  | _ => simp only [uOfS, reduceCtorEq] at hu

/-- **A number in an `ensures`/`requires`**. -/
theorem seite_ok {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    {kopf : Option Nat} (H : EInvK z ctx Γ Λ art kopf) (hr : ErgOk ctx Γ kopf)
    {τ : Ty} (e : Expr z.deklaration Γ Λ τ) (s : SExpr) (u : USide)
    (hd : delabE z kopf e = .ok s) (hu : uOfS z art kopf e = some u) : uSeite ctx s = .ok u :=
  rechne_ok H _ (blatt_seite H hr) (sizeOf e + 1) e (by omega) s u hd hu

/-- **A number in a body**. -/
theorem wert_ok {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : EInv z ctx Γ Λ art) {τ : Ty} (e : Expr z.deklaration Γ Λ τ) (s : SExpr) (u : USide)
    (hd : delabE z none e = .ok s) (hu : uOfS z art none e = some u) : uWertBody ctx s = .ok u :=
  rechne_ok H _ (blatt_wert H) (sizeOf e + 1) e (by omega) s u hd hu

theorem uParamNrAux_succ : ∀ (ns : List String) (k : Nat) (y : String) (j : Nat),
    uParamNrAux ns k y = .ok j → uParamNrAux ns (k + 1) y = .ok (j + 1)
  | [], _, _, _, h => by simp only [uParamNrAux, reduceCtorEq] at h
  | q :: rest, k, y, j, h => by
    simp only [uParamNrAux] at h ⊢
    split at h
    · simp only [Except.ok.injEq] at h; subst h; simp only [↓reduceIte, *]
    · simp only [*, Bool.false_eq_true, ite_false]
      exact uParamNrAux_succ rest (k + 1) y j h

/-- The scope under a quantifier binder `v{|Γ|}` over the table `t`. -/
def ctxAuf (ctx : UCtx) (x : String) (num : Nat) (c : Int) : UCtx :=
  { ctx with names := x :: ctx.names, kinds := .index num :: ctx.kinds, types := Ty.index c :: ctx.types,
             bits := 0 :: ctx.bits }

theorem EInvK.auf {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    {kopf : Option Nat} (H : EInvK z ctx Γ Λ art kopf) (t : z.deklaration.Tab) :
    EInvK z (ctxAuf ctx (nVar Γ.length) (tN z t) (z.deklaration.count t)) (.index (z.deklaration.count t) :: Γ) Λ
      (artAuf (.index (tN z t)) art) kopf where
  var d hd hk := by
    cases d with
    | zero =>
      refine ⟨0, ?_, rfl⟩
      simp only [uParamNr, ctxAuf, List.length_cons, Nat.add_one_sub_one, Nat.sub_zero, uParamNrAux, strEq_nVar,
  BEq.rfl, ↓reduceIte]
    | succ d =>
      simp only [List.length_cons] at hd hk
      have hk' : kopf ≠ some (Γ.length - 1 - d) := by
        have : Γ.length + 1 - 1 - (d + 1) = Γ.length - 1 - d := by omega
        rw [this] at hk; exact hk
      obtain ⟨j, hj, ha⟩ := H.var d (by omega) hk'
      refine ⟨j + 1, ?_, ha⟩
      have hne : strEq (nVar Γ.length) (nVar (Γ.length + 1 - 1 - (d + 1))) = false := by
        simp only [strEq_nVar, beq_eq_false_iff_ne]; omega
      simp only [uParamNr, ctxAuf, List.length_cons, uParamNrAux, hne, Bool.false_eq_true, ite_false]
      have : Γ.length + 1 - 1 - (d + 1) = Γ.length - 1 - d := by omega
      rw [this]
      exact uParamNrAux_succ _ 0 _ j hj
  namen n hn := by
    simp only [ctxAuf, List.mem_cons] at hn
    rcases hn with rfl | hn
    · exact Or.inl ⟨_, rfl⟩
    · exact H.namen n hn
  lits := H.lits
  arrKonst := H.arrKonst
  glob := H.glob
  tab := H.tab
  wrapsLeer := H.wrapsLeer
  tabNr := H.tabNr
  waechter := H.waechter

theorem rechne_vgl (ctx : UCtx) (op : String) (a b : SExpr) (x y : USide)
    (ha : uSeite ctx a = .ok x) (hb : uSeite ctx b = .ok y) (hop : op = "<" ∨ op = "<=" ∨ op = "==") :
    uSichert ctx (.bin op a b) = .ok (.cmp op x y) := by
  rcases hop with rfl | rfl | rfl <;> simp only [uSichert, uIstVgl, ↓reduceIte, ha, hb]

end Gabbro.Grammatik.Gen.Text
