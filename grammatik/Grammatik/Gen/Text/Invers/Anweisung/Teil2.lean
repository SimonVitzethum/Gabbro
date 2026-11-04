module
public import Grammatik.Gen.Text.Invers.Anweisung.WertKopf

@[expose] public section
namespace Gabbro.Grammatik.Gen.Text
open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
variable {z : Spez} {V : Vertrag z.deklaration}

/-- A `let` without a type of a printed value is the general value reader. -/
theorem bindWert_allg (ctx : UCtx) (tabs : List UTab) (koepfe : List UFnKopf) (x : String) (s : SExpr)
    (h : kopfOk s = true)
    (hleft : ∀ op a b, s = .bin op a b → ∀ u, uWertBody ctx a = .ok u → ScalarType (uValueType ctx u)) :
    uBindWert ctx tabs koepfe false x none s = uBindWertAllg ctx false x none s := by
  have hr := regOrt_kopfOk ctx s h
  cases s with
  | fnref _ => simp only [kopfOk, Bool.false_eq_true] at h
  | call _ _ => simp only [kopfOk, Bool.false_eq_true] at h
  | why _ _ => simp only [kopfOk, Bool.false_eq_true] at h
  | float _ => simp only [kopfOk, Bool.false_eq_true] at h
  | bin op a b =>
    cases ha : uWertBody ctx a with
    | error err =>
      simp only [uBindWert, hr, ha, Except.toOption, Option.bind_eq_bind, Option.bind_none,
        Option.bind_fun_none]
    | ok left =>
      have ht := hleft op a b rfl left ha
      cases hty : uValueType ctx left with
      | none =>
        simp only [uBindWert, hr, ha, hty, Except.toOption, Option.bind_eq_bind, Option.bind_none,
          Option.bind_some, Option.bind_fun_none]
      | some ty =>
        cases ty <;> simp only [hty, ScalarType] at ht
        all_goals simp only [uBindWert, hr, ha, hty, Except.toOption, Option.bind_eq_bind,
          Option.bind_none, Option.bind_some, Option.bind_fun_none]
  | un op body =>
    cases body <;> simp only [kopfOk] at h
    all_goals first
      | (simp only [uBindWert, hr]; rfl)
      | (repeat' (split at h); all_goals simp_all only [Bool.false_eq_true, uBindWert, hr])
  | _ => simp only [uBindWert, hr]

/-- `let v = e;` of a number. -/
theorem bindWert_int {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (tabs : List UTab) (koepfe : List UFnKopf) {τ : Ty} (e : Expr z.deklaration Γ Λ τ)
    (s : SExpr) (u : USide) (hd : delabE z none e = .ok s) (hu : uOfS z art none e = some u) :
    uBindWert ctx tabs koepfe false (nVar Γ.length) none s =
      .ok (.bind (nVar Γ.length) none u, ctxMit ctx (nVar Γ.length) .int (.int 0 0) 0 [] ctx.loops) := by
  have accepted : (uOfS z art none e).isSome = true ∨ (uOfB z art none e).isSome = true :=
    Or.inl (by simp only [hu, Option.isSome_some])
  rw [bindWert_allg ctx tabs koepfe _ s (kopfOk_delab art none (sizeOf e + 1) e (by omega) s hd accepted)
    (printed_left_scalar H (sizeOf e + 1) e (by omega) s hd accepted)]
  have scalar := scalar_type H (sizeOf e + 1) e (by omega) u hu
  cases ht : uValueType ctx u with
  | none =>
    simp only [uBindWertAllg, wert_ok H.einv e s u hd hu, ht, uBindKopf, H.muts, List.filter_nil,
      Bool.false_eq_true, ↓reduceIte]
    rfl
  | some ty =>
    cases ty <;> simp only [ht, ScalarType] at scalar
    all_goals simp only [uBindWertAllg, wert_ok H.einv e s u hd hu, ht, uBindKopf, H.muts,
      List.filter_nil, Bool.false_eq_true, ↓reduceIte] <;> rfl

/-- `let v = p;` of a truth value. -/
theorem bindWert_bool {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (tabs : List UTab) (koepfe : List UFnKopf) {τ : Ty} (e : Expr z.deklaration Γ Λ τ)
    (s : SExpr) (u : UEns) (hd : delabE z none e = .ok s) (hu : uOfB z art none e = some u) :
    uBindWert ctx tabs koepfe false (nVar Γ.length) none s =
      .ok (.bindB (nVar Γ.length) u, ctxMit ctx (nVar Γ.length) .bool .bool 0 [] ctx.loops) := by
  have accepted : (uOfS z art none e).isSome = true ∨ (uOfB z art none e).isSome = true :=
    Or.inr (by simp only [hu, Option.isSome_some])
  rw [bindWert_allg ctx tabs koepfe _ s (kopfOk_delab art none (sizeOf e + 1) e (by omega) s hd accepted)
    (printed_left_scalar H (sizeOf e + 1) e (by omega) s hd accepted)]
  obtain ⟨err, he⟩ := wert_bool_fehler H.einv e s u hd hu
  simp only [uBindWertAllg, he, bool_ok H.einv e s u hd hu, H.muts, List.filter_nil]
  rfl

/-- The header of a printed `traverse`. -/
theorem schleifenKopf_ok {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (t : z.deklaration.Tab) (inv : Option SExpr) (iv : UEns)
    (hi : (inv = none ∧ iv = .tru) ∨ ∃ p, inv = some p ∧ uBool ctx p = .ok iv) :
    ∃ cnt, uSchleifenKopf ctx (nVar Γ.length) none "slots" (.variable (nTab (tN z t))) "unvisited" inv =
      .ok (nTab (tN z t), iv, ctxMit ctx (nVar Γ.length) (.index (tN z t)) (.index cnt) 0 ctx.muts
        (nVar Γ.length :: ctx.loops)) := by
  have h1 : strEq "slots" "slots" = true := by decide
  have h2 : strEq "unvisited" "unvisited" = true := by decide
  rcases hi with ⟨rfl, rfl⟩ | ⟨p, rfl, hp⟩
  · exact ⟨_, by simp only [uSchleifenKopf, Option.isSome_none, h1, h2, H.tabIdx t]; rfl⟩
  · exact ⟨_, by simp only [uSchleifenKopf, Option.isSome_none, h1, h2, H.tabIdx t, hp]; rfl⟩

/-- **`return v;`** -/
theorem ende_ok {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) {o : Option Ty} (ho : o = V.erg) (e : ErgExpr z.deklaration Γ Λ o)
    (v : Option SExpr) (r : URet) (hd : delabR z e = .ok v) (hu : uOfR z art e = some r) :
    uEnde ctx (some (.ret v)) = .ok r := by
  cases e with
  | empty =>
    simp only [delabR, Except.ok.injEq] at hd; subst hd
    simp only [uOfR, Option.some.injEq] at hu; subst hu
    obtain ⟨h1, h2⟩ := H.ergNone ho.symm
    simp only [uEnde, h1, h2, H.resOpt, Option.isSome_none, Bool.or_self, H.resSum, H.resTy, Bool.false_eq_true,
  ↓reduceIte]
  | val e =>
    simp only [delabR] at hd
    cases hs : delabE z none e with
    | error _ => simp only [bind, Except.bind, hs, reduceCtorEq] at hd
    | ok s =>
      simp only [hs, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
      subst hd
      rename_i τ
      cases τ with
      | bool =>
        simp only [uOfR] at hu
        cases hb : uOfB z art none e with
        | none => simp only [hb, Option.map_none, reduceCtorEq] at hu
        | some b =>
          simp only [hb, Option.map_some, Option.some.injEq] at hu; subst hu
          have hk := kopfOk_delab art none (sizeOf e + 1) e (by omega) s hs (Or.inr (by simp only [hb, Option.isSome_some]))
          obtain ⟨h1, h2⟩ := H.ergBool ho.symm
          have hw : ∀ a c, s ≠ .why a c := fun a c h => by subst h; simp only [kopfOk, Bool.false_eq_true] at hk
          cases s with
          | why a c => exact absurd rfl (hw a c)
          | _ => simp only [uEnde, H.resTy, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, H.resWhy, H.resSum, H.resOpt,
  h2, bool_ok H.einv e _ b hs hb]
      | int lo hi =>
        simp only [uOfR] at hu
        cases hb : uOfS z art none e with
        | none => simp only [hb, Option.map_none, reduceCtorEq] at hu
        | some b =>
          simp only [hb, Option.map_some, Option.some.injEq] at hu; subst hu
          have hk := kopfOk_delab art none (sizeOf e + 1) e (by omega) s hs (Or.inl (by simp only [hb, Option.isSome_some]))
          obtain ⟨h1, h2⟩ := H.ergInt lo hi ho.symm
          have hw : ∀ a c, s ≠ .why a c := fun a c h => by subst h; simp only [kopfOk, Bool.false_eq_true] at hk
          obtain ⟨rg, hrg⟩ := Option.isSome_iff_exists.1 h1
          cases s with
          | why a c => exact absurd rfl (hw a c)
          | _ => simp only [uEnde, H.resTy, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, H.resWhy, H.resSum, H.resOpt,
  h2, hrg, wert_ok H.einv e _ b hs hb]
      | _ => simp only [uOfR, reduceCtorEq] at hu

/-- **`return R::C;`** -/
theorem ende_why {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (r : Fin V.gruende) :
    uEnde ctx (some (.ret (some (.why (nGrund V.gruende) (nFall r.val))))) = .ok (.why r.val) := by
  obtain ⟨k, w, hk, hj, hw, hc⟩ := H.kanal (by have := r.isLt; omega)
  simp only [uEnde, H.resWhy, hj, uEndeKanal, hk, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hw,
  hc r.val r.isLt]

end Gabbro.Grammatik.Gen.Text
