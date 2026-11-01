module

public import Grammatik.Gen.Text.Invers.Ausdruck
public import Grammatik.Gen.Text.Invers.Anweisung.Teil1

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
          simp only [uWertBody, uRechne, uWertBlatt, uGrenzwort, hz, H.boolFeld t f, hb, decide_true, ↓reduceIte,
  Except.error.injEq, exists_eq']
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
  | neg a | not a =>
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

/-- A `let` without a type of a printed value is the general value reader. -/
theorem bindWert_allg (ctx : UCtx) (tabs : List UTab) (koepfe : List UFnKopf) (x : String) (s : SExpr)
    (h : kopfOk s = true) : uBindWert ctx tabs koepfe false x none s = uBindWertAllg ctx false x none s := by
  have hr := regOrt_kopfOk ctx s h
  cases s with
  | fnref _ => simp only [kopfOk, Bool.false_eq_true] at h
  | call _ _ => simp only [kopfOk, Bool.false_eq_true] at h
  | why _ _ => simp only [kopfOk, Bool.false_eq_true] at h
  | _ => simp only [uBindWert, hr]

/-- `let v = e;` of a number. -/
theorem bindWert_int {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (tabs : List UTab) (koepfe : List UFnKopf) {τ : Ty} (e : Expr z.deklaration Γ Λ τ)
    (s : SExpr) (u : USide) (hd : delabE z none e = .ok s) (hu : uOfS z art none e = some u) :
    uBindWert ctx tabs koepfe false (nVar Γ.length) none s =
      .ok (.bind (nVar Γ.length) none u, ctxMit ctx (nVar Γ.length) .int (.int 0 0) 0 [] ctx.loops) := by
  rw [bindWert_allg ctx tabs koepfe _ s (kopfOk_delab art none (sizeOf e + 1) e (by omega) s hd (Or.inl (by simp only [hu, Option.isSome_some])))]
  simp only [uBindWertAllg, wert_ok H.einv e s u hd hu, uBindKopf, H.muts, List.filter_nil, Bool.false_eq_true,
    ite_false]
  rfl

/-- `let v = p;` of a truth value. -/
theorem bindWert_bool {ctx : UCtx} {Γ : Ctx} {Λ : List (Res z.deklaration)} {art : Nat → UParamArt}
    (H : SInv z V ctx Γ Λ art) (tabs : List UTab) (koepfe : List UFnKopf) {τ : Ty} (e : Expr z.deklaration Γ Λ τ)
    (s : SExpr) (u : UEns) (hd : delabE z none e = .ok s) (hu : uOfB z art none e = some u) :
    uBindWert ctx tabs koepfe false (nVar Γ.length) none s =
      .ok (.bindB (nVar Γ.length) u, ctxMit ctx (nVar Γ.length) .bool .bool 0 [] ctx.loops) := by
  rw [bindWert_allg ctx tabs koepfe _ s (kopfOk_delab art none (sizeOf e + 1) e (by omega) s hd (Or.inr (by simp only [hu, Option.isSome_some])))]
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
