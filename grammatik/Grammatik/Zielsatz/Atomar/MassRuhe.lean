/-
  File:      Grammatik/Zielsatz/Atomar/MassRuhe.lean
  Subject:   THE MEASURE DUTY ON `P` IS THE DUTY ON `P.mitRuhe` (2026-10-22): `massPflicht_mitRuhe`, the twin of
             `koerperGutSA_mitRuhe` (AtomarRuheNutzer.lean) for the `decreases` obligation.

  * `Mass.mitRuhe` -- the measure of `some f` is `f`'s, translated; the idle root has none. `Mass.wert_mitRuhe`: the
    same value on the translated world and arguments.
  * `zykS_mitRuhe` -- the cycle relation of `P.mitRuhe` at translated functions is `P`'s; the idle root lies on no
    cycle.
  * `rufRel_massTor` -- the measure gates of `D` and `D.mitRuhe` answer alike; with the label of a descent read back
    (`rufZ`, `LogikTreu`), a descent of the lifted body is a descent of the body.
-/
import Grammatik.Zielsatz.Atomar.AtomarRuheNutzer
import Grammatik.Logik.Terminierung.Entscheidung
import Grammatik.Nebenlaeufigkeit.Sperren.MitRuheStatisch

namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}

/-! ## 1. The measure, translated -/

/-- **The measure of `P.mitRuhe`**: `some f` carries `f`'s, translated; the idle root carries none. -/
def Mass.mitRuhe (m : Mass D) : Mass D.mitRuhe
  | none => []
  | some f => (m f).map fun e =>
      ⟨e.1, Expr.umΛ (anfang_map (D.signatur f)) (ruE e.2.1), (umΛ_orte _ _).trans ((ruE_orte _).trans e.2.2)⟩

theorem Mass.wert_mitRuhe (m : Mass D) (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) :
    m.mitRuhe.wert (some f) (worldR σ) (envR ρ) = m.wert f σ ρ := by
  unfold Mass.wert Mass.mitRuhe
  rw [List.map_map]
  apply List.map_congr_left
  intro e _
  show ((eval (worldR σ) (Expr.umΛ (anfang_map (D.signatur f)) (ruE e.2.1)) (worldR σ) (envR ρ) :
    Zahl 0 e.1)).n.toNat = _
  rw [eval_umΛ', eval_ru]

theorem Mass.laenge_mitRuhe (m : Mass D) (f : D.Fn) : (m.mitRuhe (some f)).length = (m f).length :=
  List.length_map _

theorem Mass.hat_mitRuhe (m : Mass D) (f : D.Fn) : m.mitRuhe.hat (some f) = m.hat f := by
  simp only [hat, mitRuhe, List.isEmpty_map]

/-! ## 2. The cycles, translated -/

section Zyklus

variable [DecidableEq D.Fn] (P : Programm D) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
  (hA : ∀ w, AbgK P fs (reachB P fs w))
include hvoll hA

theorem zykS_mitRuhe (f g : D.Fn) : zykS P.mitRuhe (fsRuhe fs) (some f) (some g) = zykS P fs f g := by
  unfold zykS zyklusMit
  rw [reachB_mitRuhe P hvoll hA, reachB_mitRuhe P hvoll hA]
  congr 1
  simp only [fsRuhe, List.any_cons, List.any_map, Function.comp_def,
    ruftB_mitRuhe_ruhe_ziel P (mVoll_of_abg P hA), Bool.false_and, Bool.false_or, ruftB_mitRuhe,
    reachB_mitRuhe P hvoll hA]
  apply congrArg (List.any fs)
  funext x
  exact congrArg _ (reachB_mitRuhe P hvoll hA x f)

omit hvoll hA in
theorem zykS_mitRuhe_ruhe (g : D.mitRuhe.Fn) : zykS P.mitRuhe (fsRuhe fs) none g = false := by
  unfold zykS
  simp only [ruftB_mitRuhe_ruhe, Bool.false_and, Bool.and_eq_false_imp, List.any_eq_false, Bool.false_eq_true,
  not_false_eq_true, implies_true]

omit hvoll hA in
theorem zykS_mitRuhe_zur_ruhe (f : D.Fn) : zykS P.mitRuhe (fsRuhe fs) (some f) none = false := by
  unfold zykS zyklusMit
  simp only [reachB_mitRuhe_ruhe, Bool.and_false, Bool.false_and]

end Zyklus

/-! ## 3. The measure gates answer alike -/

theorem ohneAbstieg_rufZuD
    {R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f}
    (h : OhneAbstieg R') : OhneAbstieg (rufZuD R') := by
  intro g σ ρ k hx
  unfold rufZuD at hx
  cases hy : R' (some g) (worldR σ) (envR ρ) with
  | ok => rw [hy] at hx; cases hx
  | why => rw [hy] at hx; cases hx
  | logik e' =>
      rw [hy] at hx
      simp only [rufZ, RufAusgang.logik.injEq] at hx
      unfold logikZ at hx
      split at hx
      · exact h _ _ _ _ hy
      · cases hx
  | hardware => rw [hy] at hx; cases hx

theorem rufRel_massTor {m : Mass D} {Z : D.Fn → Bool} {Z' : D.mitRuhe.Fn → Bool} {w : List Nat}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    {R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f}
    (h : RufRel R R') (hZ : ∀ g, Z' (some g) = Z g) :
    RufRel (massTor m Z w R) (massTor m.mitRuhe Z' w R') := by
  intro g σ ρ
  unfold massTor
  rw [hZ]
  erw [Mass.wert_mitRuhe]
  split
  · exact Or.inl rfl
  · exact h g σ ρ

/-! ## 4. The duty, transferred -/

section Transfer

variable [DecidableEq D.Fn] {P : Programm D} {fs : List D.Fn} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {T : D.Tab ⊕ D.Glob → Prop} {m : Mass D}

/-- **THE MEASURE DUTY ON `P` IS THE DUTY ON `P.mitRuhe`.** -/
theorem massPflicht_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs) (hA : ∀ w, AbgK P fs (reachB P fs w))
    (hM : ∀ f, MassPflicht P passes Q S T m (zykS P fs) f) :
    ∀ f', MassPflicht P.mitRuhe passes (axEnsRuhe Q) S.mitRuhe T m.mitRuhe (zykS P.mitRuhe (fsRuhe fs)) f'
  | none => massPflicht_ohne_zyklus P.mitRuhe (fsRuhe fs) passes _ _ T _ none (zykS_mitRuhe_ruhe P)
  | some f => by
    intro O' hr hl hq U' hU' A' hA' R' hR hOA hOV σ ρ hreq g' hz
    obtain ⟨σ0, rfl⟩ : ∃ σ0, σ = worldR σ0 := ⟨worldZ σ, (worldR_worldZ σ).symm⟩
    obtain ⟨ρ0, rfl⟩ : ∃ ρ0 : Env D (D.params f), ρ = envR ρ0 :=
      ⟨envZ ρ, (envR_envZ (Γ := D.params f) ρ).symm⟩
    have hreq0 : ReqAmEintritt P f σ0 ρ0 := (req_mitRuhe_iff P f σ0 ρ0).mp hreq
    cases g' with
    | none => rw [zykS_mitRuhe_zur_ruhe P] at hz; cases hz
    | some g =>
    have hzg : zykS P fs f g = true := by rwa [zykS_mitRuhe P hvoll hA] at hz
    have hk := hM f (Orakel.zurueck O') (rahmenO_zurueck hr) (regLokal_zurueck hl) (axVertrag_zurueck hq)
      (umweltZ U') (havocOk_umweltZ hU') (umweltZA A') (havocA_umweltZA hA') (rufZuD R')
      (respektiert_rufZuD hR) (ohneAbstieg_rufZuD hOA) (ohneVorbedingung_rufZuD R') σ0 ρ0 hreq0 g hzg
    have hrel := rumpfA_rel P S passes O' U' A' (massTor m (zykS P fs f) (m.wert f σ0 ρ0) (rufZuD R'))
      (massTor m.mitRuhe (zykS P.mitRuhe (fsRuhe fs) (some f)) (m.wert f σ0 ρ0) R')
      (rufRel_massTor (rufRel_rufZuD hOV) (fun g => zykS_mitRuhe P hvoll hA f g)) f σ0 ρ0
    erw [Mass.wert_mitRuhe]
    intro hx
    rcases hrel with e | ⟨e', e, h1, h2, ht⟩
    · have e := hx.symm.trans e
      cases hy : execEndHA (V := vertragVon D f) S (Orakel.zurueck O') (umweltZ U') (umweltZA A') passes
          (massTor m (zykS P fs f) (m.wert f σ0 ρ0) (rufZuD R')) (P.rumpf f) σ0 ρ0 with
      | logik e0 =>
          rw [hy] at e
          simp only [endR, EndAusgang.logik.injEq] at e
          have e := e.symm
          cases e0 with
          | abstieg g0 =>
              have hg : g0 = g := by
                injection e with e1
                injection e1 with e2
                injection e2
              subst hg
              exact hk hy
          | _ => injection e with e1; cases e1
      | zurueck => rw [hy] at e; cases e
      | why => rw [hy] at e; cases e
      | leave => rw [hy] at e; cases e
      | next => rw [hy] at e; cases e
      | hardware => rw [hy] at e; cases e
    · have h1 := hx.symm.trans h1
      cases h1
      exact hk (h2.trans (congrArg _ (ht.2 g rfl)))

end Transfer

/-! ## 5. A `forever`-free hull, translated -/

section Ewig

variable {V : Vertrag D}

theorem ewig_nachΛ {l : Bool} {Γ : Ctx} {Λ Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂) (s : Stmt D V l Γ Λ Λ₁)
    (eb ie dl : Bool) : (befS eb ie dl (Stmt.nachΛ h s)).ewig = (befS eb ie dl s).ewig := by
  subst h; rfl

theorem ewig_vorΛ {l : Bool} {Γ : Ctx} {Λ₁ Λ₂ Λ' : List (Res D)} (h : Λ₁ = Λ₂) (b : Block D V l Γ Λ₁ Λ')
    (eb ie : Bool) : (befB eb ie (Block.vorΛ h b)).ewig = (befB eb ie b).ewig := by
  subst h; rfl

theorem ewig_umΛE {l : Bool} {Γ : Ctx} {Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂) (e : Endblock D V l Γ Λ₁)
    (eb ie : Bool) : (befE eb ie (Endblock.umΛ h e)).ewig = (befE eb ie e).ewig := by
  subst h; rfl

mutual

theorem ewig_ruS : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (eb ie dl dl' : Bool),
    (befS eb ie dl (ruS s)).ewig = (befS eb ie dl' s).ewig
  | _, _, _, _, .assignSlot .., _, _, _, _ => rfl
  | _, _, _, _, .assignThru .., _, _, _, _ | _, _, _, _, .assignSlotRef .., _, _, _, _ => rfl
  | _, _, _, _, .assignGlob .., _, _, _, _ => rfl
  | _, _, _, _, .putBytes .., _, _, _, _ => rfl
  | _, _, _, _, .assignVar .., _, _, _, _ => rfl
  | _, _, _, _, .shift .., _, _, _, _ => rfl
  | _, _, _, _, .ite _ t e, eb, ie, _, _ => kongr₂ (· || ·) (ewig_ruB t eb ie) (ewig_ruB e eb ie)
  | _, _, _, _, .onOption _ p a, eb, ie, _, _ => kongr₂ (· || ·) (ewig_ruB p eb ie) (ewig_ruB a eb ie)
  | _, _, _, _, .onTag _ arms, eb, ie, _, _ => ewig_ruArms arms eb ie
  | _, _, _, _, .onWhy _ arms, eb, ie, _, _ => ewig_ruGArms arms eb ie
  | _, _, _, _, .call .., eb, ie, dl, _ => (ewig_nachΛ _ _ eb ie dl).trans rfl
  | _, _, _, _, .callInd .., eb, ie, dl, _ => (ewig_nachΛ _ _ eb ie dl).trans rfl
  | _, _, _, _, .locks _ _ body, eb, ie, _, _ => ewig_ruB body eb ie
  | _, _, _, _, .breaking _ body, eb, ie, _, _ => ewig_ruB body eb ie
  | _, _, _, _, .traverse _ _ body, _, ie, _, _ => ewig_ruB body false ie
  | _, _, _, _, .retry _ _ body ueber, eb, ie, _, _ => kongr₂ (· || ·) (ewig_ruB body false ie) (ewig_ruB ueber eb ie)
  | _, _, _, _, .forever _ _ body, _, _, _, _ => by simp only [ruS, befS, befund_und_ewig, Bool.true_or]
  | _, _, _, _, .axiomCall .., _, _, _, _ => rfl
  | _, _, _, _, .regWrite .., _, _, _, _ => rfl
  | _, _, _, _, .transition .., _, _, _, _ => rfl
  | _, _, _, _, .publish .., _, _, _, _ => rfl
  | _, _, _, _, .advances .., eb, ie, dl, _ => (ewig_nachΛ _ _ eb ie dl).trans rfl
  | _, _, _, _, .retires .., eb, ie, dl, _ => (ewig_nachΛ _ _ eb ie dl).trans rfl
  | _, _, _, _, .ret .., _, _, _, _ => rfl
  | _, _, _, _, .retWhy .., _, _, _, _ => rfl
  | _, _, _, _, .leave _, _, _, _, _ => rfl
  | _, _, _, _, .next _, _, _, _, _ => rfl

theorem ewig_ruB : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (eb ie : Bool),
    (befB eb ie (ruB b)).ewig = (befB eb ie b).ewig
  | _, _, _, _, .nil, _, _ => rfl
  | _, _, _, _, .cons s rest, eb, ie => kongr₂ (· || ·) (ewig_ruS s eb ie _ _) (ewig_ruB rest eb ie)
  | _, _, _, _, .bind _ rest, eb, ie => ewig_ruB rest eb ie
  | _, _, _, _, .bindCall _ _ _ _ _ rest, eb, ie => by
      simp only [ruB, befB, befund_und_ewig]
      exact kongr₂ (· || ·) rfl ((ewig_vorΛ _ _ eb ie).trans (ewig_ruB rest eb ie))
  | _, _, _, _, .bindCallInd _ _ _ _ _ rest, eb, ie => by
      simp only [ruB, befB, befund_und_ewig]
      exact kongr₂ (· || ·) rfl ((ewig_vorΛ _ _ eb ie).trans (ewig_ruB rest eb ie))
  | _, _, _, _, .bindCallElse _ _ _ _ _ err rest, eb, ie => by
      simp only [ruB, befB, befund_und_ewig]
      exact kongr₂ (· || ·) (kongr₂ (· || ·) rfl ((ewig_umΛE _ _ eb ie).trans (ewig_ruEnd err eb ie)))
        ((ewig_vorΛ _ _ eb ie).trans (ewig_ruB rest eb ie))
  | _, _, _, _, .bindAxiom _ _ _ _ _ _ _ rest, eb, ie => ewig_ruB rest eb ie
  | _, _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest, eb, ie => kongr₂ (· || ·) (ewig_ruEnd err eb ie) (ewig_ruB rest eb ie)
  | _, _, _, _, .regRead _ _ rest, eb, ie => ewig_ruB rest eb ie
  | _, _, _, _, .regReadElse _ _ _ sonst rest, eb, ie => kongr₂ (· || ·) (ewig_ruEnd sonst eb ie) (ewig_ruB rest eb ie)
  | _, _, _, _, .awaits _ _ _ _ _ rest, eb, ie => ewig_ruB rest eb ie
  | _, _, _, _, .exchange _ _ _ _ rest, eb, ie => ewig_ruB rest eb ie
  | _, _, _, _, .narrow _ _ _ sonst rest, eb, ie => kongr₂ (· || ·) (ewig_ruEnd sonst eb ie) (ewig_ruB rest eb ie)
  | _, _, _, _, .check _ sonst rest, eb, ie => kongr₂ (· || ·) (ewig_ruEnd sonst eb ie) (ewig_ruB rest eb ie)
  | _, _, _, _, .float _ _ _ _ _ rest, eb, ie => ewig_ruB rest eb ie
  | _, _, _, _, .floatLit _ _ _ rest, eb, ie => ewig_ruB rest eb ie
  | _, _, _, _, .floatOf _ _ _ rest, eb, ie => ewig_ruB rest eb ie
  | _, _, _, _, .floatNarrow _ _ _ sonst rest, eb, ie => kongr₂ (· || ·) (ewig_ruEnd sonst eb ie) (ewig_ruB rest eb ie)

theorem ewig_ruEnd : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) (eb ie : Bool),
    (befE eb ie (ruEnd e)).ewig = (befE eb ie e).ewig
  | _, _, _, .ret .., _, _ => rfl
  | _, _, _, .retWhy .., _, _ => rfl
  | _, _, _, .leave _, _, _ => rfl
  | _, _, _, .next _, _, _ => rfl
  | _, _, _, .cons s rest, eb, ie => kongr₂ (· || ·) (ewig_ruS s eb ie _ _) (ewig_ruEnd rest eb ie)
  | _, _, _, .bind _ rest, eb, ie => ewig_ruEnd rest eb ie
  | _, _, _, .bindCall _ _ _ _ _ rest, eb, ie => by
      simp only [ruEnd, befE, befund_und_ewig]
      exact kongr₂ (· || ·) rfl ((ewig_umΛE _ _ eb ie).trans (ewig_ruEnd rest eb ie))
  | _, _, _, .bindCallElse _ _ _ _ _ err rest, eb, ie => by
      simp only [ruEnd, befE, befund_und_ewig]
      exact kongr₂ (· || ·) (kongr₂ (· || ·) rfl ((ewig_umΛE _ _ eb ie).trans (ewig_ruEnd err eb ie)))
        ((ewig_umΛE _ _ eb ie).trans (ewig_ruEnd rest eb ie))
  | _, _, _, .bindAxiom _ _ _ _ _ _ _ rest, eb, ie => ewig_ruEnd rest eb ie
  | _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest, eb, ie => kongr₂ (· || ·) (ewig_ruEnd err eb ie) (ewig_ruEnd rest eb ie)
  | _, _, _, .regRead _ _ rest, eb, ie => ewig_ruEnd rest eb ie
  | _, _, _, .regReadElse _ _ _ sonst rest, eb, ie => kongr₂ (· || ·) (ewig_ruEnd sonst eb ie) (ewig_ruEnd rest eb ie)
  | _, _, _, .awaits _ _ _ _ _ rest, eb, ie => ewig_ruEnd rest eb ie
  | _, _, _, .bindCallInd _ _ _ _ _ rest, eb, ie => by
      simp only [ruEnd, befE, befund_und_ewig]
      exact kongr₂ (· || ·) rfl ((ewig_umΛE _ _ eb ie).trans (ewig_ruEnd rest eb ie))
  | _, _, _, .narrow _ _ _ sonst rest, eb, ie => kongr₂ (· || ·) (ewig_ruEnd sonst eb ie) (ewig_ruEnd rest eb ie)
  | _, _, _, .exchange _ _ _ _ rest, eb, ie => ewig_ruEnd rest eb ie
  | _, _, _, .ite _ t e, eb, ie => kongr₂ (· || ·) (ewig_ruEnd e eb ie) (ewig_ruEnd t eb ie)

theorem ewig_ruArms : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    (arms : Arms D V l Γ Λ Λ' cs) (eb ie : Bool), (befArms eb ie (ruArms arms)).ewig = (befArms eb ie arms).ewig
  | _, _, _, _, _, .nil, _, _ => rfl
  | _, _, _, _, _, .cons (c := none) b rest, eb, ie => kongr₂ (· || ·) (ewig_ruB b eb ie) (ewig_ruArms rest eb ie)
  | _, _, _, _, _, .cons (c := some (_, _)) b rest, eb, ie => kongr₂ (· || ·) (ewig_ruB b eb ie) (ewig_ruArms rest eb ie)

theorem ewig_ruGArms : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n) (eb ie : Bool), (befGArms eb ie (ruGArms arms)).ewig = (befGArms eb ie arms).ewig
  | _, _, _, _, _, .nil, _, _ => rfl
  | _, _, _, _, _, .cons b rest, eb, ie => kongr₂ (· || ·) (ewig_ruB b eb ie) (ewig_ruGArms rest eb ie)

end

end Ewig

section EwigFrei

variable [DecidableEq D.Fn] (P : Programm D) {fs : List D.Fn}

theorem befund_mitRuhe_ewig (h : D.Fn) : (befund P.mitRuhe (some h)).ewig = (befund P h).ewig := by
  unfold befund
  show (befE false false (Endblock.umΛ (anfang_map (D.signatur h)) (ruEnd (P.rumpf h)))).ewig = _
  rw [ewig_umΛE, ewig_ruEnd]

/-- **A `forever`-free hull stays `forever`-free on `P.mitRuhe`.** -/
theorem ewigFrei_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs) (hA : ∀ w, AbgK P fs (reachB P fs w)) {w : D.Fn}
    (h : ewigFrei P fs w = true) : ewigFrei P.mitRuhe (fsRuhe fs) (some w) = true := by
  unfold ewigFrei at h ⊢
  simp only [fsRuhe, List.all_cons, List.all_map, Function.comp_def, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · have := reachB_mitRuhe_nicht_ruhe P hA w
    simp only [fsRuhe] at this
    simp only [this, Bool.not_false, Bool.true_or]
  · rw [← h]
    apply congrArg (List.all fs)
    funext x
    rw [befund_mitRuhe_ewig]
    exact congrArg (fun b => !b || !(befund P x).ewig) (reachB_mitRuhe P hvoll hA w x)

/-- The idle root reaches no `forever`. -/
theorem ewigFrei_mitRuhe_ruhe : ewigFrei P.mitRuhe (fsRuhe fs) none = true := by
  unfold ewigFrei
  simp only [fsRuhe, List.all_cons, List.all_map, Function.comp_def, Bool.and_eq_true]
  refine ⟨?_, List.all_eq_true.2 fun x _ => ?_⟩
  · have hb : (befund P.mitRuhe none).ewig = false := rfl
    simp only [hb, Bool.not_false, Bool.or_true]
  · have := reachB_mitRuhe_ruhe (P := P) (fs := fs) x
    simp only [fsRuhe] at this
    simp only [this, Bool.not_false, Bool.true_or]

end EwigFrei

end Gabbro.Grammatik
