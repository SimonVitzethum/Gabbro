module

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre
public import Grammatik.Speichermodell.Maschine.SperreSemA
public import Grammatik.Speichermodell.Atomar.AtomarRuhe.Teil2

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section HauptA
variable (S : SperrInv D) (O : Orakel D) (O' : Orakel D.mitRuhe) (hO : OrakelRu O O')
  (U : Umwelt D) (U' : Umwelt D.mitRuhe) (A : AUmwelt D) (A' : AUmwelt D.mitRuhe) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f)
  (hU : ∀ L σ, U' L (worldR σ) = worldR (U L σ))
  (hA : ∀ X σ, A' X (worldR σ) = worldR (A X σ))
  (hR : RufRel R R')
include hO hU hA hR

set_option linter.unusedSectionVars false in
theorem execBlockHA_ru_awaits {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (g)
    (payload)
    (hp)
    (hL)
    (hat)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R rest σ ρ))
    : AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB (.awaits g payload hp hL hat rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R (.awaits g payload hp hL hat rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockHA]
  rw [show ([Sum.inr g] : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) = [Sum.inr g] from rfl,
    worldR_fragt, leseA_worldR hA, hO.sichtbar]
  cases O.sichtbar g (leseA A (σ.fragt (.inr (.inr g))) Λ [Sum.inr g]) with
  | false => exact Or.inl rfl
  | true =>
      simp only [if_true]
      exact AusRelRu.schrumpf (ih_execBlockHA_ru_rest (leseA A (σ.fragt (.inr (.inr g))) Λ [Sum.inr g])
        (Env.cons ((leseA A (σ.fragt (.inr (.inr g))) Λ [Sum.inr g]).globs g) ρ))

set_option linter.unusedSectionVars false in
theorem execBlockHA_ru_exchange {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (g)
    (neu)
    (hw)
    (hL)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R rest σ ρ))
    : AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB (.exchange g neu hw hL rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R (.exchange g neu hw hL rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockHA]
  rw [show (Sum.inr g :: (ruE neu).orte : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) =
    Sum.inr g :: neu.orte from congrArg (Sum.inr g :: ·) (ruE_orte neu), leseA_worldR hA]
  have ez := eval_ru (leseA A σ Λ (Sum.inr g :: neu.orte)) (leseA A σ Λ (Sum.inr g :: neu.orte)) neu
    (Env.cons ((leseA A σ Λ (Sum.inr g :: neu.orte)).globs g) ρ)
  change eval _ (ruE neu) _ (Env.cons (valR _ _) (envR ρ)) = _ at ez
  rw [show ((worldR (leseA A σ Λ (Sum.inr g :: neu.orte))).globs g) =
    valR _ ((leseA A σ Λ (Sum.inr g :: neu.orte)).globs g) from rfl, ez, schreibGlob_worldR]
  exact AusRelRu.schrumpf (ih_execBlockHA_ru_rest
    ((leseA A σ Λ (Sum.inr g :: neu.orte)).schreibGlob g Λ (eval (leseA A σ Λ (Sum.inr g :: neu.orte)) neu
      (leseA A σ Λ (Sum.inr g :: neu.orte)) (Env.cons ((leseA A σ Λ (Sum.inr g :: neu.orte)).globs g) ρ)))
    (Env.cons ((leseA A σ Λ (Sum.inr g :: neu.orte)).globs g) ρ))

set_option linter.unusedSectionVars false in
theorem execBlockHA_ru_narrow {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_lo}
    {zi_hi}
    (e)
    (lo')
    (hi')
    (sonst)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R rest σ ρ))
    (ih_execEndHA_ru_sonst : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd sonst) (worldR σ) (envR ρ)) (execEndHA S O U A passes R sonst σ ρ))
    : AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockHA]
  have hread : leseA A' (worldR σ) (Λ.map resR) (ruE e).orte =
      worldR (leseA A σ Λ e.orte) :=
    (leseA_worldR hA σ Λ _).trans
      (congrArg (fun os => worldR (leseA A σ Λ os)) (ruE_orte e))
  have hv : @Eq (Zahl zi_lo zi_hi)
      (eval (leseA A' (worldR σ) (Λ.map resR) (ruE e).orte) (ruE e)
        (leseA A' (worldR σ) (Λ.map resR) (ruE e).orte) (envR ρ))
      (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ) :=
    (congrArg (fun W => eval W (ruE e) W (envR ρ)) hread).trans
      (eval_ru (leseA A σ Λ e.orte) (leseA A σ Λ e.orte) e ρ)
  let branch (W : World D.mitRuhe) (z : Zahl zi_lo zi_hi) :
      Ausgang (vertragR V) l (Γ.map tyR) :=
    if h : lo' ≤ z.n ∧ z.n ≤ hi' then
      (execBlockHA S.mitRuhe O' U' A' passes R' (ruB rest) W
        (Env.cons (τ := .int lo' hi') ⟨z.n, h.1, h.2⟩ (envR ρ))).schrumpf
    else (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd sonst) W (envR ρ)).zuAusgang
  change AusRelRu (branch (leseA A' (worldR σ) (Λ.map resR) (ruE e).orte)
    (eval (leseA A' (worldR σ) (Λ.map resR) (ruE e).orte) (ruE e)
      (leseA A' (worldR σ) (Λ.map resR) (ruE e).orte) (envR ρ))) _
  erw [hv, hread]
  dsimp only [branch]
  by_cases hc : lo' ≤ (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ∧
      (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ≤ hi'
  · erw [dif_pos hc, dif_pos hc]
    exact AusRelRu.schrumpf (ih_execBlockHA_ru_rest _
      (Env.cons (⟨(eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n, hc.1, hc.2⟩ : Zahl lo' hi') ρ))
  · erw [dif_neg hc, dif_neg hc]
    exact EndRel.zuAusgang (ih_execEndHA_ru_sonst _ ρ)

set_option linter.unusedSectionVars false in
theorem execBlockHA_ru_narrowRequired {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_lo}
    {zi_hi}
    (e)
    (lo')
    (hi')
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R rest σ ρ))
    : AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB (.narrowRequired (lo := zi_lo) (hi := zi_hi) e lo' hi' rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R (.narrowRequired (lo := zi_lo) (hi := zi_hi) e lo' hi' rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockHA]
  have hread : leseA A' (worldR σ) (Λ.map resR) (ruE e).orte =
      worldR (leseA A σ Λ e.orte) :=
    (leseA_worldR hA σ Λ _).trans
      (congrArg (fun os => worldR (leseA A σ Λ os)) (ruE_orte e))
  have hv : @Eq (Zahl zi_lo zi_hi)
      (eval (leseA A' (worldR σ) (Λ.map resR) (ruE e).orte) (ruE e)
        (leseA A' (worldR σ) (Λ.map resR) (ruE e).orte) (envR ρ))
      (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ) :=
    (congrArg (fun W => eval W (ruE e) W (envR ρ)) hread).trans
      (eval_ru (leseA A σ Λ e.orte) (leseA A σ Λ e.orte) e ρ)
  let branch (W : World D.mitRuhe) (z : Zahl zi_lo zi_hi) :
      Ausgang (vertragR V) l (Γ.map tyR) :=
    if h : lo' ≤ z.n ∧ z.n ≤ hi' then
      (execBlockHA S.mitRuhe O' U' A' passes R' (ruB rest) W
        (Env.cons (τ := .int lo' hi') ⟨z.n, h.1, h.2⟩ (envR ρ))).schrumpf
    else .logik .kapazitaet
  change AusRelRu (branch (leseA A' (worldR σ) (Λ.map resR) (ruE e).orte)
    (eval (leseA A' (worldR σ) (Λ.map resR) (ruE e).orte) (ruE e)
      (leseA A' (worldR σ) (Λ.map resR) (ruE e).orte) (envR ρ))) _
  erw [hv, hread]
  dsimp only [branch]
  by_cases hc : lo' ≤ (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ∧
      (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ≤ hi'
  · erw [dif_pos hc, dif_pos hc]
    exact AusRelRu.schrumpf (ih_execBlockHA_ru_rest _
      (Env.cons (⟨(eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n, hc.1, hc.2⟩ : Zahl lo' hi') ρ))
  · erw [dif_neg hc, dif_neg hc]
    exact Or.inl rfl

set_option linter.unusedSectionVars false in
theorem execBlockHA_ru_check {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (c)
    (sonst)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R rest σ ρ))
    (ih_execEndHA_ru_sonst : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd sonst) (worldR σ) (envR ρ)) (execEndHA S O U A passes R sonst σ ρ))
    : AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB (.check c sonst rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R (.check c sonst rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockHA]
  erw [ruE_orte, leseA_worldR hA, eval_ru]
  cases h : (eval (leseA A σ Λ c.orte) c (leseA A σ Λ c.orte) ρ : Bool) with
  | false =>
      simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
      exact EndRel.zuAusgang (ih_execEndHA_ru_sonst _ ρ)
  | true =>
      simp only [wahr?, valR_bool, h, if_true]
      exact ih_execBlockHA_ru_rest _ ρ

set_option linter.unusedSectionVars false in
theorem execBlockHA_ru_float {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_l1}
    {zi_h1}
    {zi_l2}
    {zi_h2}
    (op)
    (a)
    (b)
    (lo)
    (hi)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R rest σ ρ))
    : AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockHA]
  erw [orte2, leseA_worldR hA, eval_ru, eval_ru]
  have ha := congrArg (fun v : Gleit zi_l1 zi_h1 => v.x)
    (valR_fl (D := D)
      (eval (leseA A σ Λ (a.orte ++ b.orte)) a (leseA A σ Λ (a.orte ++ b.orte)) ρ))
  have hb := congrArg (fun v : Gleit zi_l2 zi_h2 => v.x)
    (valR_fl (D := D)
      (eval (leseA A σ Λ (a.orte ++ b.orte)) b (leseA A σ Λ (a.orte ++ b.orte)) ρ))
  erw [ha, hb]
  cases gleitPasst lo hi (gleitRechne op
      (eval (leseA A σ Λ (a.orte ++ b.orte)) a (leseA A σ Λ (a.orte ++ b.orte)) ρ).x
      (eval (leseA A σ Λ (a.orte ++ b.orte)) b (leseA A σ Λ (a.orte ++ b.orte)) ρ).x) with
  | none => exact Or.inl rfl
  | some v => exact AusRelRu.schrumpf (ih_execBlockHA_ru_rest _ (Env.cons v ρ))

set_option linter.unusedSectionVars false in
theorem execBlockHA_ru_floatLit {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (q)
    (lo)
    (hi)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R rest σ ρ))
    : AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB (.floatLit q lo hi rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R (.floatLit q lo hi rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockHA]
  cases gleitPasst lo hi (bruch q) with
  | none => exact Or.inl rfl
  | some v => exact AusRelRu.schrumpf (ih_execBlockHA_ru_rest _ (Env.cons v ρ))

set_option linter.unusedSectionVars false in
theorem execBlockHA_ru_floatOf {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_l1}
    {zi_h1}
    (e)
    (lo)
    (hi)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R rest σ ρ))
    : AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockHA]
  erw [ruE_orte, leseA_worldR hA, eval_ru]
  have he := congrArg (fun v : Zahl zi_l1 zi_h1 => v.n)
    (valR_int (D := D) (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ))
  erw [he]
  cases gleitPasst lo hi (gleitAusInt (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n) with
  | none => exact Or.inl rfl
  | some v => exact AusRelRu.schrumpf (ih_execBlockHA_ru_rest _ (Env.cons v ρ))

set_option linter.unusedSectionVars false in
theorem execBlockHA_ru_floatNarrow {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_l1}
    {zi_h1}
    (e)
    (lo)
    (hi)
    (sonst)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execBlockHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB rest) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R rest σ ρ))
    (ih_execEndHA_ru_sonst : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd sonst) (worldR σ) (envR ρ)) (execEndHA S O U A passes R sonst σ ρ))
    : AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Block D V l Γ Λ Λ')) (worldR σ) (envR ρ)) (execBlockHA S O U A passes R (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Block D V l Γ Λ Λ') σ ρ) :=
  by
  simp only [ruB, execBlockHA]
  erw [ruE_orte, leseA_worldR hA, eval_ru]
  have he := congrArg (fun v : Gleit zi_l1 zi_h1 => v.x)
    (valR_fl (D := D) (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ))
  erw [he]
  cases gleitPasst lo hi (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).x with
  | none => exact EndRel.zuAusgang (ih_execEndHA_ru_sonst _ ρ)
  | some v => exact AusRelRu.schrumpf (ih_execBlockHA_ru_rest _ (Env.cons v ρ))


theorem execEndHA_ru_float {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_l1}
    {zi_h1}
    {zi_l2}
    {zi_h2}
    (op)
    (a)
    (b)
    (lo)
    (hi)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.float (l1 := zi_l1) (h1 := zi_h1) (l2 := zi_l2) (h2 := zi_h2) op a b lo hi rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  erw [orte2, leseA_worldR hA, eval_ru, eval_ru]
  have ha := congrArg (fun v : Gleit zi_l1 zi_h1 => v.x)
    (valR_fl (D := D)
      (eval (leseA A σ Λ (a.orte ++ b.orte)) a (leseA A σ Λ (a.orte ++ b.orte)) ρ))
  have hb := congrArg (fun v : Gleit zi_l2 zi_h2 => v.x)
    (valR_fl (D := D)
      (eval (leseA A σ Λ (a.orte ++ b.orte)) b (leseA A σ Λ (a.orte ++ b.orte)) ρ))
  erw [ha, hb]
  cases gleitPasst lo hi (gleitRechne op
      (eval (leseA A σ Λ (a.orte ++ b.orte)) a (leseA A σ Λ (a.orte ++ b.orte)) ρ).x
      (eval (leseA A σ Λ (a.orte ++ b.orte)) b (leseA A σ Λ (a.orte ++ b.orte)) ρ).x) with
  | none => exact Or.inl rfl
  | some v => exact EndRel.schrumpf (ih_execEndHA_ru_rest _ (Env.cons v ρ))

theorem execEndHA_ru_floatLit {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (q)
    (lo)
    (hi)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.floatLit q lo hi rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.floatLit q lo hi rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  cases gleitPasst lo hi (bruch q) with
  | none => exact Or.inl rfl
  | some v => exact EndRel.schrumpf (ih_execEndHA_ru_rest _ (Env.cons v ρ))

theorem execEndHA_ru_floatOf {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_l1}
    {zi_h1}
    (e)
    (lo)
    (hi)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.floatOf (l1 := zi_l1) (h1 := zi_h1) e lo hi rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  erw [ruE_orte, leseA_worldR hA, eval_ru]
  have he := congrArg (fun v : Zahl zi_l1 zi_h1 => v.n)
    (valR_int (D := D) (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ))
  erw [he]
  cases gleitPasst lo hi (gleitAusInt (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n) with
  | none => exact Or.inl rfl
  | some v => exact EndRel.schrumpf (ih_execEndHA_ru_rest _ (Env.cons v ρ))

theorem execEndHA_ru_floatNarrow {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_l1}
    {zi_h1}
    (e)
    (lo)
    (hi)
    (sonst)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    (ih_execEndHA_ru_sonst : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd sonst) (worldR σ) (envR ρ)) (execEndHA S O U A passes R sonst σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.floatNarrow (l1 := zi_l1) (h1 := zi_h1) e lo hi sonst rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  erw [ruE_orte, leseA_worldR hA, eval_ru]
  have he := congrArg (fun v : Gleit zi_l1 zi_h1 => v.x)
    (valR_fl (D := D) (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ))
  erw [he]
  cases gleitPasst lo hi (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).x with
  | none => exact (ih_execEndHA_ru_sonst _ ρ)
  | some v => exact EndRel.schrumpf (ih_execEndHA_ru_rest _ (Env.cons v ρ))


end HauptA

end Gabbro.Grammatik
