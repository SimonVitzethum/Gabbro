module

public import Grammatik.Nebenlaeufigkeit.Sperren.MitRuheSperre
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
  simp only [ruE_orte, leseA_worldR hA, eval_ru, valR_int]
  by_cases hc : lo' ≤ (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ∧
      (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ≤ hi'
  · erw [dif_pos hc, dif_pos hc]
    exact AusRelRu.schrumpf (ih_execBlockHA_ru_rest _
      (Env.cons (⟨(eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n, hc.1, hc.2⟩ : Zahl lo' hi') ρ))
  · erw [dif_neg hc, dif_neg hc]
    exact EndRel.zuAusgang (ih_execEndHA_ru_sonst _ ρ)

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
  rw [ruE_orte, leseA_worldR hA, eval_ru]
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
  rw [orte2, leseA_worldR hA, eval_ru, eval_ru]
  try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
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
  rw [ruE_orte, leseA_worldR hA, eval_ru]
  try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
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
  rw [ruE_orte, leseA_worldR hA, eval_ru]
  try simp only [valR_int, valR_opt, valR_fl, valR_fnptr]
  cases gleitPasst lo hi (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).x with
  | none => exact EndRel.zuAusgang (ih_execEndHA_ru_sonst _ ρ)
  | some v => exact AusRelRu.schrumpf (ih_execBlockHA_ru_rest _ (Env.cons v ρ))

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_ret {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (e)
    (hΛ)
    (σ : World D)
    (ρ : Env D Γ)
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.ret e hΛ : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.ret e hΛ : Endblock D V l Γ Λ) σ ρ) :=
  by
  refine Or.inl ?_
  simp only [ruEnd, execEndHA]
  erw [ruErg_orte, leseA_worldR hA, evalErg_ru]
  rfl

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_cons {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_Λ'}
    (s)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execStmtHA_ru_s : ∀ (σ : World D), ∀ (ρ : Env D _), AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS s) (worldR σ) (envR ρ)) (execStmtHA S O U A passes R s σ ρ))
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.cons (Λ' := zi_Λ') s rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.cons (Λ' := zi_Λ') s rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  rcases ih_execStmtHA_ru_s σ ρ with h | ⟨e', e, h1, h2, ht⟩
  · rw [h]
    cases execStmtHA S O U A passes R s σ ρ with
    | ok σ' ρ' => exact ih_execEndHA_ru_rest σ' ρ'
    | _ => exact Or.inl rfl
  · rw [h1, h2]
    exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_bind {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (e)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.bind (τ := zi_τ) e rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.bind (τ := zi_τ) e rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  rw [ruE_orte, leseA_worldR hA, eval_ru]
  exact EndRel.schrumpf (ih_execEndHA_ru_rest (leseA A σ Λ e.orte)
    (Env.cons (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ) ρ))

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_bindCall {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (g)
    (args)
    (he)
    (hp)
    (hr)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.bindCall (τ := zi_τ) g args he hp hr rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.bindCall (τ := zi_τ) g args he hp hr rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  erw [ruA_orte, leseA_worldR hA, evalArgs_ru]
  rcases hR g (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ)
    with hx' | ⟨e', e, h1, h2, ht⟩
  · erw [hx']
    cases hx : R g (leseA A σ Λ args.orte)
        (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) with
    | ok σ' v =>
        try erw [hx]
        simp only [rufR]
        erw [execEndHA_umΛ, ergWert_ru he]
        exact EndRel.schrumpf (ih_execEndHA_ru_rest σ' (Env.cons (ergWert he v) ρ))
    | why σ' r => exact (Fin.cast hr r).elim0
    | logik e => (try erw [hx]); exact Or.inl rfl
    | hardware e => (try erw [hx]); exact Or.inl rfl
  · erw [h1, h2]
    exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_bindCallElse {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (g)
    (args)
    (he)
    (hp)
    (hr)
    (err)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    (ih_execEndHA_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd err) (worldR σ) (envR ρ)) (execEndHA S O U A passes R err σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.bindCallElse (τ := zi_τ) g args he hp hr err rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.bindCallElse (τ := zi_τ) g args he hp hr err rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  erw [ruA_orte, leseA_worldR hA, evalArgs_ru]
  rcases hR g (leseA A σ Λ args.orte) (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ)
    with hx' | ⟨e', e, h1, h2, ht⟩
  · erw [hx']
    cases hx : R g (leseA A σ Λ args.orte)
        (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) with
    | ok σ' v =>
        try erw [hx]
        simp only [rufR]
        erw [execEndHA_umΛ, ergWert_ru he]
        exact EndRel.schrumpf (ih_execEndHA_ru_rest σ' (Env.cons (ergWert he v) ρ))
    | why σ' r =>
        try erw [hx]
        simp only [rufR]
        erw [execEndHA_umΛ]
        exact EndRel.schrumpf (ih_execEndHA_ru_err σ' (Env.cons r ρ))
    | logik e => (try erw [hx]); exact Or.inl rfl
    | hardware e => (try erw [hx]); exact Or.inl rfl
  · erw [h1, h2]
    exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_bindAxiom {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (a)
    (args)
    (he)
    (hw)
    (hg)
    (hd)
    (hgd)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.bindAxiom (τ := zi_τ) a args he hw hg hd hgd rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.bindAxiom (τ := zi_τ) a args he hw hg hd hgd rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  erw [ruA_orte, leseA_worldR hA, evalArgs_ru, axiomAntwort_ruG hO]
  cases axiomAntwort O a (leseA A σ Λ args.orte)
    (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) with
  | mk σ' w =>
      cases w with
      | none => exact Or.inl rfl
      | some v =>
          simp only [Option.map]
          rw [ergWert_ru he]
          exact EndRel.schrumpf (ih_execEndHA_ru_rest σ' (Env.cons (ergWert he v) ρ))

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_bindAxiomElse {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (a)
    (args)
    (he)
    (hr)
    (hw)
    (hg)
    (hd)
    (hgd)
    (err)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    (ih_execEndHA_ru_err : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd err) (worldR σ) (envR ρ)) (execEndHA S O U A passes R err σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.bindAxiomElse (τ := zi_τ) a args he hr hw hg hd hgd err rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.bindAxiomElse (τ := zi_τ) a args he hr hw hg hd hgd err rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  erw [ruA_orte, leseA_worldR hA, evalArgs_ru, axiomAntwortSonst_ruG hO]
  cases axiomAntwortSonst O a (leseA A σ Λ args.orte)
    (evalArgs (leseA A σ Λ args.orte) args (leseA A σ Λ args.orte) ρ) with
  | mk σ' w =>
      rcases w with _ | v | r
      · exact Or.inl rfl
      · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply]
        rw [ergWert_ru he]
        exact EndRel.schrumpf (ih_execEndHA_ru_rest σ' (Env.cons (ergWert he v) ρ))
      · dsimp only [Option.map, Sum.map, Sum.elim, Function.comp_apply, id]
        exact EndRel.schrumpf (ih_execEndHA_ru_err σ' (Env.cons (τ := .why (D.agruende a)) r ρ))

end HauptA
end Gabbro.Grammatik
