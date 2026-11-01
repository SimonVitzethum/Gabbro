module

public import Grammatik.Nebenlaeufigkeit.Sperren.MitRuheSemantik.T2
public import Grammatik.Nebenlaeufigkeit.Sperren.MitRuheSemantik.T3.Teil3

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Haupt
variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f)
  (hR : RufRu R R')
include hR

set_option linter.unusedSectionVars false in
theorem execEnd_ru_bindCallInd {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (n)
    (p)
    (args)
    (he)
    (hp)
    (hr)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEnd_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd rest) (worldR σ) (envR ρ) = endR (execEnd O passes R rest σ ρ))
    : execEnd O.mitRuhe passes R' (ruEnd (.bindCallInd (τ := zi_τ) (n := n) p args he hp hr rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ) = endR (execEnd O passes R (.bindCallInd (τ := zi_τ) (n := n) p args he hp hr rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEnd]
  erw [show (ruE p).orte ++ (ruA args).orte = p.orte ++ args.orte from
    kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args)]
  erw [lese_worldR, eval_ru, evalArgs_ru]
  cases h : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ with
  | mk g hg =>
      rw [valR_fnptr]
      dsimp only
      erw [umsig_ru hg, hR]
      cases hx : R g (σ.lese Λ (p.orte ++ args.orte)) (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
      | ok σ' v =>
          try erw [hx]
          simp only [rufR]
          erw [execEnd_umΛ, ergWert_ru (ergSig hg he)]
          exact (congrArg EndAusgang.schrumpf
            (ih_execEnd_ru_rest σ' (Env.cons (ergWert (ergSig hg he) v) ρ))).trans (endR_schrumpf _)
      | why σ' r => exact keinGrundSig hg hr r
      | logik e => (try erw [hx]); rfl
      | hardware e => (try erw [hx]); rfl

set_option linter.unusedSectionVars false in
theorem execEnd_ru_narrow {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_lo}
    {zi_hi}
    (e)
    (lo')
    (hi')
    (sonst)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEnd_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd rest) (worldR σ) (envR ρ) = endR (execEnd O passes R rest σ ρ))
    (ih_execEnd_ru_sonst : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd sonst) (worldR σ) (envR ρ) = endR (execEnd O passes R sonst σ ρ))
    : execEnd O.mitRuhe passes R' (ruEnd (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ) = endR (execEnd O passes R (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEnd]
  simp only [ruE_orte, lese_worldR, eval_ru, valR_int]
  by_cases hc : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi'
  · erw [dif_pos hc, dif_pos hc]
    exact (congrArg EndAusgang.schrumpf (ih_execEnd_ru_rest _
      (Env.cons (⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, hc.1, hc.2⟩ : Zahl lo' hi') ρ))).trans
      (endR_schrumpf _)
  · erw [dif_neg hc, dif_neg hc]
    exact ih_execEnd_ru_sonst _ ρ

set_option linter.unusedSectionVars false in
theorem execEnd_ru_exchange {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (g)
    (neu)
    (hw)
    (hL)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEnd_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd rest) (worldR σ) (envR ρ) = endR (execEnd O passes R rest σ ρ))
    : execEnd O.mitRuhe passes R' (ruEnd (.exchange g neu hw hL rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ) = endR (execEnd O passes R (.exchange g neu hw hL rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEnd]
  rw [show (Sum.inr g :: (ruE neu).orte : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) =
    Sum.inr g :: neu.orte from congrArg (Sum.inr g :: ·) (ruE_orte neu), lese_worldR]
  have ez := eval_ru (σ.lese Λ (Sum.inr g :: neu.orte)) (σ.lese Λ (Sum.inr g :: neu.orte)) neu
    (Env.cons ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) ρ)
  change eval _ (ruE neu) _ (Env.cons (valR _ _) (envR ρ)) = _ at ez
  rw [show ((worldR (σ.lese Λ (Sum.inr g :: neu.orte))).globs g) =
    valR _ ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) from rfl, ez, schreibGlob_worldR,
    ← endR_schrumpf, ← ih_execEnd_ru_rest _ (Env.cons _ ρ)]
  rfl

set_option linter.unusedSectionVars false in
theorem execEnd_ru_ite {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (c)
    (t)
    (e)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEnd_ru_e : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd e) (worldR σ) (envR ρ) = endR (execEnd O passes R e σ ρ))
    (ih_execEnd_ru_t : ∀ (σ : World D), ∀ (ρ : Env D _), execEnd O.mitRuhe passes R' (ruEnd t) (worldR σ) (envR ρ) = endR (execEnd O passes R t σ ρ))
    : execEnd O.mitRuhe passes R' (ruEnd (.ite c t e : Endblock D V l Γ Λ)) (worldR σ) (envR ρ) = endR (execEnd O passes R (.ite c t e : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEnd]
  rw [ruE_orte, lese_worldR, eval_ru]
  cases h : (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ : Bool)
  · simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
    exact ih_execEnd_ru_e _ ρ
  · simp only [wahr?, valR_bool, h, if_true]
    exact ih_execEnd_ru_t _ ρ

set_option maxHeartbeats 4000000 in
mutual

/-- **A translated statement runs as the statement**: from the translated
    world and environment to the translated outcome, given a handler that
    answers translated calls with translated answers. -/
theorem execStmt_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ),
    execStmt O.mitRuhe passes R' (ruS s) (worldR σ) (envR ρ) = ausR (execStmt O passes R s σ ρ)
  | _, _, Λ, _, .assignSlot t f i e hw hL, σ, ρ =>
      execStmt_ru_assignSlot (t := t) (f := f) (i := i) (e := e) (hw := hw) (hL := hL) (σ := σ) (ρ := ρ) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .assignThru p t ht f i e hw hL, σ, ρ =>
      execStmt_ru_assignThru (p := p) (t := t) (ht := ht) (f := f) (i := i) (e := e) (hw := hw) (hL := hL) (σ := σ) (ρ := ρ) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .assignSlotRef r t ht ho f e hw hL, σ, ρ =>
      execStmt_ru_assignSlotRef (r := r) (t := t) (ht := ht) (ho := ho) (f := f) (e := e) (hw := hw) (hL := hL) (σ := σ) (ρ := ρ) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .assignGlob g e hw hL, σ, ρ =>
      execStmt_ru_assignGlob (g := g) (e := e) (hw := hw) (hL := hL) (σ := σ) (ρ := ρ) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .putBytes t f hf n i hlo hhi e hw hL, σ, ρ =>
      execStmt_ru_putBytes (t := t) (f := f) (hf := hf) (n := n) (i := i) (hlo := hlo) (hhi := hhi) (e := e) (hw := hw) (hL := hL) (σ := σ) (ρ := ρ) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .assignVar x e, σ, ρ =>
      execStmt_ru_assignVar (x := x) (e := e) (σ := σ) (ρ := ρ) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .shift (lo := lo) (hi := hi) t f hτ i von nach hn he hw hL, σ, ρ =>
      execStmt_ru_shift (lo := lo) (hi := hi) (t := t) (f := f) (hτ := hτ) (i := i) (von := von) (nach := nach) (hn := hn) (he := he) (hw := hw) (hL := hL) (σ := σ) (ρ := ρ) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .ite c t e, σ, ρ =>
      execStmt_ru_ite (c := c) (t := t) (e := e) (σ := σ) (ρ := ρ) (ih_execBlock_ru_e := execBlock_ru e) (ih_execBlock_ru_t := execBlock_ru t) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .onOption o p a, σ, ρ =>
      execStmt_ru_onOption (o := o) (p := p) (a := a) (σ := σ) (ρ := ρ) (ih_execBlock_ru_a := execBlock_ru a) (ih_execBlock_ru_p := execBlock_ru p) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .onTag v arms, σ, ρ =>
      execStmt_ru_onTag (v := v) (arms := arms) (σ := σ) (ρ := ρ) (ih_execArms_ru_arms := execArms_ru arms) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .onWhy r arms, σ, ρ =>
      execStmt_ru_onWhy (r := r) (arms := arms) (σ := σ) (ρ := ρ) (ih_execGrund_ru_arms := execGrund_ru arms) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .call g args hp hr, σ, ρ =>
      execStmt_ru_call (g := g) (args := args) (hp := hp) (hr := hr) (σ := σ) (ρ := ρ) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .callInd (n := n) p args hp hr, σ, ρ =>
      execStmt_ru_callInd (n := n) (p := p) (args := args) (hp := hp) (hr := hr) (σ := σ) (ρ := ρ) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .locks L hr body, σ, ρ =>
      execStmt_ru_locks (hr := hr) (body := body) (σ := σ) (ρ := ρ) (ih_execBlock_ru_body := execBlock_ru body) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, _, _, .breaking _ body, σ, ρ => by
      simp only [ruS, execStmt]
      exact execBlock_ru body σ ρ
  | _, _, Λ, _, .traverse t inv body, σ, ρ =>
      execStmt_ru_traverse (t := t) (inv := inv) (body := body) (σ := σ) (ρ := ρ) (ih_execBlock_ru_body := execBlock_ru body) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .retry n bis body ueber, σ, ρ =>
      execStmt_ru_retry (n := n) (bis := bis) (body := body) (ueber := ueber) (σ := σ) (ρ := ρ) (ih_execBlock_ru_body := execBlock_ru body) (ih_execBlock_ru_ueber := execBlock_ru ueber) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .forever a inv body, σ, ρ =>
      execStmt_ru_forever (a := a) (inv := inv) (body := body) (σ := σ) (ρ := ρ) (ih_execBlock_ru_body := execBlock_ru body) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .axiomCall a args h hw hg hd hgd, σ, ρ =>
      execStmt_ru_axiomCall (a := a) (args := args) (h := h) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (σ := σ) (ρ := ρ) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .regWrite r hk e, σ, ρ =>
      execStmt_ru_regWrite (r := r) (hk := hk) (e := e) (σ := σ) (ρ := ρ) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, _, _, .transition .., σ, ρ => rfl
  | _, _, Λ, _, .publish g e payload hp hw hL, σ, ρ =>
      execStmt_ru_publish (g := g) (e := e) (payload := payload) (hp := hp) (hw := hw) (hL := hL) (σ := σ) (ρ := ρ) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, _, _, .advances .., σ, ρ => by
      simp only [ruS]
      erw [execStmt_nachΛ]
      rfl
  | _, _, _, _, .retires .., σ, ρ => by
      simp only [ruS]
      erw [execStmt_nachΛ]
      rfl
  | _, _, Λ, _, .ret e hΛ, σ, ρ =>
      execStmt_ru_ret (e := e) (hΛ := hΛ) (σ := σ) (ρ := ρ) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, _, _, .retWhy .., σ, ρ => rfl
  | _, _, _, _, .leave _, σ, ρ => rfl
  | _, _, _, _, .next _, σ, ρ => rfl

theorem execBlock_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ),
    execBlock O.mitRuhe passes R' (ruB b) (worldR σ) (envR ρ) = ausR (execBlock O passes R b σ ρ)
  | _, _, _, _, .nil, σ, ρ => rfl
  | _, _, _, _, .cons s rest, σ, ρ =>
      execBlock_ru_cons (s := s) (rest := rest) (σ := σ) (ρ := ρ) (ih_execStmt_ru_s := execStmt_ru s) (ih_execBlock_ru_rest := execBlock_ru rest) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .bind e rest, σ, ρ =>
      execBlock_ru_bind (e := e) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlock_ru_rest := execBlock_ru rest) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .bindCall g args he hp hr rest, σ, ρ =>
      execBlock_ru_bindCall (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlock_ru_rest := execBlock_ru rest) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .bindCallInd (n := n) p args he hp hr rest, σ, ρ =>
      execBlock_ru_bindCallInd (n := n) (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlock_ru_rest := execBlock_ru rest) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .bindCallElse g args he hp hr err rest, σ, ρ =>
      execBlock_ru_bindCallElse (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlock_ru_rest := execBlock_ru rest) (ih_execEnd_ru_err := execEnd_ru err) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .bindAxiom a args he hw hg hd hgd rest, σ, ρ =>
      execBlock_ru_bindAxiom (a := a) (args := args) (he := he) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlock_ru_rest := execBlock_ru rest) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ =>
      execBlock_ru_bindAxiomElse (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlock_ru_rest := execBlock_ru rest) (ih_execEnd_ru_err := execEnd_ru err) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, _, _, .regRead r hk rest, σ, ρ =>
      execBlock_ru_regRead (r := r) (hk := hk) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlock_ru_rest := execBlock_ru rest) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .regReadElse r hk zusage sonst rest, σ, ρ =>
      execBlock_ru_regReadElse (r := r) (hk := hk) (zusage := zusage) (sonst := sonst) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlock_ru_rest := execBlock_ru rest) (ih_execEnd_ru_sonst := execEnd_ru sonst) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .awaits g payload hp hL hat rest, σ, ρ =>
      execBlock_ru_awaits (g := g) (payload := payload) (hp := hp) (hL := hL) (hat := hat) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlock_ru_rest := execBlock_ru rest) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .exchange g neu hw hL rest, σ, ρ =>
      execBlock_ru_exchange (g := g) (neu := neu) (hw := hw) (hL := hL) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlock_ru_rest := execBlock_ru rest) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .narrow e lo' hi' sonst rest, σ, ρ =>
      execBlock_ru_narrow (e := e) (lo' := lo') (hi' := hi') (sonst := sonst) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlock_ru_rest := execBlock_ru rest) (ih_execEnd_ru_sonst := execEnd_ru sonst) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .check c sonst rest, σ, ρ =>
      execBlock_ru_check (c := c) (sonst := sonst) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlock_ru_rest := execBlock_ru rest) (ih_execEnd_ru_sonst := execEnd_ru sonst) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .float op a b lo hi rest, σ, ρ =>
      execBlock_ru_float (op := op) (a := a) (b := b) (lo := lo) (hi := hi) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlock_ru_rest := execBlock_ru rest) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, _, _, .floatLit q lo hi rest, σ, ρ =>
      execBlock_ru_floatLit (q := q) (lo := lo) (hi := hi) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlock_ru_rest := execBlock_ru rest) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .floatOf e lo hi rest, σ, ρ =>
      execBlock_ru_floatOf (e := e) (lo := lo) (hi := hi) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlock_ru_rest := execBlock_ru rest) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, _, .floatNarrow e lo hi sonst rest, σ, ρ =>
      execBlock_ru_floatNarrow (e := e) (lo := lo) (hi := hi) (sonst := sonst) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlock_ru_rest := execBlock_ru rest) (ih_execEnd_ru_sonst := execEnd_ru sonst) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
theorem execEnd_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ),
    execEnd O.mitRuhe passes R' (ruEnd e) (worldR σ) (envR ρ) = endR (execEnd O passes R e σ ρ)
  | _, _, Λ, .ret e hΛ, σ, ρ =>
      execEnd_ru_ret (e := e) (hΛ := hΛ) (σ := σ) (ρ := ρ) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, _, .retWhy .., σ, ρ => rfl
  | _, _, _, .leave _, σ, ρ => rfl
  | _, _, _, .next _, σ, ρ => rfl
  | _, _, _, .cons s rest, σ, ρ =>
      execEnd_ru_cons (s := s) (rest := rest) (σ := σ) (ρ := ρ) (ih_execStmt_ru_s := execStmt_ru s) (ih_execEnd_ru_rest := execEnd_ru rest) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, .bind e rest, σ, ρ =>
      execEnd_ru_bind (e := e) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEnd_ru_rest := execEnd_ru rest) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, .bindCall g args he hp hr rest, σ, ρ =>
      execEnd_ru_bindCall (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEnd_ru_rest := execEnd_ru rest) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, .bindCallElse g args he hp hr err rest, σ, ρ =>
      execEnd_ru_bindCallElse (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEnd_ru_rest := execEnd_ru rest) (ih_execEnd_ru_err := execEnd_ru err) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, .bindAxiom a args he hw hg hd hgd rest, σ, ρ =>
      execEnd_ru_bindAxiom (a := a) (args := args) (he := he) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEnd_ru_rest := execEnd_ru rest) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ =>
      execEnd_ru_bindAxiomElse (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEnd_ru_rest := execEnd_ru rest) (ih_execEnd_ru_err := execEnd_ru err) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, _, .regRead r hk rest, σ, ρ =>
      execEnd_ru_regRead (r := r) (hk := hk) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEnd_ru_rest := execEnd_ru rest) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, .regReadElse r hk zusage sonst rest, σ, ρ =>
      execEnd_ru_regReadElse (r := r) (hk := hk) (zusage := zusage) (sonst := sonst) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEnd_ru_sonst := execEnd_ru sonst) (ih_execEnd_ru_rest := execEnd_ru rest) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, .awaits g payload hp hL hat rest, σ, ρ =>
      execEnd_ru_awaits (g := g) (payload := payload) (hp := hp) (hL := hL) (hat := hat) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEnd_ru_rest := execEnd_ru rest) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, .bindCallInd (n := n) p args he hp hr rest, σ, ρ =>
      execEnd_ru_bindCallInd (n := n) (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEnd_ru_rest := execEnd_ru rest) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, .narrow e lo' hi' sonst rest, σ, ρ =>
      execEnd_ru_narrow (e := e) (lo' := lo') (hi' := hi') (sonst := sonst) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEnd_ru_rest := execEnd_ru rest) (ih_execEnd_ru_sonst := execEnd_ru sonst) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, .exchange g neu hw hL rest, σ, ρ =>
      execEnd_ru_exchange (g := g) (neu := neu) (hw := hw) (hL := hL) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEnd_ru_rest := execEnd_ru rest) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
  | _, _, Λ, .ite c t e, σ, ρ =>
      execEnd_ru_ite (c := c) (t := t) (e := e) (σ := σ) (ρ := ρ) (ih_execEnd_ru_e := execEnd_ru e) (ih_execEnd_ru_t := execEnd_ru t) (O := O) (passes := passes) (R := R) (R' := R') (hR := hR)
theorem execArms_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs))
    (σ : World D) (ρ : Env D Γ),
    execArms O.mitRuhe passes R' (ruArms arms) (valR (.sum cs) v) (worldR σ) (envR ρ) =
      ausR (execArms O passes R arms v σ ρ)
  | _, _, _, _, _, .cons (c := none) b rest, ⟨⟨0, _⟩, nutz⟩, σ, ρ => execBlock_ru b σ ρ
  | _, _, _, _, _, .cons (c := some (lo, hi)) b rest, ⟨⟨0, _⟩, nutz⟩, σ, ρ => by
      exact (congrArg Ausgang.schrumpf (execBlock_ru b σ (Env.cons nutz ρ))).trans (ausR_schrumpf _)
  | _, _, _, _, _, .cons (c := none) b rest, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ =>
      execArms_ru rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩ σ ρ
  | _, _, _, _, _, .cons (c := some (lo, hi)) b rest, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ =>
      execArms_ru rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩ σ ρ

theorem execGrund_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n) (σ : World D) (ρ : Env D Γ),
    execGrund O.mitRuhe passes R' (ruGArms arms) r (worldR σ) (envR ρ) =
      ausR (execGrund O passes R arms r σ ρ)
  | _, _, _, _, _, .cons b _, ⟨0, _⟩, σ, ρ => execBlock_ru b σ ρ
  | _, _, _, _, _, .cons _ rest, ⟨i + 1, h⟩, σ, ρ =>
      execGrund_ru rest ⟨i, Nat.lt_of_succ_lt_succ h⟩ σ ρ

end

end Haupt
/-! ## 8. Every function behaves as in `P` -/

/-- **EVERY FUNCTION OF `P` BEHAVES IN `P.mitRuhe` AS IN `P`**: the body of
    `some f` in `P.mitRuhe`, run under the oracle `O.mitRuhe` from the
    translated world and parameters, ends in the translated outcome of the
    body of `f` in `P` under `O` -- for every budget and every pair of call
    handlers that answer translated calls with translated answers
    (`RufRu`). The generic form of `gPB_wie_gP_einzahlen`/`gPB_wie_gP_lies`. -/
theorem rumpf_mitRuhe_verhalten (P : Programm D) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) →
      RufAusgang f)
    (hR : RufRu R R') (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) :
    execEnd O.mitRuhe passes R' (P.mitRuhe.rumpf (some f)) (worldR σ) (envR ρ) =
      endR (execEnd O passes R (P.rumpf f) σ ρ) :=
  (execEnd_umΛ O.mitRuhe passes R' _ _ _ _).trans (execEnd_ru O passes R R' hR (P.rumpf f) σ ρ)

/-- The root's body returns at once, touching nothing. -/
theorem rumpf_ruhe_verhalten (P : Programm D) (O : Orakel D) (passes : Nat)
    (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) →
      RufAusgang f) (σ : World D.mitRuhe) (ρ : Env D.mitRuhe (D.mitRuhe.params none)) :
    execEnd O.mitRuhe passes R' (P.mitRuhe.rumpf none) σ ρ = .zurueck σ () := by rfl


/-! ## 9. Every call behaves as in `P` (`rufAt`) -/

theorem eval_umΓ_ergEnv {Γ : Ctx} {Λ' : List (Res D.mitRuhe)} :
    ∀ (e : Option Ty) (h : (ErgCtx Γ e).map tyR = ErgCtx (Γ.map tyR) (e.map tyR))
      (x : Expr D.mitRuhe ((ErgCtx Γ e).map tyR) Λ' .bool) (σ₀ σ : World D.mitRuhe)
      (v : ErgVal D e) (ρ : Env D Γ),
      eval σ₀ (Expr.umΓ h x) σ (ergEnv (e.map tyR) (ergR e v) (envR ρ)) =
        eval σ₀ x σ (envR (ergEnv e v ρ))
  | none, _, _, _, _, _, _ => rfl
  | some _, _, _, _, _, _, _ => rfl

theorem ens_mitRuhe_eval (P : Programm D) (f : D.Fn) (σ₀ σ : World D) (v : ErgVal D (D.erg f))
    (ρ : Env D (D.params f)) :
    eval (worldR σ₀) (P.mitRuhe.ensures (some f)) (worldR σ)
        (ergEnv ((D.erg f).map tyR) (ergR (D.erg f) v) (envR ρ)) =
      eval σ₀ (P.ensures f) σ (ergEnv (D.erg f) v ρ) :=
  (eval_umΓ_ergEnv (D.erg f) _ _ _ _ v ρ).trans
    ((eval_umΛ' _ _ _ _ _).trans (eval_ru σ₀ σ (P.ensures f) (ergEnv (D.erg f) v ρ)))

theorem inv_mitRuhe_eval (P : Programm D) (i : D.Inv) (σ : World D) :
    eval (worldR σ) (P.mitRuhe.invariante i) (worldR σ) Env.nil =
      eval σ (P.invariante i) σ Env.nil :=
  (eval_umΛ' _ _ _ _ _).trans (eval_ru σ σ (P.invariante i) Env.nil)


end Gabbro.Grammatik
