module

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSemantik
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre.Teil4
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre.Teil4a

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Haupt
variable (S : SperrInv D) (O : Orakel D) (O' : Orakel D.mitRuhe) (hO : OrakelRu O O')
  (U : Umwelt D) (U' : Umwelt D.mitRuhe) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) → RufAusgang f)
  (hU : ∀ L σ, U' L (worldR σ) = worldR (U L σ))
  (hR : RufRel R R')
include hO hU hR

set_option linter.unusedSectionVars false in
theorem execEndH_ru_exchange {V : Vertrag D}
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
    (ih_execEndH_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndH S O U passes R rest σ ρ))
    : EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd (.exchange g neu hw hL rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndH S O U passes R (.exchange g neu hw hL rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndH]
  rw [show (Sum.inr g :: (ruE neu).orte : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) =
    Sum.inr g :: neu.orte from congrArg (Sum.inr g :: ·) (ruE_orte neu), lese_worldR]
  have ez := eval_ru (σ.lese Λ (Sum.inr g :: neu.orte)) (σ.lese Λ (Sum.inr g :: neu.orte)) neu
    (Env.cons ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) ρ)
  change eval _ (ruE neu) _ (Env.cons (valR _ _) (envR ρ)) = _ at ez
  rw [show ((worldR (σ.lese Λ (Sum.inr g :: neu.orte))).globs g) =
    valR _ ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) from rfl, ez, schreibGlob_worldR]
  exact EndRel.schrumpf (ih_execEndH_ru_rest
    ((σ.lese Λ (Sum.inr g :: neu.orte)).schreibGlob g Λ (eval (σ.lese Λ (Sum.inr g :: neu.orte)) neu
      (σ.lese Λ (Sum.inr g :: neu.orte)) (Env.cons ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) ρ)))
    (Env.cons ((σ.lese Λ (Sum.inr g :: neu.orte)).globs g) ρ))

set_option linter.unusedSectionVars false in
theorem execEndH_ru_ite {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (c)
    (t)
    (e)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndH_ru_e : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd e) (worldR σ) (envR ρ)) (execEndH S O U passes R e σ ρ))
    (ih_execEndH_ru_t : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd t) (worldR σ) (envR ρ)) (execEndH S O U passes R t σ ρ))
    : EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd (.ite c t e : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndH S O U passes R (.ite c t e : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndH]
  rw [ruE_orte, lese_worldR, eval_ru]
  cases h : (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ : Bool)
  · simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
    exact ih_execEndH_ru_e _ ρ
  · simp only [wahr?, valR_bool, h, if_true]
    exact ih_execEndH_ru_t _ ρ

set_option maxHeartbeats 4000000 in
mutual

/-- **A translated statement runs as the statement under the lock-invariant
    semantics**, up to the label of a logic failure. -/
theorem execStmtH_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ),
    AusRelRu (execStmtH S.mitRuhe O' U' passes R' (ruS s) (worldR σ) (envR ρ))
      (execStmtH S O U passes R s σ ρ)
  | _, _, Λ, _, .assignSlot t f i e hw hL, σ, ρ =>
      execStmtH_ru_assignSlot (t := t) (f := f) (i := i) (e := e) (hw := hw) (hL := hL) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .assignThru p t ht f i e hw hL, σ, ρ =>
      execStmtH_ru_assignThru (p := p) (t := t) (ht := ht) (f := f) (i := i) (e := e) (hw := hw) (hL := hL) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .assignSlotRef r t ht ho f e hw hL, σ, ρ =>
      execStmtH_ru_assignSlotRef (r := r) (t := t) (ht := ht) (ho := ho) (f := f) (e := e) (hw := hw) (hL := hL) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .assignGlob g e hw hL, σ, ρ =>
      execStmtH_ru_assignGlob (g := g) (e := e) (hw := hw) (hL := hL) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .putBytes t f hf n i hlo hhi e hw hL, σ, ρ =>
      execStmtH_ru_putBytes (t := t) (f := f) (hf := hf) (n := n) (i := i) (hlo := hlo) (hhi := hhi) (e := e) (hw := hw) (hL := hL) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .assignVar x e, σ, ρ =>
      execStmtH_ru_assignVar (x := x) (e := e) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .shift (lo := lo) (hi := hi) t f hτ i von nach hn he hw hL, σ, ρ =>
      execStmtH_ru_shift (lo := lo) (hi := hi) (t := t) (f := f) (hτ := hτ) (i := i) (von := von) (nach := nach) (hn := hn) (he := he) (hw := hw) (hL := hL) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .ite c t e, σ, ρ =>
      execStmtH_ru_ite (c := c) (t := t) (e := e) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_e := execBlockH_ru e) (ih_execBlockH_ru_t := execBlockH_ru t) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .onOption o p a, σ, ρ =>
      execStmtH_ru_onOption (o := o) (p := p) (a := a) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_a := execBlockH_ru a) (ih_execBlockH_ru_p := execBlockH_ru p) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .onTag v arms, σ, ρ =>
      execStmtH_ru_onTag (v := v) (arms := arms) (σ := σ) (ρ := ρ) (ih_execArmsH_ru_arms := execArmsH_ru arms) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .onWhy r arms, σ, ρ =>
      execStmtH_ru_onWhy (r := r) (arms := arms) (σ := σ) (ρ := ρ) (ih_execGrundH_ru_arms := execGrundH_ru arms) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .call g args hp hr, σ, ρ =>
      execStmtH_ru_call (g := g) (args := args) (hp := hp) (hr := hr) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .callInd (n := n) p args hp hr, σ, ρ =>
      execStmtH_ru_callInd (n := n) (p := p) (args := args) (hp := hp) (hr := hr) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .locks L hr body, σ, ρ =>
      execStmtH_ru_locks (hr := hr) (body := body) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_body := execBlockH_ru body) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, _, _, .breaking _ body, σ, ρ => by
      simp only [ruS, execStmtH]
      exact execBlockH_ru body σ ρ
  | l, _, Λ, _, .traverse t inv body, σ, ρ =>
      execStmtH_ru_traverse (t := t) (inv := inv) (body := body) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_body := execBlockH_ru body) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | l, _, Λ, _, .consumeTraverse t member edge inv bound mass body, σ, ρ =>
      execStmtH_ru_consumeTraverse (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_body := execBlockH_ru body) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .retry n bis body ueber, σ, ρ =>
      execStmtH_ru_retry (n := n) (bis := bis) (body := body) (ueber := ueber) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_body := execBlockH_ru body) (ih_execBlockH_ru_ueber := execBlockH_ru ueber) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .forever a inv body, σ, ρ =>
      execStmtH_ru_forever (a := a) (inv := inv) (body := body) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_body := execBlockH_ru body) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .axiomCall a args h hw hg hd hgd, σ, ρ =>
      execStmtH_ru_axiomCall (a := a) (args := args) (h := h) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .axiomCallElse e a args he hp hd hgd hr err, σ, ρ =>
      execStmtH_ru_axiomCallElse (e := e) (a := a) (args := args) (he := he) (hp := hp) (hd := hd) (hgd := hgd) (hr := hr) (err := err) (σ := σ) (ρ := ρ) (ih_execEndH_ru_err := execEndH_ru err) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .regWrite r hk e, σ, ρ =>
      execStmtH_ru_regWrite (r := r) (hk := hk) (e := e) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, _, _, .transition .., σ, ρ => Or.inl rfl
  | _, _, Λ, _, .publish g e payload hp hw hL, σ, ρ =>
      execStmtH_ru_publish (g := g) (e := e) (payload := payload) (hp := hp) (hw := hw) (hL := hL) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, _, _, .advances .., σ, ρ => by
      refine Or.inl ?_
      simp only [ruS]
      erw [execStmtH_nachΛ]
      rfl
  | _, _, _, _, .retires .., σ, ρ => by
      refine Or.inl ?_
      simp only [ruS]
      erw [execStmtH_nachΛ]
      rfl
  | _, _, Λ, _, .ret e hΛ, σ, ρ =>
      execStmtH_ru_ret (e := e) (hΛ := hΛ) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .retScoped e R, σ, ρ =>
      execStmtH_ru_retScoped (e := e) (R := R) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, _, _, .retWhy .., σ, ρ => Or.inl rfl
  | _, _, _, _, .retWhyScoped .., σ, ρ => Or.inl rfl
  | _, _, _, _, .leave _, σ, ρ => Or.inl rfl
  | _, _, _, _, .next _, σ, ρ => Or.inl rfl

theorem execBlockH_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ),
    AusRelRu (execBlockH S.mitRuhe O' U' passes R' (ruB b) (worldR σ) (envR ρ))
      (execBlockH S O U passes R b σ ρ)
  | _, _, _, _, .nil, σ, ρ => Or.inl rfl
  | _, _, _, _, .cons s rest, σ, ρ =>
      execBlockH_ru_cons (s := s) (rest := rest) (σ := σ) (ρ := ρ) (ih_execStmtH_ru_s := execStmtH_ru s) (ih_execBlockH_ru_rest := execBlockH_ru rest) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .bind e rest, σ, ρ =>
      execBlockH_ru_bind (e := e) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_rest := execBlockH_ru rest) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .bindCall g args he hp hr rest, σ, ρ =>
      execBlockH_ru_bindCall (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_rest := execBlockH_ru rest) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .bindCallInd (n := n) p args he hp hr rest, σ, ρ =>
      execBlockH_ru_bindCallInd (n := n) (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_rest := execBlockH_ru rest) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .bindCallElse g args he hp hr err rest, σ, ρ =>
      execBlockH_ru_bindCallElse (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_rest := execBlockH_ru rest) (ih_execEndH_ru_err := execEndH_ru err) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .bindAxiom a args he hw hg hd hgd rest, σ, ρ =>
      execBlockH_ru_bindAxiom (a := a) (args := args) (he := he) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_rest := execBlockH_ru rest) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ =>
      execBlockH_ru_bindAxiomElse (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_rest := execBlockH_ru rest) (ih_execEndH_ru_err := execEndH_ru err) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .bindAxiomOpt e a args he hp hd hgd rest, σ, ρ =>
      execBlockH_ru_bindAxiomOpt (e := e) (a := a) (args := args) (he := he) (hp := hp) (hd := hd) (hgd := hgd) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_rest := execBlockH_ru rest) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .bindAxiomOptElse e a args he hp hd hgd hr err rest, σ, ρ =>
      execBlockH_ru_bindAxiomOptElse (e := e) (a := a) (args := args) (he := he) (hp := hp) (hd := hd) (hgd := hgd) (hr := hr) (err := err) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_rest := execBlockH_ru rest) (ih_execEndH_ru_err := execEndH_ru err) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, _, _, .regRead r hk rest, σ, ρ =>
      execBlockH_ru_regRead (r := r) (hk := hk) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_rest := execBlockH_ru rest) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .regReadElse r hk zusage sonst rest, σ, ρ =>
      execBlockH_ru_regReadElse (r := r) (hk := hk) (zusage := zusage) (sonst := sonst) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_rest := execBlockH_ru rest) (ih_execEndH_ru_sonst := execEndH_ru sonst) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .awaits g payload hp hL hat rest, σ, ρ =>
      execBlockH_ru_awaits (g := g) (payload := payload) (hp := hp) (hL := hL) (hat := hat) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_rest := execBlockH_ru rest) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .exchange g neu hw hL rest, σ, ρ =>
      execBlockH_ru_exchange (g := g) (neu := neu) (hw := hw) (hL := hL) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_rest := execBlockH_ru rest) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .narrow e lo' hi' sonst rest, σ, ρ =>
      execBlockH_ru_narrow (e := e) (lo' := lo') (hi' := hi') (sonst := sonst) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_rest := execBlockH_ru rest) (ih_execEndH_ru_sonst := execEndH_ru sonst) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .narrowRequired e lo' hi' rest, σ, ρ =>
      execBlockH_ru_narrowRequired (e := e) (lo' := lo') (hi' := hi') (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_rest := execBlockH_ru rest) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .check c sonst rest, σ, ρ =>
      execBlockH_ru_check (c := c) (sonst := sonst) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_rest := execBlockH_ru rest) (ih_execEndH_ru_sonst := execEndH_ru sonst) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .float op a b lo hi rest, σ, ρ =>
      execBlockH_ru_float (op := op) (a := a) (b := b) (lo := lo) (hi := hi) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_rest := execBlockH_ru rest) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, _, _, .floatLit q lo hi rest, σ, ρ =>
      execBlockH_ru_floatLit (q := q) (lo := lo) (hi := hi) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_rest := execBlockH_ru rest) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .floatOf e lo hi rest, σ, ρ =>
      execBlockH_ru_floatOf (e := e) (lo := lo) (hi := hi) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_rest := execBlockH_ru rest) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, _, .floatNarrow e lo hi sonst rest, σ, ρ =>
      execBlockH_ru_floatNarrow (e := e) (lo := lo) (hi := hi) (sonst := sonst) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockH_ru_rest := execBlockH_ru rest) (ih_execEndH_ru_sonst := execEndH_ru sonst) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
theorem execEndH_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ),
    EndRel (execEndH S.mitRuhe O' U' passes R' (ruEnd e) (worldR σ) (envR ρ))
      (execEndH S O U passes R e σ ρ)
  | _, _, Λ, .ret e hΛ, σ, ρ =>
      execEndH_ru_ret (e := e) (hΛ := hΛ) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, .retScoped e R, σ, ρ =>
      execEndH_ru_retScoped (e := e) (R := R) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, _, .retWhy .., σ, ρ => Or.inl rfl
  | _, _, _, .retWhyScoped .., σ, ρ => Or.inl rfl
  | _, _, _, .leave _, σ, ρ => Or.inl rfl
  | _, _, _, .next _, σ, ρ => Or.inl rfl
  | _, _, _, .cons s rest, σ, ρ =>
      execEndH_ru_cons (s := s) (rest := rest) (σ := σ) (ρ := ρ) (ih_execStmtH_ru_s := execStmtH_ru s) (ih_execEndH_ru_rest := execEndH_ru rest) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, .bind e rest, σ, ρ =>
      execEndH_ru_bind (e := e) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndH_ru_rest := execEndH_ru rest) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, .bindCall g args he hp hr rest, σ, ρ =>
      execEndH_ru_bindCall (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndH_ru_rest := execEndH_ru rest) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, .bindCallElse g args he hp hr err rest, σ, ρ =>
      execEndH_ru_bindCallElse (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndH_ru_rest := execEndH_ru rest) (ih_execEndH_ru_err := execEndH_ru err) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, .bindAxiom a args he hw hg hd hgd rest, σ, ρ =>
      execEndH_ru_bindAxiom (a := a) (args := args) (he := he) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndH_ru_rest := execEndH_ru rest) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ =>
      execEndH_ru_bindAxiomElse (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndH_ru_rest := execEndH_ru rest) (ih_execEndH_ru_err := execEndH_ru err) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, .bindAxiomOpt e a args he hp hd hgd rest, σ, ρ =>
      execEndH_ru_bindAxiomOpt (e := e) (a := a) (args := args) (he := he) (hp := hp) (hd := hd) (hgd := hgd) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndH_ru_rest := execEndH_ru rest) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, .bindAxiomOptElse e a args he hp hd hgd hr err rest, σ, ρ =>
      execEndH_ru_bindAxiomOptElse (e := e) (a := a) (args := args) (he := he) (hp := hp) (hd := hd) (hgd := hgd) (hr := hr) (err := err) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndH_ru_rest := execEndH_ru rest) (ih_execEndH_ru_err := execEndH_ru err) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, _, .regRead r hk rest, σ, ρ =>
      execEndH_ru_regRead (r := r) (hk := hk) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndH_ru_rest := execEndH_ru rest) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, .regReadElse r hk zusage sonst rest, σ, ρ =>
      execEndH_ru_regReadElse (r := r) (hk := hk) (zusage := zusage) (sonst := sonst) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndH_ru_sonst := execEndH_ru sonst) (ih_execEndH_ru_rest := execEndH_ru rest) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, .awaits g payload hp hL hat rest, σ, ρ =>
      execEndH_ru_awaits (g := g) (payload := payload) (hp := hp) (hL := hL) (hat := hat) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndH_ru_rest := execEndH_ru rest) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, .bindCallInd (n := n) p args he hp hr rest, σ, ρ =>
      execEndH_ru_bindCallInd (n := n) (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndH_ru_rest := execEndH_ru rest) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, .narrow e lo' hi' sonst rest, σ, ρ =>
      execEndH_ru_narrow (e := e) (lo' := lo') (hi' := hi') (sonst := sonst) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndH_ru_rest := execEndH_ru rest) (ih_execEndH_ru_sonst := execEndH_ru sonst) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, .narrowRequired e lo' hi' rest, σ, ρ =>
      execEndH_ru_narrowRequired (e := e) (lo' := lo') (hi' := hi') (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndH_ru_rest := execEndH_ru rest) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, .exchange g neu hw hL rest, σ, ρ =>
      execEndH_ru_exchange (g := g) (neu := neu) (hw := hw) (hL := hL) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndH_ru_rest := execEndH_ru rest) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
  | _, _, Λ, .ite c t e, σ, ρ =>
      execEndH_ru_ite (c := c) (t := t) (e := e) (σ := σ) (ρ := ρ) (ih_execEndH_ru_e := execEndH_ru e) (ih_execEndH_ru_t := execEndH_ru t) (S := S) (O := O) (U := U) (passes := passes) (O' := O') (hO := hO) (U' := U') (R := R) (R' := R') (hU := hU) (hR := hR)
theorem execArmsH_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs))
    (σ : World D) (ρ : Env D Γ),
    AusRelRu (execArmsH S.mitRuhe O' U' passes R' (ruArms arms) (valR (.sum cs) v)
        (worldR σ) (envR ρ))
      (execArmsH S O U passes R arms v σ ρ)
  | _, _, _, _, _, .cons (c := none) b rest, ⟨⟨0, _⟩, nutz⟩, σ, ρ => execBlockH_ru b σ ρ
  | _, _, _, _, _, .cons (c := some τ) b rest, ⟨⟨0, _⟩, nutz⟩, σ, ρ =>
      AusRelRu.schrumpf (execBlockH_ru b σ (Env.cons nutz ρ))
  | _, _, _, _, _, .cons (c := none) b rest, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ =>
      execArmsH_ru rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩ σ ρ
  | _, _, _, _, _, .cons (c := some τ) b rest, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ =>
      execArmsH_ru rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩ σ ρ

theorem execGrundH_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n) (σ : World D) (ρ : Env D Γ),
    AusRelRu (execGrundH S.mitRuhe O' U' passes R' (ruGArms arms) r (worldR σ) (envR ρ))
      (execGrundH S O U passes R arms r σ ρ)
  | _, _, _, _, _, .cons b _, ⟨0, _⟩, σ, ρ => execBlockH_ru b σ ρ
  | _, _, _, _, _, .cons _ rest, ⟨i + 1, h⟩, σ, ρ =>
      execGrundH_ru rest ⟨i, Nat.lt_of_succ_lt_succ h⟩ σ ρ

end

end Haupt

/-- **The body of `some f` in `P.mitRuhe` under the lock-invariant semantics
    runs as the body of `f` in `P`**, up to the label of a logic failure. -/
theorem rumpfH_mitRuhe (P : Programm D) (S : SperrInv D) (O : Orakel D) (O' : Orakel D.mitRuhe)
    (hO : OrakelRu O O') (U : Umwelt D) (U' : Umwelt D.mitRuhe) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) →
      RufAusgang f)
    (hU : ∀ L σ, U' L (worldR σ) = worldR (U L σ)) (hR : RufRel R R')
    (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) :
    @EndRel D (vertragVon D f) false (D.params f)
      (execEndH S.mitRuhe O' U' passes R' (P.mitRuhe.rumpf (some f)) (worldR σ) (envR ρ))
      (execEndH S O U passes R (P.rumpf f) σ ρ) := by
  have e := execEndH_umΛ S.mitRuhe O' U' passes R' (anfang_map (D.signatur f))
    (ruEnd (P.rumpf f)) (worldR σ) (envR ρ)
  show @EndRel D (vertragVon D f) false (D.params f) (execEndH S.mitRuhe O' U' passes R'
    (Endblock.umΛ (anfang_map (D.signatur f)) (ruEnd (P.rumpf f))) (worldR σ) (envR ρ)) _
  rw [e]
  exact execEndH_ru S O O' hO U U' passes R R' hU hR (P.rumpf f) σ ρ

#print axioms Gabbro.Grammatik.worldR_worldZ
#print axioms Gabbro.Grammatik.envR_envZ
#print axioms Gabbro.Grammatik.orakelRu_zurueck
#print axioms Gabbro.Grammatik.execStmtH_ru
#print axioms Gabbro.Grammatik.execEndH_ru
#print axioms Gabbro.Grammatik.rumpfH_mitRuhe

end Gabbro.Grammatik
