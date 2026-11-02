module

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheSperre
public import Grammatik.Speichermodell.Maschine.SperreSemA
public import Grammatik.Speichermodell.Atomar.AtomarRuhe.Teil3

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
theorem execEndHA_ru_regRead {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (r)
    (hk)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.regRead r hk rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.regRead r hk rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  rw [worldR_fragt, hO.regLies, einpassen_ru O.zeiger O'.zeiger hO.zeiger]
  cases einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) with
  | none => exact Or.inl rfl
  | some v =>
      simp only [Option.map]
      erw [rzusage_mitRuhe]
      cases D.rzusage r v with
      | false => exact Or.inl rfl
      | true =>
          simp only [if_true]
          exact EndRel.schrumpf (ih_execEndHA_ru_rest (σ.fragt (.inr (.inl r))) (Env.cons v ρ))

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_regReadElse {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (r)
    (hk)
    (zusage)
    (sonst)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndHA_ru_sonst : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd sonst) (worldR σ) (envR ρ)) (execEndHA S O U A passes R sonst σ ρ))
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.regReadElse r hk zusage sonst rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.regReadElse r hk zusage sonst rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  rw [worldR_fragt, hO.regLies, einpassen_ru O.zeiger O'.zeiger hO.zeiger]
  cases einpassen O.zeiger (D.rtyp r) (O.regLies r (σ.fragt (.inr (.inl r)))) with
  | none => exact Or.inl rfl
  | some v =>
      simp only [Option.map]
      rw [ruE_orte, leseA_worldR hA]
      have ez := eval_ru (leseA A (σ.fragt (.inr (.inl r))) Λ zusage.orte) (leseA A (σ.fragt (.inr (.inl r))) Λ zusage.orte) zusage (Env.cons v ρ)
      change eval _ (ruE zusage) _ (Env.cons (valR _ v) (envR ρ)) = _ at ez
      rw [ez]
      cases h : (eval (leseA A (σ.fragt (.inr (.inl r))) Λ zusage.orte) zusage (leseA A (σ.fragt (.inr (.inl r))) Λ zusage.orte) (Env.cons v ρ) : Bool) with
      | false =>
          simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
          exact ih_execEndHA_ru_sonst _ ρ
      | true =>
          simp only [wahr?, valR_bool, h, if_true]
          exact EndRel.schrumpf (ih_execEndHA_ru_rest _ (Env.cons v ρ))

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_awaits {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (g)
    (payload)
    (hp)
    (hL)
    (hat)
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.awaits g payload hp hL hat rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.awaits g payload hp hL hat rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  rw [show ([Sum.inr g] : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) = [Sum.inr g] from rfl,
    worldR_fragt, leseA_worldR hA, hO.sichtbar]
  cases O.sichtbar g (leseA A (σ.fragt (.inr (.inr g))) Λ [Sum.inr g]) with
  | false => exact Or.inl rfl
  | true =>
      simp only [if_true]
      exact EndRel.schrumpf (ih_execEndHA_ru_rest (leseA A (σ.fragt (.inr (.inr g))) Λ [Sum.inr g])
        (Env.cons ((leseA A (σ.fragt (.inr (.inr g))) Λ [Sum.inr g]).globs g) ρ))

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_bindCallInd {V : Vertrag D}
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
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.bindCallInd (τ := zi_τ) (n := n) p args he hp hr rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.bindCallInd (τ := zi_τ) (n := n) p args he hp hr rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  erw [show (ruE p).orte ++ (ruA args).orte = p.orte ++ args.orte from
    kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args)]
  erw [leseA_worldR hA, eval_ru, evalArgs_ru]
  cases h : eval (leseA A σ Λ (p.orte ++ args.orte)) p (leseA A σ Λ (p.orte ++ args.orte)) ρ with
  | mk g hg =>
      rw [valR_fnptr]
      dsimp only
      erw [umsig_ru hg]
      rcases hR g (leseA A σ Λ (p.orte ++ args.orte)) (umsig hg (evalArgs
          (leseA A σ Λ (p.orte ++ args.orte)) args (leseA A σ Λ (p.orte ++ args.orte)) ρ))
        with hx' | ⟨e', e, h1, h2, ht⟩
      · erw [hx']
        cases hx : R g (leseA A σ Λ (p.orte ++ args.orte)) (umsig hg (evalArgs
            (leseA A σ Λ (p.orte ++ args.orte)) args (leseA A σ Λ (p.orte ++ args.orte)) ρ)) with
        | ok σ' v =>
            try erw [hx]
            simp only [rufR]
            erw [execEndHA_umΛ, ergWert_ru (ergSig hg he)]
            exact EndRel.schrumpf
              (ih_execEndHA_ru_rest σ' (Env.cons (ergWert (ergSig hg he) v) ρ))
        | why σ' r => exact keinGrundSig hg hr r
        | logik e => (try erw [hx]); exact Or.inl rfl
        | hardware e => (try erw [hx]); exact Or.inl rfl
      · erw [h1, h2]
        exact Or.inr ⟨e', e, rfl, rfl, ht⟩

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_narrow {V : Vertrag D}
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
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    (ih_execEndHA_ru_sonst : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd sonst) (worldR σ) (envR ρ)) (execEndHA S O U A passes R sonst σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.narrow (lo := zi_lo) (hi := zi_hi) e lo' hi' sonst rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  simp only [ruE_orte, leseA_worldR hA, eval_ru, valR_int]
  by_cases hc : lo' ≤ (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ∧
      (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ≤ hi'
  · erw [dif_pos hc, dif_pos hc]
    exact EndRel.schrumpf (ih_execEndHA_ru_rest _
      (Env.cons (⟨(eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n, hc.1, hc.2⟩ : Zahl lo' hi') ρ))
  · erw [dif_neg hc, dif_neg hc]
    exact ih_execEndHA_ru_sonst _ ρ

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_narrowRequired {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_lo}
    {zi_hi}
    (e)
    (lo')
    (hi')
    (rest)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.narrowRequired (lo := zi_lo) (hi := zi_hi) e lo' hi' rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.narrowRequired (lo := zi_lo) (hi := zi_hi) e lo' hi' rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  simp only [ruE_orte, leseA_worldR hA, eval_ru, valR_int]
  by_cases hc : lo' ≤ (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ∧
      (eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n ≤ hi'
  · erw [dif_pos hc, dif_pos hc]
    exact EndRel.schrumpf (ih_execEndHA_ru_rest _
      (Env.cons (⟨(eval (leseA A σ Λ e.orte) e (leseA A σ Λ e.orte) ρ).n, hc.1, hc.2⟩ : Zahl lo' hi') ρ))
  · erw [dif_neg hc, dif_neg hc]
    exact Or.inl rfl

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_exchange {V : Vertrag D}
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
    (ih_execEndHA_ru_rest : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd rest) (worldR σ) (envR ρ)) (execEndHA S O U A passes R rest σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.exchange g neu hw hL rest : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.exchange g neu hw hL rest : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  rw [show (Sum.inr g :: (ruE neu).orte : List (D.mitRuhe.Tab ⊕ D.mitRuhe.Glob)) =
    Sum.inr g :: neu.orte from congrArg (Sum.inr g :: ·) (ruE_orte neu), leseA_worldR hA]
  have ez := eval_ru (leseA A σ Λ (Sum.inr g :: neu.orte)) (leseA A σ Λ (Sum.inr g :: neu.orte)) neu
    (Env.cons ((leseA A σ Λ (Sum.inr g :: neu.orte)).globs g) ρ)
  change eval _ (ruE neu) _ (Env.cons (valR _ _) (envR ρ)) = _ at ez
  rw [show ((worldR (leseA A σ Λ (Sum.inr g :: neu.orte))).globs g) =
    valR _ ((leseA A σ Λ (Sum.inr g :: neu.orte)).globs g) from rfl, ez, schreibGlob_worldR]
  exact EndRel.schrumpf (ih_execEndHA_ru_rest
    ((leseA A σ Λ (Sum.inr g :: neu.orte)).schreibGlob g Λ (eval (leseA A σ Λ (Sum.inr g :: neu.orte)) neu
      (leseA A σ Λ (Sum.inr g :: neu.orte)) (Env.cons ((leseA A σ Λ (Sum.inr g :: neu.orte)).globs g) ρ)))
    (Env.cons ((leseA A σ Λ (Sum.inr g :: neu.orte)).globs g) ρ))

set_option linter.unusedSectionVars false in
theorem execEndHA_ru_ite {V : Vertrag D}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (c)
    (t)
    (e)
    (σ : World D)
    (ρ : Env D Γ)
    (ih_execEndHA_ru_e : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd e) (worldR σ) (envR ρ)) (execEndHA S O U A passes R e σ ρ))
    (ih_execEndHA_ru_t : ∀ (σ : World D), ∀ (ρ : Env D _), EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd t) (worldR σ) (envR ρ)) (execEndHA S O U A passes R t σ ρ))
    : EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd (.ite c t e : Endblock D V l Γ Λ)) (worldR σ) (envR ρ)) (execEndHA S O U A passes R (.ite c t e : Endblock D V l Γ Λ) σ ρ) :=
  by
  simp only [ruEnd, execEndHA]
  rw [ruE_orte, leseA_worldR hA, eval_ru]
  cases h : (eval (leseA A σ Λ c.orte) c (leseA A σ Λ c.orte) ρ : Bool)
  · simp only [wahr?, valR_bool, h, Bool.false_eq_true, if_false]
    exact ih_execEndHA_ru_e _ ρ
  · simp only [wahr?, valR_bool, h, if_true]
    exact ih_execEndHA_ru_t _ ρ

set_option maxHeartbeats 4000000 in
mutual

/-- **A translated statement runs as the statement under the lock-invariant
    semantics**, up to the label of a logic failure. -/
theorem execStmtHA_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ),
    AusRelRu (execStmtHA S.mitRuhe O' U' A' passes R' (ruS s) (worldR σ) (envR ρ))
      (execStmtHA S O U A passes R s σ ρ)
  | _, _, Λ, _, .assignSlot t f i e hw hL, σ, ρ =>
      execStmtHA_ru_assignSlot (t := t) (f := f) (i := i) (e := e) (hw := hw) (hL := hL) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .assignThru p t ht f i e hw hL, σ, ρ =>
      execStmtHA_ru_assignThru (p := p) (t := t) (ht := ht) (f := f) (i := i) (e := e) (hw := hw) (hL := hL) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .assignSlotRef r t ht ho f e hw hL, σ, ρ =>
      execStmtHA_ru_assignSlotRef (r := r) (t := t) (ht := ht) (ho := ho) (f := f) (e := e) (hw := hw) (hL := hL) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .assignGlob g e hw hL, σ, ρ =>
      execStmtHA_ru_assignGlob (g := g) (e := e) (hw := hw) (hL := hL) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .putBytes t f hf n i hlo hhi e hw hL, σ, ρ =>
      execStmtHA_ru_putBytes (t := t) (f := f) (hf := hf) (n := n) (i := i) (hlo := hlo) (hhi := hhi) (e := e) (hw := hw) (hL := hL) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .assignVar x e, σ, ρ =>
      execStmtHA_ru_assignVar (x := x) (e := e) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .shift (lo := lo) (hi := hi) t f hτ i von nach hn he hw hL, σ, ρ =>
      execStmtHA_ru_shift (lo := lo) (hi := hi) (t := t) (f := f) (hτ := hτ) (i := i) (von := von) (nach := nach) (hn := hn) (he := he) (hw := hw) (hL := hL) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .ite c t e, σ, ρ =>
      execStmtHA_ru_ite (c := c) (t := t) (e := e) (σ := σ) (ρ := ρ) (ih_execBlockHA_ru_e := execBlockHA_ru e) (ih_execBlockHA_ru_t := execBlockHA_ru t) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .onOption o p a, σ, ρ =>
      execStmtHA_ru_onOption (o := o) (p := p) (a := a) (σ := σ) (ρ := ρ) (ih_execBlockHA_ru_a := execBlockHA_ru a) (ih_execBlockHA_ru_p := execBlockHA_ru p) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .onTag v arms, σ, ρ =>
      execStmtHA_ru_onTag (v := v) (arms := arms) (σ := σ) (ρ := ρ) (ih_execArmsHA_ru_arms := execArmsHA_ru arms) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .onWhy r arms, σ, ρ =>
      execStmtHA_ru_onWhy (r := r) (arms := arms) (σ := σ) (ρ := ρ) (ih_execGrundHA_ru_arms := execGrundHA_ru arms) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .call g args hp hr, σ, ρ =>
      execStmtHA_ru_call (g := g) (args := args) (hp := hp) (hr := hr) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .callInd (n := n) p args hp hr, σ, ρ =>
      execStmtHA_ru_callInd (n := n) (p := p) (args := args) (hp := hp) (hr := hr) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .locks L hr body, σ, ρ =>
      execStmtHA_ru_locks (hr := hr) (body := body) (σ := σ) (ρ := ρ) (ih_execBlockHA_ru_body := execBlockHA_ru body) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, _, _, .breaking _ body, σ, ρ => by
      simp only [ruS, execStmtHA]
      exact execBlockHA_ru body σ ρ
  | l, _, Λ, _, .traverse t inv body, σ, ρ =>
      execStmtHA_ru_traverse (t := t) (inv := inv) (body := body) (σ := σ) (ρ := ρ) (ih_execBlockHA_ru_body := execBlockHA_ru body) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | l, _, Λ, _, .consumeTraverse t member edge inv bound mass body, σ, ρ =>
      execStmtHA_ru_consumeTraverse (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (σ := σ) (ρ := ρ) (ih_execBlockHA_ru_body := execBlockHA_ru body) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .retry n bis body ueber, σ, ρ =>
      execStmtHA_ru_retry (n := n) (bis := bis) (body := body) (ueber := ueber) (σ := σ) (ρ := ρ) (ih_execBlockHA_ru_body := execBlockHA_ru body) (ih_execBlockHA_ru_ueber := execBlockHA_ru ueber) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .forever a inv body, σ, ρ =>
      execStmtHA_ru_forever (a := a) (inv := inv) (body := body) (σ := σ) (ρ := ρ) (ih_execBlockHA_ru_body := execBlockHA_ru body) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .axiomCall a args h hw hg hd hgd, σ, ρ =>
      execStmtHA_ru_axiomCall (a := a) (args := args) (h := h) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .regWrite r hk e, σ, ρ =>
      execStmtHA_ru_regWrite (r := r) (hk := hk) (e := e) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, _, _, .transition .., σ, ρ => Or.inl rfl
  | _, _, Λ, _, .publish g e payload hp hw hL, σ, ρ =>
      execStmtHA_ru_publish (g := g) (e := e) (payload := payload) (hp := hp) (hw := hw) (hL := hL) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, _, _, .advances .., σ, ρ => by
      refine Or.inl ?_
      simp only [ruS]
      erw [execStmtHA_nachΛ]
      rfl
  | _, _, _, _, .retires .., σ, ρ => by
      refine Or.inl ?_
      simp only [ruS]
      erw [execStmtHA_nachΛ]
      rfl
  | _, _, Λ, _, .ret e hΛ, σ, ρ =>
      execStmtHA_ru_ret (e := e) (hΛ := hΛ) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .retScoped e R, σ, ρ =>
      execStmtHA_ru_retScoped (e := e) (R := R) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, _, _, .retWhy .., σ, ρ => Or.inl rfl
  | _, _, _, _, .retWhyScoped .., σ, ρ => Or.inl rfl
  | _, _, _, _, .leave _, σ, ρ => Or.inl rfl
  | _, _, _, _, .next _, σ, ρ => Or.inl rfl

theorem execBlockHA_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ),
    AusRelRu (execBlockHA S.mitRuhe O' U' A' passes R' (ruB b) (worldR σ) (envR ρ))
      (execBlockHA S O U A passes R b σ ρ)
  | _, _, _, _, .nil, σ, ρ => Or.inl rfl
  | _, _, _, _, .cons s rest, σ, ρ =>
      execBlockHA_ru_cons (s := s) (rest := rest) (σ := σ) (ρ := ρ) (ih_execStmtHA_ru_s := execStmtHA_ru s) (ih_execBlockHA_ru_rest := execBlockHA_ru rest) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .bind e rest, σ, ρ =>
      execBlockHA_ru_bind (e := e) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockHA_ru_rest := execBlockHA_ru rest) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .bindCall g args he hp hr rest, σ, ρ =>
      execBlockHA_ru_bindCall (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockHA_ru_rest := execBlockHA_ru rest) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .bindCallInd (n := n) p args he hp hr rest, σ, ρ =>
      execBlockHA_ru_bindCallInd (n := n) (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockHA_ru_rest := execBlockHA_ru rest) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .bindCallElse g args he hp hr err rest, σ, ρ =>
      execBlockHA_ru_bindCallElse (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockHA_ru_rest := execBlockHA_ru rest) (ih_execEndHA_ru_err := execEndHA_ru err) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .bindAxiom a args he hw hg hd hgd rest, σ, ρ =>
      execBlockHA_ru_bindAxiom (a := a) (args := args) (he := he) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockHA_ru_rest := execBlockHA_ru rest) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ =>
      execBlockHA_ru_bindAxiomElse (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockHA_ru_rest := execBlockHA_ru rest) (ih_execEndHA_ru_err := execEndHA_ru err) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, _, _, .regRead r hk rest, σ, ρ =>
      execBlockHA_ru_regRead (r := r) (hk := hk) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockHA_ru_rest := execBlockHA_ru rest) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .regReadElse r hk zusage sonst rest, σ, ρ =>
      execBlockHA_ru_regReadElse (r := r) (hk := hk) (zusage := zusage) (sonst := sonst) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockHA_ru_rest := execBlockHA_ru rest) (ih_execEndHA_ru_sonst := execEndHA_ru sonst) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .awaits g payload hp hL hat rest, σ, ρ =>
      execBlockHA_ru_awaits (g := g) (payload := payload) (hp := hp) (hL := hL) (hat := hat) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockHA_ru_rest := execBlockHA_ru rest) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .exchange g neu hw hL rest, σ, ρ =>
      execBlockHA_ru_exchange (g := g) (neu := neu) (hw := hw) (hL := hL) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockHA_ru_rest := execBlockHA_ru rest) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .narrow e lo' hi' sonst rest, σ, ρ =>
      execBlockHA_ru_narrow (e := e) (lo' := lo') (hi' := hi') (sonst := sonst) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockHA_ru_rest := execBlockHA_ru rest) (ih_execEndHA_ru_sonst := execEndHA_ru sonst) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .narrowRequired e lo' hi' rest, σ, ρ =>
      execBlockHA_ru_narrowRequired (e := e) (lo' := lo') (hi' := hi') (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockHA_ru_rest := execBlockHA_ru rest) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .check c sonst rest, σ, ρ =>
      execBlockHA_ru_check (c := c) (sonst := sonst) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockHA_ru_rest := execBlockHA_ru rest) (ih_execEndHA_ru_sonst := execEndHA_ru sonst) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .float op a b lo hi rest, σ, ρ =>
      execBlockHA_ru_float (op := op) (a := a) (b := b) (lo := lo) (hi := hi) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockHA_ru_rest := execBlockHA_ru rest) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, _, _, .floatLit q lo hi rest, σ, ρ =>
      execBlockHA_ru_floatLit (q := q) (lo := lo) (hi := hi) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockHA_ru_rest := execBlockHA_ru rest) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .floatOf e lo hi rest, σ, ρ =>
      execBlockHA_ru_floatOf (e := e) (lo := lo) (hi := hi) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockHA_ru_rest := execBlockHA_ru rest) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, _, .floatNarrow e lo hi sonst rest, σ, ρ =>
      execBlockHA_ru_floatNarrow (e := e) (lo := lo) (hi := hi) (sonst := sonst) (rest := rest) (σ := σ) (ρ := ρ) (ih_execBlockHA_ru_rest := execBlockHA_ru rest) (ih_execEndHA_ru_sonst := execEndHA_ru sonst) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
theorem execEndHA_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ),
    EndRel (execEndHA S.mitRuhe O' U' A' passes R' (ruEnd e) (worldR σ) (envR ρ))
      (execEndHA S O U A passes R e σ ρ)
  | _, _, Λ, .ret e hΛ, σ, ρ =>
      execEndHA_ru_ret (e := e) (hΛ := hΛ) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, .retScoped e R, σ, ρ =>
      execEndHA_ru_retScoped (e := e) (R := R) (σ := σ) (ρ := ρ) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, _, .retWhy .., σ, ρ => Or.inl rfl
  | _, _, _, .retWhyScoped .., σ, ρ => Or.inl rfl
  | _, _, _, .leave _, σ, ρ => Or.inl rfl
  | _, _, _, .next _, σ, ρ => Or.inl rfl
  | _, _, _, .cons s rest, σ, ρ =>
      execEndHA_ru_cons (s := s) (rest := rest) (σ := σ) (ρ := ρ) (ih_execStmtHA_ru_s := execStmtHA_ru s) (ih_execEndHA_ru_rest := execEndHA_ru rest) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, .bind e rest, σ, ρ =>
      execEndHA_ru_bind (e := e) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndHA_ru_rest := execEndHA_ru rest) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, .bindCall g args he hp hr rest, σ, ρ =>
      execEndHA_ru_bindCall (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndHA_ru_rest := execEndHA_ru rest) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, .bindCallElse g args he hp hr err rest, σ, ρ =>
      execEndHA_ru_bindCallElse (g := g) (args := args) (he := he) (hp := hp) (hr := hr) (err := err) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndHA_ru_rest := execEndHA_ru rest) (ih_execEndHA_ru_err := execEndHA_ru err) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, .bindAxiom a args he hw hg hd hgd rest, σ, ρ =>
      execEndHA_ru_bindAxiom (a := a) (args := args) (he := he) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndHA_ru_rest := execEndHA_ru rest) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ =>
      execEndHA_ru_bindAxiomElse (a := a) (args := args) (he := he) (hr := hr) (hw := hw) (hg := hg) (hd := hd) (hgd := hgd) (err := err) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndHA_ru_rest := execEndHA_ru rest) (ih_execEndHA_ru_err := execEndHA_ru err) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, _, .regRead r hk rest, σ, ρ =>
      execEndHA_ru_regRead (r := r) (hk := hk) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndHA_ru_rest := execEndHA_ru rest) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, .regReadElse r hk zusage sonst rest, σ, ρ =>
      execEndHA_ru_regReadElse (r := r) (hk := hk) (zusage := zusage) (sonst := sonst) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndHA_ru_sonst := execEndHA_ru sonst) (ih_execEndHA_ru_rest := execEndHA_ru rest) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, .awaits g payload hp hL hat rest, σ, ρ =>
      execEndHA_ru_awaits (g := g) (payload := payload) (hp := hp) (hL := hL) (hat := hat) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndHA_ru_rest := execEndHA_ru rest) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, .bindCallInd (n := n) p args he hp hr rest, σ, ρ =>
      execEndHA_ru_bindCallInd (n := n) (p := p) (args := args) (he := he) (hp := hp) (hr := hr) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndHA_ru_rest := execEndHA_ru rest) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, .narrow e lo' hi' sonst rest, σ, ρ =>
      execEndHA_ru_narrow (e := e) (lo' := lo') (hi' := hi') (sonst := sonst) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndHA_ru_rest := execEndHA_ru rest) (ih_execEndHA_ru_sonst := execEndHA_ru sonst) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, .narrowRequired e lo' hi' rest, σ, ρ =>
      execEndHA_ru_narrowRequired (e := e) (lo' := lo') (hi' := hi') (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndHA_ru_rest := execEndHA_ru rest) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, .exchange g neu hw hL rest, σ, ρ =>
      execEndHA_ru_exchange (g := g) (neu := neu) (hw := hw) (hL := hL) (rest := rest) (σ := σ) (ρ := ρ) (ih_execEndHA_ru_rest := execEndHA_ru rest) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
  | _, _, Λ, .ite c t e, σ, ρ =>
      execEndHA_ru_ite (c := c) (t := t) (e := e) (σ := σ) (ρ := ρ) (ih_execEndHA_ru_e := execEndHA_ru e) (ih_execEndHA_ru_t := execEndHA_ru t) (S := S) (O := O) (U := U) (A := A) (passes := passes) (O' := O') (hO := hO) (U' := U') (A' := A') (R := R) (R' := R') (hU := hU) (hA := hA) (hR := hR)
theorem execArmsHA_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs))
    (σ : World D) (ρ : Env D Γ),
    AusRelRu (execArmsHA S.mitRuhe O' U' A' passes R' (ruArms arms) (valR (.sum cs) v)
        (worldR σ) (envR ρ))
      (execArmsHA S O U A passes R arms v σ ρ)
  | _, _, _, _, _, .cons (c := none) b rest, ⟨⟨0, _⟩, nutz⟩, σ, ρ => execBlockHA_ru b σ ρ
  | _, _, _, _, _, .cons (c := some (lo, hi)) b rest, ⟨⟨0, _⟩, nutz⟩, σ, ρ =>
      AusRelRu.schrumpf (execBlockHA_ru b σ (Env.cons nutz ρ))
  | _, _, _, _, _, .cons (c := none) b rest, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ =>
      execArmsHA_ru rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩ σ ρ
  | _, _, _, _, _, .cons (c := some (lo, hi)) b rest, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ =>
      execArmsHA_ru rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩ σ ρ

theorem execGrundHA_ru {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n) (σ : World D) (ρ : Env D Γ),
    AusRelRu (execGrundHA S.mitRuhe O' U' A' passes R' (ruGArms arms) r (worldR σ) (envR ρ))
      (execGrundHA S O U A passes R arms r σ ρ)
  | _, _, _, _, _, .cons b _, ⟨0, _⟩, σ, ρ => execBlockHA_ru b σ ρ
  | _, _, _, _, _, .cons _ rest, ⟨i + 1, h⟩, σ, ρ =>
      execGrundHA_ru rest ⟨i, Nat.lt_of_succ_lt_succ h⟩ σ ρ

end

end HauptA

/-- **The body of `some f` in `P.mitRuhe` under the lock-invariant semantics
    runs as the body of `f` in `P`**, up to the label of a logic failure. -/
theorem rumpfHA_mitRuhe (P : Programm D) (S : SperrInv D) (O : Orakel D) (O' : Orakel D.mitRuhe)
    (hO : OrakelRu O O') (U : Umwelt D) (U' : Umwelt D.mitRuhe) (A : AUmwelt D)
    (A' : AUmwelt D.mitRuhe) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (R' : ∀ f : D.mitRuhe.Fn, World D.mitRuhe → Env D.mitRuhe (D.mitRuhe.params f) →
      RufAusgang f)
    (hU : ∀ L σ, U' L (worldR σ) = worldR (U L σ)) (hA : ∀ X σ, A' X (worldR σ) = worldR (A X σ))
    (hR : RufRel R R')
    (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) :
    @EndRel D (vertragVon D f) false (D.params f)
      (execEndHA S.mitRuhe O' U' A' passes R' (P.mitRuhe.rumpf (some f)) (worldR σ) (envR ρ))
      (execEndHA S O U A passes R (P.rumpf f) σ ρ) := by
  have e := execEndHA_umΛ S.mitRuhe O' U' A' passes R' (anfang_map (D.signatur f))
    (ruEnd (P.rumpf f)) (worldR σ) (envR ρ)
  show @EndRel D (vertragVon D f) false (D.params f) (execEndHA S.mitRuhe O' U' A' passes R'
    (Endblock.umΛ (anfang_map (D.signatur f)) (ruEnd (P.rumpf f))) (worldR σ) (envR ρ)) _
  rw [e]
  exact execEndHA_ru S O O' hO U U' A A' passes R R' hU hA hR (P.rumpf f) σ ρ

#print axioms Gabbro.Grammatik.execEndHA_ru
#print axioms Gabbro.Grammatik.rumpfHA_mitRuhe

end Gabbro.Grammatik
