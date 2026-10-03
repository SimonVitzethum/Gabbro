/-
  File:      Grammatik/X86/OptDceDead.lean
  Subject:   Dead-code elimination rule lemma (lane 865).

  DESIGN section 7 row: local premises "pure (no token/atomic/call/check/
  stop/trap-capable FP) + dead confirmed", certificate "A+B", failure cases
  "remove `0.0/0.0` (an unused NaN hides `logik bereich`); remove a spin
  load", phase M, cost O(sites).

  What is proved here, over the REUSED canonical vocabulary (`Typen`,
  `Syntax`, `Semantik`, `KostenG`, `CFormenI`, `X86.Typen`, `X86.Wort`):
  removing a pure overwritten local write preserves the `execBlock`
  outcome. No `ensures` is derived, no refusal becomes a warning, no
  faulting form is speculated above its guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.KostenG
import Grammatik.CFormenI
import Grammatik.X86.Typen
import Grammatik.X86.Wort

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one dead-code site
    (DESIGN section 7 row): the removed computation reads no shared
    carrier (`orteLeer`, recomputed from `Expr.orte`) and its target is
    dead at the site (`zielTot`, recomputed liveness: immediate
    redefinition before any read). -/
structure DceCert where
  orteLeer : Bool
  zielTot : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL optimisation
    falls back to another certified translation, never to a warning. -/
def dceZulassen (c : DceCert) : Bool :=
  c.orteLeer && c.zielTot

/-! ## 1. Refusal: a site that reads shared state, or whose target is
    live, must NOT be eliminated.

    Both DESIGN failure cases route through these Bools: a spin load
    reads a shared carrier, so its recomputed `orteLeer` is `false`; a
    trap-capable float block is never a pure local write, so no
    overwrite window admits it (exhibited in section 5). Both are proved
    of the decided Bool, so the validator cannot silently skip them. -/

/-- A site whose removed computation reads shared state refuses. -/
theorem dceVerweigert_orte (c : DceCert)
    (h : c.orteLeer = false) :
    dceZulassen c = false := by
  simp [dceZulassen, h]

/-- A site whose target is live refuses. -/
theorem dceVerweigert_tot (c : DceCert)
    (h : c.zielTot = false) :
    dceZulassen c = false := by
  simp [dceZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_dceZulassen_ok :
    dceZulassen ⟨true, true⟩ = true := by
  decide

/-- Probe: a shared-reading site is refused. -/
theorem probe_dceZulassen_orte :
    dceZulassen ⟨false, true⟩ = false := by
  decide

/-- Probe: a live target is refused. -/
theorem probe_dceZulassen_tot :
    dceZulassen ⟨true, false⟩ = false := by
  decide

/-! ## 2. Local liveness: which locals an expression reads.

    The validator recomputes `liest e2 x` at the overwrite window: the
    first write is dead exactly when the overwriting expression does
    not read its target. Memory reads (`slot`, `glob`, `reaches`) are
    tracked separately by `Expr.orte` (section 4 premise `hRein`), so
    `liest` only answers locals. Quantified bodies (`forallSlots`,
    `existsSlots`) bind a fresh index: the analysis answers `true`
    there (conservative refusal, never a silent removal). -/

mutual

/-- Decided local read: `true` when `e` may read the local `x`.
    Recomputed by the validator from the source, never trusted. -/
def liest {Γ : Ctx} {Λ : List (Res D)} {τ τ' : Ty} :
    Expr D Γ Λ τ → Var Γ τ' → Bool
  | .lit _, _ => false
  | .wahr, _ => false
  | .falsch, _ => false
  | .var y, x => decide (y.idx = x.idx)
  | .glob _ _, _ => false
  | .slot _ _ i _, x => liest i x
  | .durch p _ _ _ i _, x => liest p x || liest i x
  | .ptrOf _ _ _ _, _ => false
  | .fnref _ _ _, _ => false
  | .altGlob _ _, _ => false
  | .altSlot _ _ i _, x => liest i x
  | .weiter _ _ e, x => liest e x
  | .add a b, x => liest a x || liest b x
  | .sub a b, x => liest a x || liest b x
  | .neg a, x => liest a x
  | .mul a b, x => liest a x || liest b x
  | .div _ _ a b, x => liest a x || liest b x
  | .rem _ _ a b, x => liest a x || liest b x
  | .sdiv _ a b, x => liest a x || liest b x
  | .srem _ a b, x => liest a x || liest b x
  | .leseBytes _ _ _ _ i _ _ _, x => liest i x
  | .band _ _ a b, x => liest a x || liest b x
  | .bor _ _ _ _ _ a b, x => liest a x || liest b x
  | .bxor _ _ _ _ _ a b, x => liest a x || liest b x
  | .shl _ _ _ _ _ a b, x => liest a x || liest b x
  | .shr _ _ _ _ _ a b, x => liest a x || liest b x
  | .lt a b, x => liest a x || liest b x
  | .le a b, x => liest a x || liest b x
  | .eq a b, x => liest a x || liest b x
  | .fllt a b, x => liest a x || liest b x
  | .flle a b, x => liest a x || liest b x
  | .und a b, x => liest a x || liest b x
  | .oder a b, x => liest a x || liest b x
  | .nicht a, x => liest a x
  | .none _, _ => false
  | .some e, x => liest e x
  | .istSome e, x => liest e x
  | .fall _ _ nutz, x => liestNutz nutz x
  | .grund _ _, _ => false
  | .forallSlots _ _ _, _ => true
  | .existsSlots _ _ _, _ => true
  | .reaches _ _ _ a b _, x => liest a x || liest b x

/-- Decided local read through a sum payload. -/
def liestNutz {Γ : Ctx} {Λ : List (Res D)} {c : Option (Int × Int)} {τ' : Ty} :
    NutzlastExpr D Γ Λ c → Var Γ τ' → Bool
  | .keine, _ => false
  | .zahl e, x => liest e x

end

/-! ## 3. Frame lemma: setting an unread local changes no `eval`.

    If the validator recomputed `liest e x = false`, evaluating `e`
    cannot observe the local `x`, so writing `x` first is invisible to
    `e`. The induction goes through `Expr.rec` with `ρ x v`
    re-quantified per case (subterms vary in type; the var type `τ'`
    stays independent of the expression type `τ`). Quantified bodies
    need no induction hypothesis: `liest` answers `true` there, so the
    premise is contradictory by computation. -/

theorem eval_set_frisch {D : Deklaration} {Λ : List (Res D)} {σ₀ σ : World D} :
    ∀ {Γ : Ctx} {τ τ' : Ty} (e : Expr D Γ Λ τ) (ρ : Env D Γ)
      (x : Var Γ τ') (v : Wert D τ'),
      liest e x = false → eval σ₀ e σ (ρ.set x v) = eval σ₀ e σ ρ := by
  intro Γ τ τ' e
  induction e using Expr.rec
    (motive_2 := fun Γ Λ c nutz =>
      ∀ (ρ : Env D Γ) (x : Var Γ τ') (v : Wert D τ'),
        liestNutz nutz x = false → evalNutz σ₀ nutz σ (ρ.set x v) = evalNutz σ₀ nutz σ ρ) with
  | lit n =>
    intro ρ x v h
    simp only [liest] at h
    rfl
  | wahr =>
    intro ρ x v h
    simp only [liest] at h
    rfl
  | falsch =>
    intro ρ x v h
    simp only [liest] at h
    rfl
  | var y =>
    intro ρ x v h
    simp only [eval]
    have hne : y.idx ≠ x.idx := of_decide_eq_false h
    exact Env.get_set_other ρ x v y hne
  | glob g hL =>
    intro ρ x v h
    simp only [liest] at h
    rfl
  | slot t f i hL ih =>
    intro ρ x v h
    have hi : liest i x = false := h
    simp only [eval, ih ρ x v hi]
  | durch p t ht f i hL ihp ihi =>
    intro ρ x v h
    cases ha : liest p x with
    | true => simp [liest, ha] at h
    | false =>
      cases hb : liest i x with
      | true => simp [liest, hb] at h
      | false => simp only [eval, ihi ρ x v hb]
  | ptrOf t n ht rw =>
    intro ρ x v h
    simp only [liest] at h
    rfl
  | fnref f n hf =>
    intro ρ x v h
    simp only [liest] at h
    rfl
  | altGlob g hL =>
    intro ρ x v h
    simp only [liest] at h
    rfl
  | altSlot t f i hL ih =>
    intro ρ x v h
    have hi : liest i x = false := h
    simp only [eval, ih ρ x v hi]
  | weiter h1 h2 e ih =>
    intro ρ x v h
    have he : liest e x = false := h
    show Zahl.weiter h1 h2 (eval σ₀ e σ (ρ.set x v)) = Zahl.weiter h1 h2 (eval σ₀ e σ ρ)
    exact congrArg _ (ih ρ x v he)
  | add a b iha ihb =>
    intro ρ x v h
    cases ha : liest a x with
    | true => simp [liest, ha] at h
    | false =>
      cases hb : liest b x with
      | true => simp [liest, hb] at h
      | false =>
        simp only [eval]
        rw [iha ρ x v ha, ihb ρ x v hb]
  | sub a b iha ihb =>
    intro ρ x v h
    cases ha : liest a x with
    | true => simp [liest, ha] at h
    | false =>
      cases hb : liest b x with
      | true => simp [liest, hb] at h
      | false =>
        simp only [eval]
        rw [iha ρ x v ha, ihb ρ x v hb]
  | neg a ih =>
    intro ρ x v h
    have ha : liest a x = false := h
    simp only [eval]
    rw [ih ρ x v ha]
  | mul a b iha ihb =>
    intro ρ x v h
    cases ha : liest a x with
    | true => simp [liest, ha] at h
    | false =>
      cases hb : liest b x with
      | true => simp [liest, hb] at h
      | false =>
        simp only [eval]
        rw [iha ρ x v ha, ihb ρ x v hb]
  | div h0 h1 a b iha ihb =>
    intro ρ x v h
    cases ha : liest a x with
    | true => simp [liest, ha] at h
    | false =>
      cases hb : liest b x with
      | true => simp [liest, hb] at h
      | false =>
        simp only [eval]
        rw [iha ρ x v ha, ihb ρ x v hb]
  | rem h0 h1 a b iha ihb =>
    intro ρ x v h
    cases ha : liest a x with
    | true => simp [liest, ha] at h
    | false =>
      cases hb : liest b x with
      | true => simp [liest, hb] at h
      | false =>
        simp only [eval]
        rw [iha ρ x v ha, ihb ρ x v hb]
  | sdiv hb a b iha ihb =>
    intro ρ x v h
    cases ha : liest a x with
    | true => simp [liest, ha] at h
    | false =>
      cases hb : liest b x with
      | true => simp [liest, hb] at h
      | false =>
        simp only [eval]
        rw [iha ρ x v ha, ihb ρ x v hb]
  | srem hb a b iha ihb =>
    intro ρ x v h
    cases ha : liest a x with
    | true => simp [liest, ha] at h
    | false =>
      cases hb : liest b x with
      | true => simp [liest, hb] at h
      | false =>
        simp only [eval]
        rw [iha ρ x v ha, ihb ρ x v hb]
  | leseBytes t f hf n i hlo hhi hL ih =>
    intro ρ x v h
    have hi : liest i x = false := h
    simp only [eval, ih ρ x v hi]
    rfl
  | band h0 h0' a b iha ihb =>
    intro ρ x v h
    cases ha : liest a x with
    | true => simp [liest, ha] at h
    | false =>
      cases hb : liest b x with
      | true => simp [liest, hb] at h
      | false =>
        simp only [eval]
        rw [iha ρ x v ha, ihb ρ x v hb]
  | bor w h0 h0' hw1 hw2 a b iha ihb =>
    intro ρ x v h
    cases ha : liest a x with
    | true => simp [liest, ha] at h
    | false =>
      cases hb : liest b x with
      | true => simp [liest, hb] at h
      | false =>
        simp only [eval]
        rw [iha ρ x v ha, ihb ρ x v hb]
  | bxor w h0 h0' hw1 hw2 a b iha ihb =>
    intro ρ x v h
    cases ha : liest a x with
    | true => simp [liest, ha] at h
    | false =>
      cases hb : liest b x with
      | true => simp [liest, hb] at h
      | false =>
        simp only [eval]
        rw [iha ρ x v ha, ihb ρ x v hb]
  | shl w hw1 hw2 h0 h0' a b iha ihb =>
    intro ρ x v h
    cases ha : liest a x with
    | true => simp [liest, ha] at h
    | false =>
      cases hb : liest b x with
      | true => simp [liest, hb] at h
      | false =>
        simp only [eval]
        rw [iha ρ x v ha, ihb ρ x v hb]
  | shr w hw1 hw2 h0 h0' a b iha ihb =>
    intro ρ x v h
    cases ha : liest a x with
    | true => simp [liest, ha] at h
    | false =>
      cases hb : liest b x with
      | true => simp [liest, hb] at h
      | false =>
        simp only [eval]
        rw [iha ρ x v ha, ihb ρ x v hb]
  | lt a b iha ihb =>
    intro ρ x v h
    cases ha : liest a x with
    | true => simp [liest, ha] at h
    | false =>
      cases hb : liest b x with
      | true => simp [liest, hb] at h
      | false =>
        simp only [eval]
        rw [iha ρ x v ha, ihb ρ x v hb]
  | le a b iha ihb =>
    intro ρ x v h
    cases ha : liest a x with
    | true => simp [liest, ha] at h
    | false =>
      cases hb : liest b x with
      | true => simp [liest, hb] at h
      | false =>
        simp only [eval]
        rw [iha ρ x v ha, ihb ρ x v hb]
  | eq a b iha ihb =>
    intro ρ x v h
    cases ha : liest a x with
    | true => simp [liest, ha] at h
    | false =>
      cases hb : liest b x with
      | true => simp [liest, hb] at h
      | false =>
        simp only [eval]
        rw [iha ρ x v ha, ihb ρ x v hb]
  | fllt a b iha ihb =>
    intro ρ x v h
    cases ha : liest a x with
    | true => simp [liest, ha] at h
    | false =>
      cases hb : liest b x with
      | true => simp [liest, hb] at h
      | false =>
        simp only [eval]
        rw [iha ρ x v ha, ihb ρ x v hb]
  | flle a b iha ihb =>
    intro ρ x v h
    cases ha : liest a x with
    | true => simp [liest, ha] at h
    | false =>
      cases hb : liest b x with
      | true => simp [liest, hb] at h
      | false =>
        simp only [eval]
        rw [iha ρ x v ha, ihb ρ x v hb]
  | und a b iha ihb =>
    intro ρ x v h
    cases ha : liest a x with
    | true => simp [liest, ha] at h
    | false =>
      cases hb : liest b x with
      | true => simp [liest, hb] at h
      | false =>
        simp only [eval]
        rw [iha ρ x v ha, ihb ρ x v hb]
  | oder a b iha ihb =>
    intro ρ x v h
    cases ha : liest a x with
    | true => simp [liest, ha] at h
    | false =>
      cases hb : liest b x with
      | true => simp [liest, hb] at h
      | false =>
        simp only [eval]
        rw [iha ρ x v ha, ihb ρ x v hb]
  | nicht a ih =>
    intro ρ x v h
    have ha : liest a x = false := h
    simp only [eval]
    rw [ih ρ x v ha]
  | none n =>
    intro ρ x v h
    simp only [liest] at h
    rfl
  | some e ih =>
    intro ρ x v h
    have he : liest e x = false := h
    simp only [eval]
    rw [ih ρ x v he]
  | istSome e ih =>
    intro ρ x v h
    have he : liest e x = false := h
    simp only [eval]
    rw [ih ρ x v he]
  | fall cs i nutz ih =>
    intro ρ x v h
    have hn : liestNutz nutz x = false := h
    simp only [eval]
    rw [ih ρ x v hn]
  | grund n r =>
    intro ρ x v h
    simp only [liest] at h
    rfl
  | forallSlots t body hL ih =>
    intro ρ x v h
    simp [liest] at h
  | existsSlots t body hL ih =>
    intro ρ x v h
    simp [liest] at h
  | reaches t f hf a b hL iha ihb =>
    intro ρ x v h
    cases ha : liest a x with
    | true => simp [liest, ha] at h
    | false =>
      cases hb : liest b x with
      | true => simp [liest, hb] at h
      | false =>
        simp only [eval]
        rw [iha ρ x v ha, ihb ρ x v hb]
  | keine =>
    rfl
  | zahl e ih =>
    simp only [evalNutz]
    refine ih _ _ _ ?_
    assumption

/-! ## 4. Concrete witness components on the reference program.

    The removed write `x = 5`, the overwriting write `x = 7` (both
    widened to `0 .. 10`), the one-variable environment, and the
    overwriting value -- all as closed definitions, so every joint
    witness below unifies without placeholders. -/

/-- The removed write's expression: `5` widened to `0 .. 10`. -/
def dceE1 : Expr refD [.int 0 10] [] (.int 0 10) :=
  .weiter (by decide) (by decide) (.lit 5)

/-- The overwriting write's expression: `7` widened to `0 .. 10`. -/
def dceE2 : Expr refD [.int 0 10] [] (.int 0 10) :=
  .weiter (by decide) (by decide) (.lit 7)

/-- The one-variable environment holding `5`. -/
def dceRho : Env refD [.int 0 10] :=
  Env.cons (⟨5, by decide, by decide⟩ : Wert refD (.int 0 10)) Env.nil

/-- The overwriting value `7`. -/
def dceV7 : Wert refD (.int 0 10) :=
  ⟨7, by decide, by decide⟩

/-- The removed computation reads no shared carrier. -/
theorem dceE1_rein : dceE1.orte = [] := by decide

/-- The overwriting expression does not read the target. -/
theorem dceE2_tot : liest dceE2 (Var.hier : Var [.int 0 10] (.int 0 10)) = false := by decide

/-- The removed expression does not read the target either. -/
theorem dceE1_tot : liest dceE1 (Var.hier : Var [.int 0 10] (.int 0 10)) = false := by decide

/-! ## 5. Joint witness for the frame lemma: all premises together.

    Instantiated on the non-degenerate reference program `refD` (whose
    `einzahlen` writes its table): `dceE1` under `dceRho`, beside the
    reached F-machine run `MB` that changes memory (`refB_erreicht`,
    `refB_schreibt`). -/

/-- JOINT WITNESS for `eval_set_frisch`: setting an unread local
    changes no value, on `refD` beside the memory-changing run. -/
theorem eval_set_frisch_zeuge :
    ∃ (Γ : Ctx) (Λ : List (Res refD)) (τ τ' : Ty) (e : Expr refD Γ Λ τ)
      (σ₀ σ : World refD) (ρ : Env refD Γ) (x : Var Γ τ') (v : Wert refD τ')
      (_h : liest e x = false),
      eval σ₀ e σ (ρ.set x v) = eval σ₀ e σ ρ
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hF := eval_set_frisch (D := refD) (Λ := [])
    (σ₀ := refSp0.welt []) (σ := refSp0.welt [])
    (Γ := [.int 0 10]) (τ := .int 0 10) (τ' := .int 0 10)
    (e := dceE1) (ρ := dceRho) (x := Var.hier) (v := dceV7) dceE1_tot
  refine ⟨[.int 0 10], [], .int 0 10, .int 0 10, dceE1, refSp0.welt [], refSp0.welt [],
    dceRho, Var.hier, dceV7, dceE1_tot, hF, refEin_schreibt (),
    refB_erreicht, refB_schreibt⟩

/-! ## 6. Small helpers: empty reads observe nothing, double set collapses. -/

/-- Reading no carrier appends no trace event: the world is unchanged. -/
theorem lese_nil {D : Deklaration} (σ : World D) (Λ : List (Res D)) :
    σ.lese Λ [] = σ := by
  simp [World.lese, World.merke]

/-- Setting the same local twice keeps only the second value. -/
theorem envSet_twice {D : Deklaration} {Γ : Ctx} {τ : Ty}
    (ρ : Env D Γ) (x : Var Γ τ) (a b : Wert D τ) :
    (ρ.set x a).set x b = ρ.set x b := by
  cases x with
  | hier =>
    cases ρ with
    | cons _ _ => rfl
  | dort x' =>
    cases ρ with
    | cons _ ρ' => simp only [Env.set, envSet_twice ρ' x' a b]

/-! ## 7. Connection: removing a pure overwritten write preserves the run.

    The rewrite fires on two consecutive writes to the same local
    (the DESIGN overwrite window): the first value is dead exactly
    when the overwriting expression does not read its target (`hTot`,
    recomputed `liest`) and the removed computation reads no shared
    carrier (`hRein`, recomputed `Expr.orte`). Conclusion, jointly:
    (1) the `execBlock` OUTCOME is equal -- same constructor, same
    successor worlds and environments -- so the evaluated VALUES
    agree, no fault is added or removed (`logik`/`hardware` agree:
    `assignVar` never faults, and `e2` evaluates identically by the
    frame lemma), every downstream observation agrees (contracts at
    their place read the same values from the same environments, call
    logs gain no event since the window holds no call, no shared
    access is added or removed for concurrency -- `e1.orte = []`
    appends no trace event by `lese_nil`), and the step-budget
    accounting only shrinks (section 7);
    (2) IEEE: the window covers local writes only -- a trap-capable
    float block (`Block.gleit`, `logik bereich` on out-of-range or
    NaN) is a different constructor the rule never fires on
    (section 8 refusal exhibit).
    Nothing here derives an `ensures`, turns a refusal into a warning,
    or speculates a faulting form above its guard. The checker's range
    at any site is untouched by the removal and still enforced there. -/

/-- CONNECTION: removing `x = e1` before `x = e2` preserves the
    `execBlock` outcome when `e1` reads nothing shared and `e2`
    does not read `x`. -/
theorem OptDceDead_verbindung {D : Deklaration} {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ'' : List (Res D)} {τ : Ty}
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (x : Var Γ τ) (e1 e2 : Expr D Γ Λ τ)
    (rest : Block D V l Γ Λ Λ'')
    (hRein : e1.orte = [])
    (hTot : liest e2 x = false)
    (σ : World D) (ρ : Env D Γ) :
    execBlock O passes R (Block.cons (Stmt.assignVar x e1) (Block.cons (Stmt.assignVar x e2) rest)) σ ρ
    = execBlock O passes R (Block.cons (Stmt.assignVar x e2) rest) σ ρ := by
  have hL : σ.lese Λ e1.orte = σ := by
    rw [hRein]
    exact lese_nil σ Λ
  have hFr : ∀ (σ' : World D) (w : Wert D τ),
      eval σ' e2 σ' (ρ.set x w) = eval σ' e2 σ' ρ :=
    fun σ' w => eval_set_frisch e2 ρ x w hTot
  simp only [execBlock, execStmt, hL, hFr, envSet_twice]

/-! ## 8. Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptDceDead_verbindung` instantiated JOINTLY:
    `x = 5` overwritten by `x = 7` (both widened to `0 .. 10`) before
    `nil`, in the NON-DEGENERATE reference program `refD` (whose
    `einzahlen` writes its table, `refEin_schreibt`), beside the
    reached F-machine run `MB` that changes memory (`refB_erreicht`,
    `refB_schreibt`: slot `0` changes). -/

/-- JOINT WITNESS for `OptDceDead_verbindung`: the dead `x = 5`
    vanishes before `x = 7` on `refD`, beside the memory-changing
    reached run. -/
theorem OptDceDead_verbindung_zeuge :
    ∃ (V : Vertrag refD) (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) → RufAusgang f)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res refD)) (τ : Ty)
      (x : Var Γ τ) (e1 e2 : Expr refD Γ Λ τ)
      (rest : Block refD V l Γ Λ Λ')
      (_hRein : e1.orte = [])
      (_hTot : liest e2 x = false)
      (σ : World refD) (ρ : Env refD Γ),
      execBlock O passes R (Block.cons (Stmt.assignVar x e1) (Block.cons (Stmt.assignVar x e2) rest)) σ ρ
      = execBlock O passes R (Block.cons (Stmt.assignVar x e2) rest) σ ρ
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptDceDead_verbindung (D := refD) (V := vertragVon refD refEin)
    (O := refO) (passes := 0) (R := keinRuf) (l := true)
    (Γ := [.int 0 10]) (Λ := []) (Λ'' := []) (τ := .int 0 10)
    (x := Var.hier) (e1 := dceE1) (e2 := dceE2)
    (rest := Block.nil) (hRein := dceE1_rein) (hTot := dceE2_tot)
    (σ := refSp0.welt []) (ρ := dceRho)
  refine ⟨vertragVon refD refEin, refO, 0, keinRuf, true, [.int 0 10], [], [], .int 0 10,
    Var.hier, dceE1, dceE2, Block.nil, dceE1_rein, dceE2_tot, refSp0.welt [], dceRho,
    hV, refEin_schreibt (), refB_erreicht, refB_schreibt⟩

/-! ## 9. Budget: removing a write only shrinks the source cost.

    The optimized window is the original minus `1 + kostenExpr e1`
    (the removed `assignVar` and its expression): any source budget
    covering the original covers the optimized block. Step-budget
    exhaustion timing is the separate OPEN obligation per
    IR-VALIDIERUNG (lane 278); what is proved here is the cost
    inequality, so the budget side never grows. -/

/-- Removing the dead write does not grow `kostenBlock`. -/
theorem dceKosten_faellt {D : Deklaration} {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ'' : List (Res D)} {τ : Ty}
    (c : D.Fn → Nat) (pa : Nat)
    (x : Var Γ τ) (e1 e2 : Expr D Γ Λ τ)
    (rest : Block D V l Γ Λ Λ'') :
    kostenBlock c pa (Block.cons (Stmt.assignVar x e2) rest)
    ≤ kostenBlock c pa (Block.cons (Stmt.assignVar x e1) (Block.cons (Stmt.assignVar x e2) rest)) := by
  simp only [kostenBlock, kostenStmt]
  omega

/-- JOINT WITNESS for `dceKosten_faellt`: the counted inequality on
    `refD` beside the memory-changing reached run. -/
theorem dceKosten_faellt_zeuge :
    ∃ (V : Vertrag refD) (c : refD.Fn → Nat) (pa : Nat)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res refD)) (τ : Ty)
      (x : Var Γ τ) (e1 e2 : Expr refD Γ Λ τ)
      (rest : Block refD V l Γ Λ Λ'),
      kostenBlock c pa (Block.cons (Stmt.assignVar x e2) rest)
      ≤ kostenBlock c pa (Block.cons (Stmt.assignVar x e1) (Block.cons (Stmt.assignVar x e2) rest))
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hK := dceKosten_faellt (D := refD) (V := vertragVon refD refEin)
    (c := fun _ => 0) (pa := 0) (l := true)
    (Γ := [.int 0 10]) (Λ := []) (Λ'' := []) (τ := .int 0 10)
    (x := Var.hier) (e1 := dceE1) (e2 := dceE2) (rest := Block.nil)
  refine ⟨vertragVon refD refEin, fun _ => 0, 0, true, [.int 0 10], [], [], .int 0 10,
    Var.hier, dceE1, dceE2, Block.nil, hK, refEin_schreibt (),
    refB_erreicht, refB_schreibt⟩

/-! ## 10. Refusal exhibit I: a dead float block can fault (IEEE).

    The DESIGN failure case "remove `0.0/0.0`": an unused NaN hides
    `logik bereich`. A `Block.gleitLit` whose literal lies outside its
    declared range evaluates to `.logik .bereich` -- removing such a
    block would delete a stop the source demands. The overwrite rule
    of section 7 never fires here: it removes `Stmt.assignVar`
    only. Concretely: `1` against the range `0 .. 0` faults. -/

/-- Probe: `1` against the range `0 .. 0` is no value. -/
theorem dceGleit_beispiel :
    gleitPasst (0, 1) (0, 1) (bruch (1, 1)) = none := by decide

/-- A dead float literal block faults instead of binding: removing it
    would hide `logik bereich`, so the rule must NOT fire here. -/
theorem dceVerweigert_gleit {D : Deklaration} {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (rest : Block D V l ((.fl (0, 1) (0, 1)) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) :
    execBlock O passes R (Block.gleitLit (1, 1) (0, 1) (0, 1) rest) σ ρ
    = .logik .bereich := by
  have hN := dceGleit_beispiel
  simp only [execBlock, hN]
  try rfl

/-- JOINT WITNESS for `dceVerweigert_gleit`: the faulting float block
    on `refD` beside the memory-changing reached run. -/
theorem dceVerweigert_gleit_zeuge :
    ∃ (V : Vertrag refD) (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) → RufAusgang f)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res refD))
      (rest : Block refD V l ((.fl (0, 1) (0, 1)) :: Γ) Λ Λ')
      (σ : World refD) (ρ : Env refD Γ),
      execBlock O passes R (Block.gleitLit (1, 1) (0, 1) (0, 1) rest) σ ρ
      = .logik .bereich
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hG := dceVerweigert_gleit (D := refD) (V := vertragVon refD refEin)
    (O := refO) (passes := 0) (R := keinRuf) (l := true)
    (Γ := []) (Λ := []) (Λ' := []) (rest := Block.nil)
    (σ := refSp0.welt []) (ρ := Env.nil)
  refine ⟨vertragVon refD refEin, refO, 0, keinRuf, true, [], [], [],
    Block.nil, refSp0.welt [], Env.nil, hG, refEin_schreibt (),
    refB_erreicht, refB_schreibt⟩

/-! ## 11. Refusal exhibit II: a shared read always observes (concurrency).

    The DESIGN failure case "remove a spin load": a spin/wait loop's
    load observes shared state, so removing it deletes a concurrency
    observation (and the loop's termination behaviour). Every shared
    read appends a trace event (`lese` grows `spur` by exactly one),
    hence no removed computation with `orte ≠ []` is pure: the
    `hRein` premise of section 7 refuses it. -/

/-- A shared-carrier read appends exactly one trace event: it is
    never pure, so removing it is refused by `hRein`. -/
theorem dceSpin_beobachtet {D : Deklaration} (σ : World D) (Λ : List (Res D)) (t : D.Tab) :
    (σ.lese Λ [.inl t]).spur.length = σ.spur.length + 1 := by
  simp [World.lese, World.merke]
  try rfl

/- CUTS:
    - No block-window float rewrite: section 10 exhibits the fault a
      dead `gleitLit` keeps (`logik bereich`); the two-block
      `gleitLit`/`gleit` window with recomputed avail facts (DESIGN
      certificate "A+B") stays with the lowering lane.
    - No non-overwrite deadness: `zielTot` beyond the immediate
      overwrite window (redefinition before any read across longer
      windows) needs recomputed liveness over whole blocks; only the
      overwrite window is connected here, where deadness holds by
      construction and `liest e2 x` is the recomputed check.
    - No totalCost/budget-exhaustion transfer: section 9 proves the
      source-cost inequality; relating machine work to `passes`
      exhaustion (`budget_simulation`) is the separate OPEN
      obligation per IR-VALIDIERUNG (lane 278).
    - No silicon correspondence, no TSO/GX bridge, no ABI/loader
      claim: correspondence stops at `execBlock` outcomes and
      `kostenBlock` numbers over the canonical source semantics.
    - No new `Befehl` evaluation: the one target semantics
      (`Ausfuehrung.schritt`) is reused untouched; this file adds no
      target forms.
    - No checker change: no source admission is tightened to ease
      proof; everything is over the real source semantics
      (`eval`/`execBlock`) and the real cost functions.
-/

#print axioms dceZulassen
#print axioms dceVerweigert_orte
#print axioms dceVerweigert_tot
#print axioms eval_set_frisch
#print axioms eval_set_frisch_zeuge
#print axioms OptDceDead_verbindung
#print axioms OptDceDead_verbindung_zeuge
#print axioms dceKosten_faellt
#print axioms dceKosten_faellt_zeuge
#print axioms dceGleit_beispiel
#print axioms dceVerweigert_gleit
#print axioms dceVerweigert_gleit_zeuge
#print axioms dceSpin_beobachtet

end Gabbro.Grammatik.X86
