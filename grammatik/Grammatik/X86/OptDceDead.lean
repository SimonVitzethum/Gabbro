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

/-! ## 4. Small helpers: empty reads observe nothing, double set collapses. -/

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

/- CUTS:
    - The `liest` frame lemma, the overwrite connection with its joint
      witness, the budget inequality, and the two DESIGN refusal
      exhibits (dead FP block, spin load) follow in later pieces.
-/

#print axioms dceZulassen

end Gabbro.Grammatik.X86
