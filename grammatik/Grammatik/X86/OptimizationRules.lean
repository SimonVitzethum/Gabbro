/-
  File:      Grammatik/X86/OptimizationRules.lean
  Subject:   Certified optimisation rules over the ACTUAL source syntax:
             rule statements, certificate schemas, executable validators
             and their generic soundness (grammatik/OPTIMIZER.md §11.2).

  Scope (OPTIMIZER.md §11.4, "start with arithmetic / constant-fold /
  strength-reduction rules against the actual existing helpers", and §11.5,
  "do NOT invent a second IR"; the accepted direct-lowering decision 594/606
  makes the typed source the one reference): every rule here is a function on the real
  typed source syntax (`Syntax.lean`: `Expr`/`Stmt`/`Block`), every
  correspondence a theorem over the real semantics (`Semantik.lean`:
  `eval`/`execStmt`/`execBlock`). No IR, no per-program rule, no trusted
  Rust verdict: a certificate only says WHERE and WHICH rule; the Lean
  validator recomputes every fact it needs from the source text.

  Shape (OPTIMIZER.md §7.1): untrusted candidate (a certificate) ->
  executable Lean validator (`applyExpr`/`applyStmt`/`applyBlock`,
  `checkStrength`, `applyPipeline`) -> either a checked output or `none`
  (refusal). Each validator has ONE generic soundness theorem, derived from
  the validator, never assumed as a simulation premise (§7.3).

  The joint `_zeuge` witnesses and the poison/positive probes live in
  `Grammatik/X86/OptimizationWitnesses.lean`.
-/
import Grammatik.Semantik
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.StaerkeReduktion
import Grammatik.X86.SourceMemory

namespace Gabbro.Grammatik.X86.OptimizationRules

open Gabbro.Grammatik
open Gabbro.Grammatik.X86

variable {D : Deklaration}

/-! ## 1. Reading values back at a general type

    Every rule is defined at a GENERAL type index (the
    `InvariantenOpt.alsLitOpt` precedent): a match on `Expr D Γ Λ (.int lo hi)`
    gets stuck on declaration-indexed constructors (`slot` at `D.typ t f`),
    while a free index unifies with every arm. `intOf`/`boolOf` read the
    carried number / truth value back where the type is an integer /
    boolean, and answer `none` elsewhere. -/

/-- The integer a value carries, at integer types only. -/
def intOf : (τ : Ty) → Wert D τ → Option Int
  | .int _ _, v => some v.n
  | _, _ => none

/-! ## 2. Constant evaluation (rule C1's fact source, OPTIMIZER.md §3.1)

    `constInt?` recomputes, inside Lean, the value of an integer expression
    built only from literals and the pure integer operators. Each arm uses
    EXACTLY the operation `eval` uses (`Zahl.add` … `Zahl.shr`, `Typen.lean`),
    so the soundness proof is a plain induction. Signed `sdiv`/`srem` FOLD
    here (a literal quotient is a literal quotient); what is refused for
    them is the shift lowering (§5, R4). Everything that reads memory,
    a variable, a global, a register or a float answers `none`. -/

/-- Both operands known: apply `f`; otherwise unknown. -/
def lift2 (f : Int → Int → Int) : Option Int → Option Int → Option Int
  | some x, some y => some (f x y)
  | _, _ => none

/-- The Lean-side constant evaluator for integer source expressions. -/
def constInt? {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} : Expr D Γ Λ τ → Option Int
  | .lit n => some n
  | .weiter _ _ e => constInt? e
  | .add a b => lift2 (· + ·) (constInt? a) (constInt? b)
  | .sub a b => lift2 (· - ·) (constInt? a) (constInt? b)
  | .neg a => (constInt? a).map (- ·)
  | .mul a b => lift2 (· * ·) (constInt? a) (constInt? b)
  | .div _ _ a b => lift2 Int.tdiv (constInt? a) (constInt? b)
  | .rem _ _ a b => lift2 Int.tmod (constInt? a) (constInt? b)
  | .sdiv _ a b => lift2 Int.tdiv (constInt? a) (constInt? b)
  | .srem _ a b => lift2 Int.tmod (constInt? a) (constInt? b)
  | .band _ _ a b => lift2 (fun x y => ((x.toNat &&& y.toNat : Nat) : Int)) (constInt? a) (constInt? b)
  | .bor _ _ _ _ _ a b => lift2 (fun x y => ((x.toNat ||| y.toNat : Nat) : Int)) (constInt? a) (constInt? b)
  | .bxor _ _ _ _ _ a b => lift2 (fun x y => ((x.toNat ^^^ y.toNat : Nat) : Int)) (constInt? a) (constInt? b)
  | .shl _ _ _ _ _ a b => lift2 (fun x y => x * 2 ^ y.toNat) (constInt? a) (constInt? b)
  | .shr _ _ _ _ _ a b => lift2 (fun x y => x / 2 ^ y.toNat) (constInt? a) (constInt? b)
  | _ => none

/-- Inversion for `lift2`. -/
theorem lift2_some {f : Int → Int → Int} {oa ob : Option Int} {v : Int}
    (h : lift2 f oa ob = some v) : ∃ x y, oa = some x ∧ ob = some y ∧ v = f x y := by
  cases oa <;> cases ob <;> simp_all [lift2]

/-- **Soundness of the constant evaluator**: a constant the validator
    recomputes is the value the real `eval` gives, in every world and
    environment. -/
theorem constInt?_sound {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (σ₀ σ : World D) (ρ : Env D Γ) (v : Int) (h : constInt? e = some v) :
    intOf τ (eval σ₀ e σ ρ) = some v := by
  revert ρ v h
  induction e using Expr.rec (motive_2 := fun _ _ _ _ => True) with
  | lit n => intro ρ v h; simp_all [constInt?, eval, intOf]
  | weiter h1 h2 e ih => intro ρ v h; have := ih ρ v h; simp_all [constInt?, eval, intOf, Zahl.weiter]
  | add a b iha ihb =>
    intro ρ v h
    obtain ⟨x, y, hx, hy, rfl⟩ := lift2_some h
    have := iha ρ x hx; have := ihb ρ y hy
    simp_all [eval, intOf, Zahl.add]
  | sub a b iha ihb =>
    intro ρ v h
    obtain ⟨x, y, hx, hy, rfl⟩ := lift2_some h
    have := iha ρ x hx; have := ihb ρ y hy
    simp_all [eval, intOf, Zahl.sub]
  | mul a b iha ihb =>
    intro ρ v h
    obtain ⟨x, y, hx, hy, rfl⟩ := lift2_some h
    have := iha ρ x hx; have := ihb ρ y hy
    simp_all [eval, intOf, Zahl.mul]
  | div h0 h1 a b iha ihb =>
    intro ρ v h
    obtain ⟨x, y, hx, hy, rfl⟩ := lift2_some h
    have := iha ρ x hx; have := ihb ρ y hy
    simp_all [eval, intOf, Zahl.div]
  | rem h0 h1 a b iha ihb =>
    intro ρ v h
    obtain ⟨x, y, hx, hy, rfl⟩ := lift2_some h
    have := iha ρ x hx; have := ihb ρ y hy
    simp_all [eval, intOf, Zahl.rem]
  | sdiv hb a b iha ihb =>
    intro ρ v h
    obtain ⟨x, y, hx, hy, rfl⟩ := lift2_some h
    have := iha ρ x hx; have := ihb ρ y hy
    simp_all [eval, intOf, Zahl.sdiv]
  | srem hb a b iha ihb =>
    intro ρ v h
    obtain ⟨x, y, hx, hy, rfl⟩ := lift2_some h
    have := iha ρ x hx; have := ihb ρ y hy
    simp_all [eval, intOf, Zahl.srem]
  | band h0 h0' a b iha ihb =>
    intro ρ v h
    obtain ⟨x, y, hx, hy, rfl⟩ := lift2_some h
    have := iha ρ x hx; have := ihb ρ y hy
    simp_all [eval, intOf, Zahl.band]
  | bor w h0 h0' hw1 hw2 a b iha ihb =>
    intro ρ v h
    obtain ⟨x, y, hx, hy, rfl⟩ := lift2_some h
    have := iha ρ x hx; have := ihb ρ y hy
    simp_all [eval, intOf, Zahl.bor]
  | bxor w h0 h0' hw1 hw2 a b iha ihb =>
    intro ρ v h
    obtain ⟨x, y, hx, hy, rfl⟩ := lift2_some h
    have := iha ρ x hx; have := ihb ρ y hy
    simp_all [eval, intOf, Zahl.bxor]
  | shl w hw1 hw2 h0 h0' a b iha ihb =>
    intro ρ v h
    obtain ⟨x, y, hx, hy, rfl⟩ := lift2_some h
    have := iha ρ x hx; have := ihb ρ y hy
    simp_all [eval, intOf, Zahl.shl]
  | shr w hw1 hw2 h0 h0' a b iha ihb =>
    intro ρ v h
    obtain ⟨x, y, hx, hy, rfl⟩ := lift2_some h
    have := iha ρ x hx; have := ihb ρ y hy
    simp_all [eval, intOf, Zahl.shr]
  | neg a iha =>
    intro ρ v h
    cases hx : constInt? a with
    | none => simp [constInt?, hx] at h
    | some x =>
      simp [constInt?, hx] at h; subst h
      have := iha ρ x hx
      simp_all [eval, intOf, Zahl.neg]
  | keine => trivial
  | zahl e ih => trivial
  | _ => intro ρ v h; simp [constInt?] at h

/-- A constant expression reads nothing: its `orte` (the read events the
    semantics logs) are empty. This is what makes folding EXACT on the
    trace, not only on the value. -/
theorem constInt?_orte {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (v : Int) (h : constInt? e = some v) : e.orte = [] := by
  revert v h
  induction e using Expr.rec (motive_2 := fun _ _ _ _ => True) with
  | lit n => intro v h; rfl
  | weiter h1 h2 e ih => intro v h; exact ih v h
  | neg a iha =>
    intro v h
    cases hx : constInt? a with
    | none => simp [constInt?, hx] at h
    | some x => exact iha x hx
  | keine => trivial
  | zahl e ih => trivial
  | _ =>
    first
    | (intro v h; simp [constInt?] at h; done)
    | (intro v h
       obtain ⟨x, y, hx, hy, _⟩ := lift2_some h
       simp_all [Expr.orte])

/-- The truth value a value carries, at the boolean type only. -/
def boolOf : (τ : Ty) → Wert D τ → Option Bool
  | .bool, v => some v
  | _, _ => none

/-! ## 3. Range entailment (rules S1/S3 and B1/B3, OPTIMIZER.md §§3.2, 3.5)

    The fact source for deciding a comparison is the static range in the
    TYPE of each operand (`Ty.int lo hi`), narrowed to a point when the
    operand is constant. A source value outside its type does not exist
    (`Typen.lean` §2), so this fact holds at every program point of THIS
    expression -- it is attached to the expression itself, hence there is
    no stale-SSA-version hazard (§4.2): a later version of a variable is a
    different expression with its own type. No contract, invariant or
    profile is consulted (§4.5: no compiler-guessed `ensures`). -/

/-- The interval a value of `e` is known to lie in: the point for a
    constant, the type range otherwise. -/
def bounds {Γ : Ctx} {Λ : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi)) : Int × Int :=
  match constInt? e with
  | some x => (x, x)
  | none => (lo, hi)

/-- Every value of `e` lies in `bounds e`. -/
theorem bounds_sound {Γ : Ctx} {Λ : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (σ₀ σ : World D) (ρ : Env D Γ) :
    (bounds e).1 ≤ (eval σ₀ e σ ρ).n ∧ (eval σ₀ e σ ρ).n ≤ (bounds e).2 := by
  unfold bounds
  cases hx : constInt? e with
  | none => exact ⟨(eval σ₀ e σ ρ).lo_le, (eval σ₀ e σ ρ).le_hi⟩
  | some x =>
    have := constInt?_sound e σ₀ σ ρ x hx
    simp [intOf] at this
    simp [this]

/-- Decide `x ≤ y` from intervals, or answer `none`. -/
def decideLe (pa pb : Int × Int) : Option Bool :=
  if pa.2 ≤ pb.1 then some true else if pb.2 < pa.1 then some false else none

/-- Decide `x < y` from intervals, or answer `none`. -/
def decideLt (pa pb : Int × Int) : Option Bool :=
  if pa.2 < pb.1 then some true else if pb.2 ≤ pa.1 then some false else none

/-- Decide `x = y` from intervals, or answer `none`. -/
def decideEq (pa pb : Int × Int) : Option Bool :=
  if pa.1 = pa.2 ∧ pb.1 = pb.2 ∧ pa.1 = pb.1 then some true
  else if pa.2 < pb.1 ∨ pb.2 < pa.1 then some false else none

/-- A decided `≤` is the real `≤`. -/
theorem decideLe_sound {pa pb : Int × Int} {x y : Int} {b : Bool}
    (hx : pa.1 ≤ x ∧ x ≤ pa.2) (hy : pb.1 ≤ y ∧ y ≤ pb.2) (h : decideLe pa pb = some b) :
    decide (x ≤ y) = b := by
  unfold decideLe at h
  split at h
  · cases h; simp; omega
  · split at h
    · cases h; simp; omega
    · cases h

/-- A decided `<` is the real `<`. -/
theorem decideLt_sound {pa pb : Int × Int} {x y : Int} {b : Bool}
    (hx : pa.1 ≤ x ∧ x ≤ pa.2) (hy : pb.1 ≤ y ∧ y ≤ pb.2) (h : decideLt pa pb = some b) :
    decide (x < y) = b := by
  unfold decideLt at h
  split at h
  · cases h; simp; omega
  · split at h
    · cases h; simp; omega
    · cases h

/-- A decided `=` is the real `=`. -/
theorem decideEq_sound {pa pb : Int × Int} {x y : Int} {b : Bool}
    (hx : pa.1 ≤ x ∧ x ≤ pa.2) (hy : pb.1 ≤ y ∧ y ≤ pb.2) (h : decideEq pa pb = some b) :
    decide (x = y) = b := by
  unfold decideEq at h
  split at h
  · cases h; simp; omega
  · split at h
    · cases h; simp; omega
    · cases h

/-- Reading back at `.bool` is the value itself. -/
theorem boolOf_bool {v : Wert D .bool} {c : Bool} (h : boolOf .bool v = some c) :
    (v : Bool) = c :=
  Option.some.inj h

/-- Three-valued conjunction: a known `false` decides. -/
def andOpt : Option Bool → Option Bool → Option Bool
  | some false, _ => some false
  | _, some false => some false
  | some true, some true => some true
  | _, _ => none

/-- Three-valued disjunction: a known `true` decides. -/
def orOpt : Option Bool → Option Bool → Option Bool
  | some true, _ => some true
  | _, some true => some true
  | some false, some false => some false
  | _, _ => none

/-- The Lean-side decider for boolean source conditions: literals,
    integer comparisons by range entailment, and `and`/`or`/`not`. Unlike
    `InvariantenOpt.isWahrAll` it is EXACT where it answers, so negation
    is sound here (an answer is a proved value, not a one-sided check).
    Float comparisons answer `none`: no FP rule exists (§3.9, F2–F4). -/
def constBool? {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} : Expr D Γ Λ τ → Option Bool
  | .wahr => some true
  | .falsch => some false
  | .lt a b => decideLt (bounds a) (bounds b)
  | .le a b => decideLe (bounds a) (bounds b)
  | .eq a b => decideEq (bounds a) (bounds b)
  | .und a b => andOpt (constBool? a) (constBool? b)
  | .oder a b => orOpt (constBool? a) (constBool? b)
  | .nicht a => (constBool? a).map (! ·)
  | _ => none

/-- `andOpt` agrees with `&&` on every value consistent with its inputs. -/
theorem andOpt_sound {oa ob : Option Bool} {x y r : Bool}
    (ha : ∀ c, oa = some c → x = c) (hb : ∀ c, ob = some c → y = c)
    (h : andOpt oa ob = some r) : (x && y) = r := by
  cases oa with
  | none => cases ob with
    | none => simp [andOpt] at h
    | some c => cases c <;> simp_all [andOpt]
  | some c => cases ob with
    | none => cases c <;> simp_all [andOpt]
    | some d => cases c <;> cases d <;> simp_all [andOpt]

/-- `orOpt` agrees with `||` on every value consistent with its inputs. -/
theorem orOpt_sound {oa ob : Option Bool} {x y r : Bool}
    (ha : ∀ c, oa = some c → x = c) (hb : ∀ c, ob = some c → y = c)
    (h : orOpt oa ob = some r) : (x || y) = r := by
  cases oa with
  | none => cases ob with
    | none => simp [orOpt] at h
    | some c => cases c <;> simp_all [orOpt]
  | some c => cases ob with
    | none => cases c <;> simp_all [orOpt]
    | some d => cases c <;> cases d <;> simp_all [orOpt]

/-- **Soundness of the condition decider** over the real `eval`. -/
theorem constBool?_sound {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (σ₀ σ : World D) (ρ : Env D Γ) (b : Bool) (h : constBool? e = some b) :
    boolOf τ (eval σ₀ e σ ρ) = some b := by
  revert ρ b h
  induction e using Expr.rec (motive_2 := fun _ _ _ _ => True) with
  | wahr => intro ρ b h; simp_all [constBool?, eval, boolOf]
  | falsch => intro ρ b h; simp_all [constBool?, eval, boolOf]
  | lt a b' iha ihb =>
    intro ρ r h
    have := decideLt_sound (bounds_sound a σ₀ σ ρ) (bounds_sound b' σ₀ σ ρ) h
    simp [eval, boolOf, this]
  | le a b' iha ihb =>
    intro ρ r h
    have := decideLe_sound (bounds_sound a σ₀ σ ρ) (bounds_sound b' σ₀ σ ρ) h
    simp [eval, boolOf, this]
  | eq a b' iha ihb =>
    intro ρ r h
    have := decideEq_sound (bounds_sound a σ₀ σ ρ) (bounds_sound b' σ₀ σ ρ) h
    simp [eval, boolOf, this]
  | und a b' iha ihb =>
    intro ρ r h
    have := andOpt_sound (x := eval σ₀ a σ ρ) (y := eval σ₀ b' σ ρ)
      (fun c hc => boolOf_bool (iha ρ c hc))
      (fun c hc => boolOf_bool (ihb ρ c hc)) h
    simp [eval, boolOf, wahr?, this]
  | oder a b' iha ihb =>
    intro ρ r h
    have := orOpt_sound (x := eval σ₀ a σ ρ) (y := eval σ₀ b' σ ρ)
      (fun c hc => boolOf_bool (iha ρ c hc))
      (fun c hc => boolOf_bool (ihb ρ c hc)) h
    simp [eval, boolOf, wahr?, this]
  | nicht a iha =>
    intro ρ r h
    cases hx : constBool? a with
    | none => simp [constBool?, hx] at h
    | some x =>
      have h2 : (!x) = r := by simpa [constBool?, hx] using h
      have h3 := boolOf_bool (iha ρ x hx)
      subst h2
      simp [eval, boolOf, wahr?, h3]
  | keine => trivial
  | zahl e ih => trivial
  | _ => intro ρ b h; simp [constBool?] at h

/-! ## 4. Expression rewrites, their certificate and their validator

    `ExprEquiv e e'`: `e'` reads exactly the locations `e` reads (so
    `World.lese` logs the same events, the observation the race-freedom
    legs are stated over) and evaluates to the same value in every world
    and environment. It is the refinement every expression rule must
    establish; equality of values ALONE would let a rule drop a read. -/

/-- Same read events, same value, everywhere. -/
structure ExprEquiv {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e e' : Expr D Γ Λ τ) : Prop where
  orte : e'.orte = e.orte
  wert : ∀ (σ₀ σ : World D) (ρ : Env D Γ), eval σ₀ e' σ ρ = eval σ₀ e σ ρ

/-- Reflexivity: the conservative route (keep the expression). -/
theorem ExprEquiv.refl {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) : ExprEquiv e e :=
  ⟨rfl, fun _ _ _ => rfl⟩

/-- Composition: rewrites chain. -/
theorem ExprEquiv.trans {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} {e₁ e₂ e₃ : Expr D Γ Λ τ}
    (h₁ : ExprEquiv e₁ e₂) (h₂ : ExprEquiv e₂ e₃) : ExprEquiv e₁ e₃ :=
  ⟨h₂.orte.trans h₁.orte, fun σ₀ σ ρ => (h₂.wert σ₀ σ ρ).trans (h₁.wert σ₀ σ ρ)⟩

/-- Two numbers of one range are equal when their values are. -/
theorem Zahl.ext' {lo hi : Int} {a b : Zahl lo hi} (h : a.n = b.n) : a = b := by
  cases a; cases b; simp at h; subst h; rfl

/-- Rule **C1** (integer constant folding): a constant expression becomes
    its literal, widened back to the SAME type, so the result is a
    drop-in replacement (no range check downstream is lost: the type does
    not move). A literal outside the type cannot occur (soundness), and
    the validator refuses rather than trusting that. -/
def foldInt {Γ : Ctx} {Λ : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi)) :
    Option (Expr D Γ Λ (.int lo hi)) :=
  match constInt? e with
  | some v => if h : lo ≤ v ∧ v ≤ hi then some (.weiter h.1 h.2 (.lit v)) else none
  | none => none

/-- **C1 is sound**: exact on value and read events. -/
theorem foldInt_sound {Γ : Ctx} {Λ : List (Res D)} {lo hi : Int} (e e' : Expr D Γ Λ (.int lo hi))
    (h : foldInt e = some e') : ExprEquiv e e' := by
  unfold foldInt at h
  cases hv : constInt? e with
  | none => simp [hv] at h
  | some v =>
    simp only [hv] at h
    split at h
    · cases h
      refine ⟨?_, ?_⟩
      · rw [constInt?_orte e v hv]; rfl
      · intro σ₀ σ ρ
        have := constInt?_sound e σ₀ σ ρ v hv
        simp [intOf] at this
        exact Zahl.ext' (by simp [eval, Zahl.weiter, this])
    · cases h

/-- Rule **C1/S3** for conditions: a decided condition becomes `true` /
    `false` -- but ONLY when it reads nothing. A range-decided comparison
    over a table slot is still decided, yet folding it would delete the
    read event; the validator refuses that (poison probe in the witness
    file). -/
def foldBool {Γ : Ctx} {Λ : List (Res D)} (e : Expr D Γ Λ .bool) : Option (Expr D Γ Λ .bool) :=
  if e.orte.isEmpty then
    match constBool? e with
    | some true => some .wahr
    | some false => some .falsch
    | none => none
  else none

/-- **The condition fold is sound**: exact on value and read events. -/
theorem foldBool_sound {Γ : Ctx} {Λ : List (Res D)} (e e' : Expr D Γ Λ .bool)
    (h : foldBool e = some e') : ExprEquiv e e' := by
  unfold foldBool at h
  split at h
  · rename_i ho
    have ho' : e.orte = [] := List.isEmpty_iff.mp ho
    cases hb : constBool? e with
    | none => simp [hb] at h
    | some b =>
      have hs := fun σ₀ σ ρ => boolOf_bool (constBool?_sound e σ₀ σ ρ b hb)
      cases b <;> simp [hb] at h <;> subst h <;>
        exact ⟨by rw [ho']; rfl, fun σ₀ σ ρ => by rw [hs σ₀ σ ρ]; rfl⟩
  · cases h

/-- Expression certificates. A certificate names the rule; it carries no
    value, no range and no proof the validator would have to trust. -/
inductive ExprCert where
  | foldInt
  | foldBool
  deriving DecidableEq, Repr

/-- The expression validator: recomputes the rule's facts and either
    returns the checked output or refuses. Rules apply only at their type
    (an integer fold at a boolean type is refused, not coerced). -/
def applyExpr {Γ : Ctx} {Λ : List (Res D)} : ExprCert → (τ : Ty) → Expr D Γ Λ τ → Option (Expr D Γ Λ τ)
  | .foldInt, .int _ _, e => foldInt e
  | .foldBool, .bool, e => foldBool e
  | _, _, _ => none

/-- **Generic soundness of the expression validator.** -/
theorem applyExpr_sound {Γ : Ctx} {Λ : List (Res D)} (c : ExprCert) (τ : Ty) (e e' : Expr D Γ Λ τ)
    (h : applyExpr c τ e = some e') : ExprEquiv e e' := by
  cases c <;> cases τ <;> simp [applyExpr] at h
  · exact foldInt_sound e e' h
  · exact foldBool_sound e e' h

/-! ## 5. Strength reduction to target words (rules R1–R4, OPTIMIZER.md §3.6)

    Instruction selection for `a * 2^k`, `a / 2^k`, `a % 2^k`: the source
    expression keeps its form, and the validator certifies which canonical
    target WORD operation (`shlW`/`shrW`/`&&& maskW`, the accepted helpers
    of `StaerkeReduktion.lean`) computes its value from the encoded left
    operand. Side conditions are recomputed from the source text: the
    divisor/multiplier is a constant `2^k` (`constInt?`), the left operand
    is nonnegative by its TYPE, and its range fits 64 bits -- for `mul`
    including the product, so no wrap is hidden. `sdiv`/`srem` are REFUSED
    (truncation is not a shift for negative numerators:
    `StaerkeReduktion.sdiv_kein_shift`). -/

/-- The selected target word operation. -/
inductive TargetOp where
  | shl (k : Nat)
  | shr (k : Nat)
  | mask (k : Nat)
  deriving DecidableEq, Repr

/-- Its meaning: the accepted canonical word helpers. -/
def TargetOp.run : TargetOp → Wort → Wort
  | .shl k, x => shlW x k
  | .shr k, x => shrW x k
  | .mask k, x => x &&& maskW k

/-- A nonnegative source number as a 64-bit word: the accepted
    representation interface `SourceMemory.zahlWort` (lane 570), read at
    the point range of the number itself -- reused, not redefined. -/
def encodeNat (x : Int) : Wort := zahlWort (⟨x, Int.le_refl x, Int.le_refl x⟩ : Zahl x x)

/-- The encoding of a source value is exactly its `zahlWort`. -/
theorem encodeNat_zahlWort {lo hi : Int} (v : Zahl lo hi) : encodeNat v.n = zahlWort v := rfl

/-- The encoding is faithful below `2^64`. -/
theorem encodeNat_toNat {x : Int} (h0 : 0 ≤ x) (h : x < 2 ^ 64) :
    ((encodeNat x).toNat : Int) = x := by
  have hn : x.toNat < 2 ^ 64 := by omega
  simp [encodeNat, zahlWort, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  omega

/-- The shift word on an encoded nonnegative number is the product, as
    long as the product fits 64 bits (no hidden wrap). -/
theorem shlW_encodeNat {x : Int} (k : Nat) (h0 : 0 ≤ x) (h : x * 2 ^ k < 2 ^ 64) :
    ((shlW (encodeNat x) k).toNat : Int) = x * 2 ^ k := by
  have hpos : (0 : Int) < 2 ^ k := by
    have : (0 : Nat) < 2 ^ k := Nat.two_pow_pos k
    exact_mod_cast this
  have hxlt : x < 2 ^ 64 := by
    have h1 : (1 : Int) ≤ 2 ^ k := by omega
    have := Int.mul_le_mul_of_nonneg_left h1 h0
    simp at this
    omega
  have henc := encodeNat_toNat h0 hxlt
  have hnat : (encodeNat x).toNat * 2 ^ k < 2 ^ 64 := by
    have : (((encodeNat x).toNat * 2 ^ k : Nat) : Int) < 2 ^ 64 := by
      push_cast; rw [henc]; exact h
    exact_mod_cast this
  rw [shlW_keinUeberlauf _ _ hnat]
  push_cast
  rw [henc]

/-- R1 side conditions: `b` is the constant `2^k`, `a` is nonnegative by
    type, and the largest product fits 64 bits. -/
def strengthMul {Γ : Ctx} {Λ : List (Res D)} {l1 h1 l2 h2 : Int} (k : Nat)
    (_a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) : Option TargetOp :=
  if constInt? b = some (2 ^ k) ∧ 0 ≤ l1 ∧ h1 * 2 ^ k < 2 ^ 64 then some (.shl k) else none

/-- R1, commuted (`2^k * b`): `a` is the constant `2^k`, `b` is NOT a
    constant (so the shifted operand is unambiguous: a constant `b` is
    the left-constant case of `strengthMul`, or a fold), `b` is
    nonnegative by type and the largest product fits 64 bits. -/
def strengthMulComm {Γ : Ctx} {Λ : List (Res D)} {l1 h1 l2 h2 : Int} (k : Nat)
    (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) : Option TargetOp :=
  if constInt? a = some (2 ^ k) ∧ constInt? b = none ∧ 0 ≤ l2 ∧ h2 * 2 ^ k < 2 ^ 64 then
    some (.shl k)
  else none

/-- R2 side conditions: `b` is the constant `2^k`, `a` is nonnegative and
    fits 64 bits (the divisor is never zero: `2^k ≥ 1`). -/
def strengthDiv {Γ : Ctx} {Λ : List (Res D)} {l1 h1 l2 h2 : Int} (k : Nat)
    (_a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) : Option TargetOp :=
  if constInt? b = some (2 ^ k) ∧ 0 ≤ l1 ∧ h1 < 2 ^ 64 then some (.shr k) else none

/-- R3 side conditions: as R2, plus `k ≤ 64` for the mask word. -/
def strengthRem {Γ : Ctx} {Λ : List (Res D)} {l1 h1 l2 h2 : Int} (k : Nat)
    (_a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) : Option TargetOp :=
  if constInt? b = some (2 ^ k) ∧ 0 ≤ l1 ∧ h1 < 2 ^ 64 ∧ k ≤ 64 then some (.mask k) else none

/-- The strength validator. Everything that is not unsigned `mul`/`div`/`rem`
    -- in particular `sdiv`/`srem` (R4) -- is refused. Division and
    remainder are never commuted: only the divisor may be the constant. -/
def checkStrength {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (k : Nat) : Expr D Γ Λ τ → Option TargetOp
  | .mul a b =>
    match strengthMul k a b with
    | some op => some op
    | none => strengthMulComm k a b
  | .div _ _ a b => strengthDiv k a b
  | .rem _ _ a b => strengthRem k a b
  | _ => none

/-- The operand the selected word operation acts on, read through the
    REAL `eval`: the left operand, except for a product whose right
    operand is not a constant (the commuted `2^k * b`). -/
def shiftedOperand {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (σ₀ : World D) :
    Expr D Γ Λ τ → World D → Env D Γ → Option Int
  | .mul a b, σ, ρ =>
    match constInt? b with
    | some _ => some (eval σ₀ a σ ρ).n
    | none => some (eval σ₀ b σ ρ).n
  | .div _ _ a _, σ, ρ => some (eval σ₀ a σ ρ).n
  | .rem _ _ a _, σ, ρ => some (eval σ₀ a σ ρ).n
  | _, _, _ => none

/-- **Generic soundness of strength reduction**: the selected word
    operation on the encoded operand reads back as exactly the value the
    source expression evaluates to. -/
theorem checkStrength_sound {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (k : Nat) (e : Expr D Γ Λ τ)
    (op : TargetOp) (h : checkStrength k e = some op) (σ₀ σ : World D) (ρ : Env D Γ) :
    ∃ x, shiftedOperand σ₀ e σ ρ = some x ∧ 0 ≤ x ∧ x < 2 ^ 64 ∧
      intOf τ (eval σ₀ e σ ρ) = some ((op.run (encodeNat x)).toNat : Int) := by
  have hpos : (0 : Int) < 2 ^ k := by
    have : (0 : Nat) < 2 ^ k := Nat.two_pow_pos k
    exact_mod_cast this
  cases e with
  | mul a b =>
    simp only [checkStrength] at h
    cases hm : strengthMul k a b with
    | some op' =>
      rw [hm] at h
      cases h
      simp only [strengthMul] at hm
      split at hm
      · rename_i hc
        cases hm
        obtain ⟨hb, hl, hh⟩ := hc
        have hbv := constInt?_sound b σ₀ σ ρ _ hb
        simp only [intOf, Option.some.injEq] at hbv
        have ha1 := (eval σ₀ a σ ρ).lo_le
        have ha2 := (eval σ₀ a σ ρ).le_hi
        have hx64 : (eval σ₀ a σ ρ).n * 2 ^ k < 2 ^ 64 :=
          Int.lt_of_le_of_lt (Int.mul_le_mul_of_nonneg_right ha2 (Int.le_of_lt hpos)) hh
        have hxlt : (eval σ₀ a σ ρ).n < 2 ^ 64 := by
          have h1 : (1 : Int) ≤ 2 ^ k := by omega
          have := Int.mul_le_mul_of_nonneg_left h1 (by omega : (0 : Int) ≤ (eval σ₀ a σ ρ).n)
          simp at this
          omega
        refine ⟨(eval σ₀ a σ ρ).n, by simp [shiftedOperand, hb], by omega, hxlt, ?_⟩
        simp only [intOf, eval, Zahl.mul, TargetOp.run, Option.some.injEq]
        rw [shlW_encodeNat k (by omega) hx64, hbv]
      · cases hm
    | none =>
      rw [hm] at h
      simp only [strengthMulComm] at h
      split at h
      · rename_i hc
        cases h
        obtain ⟨ha, hbn, hl, hh⟩ := hc
        have hav := constInt?_sound a σ₀ σ ρ _ ha
        simp only [intOf, Option.some.injEq] at hav
        have hb1 := (eval σ₀ b σ ρ).lo_le
        have hb2 := (eval σ₀ b σ ρ).le_hi
        have hx64 : (eval σ₀ b σ ρ).n * 2 ^ k < 2 ^ 64 :=
          Int.lt_of_le_of_lt (Int.mul_le_mul_of_nonneg_right hb2 (Int.le_of_lt hpos)) hh
        have hxlt : (eval σ₀ b σ ρ).n < 2 ^ 64 := by
          have h1 : (1 : Int) ≤ 2 ^ k := by omega
          have := Int.mul_le_mul_of_nonneg_left h1 (by omega : (0 : Int) ≤ (eval σ₀ b σ ρ).n)
          simp at this
          omega
        refine ⟨(eval σ₀ b σ ρ).n, by simp [shiftedOperand, hbn], by omega, hxlt, ?_⟩
        simp only [intOf, eval, Zahl.mul, TargetOp.run, Option.some.injEq]
        rw [shlW_encodeNat k (by omega) hx64, hav, Int.mul_comm]
      · cases h
  | div h0 h1' a b =>
    simp only [checkStrength, strengthDiv] at h
    split at h
    · rename_i hc
      cases h
      obtain ⟨hb, hl, hh⟩ := hc
      have hbv := constInt?_sound b σ₀ σ ρ _ hb
      simp only [intOf, Option.some.injEq] at hbv
      have ha1 := (eval σ₀ a σ ρ).lo_le
      have ha2 := (eval σ₀ a σ ρ).le_hi
      have hxlt : (eval σ₀ a σ ρ).n < 2 ^ 64 := by omega
      refine ⟨(eval σ₀ a σ ρ).n, rfl, by omega, hxlt, ?_⟩
      have henc := encodeNat_toNat (x := (eval σ₀ a σ ρ).n) (by omega) hxlt
      simp only [intOf, eval, Zahl.div, TargetOp.run, Option.some.injEq]
      rw [shrW_toNat]
      push_cast
      rw [henc, hbv, Int.tdiv_eq_ediv_of_nonneg (by omega)]
    · cases h
  | rem h0 h1' a b =>
    simp only [checkStrength, strengthRem] at h
    split at h
    · rename_i hc
      cases h
      obtain ⟨hb, hl, hh, hk⟩ := hc
      have hbv := constInt?_sound b σ₀ σ ρ _ hb
      simp only [intOf, Option.some.injEq] at hbv
      have ha1 := (eval σ₀ a σ ρ).lo_le
      have ha2 := (eval σ₀ a σ ρ).le_hi
      have hxlt : (eval σ₀ a σ ρ).n < 2 ^ 64 := by omega
      refine ⟨(eval σ₀ a σ ρ).n, rfl, by omega, hxlt, ?_⟩
      have henc := encodeNat_toNat (x := (eval σ₀ a σ ρ).n) (by omega) hxlt
      simp only [intOf, eval, Zahl.rem, TargetOp.run, Option.some.injEq]
      rw [maskW_and _ _ hk]
      push_cast
      rw [henc, hbv, Int.tmod_eq_emod_of_nonneg (by omega)]
    · cases h
  | _ => simp [checkStrength] at h

/-- The selected word, stated on the accepted representation: for a
    source operand value `v`, the word operation runs on `zahlWort v`. -/
theorem checkStrength_sound_zahlWort {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (k : Nat)
    (e : Expr D Γ Λ τ) (op : TargetOp) (h : checkStrength k e = some op)
    (σ₀ σ : World D) (ρ : Env D Γ) {lo hi : Int} (v : Zahl lo hi)
    (hv : shiftedOperand σ₀ e σ ρ = some v.n) :
    intOf τ (eval σ₀ e σ ρ) = some ((op.run (zahlWort v)).toNat : Int) := by
  obtain ⟨x, hx, _, _, hval⟩ := checkStrength_sound k e op h σ₀ σ ρ
  rw [hv] at hx
  cases hx
  rw [hval, encodeNat_zahlWort]

/-- R4: signed division is never strength-reduced. -/
theorem checkStrength_sdiv {Γ : Ctx} {Λ : List (Res D)} {l1 h1 l2 h2 : Int} (k : Nat)
    (hb : 1 ≤ l2 ∨ h2 ≤ -1) (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    checkStrength k (.sdiv hb a b) = none := rfl

/-- R4: signed remainder is never strength-reduced. -/
theorem checkStrength_srem {Γ : Ctx} {Λ : List (Res D)} {l1 h1 l2 h2 : Int} (k : Nat)
    (hb : 1 ≤ l2 ∨ h2 ≤ -1) (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    checkStrength k (.srem hb a b) = none := rfl

/-! ## 6. Statements and blocks: certificates, validators, soundness

    Rewrites inside statements and blocks, over the real `execStmt` /
    `execBlock`. The certificate is a path to a position plus a rule; the
    validator descends along the path, applies the rule's own check, and
    rebuilds the block. Soundness is ONE mutual theorem by recursion on the
    certificate. -/

section Statements
variable {V : Vertrag D}

/-- Reading no location logs no event. -/
theorem lese_nil' (σ : World D) (Λ : List (Res D)) : σ.lese Λ [] = σ := rfl

/-- Statement refinement: identical outcome (`Ausgang`: world, trace,
    environment, returns, reasons, logic and hardware stops) under EVERY
    oracle, loop budget and call handler. -/
def StmtEquiv {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (s s' : Stmt D V l Γ Λ Λ') : Prop :=
  ∀ (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ), execStmt O passes R s' σ ρ = execStmt O passes R s σ ρ

/-- Block refinement, as for statements. Equality of the whole `Ausgang`
    of single-thread `execBlock` carries values, faults, budget refusals
    (`logik`), hardware stops and the read/write event trace through a rule
    (OPTIMIZER.md §1.2 items 1, 2 and the single-thread part of 9-10). It
    does NOT carry concurrent observations (item 3): machine G steps a
    `pruefung`/`narrow` as a step of its own, so a removed check removes a
    G step, an interleaving point and its time (`ZeitAb`). The G/GX
    transfer is OPEN. -/
def BlockEquiv {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b b' : Block D V l Γ Λ Λ') : Prop :=
  ∀ (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ), execBlock O passes R b' σ ρ = execBlock O passes R b σ ρ

/-- Reflexivity: the conservative route (keep the block). -/
theorem BlockEquiv.refl {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') :
    BlockEquiv b b := fun _ _ _ _ _ => rfl

/-- Composition: passes chain. -/
theorem BlockEquiv.trans {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {b₁ b₂ b₃ : Block D V l Γ Λ Λ'}
    (h₁ : BlockEquiv b₁ b₂) (h₂ : BlockEquiv b₂ b₃) : BlockEquiv b₁ b₃ :=
  fun O p R σ ρ => (h₂ O p R σ ρ).trans (h₁ O p R σ ρ)

mutual
/-- Statement certificates: rewrite an expression in place, or descend into
    a nested block. -/
inductive StmtCert where
  | iteCond (c : ExprCert)
  | iteThen (c : BlockCert)
  | iteElse (c : BlockCert)
  | lockBody (c : BlockCert)
  | assignSlotIndex (c : ExprCert)
  | assignSlotValue (c : ExprCert)
  | assignVarValue (c : ExprCert)
  | assignGlobValue (c : ExprCert)
  | breakingBody (c : BlockCert)
  | optSomeBranch (c : BlockCert)
  | optNoneBranch (c : BlockCert)
  | traverseBody (c : BlockCert)
  | retryCond (c : ExprCert)
  | retryBody (c : BlockCert)
  | retryOverflow (c : BlockCert)
  | foreverBody (c : BlockCert)
/-- Block certificates: a block rule at this position, an expression
    rewrite in place, or a path step (`head` into the first statement,
    `rest` into the continuation). -/
inductive BlockCert where
  | dropCheck
  | narrowEntailed
  | checkCond (c : ExprCert)
  | bindValue (c : ExprCert)
  | narrowValue (c : ExprCert)
  | head (c : StmtCert)
  | rest (c : BlockCert)
end

/-- Rule **B1/B3/S1** (redundant check): the condition reads nothing and is
    decided `true`. -/
def dropCheckOk {Γ : Ctx} {Λ : List (Res D)} (c : Expr D Γ Λ .bool) : Bool :=
  c.orte.isEmpty && constBool? c == some true

/-- Rule **B2** (redundant `narrow`): the operand's type range already lies
    inside the target range, so the `narrow` is a plain widening `bind`. -/
def narrowEntailed {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {lo hi : Int}
    (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int)
    (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ') : Option (Block D V l Γ Λ Λ') :=
  if h : lo' ≤ lo ∧ hi ≤ hi' then some (.bind (.weiter h.1 h.2 e) rest) else none

mutual
/-- The statement validator. -/
def applyStmt {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    StmtCert → Stmt D V l Γ Λ Λ' → Option (Stmt D V l Γ Λ Λ')
  | .iteCond c, .ite e t f => (applyExpr c .bool e).map (fun e' => .ite e' t f)
  | .iteThen c, .ite e t f => (applyBlock c t).map (fun t' => .ite e t' f)
  | .iteElse c, .ite e t f => (applyBlock c f).map (fun f' => .ite e t f')
  | .lockBody c, .locks L hr body => (applyBlock c body).map (fun b' => .locks L hr b')
  | .assignSlotIndex c, .assignSlot t f i e h1 h2 =>
      (applyExpr c _ i).map (fun i' => .assignSlot t f i' e h1 h2)
  | .assignSlotValue c, .assignSlot t f i e h1 h2 =>
      (applyExpr c _ e).map (fun e' => .assignSlot t f i e' h1 h2)
  | .assignVarValue c, .assignVar x e => (applyExpr c _ e).map (fun e' => .assignVar x e')
  | .assignGlobValue c, .assignGlob g e h1 h2 =>
      (applyExpr c _ e).map (fun e' => .assignGlob g e' h1 h2)
  | .breakingBody c, .breaking i body => (applyBlock c body).map (fun b' => .breaking i b')
  | .optSomeBranch c, .onOption o p a => (applyBlock c p).map (fun p' => .onOption o p' a)
  | .optNoneBranch c, .onOption o p a => (applyBlock c a).map (fun a' => .onOption o p a')
  | .traverseBody c, .traverse t inv body => (applyBlock c body).map (fun b' => .traverse t inv b')
  | .retryCond c, .retry n bis body ue => (applyExpr c .bool bis).map (fun b' => .retry n b' body ue)
  | .retryBody c, .retry n bis body ue => (applyBlock c body).map (fun b' => .retry n bis b' ue)
  | .retryOverflow c, .retry n bis body ue => (applyBlock c ue).map (fun u' => .retry n bis body u')
  | .foreverBody c, .forever a inv body => (applyBlock c body).map (fun b' => .forever a inv b')
  | _, _ => none

/-- The block validator. A check that is decided `false` is NOT removed:
    it always fails, and its `else` is the behaviour (refused here). -/
def applyBlock {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    BlockCert → Block D V l Γ Λ Λ' → Option (Block D V l Γ Λ Λ')
  | .dropCheck, .pruefung c _ rest => if dropCheckOk c then some rest else none
  | .narrowEntailed, .narrow e lo' hi' _ rest => narrowEntailed e lo' hi' rest
  | .checkCond c, .pruefung e sonst rest => (applyExpr c .bool e).map (fun e' => .pruefung e' sonst rest)
  | .bindValue c, .bind e rest => (applyExpr c _ e).map (fun e' => .bind e' rest)
  | .narrowValue c, .narrow e lo' hi' sonst rest =>
      (applyExpr c _ e).map (fun e' => .narrow e' lo' hi' sonst rest)
  | .head c, .cons s rest => (applyStmt c s).map (fun s' => .cons s' rest)
  | .rest c, .cons s rest => (applyBlock c rest).map (fun r' => .cons s r')
  | .rest c, .bind e rest => (applyBlock c rest).map (fun r' => .bind e r')
  | .rest c, .bindCall f args he hp hr rest =>
      (applyBlock c rest).map (fun r' => .bindCall f args he hp hr r')
  | .rest c, .pruefung e sonst rest => (applyBlock c rest).map (fun r' => .pruefung e sonst r')
  | .rest c, .narrow e lo' hi' sonst rest =>
      (applyBlock c rest).map (fun r' => .narrow e lo' hi' sonst r')
  | _, _ => none
end

/-- **B1/B3/S1 are sound**: removing a decided, read-free check changes no
    outcome. -/
theorem dropCheck_sound {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (h : dropCheckOk c = true) :
    BlockEquiv (.pruefung c sonst rest) rest := by
  intro O passes R σ ρ
  unfold dropCheckOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have ho : c.orte = [] := List.isEmpty_iff.mp h.1
  have hv : (eval σ c σ ρ : Bool) = true := boolOf_bool (constBool?_sound c σ σ ρ true h.2)
  have hv' : wahr? (eval σ c σ ρ) = true := hv
  simp only [execBlock, ho, lese_nil']
  rw [if_pos hv']

/-- **B2 is sound**: an entailed `narrow` and its widening `bind` have the
    same outcome. -/
theorem narrowEntailed_sound {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {lo hi : Int}
    (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ') (b' : Block D V l Γ Λ Λ')
    (h : narrowEntailed e lo' hi' rest = some b') :
    BlockEquiv (.narrow e lo' hi' sonst rest) b' := by
  unfold narrowEntailed at h
  split at h
  · rename_i hr
    cases h
    intro O passes R σ ρ
    have hv := bounds_sound e (σ.lese Λ e.orte) (σ.lese Λ e.orte) ρ
    have hlo := (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).lo_le
    have hhi := (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).le_hi
    have hin : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
        (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi' := ⟨by omega, by omega⟩
    simp only [execBlock, Expr.orte, eval, Zahl.weiter]
    rw [dif_pos hin]
  · cases h

mutual
/-- **Generic soundness of the statement validator.** -/
theorem applyStmt_sound {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (c : StmtCert) → (s s' : Stmt D V l Γ Λ Λ') → applyStmt c s = some s' → StmtEquiv s s'
  | .iteCond c, s, s', h => by
    cases s with
    | ite e t f =>
      simp only [applyStmt, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyExpr_sound c _ e x' hx
      intro O passes R σ ρ
      simp only [execStmt, q.orte, q.wert]
    | _ => simp [applyStmt] at h
  | .iteThen c, s, s', h => by
    cases s with
    | ite e t f =>
      simp only [applyStmt, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyBlock_sound c t x' hx
      intro O passes R σ ρ
      simp only [execStmt, q O passes R]
    | _ => simp [applyStmt] at h
  | .iteElse c, s, s', h => by
    cases s with
    | ite e t f =>
      simp only [applyStmt, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyBlock_sound c f x' hx
      intro O passes R σ ρ
      simp only [execStmt, q O passes R]
    | _ => simp [applyStmt] at h
  | .lockBody c, s, s', h => by
    cases s with
    | locks L hr body =>
      simp only [applyStmt, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyBlock_sound c body x' hx
      intro O passes R σ ρ
      simp only [execStmt, q O passes R]
    | _ => simp [applyStmt] at h
  | .assignSlotIndex c, s, s', h => by
    cases s with
    | assignSlot t f i e hw hL =>
      simp only [applyStmt, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyExpr_sound c _ i x' hx
      intro O passes R σ ρ
      simp only [execStmt, q.orte, q.wert]
    | _ => simp [applyStmt] at h
  | .assignSlotValue c, s, s', h => by
    cases s with
    | assignSlot t f i e hw hL =>
      simp only [applyStmt, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyExpr_sound c _ e x' hx
      intro O passes R σ ρ
      simp only [execStmt, q.orte, q.wert]
    | _ => simp [applyStmt] at h
  | .assignVarValue c, s, s', h => by
    cases s with
    | assignVar x e =>
      simp only [applyStmt, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyExpr_sound c _ e x' hx
      intro O passes R σ ρ
      simp only [execStmt, q.orte, q.wert]
    | _ => simp [applyStmt] at h
  | .assignGlobValue c, s, s', h => by
    cases s with
    | assignGlob g e hw hL =>
      simp only [applyStmt, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyExpr_sound c _ e x' hx
      intro O passes R σ ρ
      simp only [execStmt, q.orte, q.wert]
    | _ => simp [applyStmt] at h
  | .breakingBody c, s, s', h => by
    cases s with
    | breaking i body =>
      simp only [applyStmt, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyBlock_sound c body x' hx
      intro O passes R σ ρ
      simp only [execStmt, q O passes R]
    | _ => simp [applyStmt] at h
  | .optSomeBranch c, s, s', h => by
    cases s with
    | onOption o p a =>
      simp only [applyStmt, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyBlock_sound c p x' hx
      intro O passes R σ ρ
      simp only [execStmt, q O passes R]
    | _ => simp [applyStmt] at h
  | .optNoneBranch c, s, s', h => by
    cases s with
    | onOption o p a =>
      simp only [applyStmt, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyBlock_sound c a x' hx
      intro O passes R σ ρ
      simp only [execStmt, q O passes R]
    | _ => simp [applyStmt] at h
  | .traverseBody c, s, s', h => by
    cases s with
    | traverse t inv body =>
      simp only [applyStmt, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyBlock_sound c body x' hx
      intro O passes R σ ρ
      simp only [execStmt, q O passes R]
    | _ => simp [applyStmt] at h
  | .retryCond c, s, s', h => by
    cases s with
    | retry n bis body ue =>
      simp only [applyStmt, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyExpr_sound c _ bis x' hx
      intro O passes R σ ρ
      simp only [execStmt, q.orte, q.wert]
    | _ => simp [applyStmt] at h
  | .retryBody c, s, s', h => by
    cases s with
    | retry n bis body ue =>
      simp only [applyStmt, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyBlock_sound c body x' hx
      intro O passes R σ ρ
      simp only [execStmt, q O passes R]
    | _ => simp [applyStmt] at h
  | .retryOverflow c, s, s', h => by
    cases s with
    | retry n bis body ue =>
      simp only [applyStmt, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyBlock_sound c ue x' hx
      intro O passes R σ ρ
      simp only [execStmt, q O passes R]
    | _ => simp [applyStmt] at h
  | .foreverBody c, s, s', h => by
    cases s with
    | forever a inv body =>
      simp only [applyStmt, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyBlock_sound c body x' hx
      intro O passes R σ ρ
      simp only [execStmt, q O passes R]
    | _ => simp [applyStmt] at h

/-- **Generic soundness of the block validator.** -/
theorem applyBlock_sound {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (c : BlockCert) → (b b' : Block D V l Γ Λ Λ') → applyBlock c b = some b' → BlockEquiv b b'
  | .dropCheck, b, b', h => by
    cases b with
    | pruefung c sonst rest =>
      simp only [applyBlock] at h
      split at h
      · cases h; exact dropCheck_sound c sonst _ (by assumption)
      · cases h
    | _ => simp [applyBlock] at h
  | .narrowEntailed, b, b', h => by
    cases b with
    | narrow e lo' hi' sonst rest =>
      simp only [applyBlock] at h
      exact narrowEntailed_sound e lo' hi' sonst rest b' h
    | _ => simp [applyBlock] at h
  | .checkCond c, b, b', h => by
    cases b with
    | pruefung e sonst rest =>
      simp only [applyBlock, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyExpr_sound c _ e x' hx
      intro O passes R σ ρ
      simp only [execBlock, q.orte, q.wert]
    | _ => simp [applyBlock] at h
  | .bindValue c, b, b', h => by
    cases b with
    | bind e rest =>
      simp only [applyBlock, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyExpr_sound c _ e x' hx
      intro O passes R σ ρ
      simp only [execBlock, q.orte, q.wert]
    | _ => simp [applyBlock] at h
  | .narrowValue c, b, b', h => by
    cases b with
    | narrow e lo' hi' sonst rest =>
      simp only [applyBlock, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyExpr_sound c _ e x' hx
      intro O passes R σ ρ
      simp only [execBlock, q.orte, q.wert]
    | _ => simp [applyBlock] at h
  | .head c, b, b', h => by
    cases b with
    | cons s rest =>
      simp only [applyBlock, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyStmt_sound c s x' hx
      intro O passes R σ ρ
      simp only [execBlock, q O passes R]
    | _ => simp [applyBlock] at h
  | .rest c, b, b', h => by
    cases b with
    | cons s rest =>
      simp only [applyBlock, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyBlock_sound c rest x' hx
      intro O passes R σ ρ
      simp only [execBlock, q O passes R]
    | bind e rest =>
      simp only [applyBlock, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyBlock_sound c rest x' hx
      intro O passes R σ ρ
      simp only [execBlock, q O passes R]
    | bindCall f args he hp hr rest =>
      simp only [applyBlock, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyBlock_sound c rest x' hx
      intro O passes R σ ρ
      simp only [execBlock, q O passes R]
    | pruefung e sonst rest =>
      simp only [applyBlock, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyBlock_sound c rest x' hx
      intro O passes R σ ρ
      simp only [execBlock, q O passes R]
    | narrow e lo' hi' sonst rest =>
      simp only [applyBlock, Option.map_eq_some_iff] at h
      obtain ⟨x', hx, rfl⟩ := h
      have q := applyBlock_sound c rest x' hx
      intro O passes R σ ρ
      simp only [execBlock, q O passes R]
    | _ => simp [applyBlock] at h
end

/-! ## 7. Conservative route and the pass pipeline (OPTIMIZER.md §§7.6, 8.5, 9)

    A refused OPTIONAL rewrite falls back to the input (`applyOrKeep`),
    which is itself validated (reflexivity) -- never to unchecked output.
    A pipeline is a list of (pass, certificate); it is accepted only if the
    passes come in the admitted order of §9 and every certificate uses
    only rules of the pass it is filed under, and then every step is
    validated. -/

/-- Apply, or keep the input when the validator refuses. -/
def applyOrKeep {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (c : BlockCert)
    (b : Block D V l Γ Λ Λ') : Block D V l Γ Λ Λ' :=
  (applyBlock c b).getD b

/-- The conservative route is always sound. -/
theorem applyOrKeep_sound {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (c : BlockCert)
    (b : Block D V l Γ Λ Λ') : BlockEquiv b (applyOrKeep c b) := by
  unfold applyOrKeep
  cases h : applyBlock c b with
  | none => exact BlockEquiv.refl b
  | some b' => exact applyBlock_sound c b b' h

/-- The passes of OPTIMIZER.md §9, in table order. -/
inductive PassKind where
  | fold | cfg | gvn | checks | strength | alias | licm | inline | unroll | peephole
  deriving DecidableEq, Repr

/-- Their position in the standard order. -/
def PassKind.rank : PassKind → Nat
  | .fold => 1 | .cfg => 2 | .gvn => 3 | .checks => 4 | .strength => 5
  | .alias => 6 | .licm => 7 | .inline => 8 | .unroll => 9 | .peephole => 10

/-- Admitted order: ranks never decrease. -/
def admittedOrder : List PassKind → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a.rank ≤ b.rank) && admittedOrder (b :: rest)

/-- The pass an expression rule belongs to. -/
def ExprCert.pass : ExprCert → PassKind
  | .foldInt => .fold
  | .foldBool => .fold

mutual
/-- Every rule a statement certificate uses belongs to pass `k`. -/
def StmtCert.fits (k : PassKind) : StmtCert → Bool
  | .iteCond c | .assignSlotIndex c | .assignSlotValue c | .assignVarValue c
  | .assignGlobValue c | .retryCond c => c.pass == k
  | .iteThen c | .iteElse c | .lockBody c | .breakingBody c | .optSomeBranch c
  | .optNoneBranch c | .traverseBody c | .retryBody c | .retryOverflow c
  | .foreverBody c => BlockCert.fits k c
/-- Every rule a block certificate uses belongs to pass `k`. -/
def BlockCert.fits (k : PassKind) : BlockCert → Bool
  | .dropCheck | .narrowEntailed => k == .checks
  | .checkCond c | .bindValue c | .narrowValue c => c.pass == k
  | .head c => StmtCert.fits k c
  | .rest c => BlockCert.fits k c
end

/-- Run certificates in order; one refusal refuses the run. -/
def runCerts {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    List (PassKind × BlockCert) → Block D V l Γ Λ Λ' → Option (Block D V l Γ Λ Λ')
  | [], b => some b
  | (_, c) :: rest, b =>
    match applyBlock c b with
    | some b' => runCerts rest b'
    | none => none

/-- The pipeline validator: order check, pass-membership check, then every
    step validated. -/
def applyPipeline {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (p : List (PassKind × BlockCert))
    (b : Block D V l Γ Λ Λ') : Option (Block D V l Γ Λ Λ') :=
  if admittedOrder (p.map Prod.fst) && p.all (fun kc => kc.2.fits kc.1) then runCerts p b
  else none

/-- Every validated run refines its input. -/
theorem runCerts_sound {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (p : List (PassKind × BlockCert)) → (b b' : Block D V l Γ Λ Λ') →
      runCerts p b = some b' → BlockEquiv b b'
  | [], b, b', h => by cases h; exact BlockEquiv.refl b
  | (_, c) :: rest, b, b', h => by
    simp only [runCerts] at h
    split at h
    · rename_i b₁ h₁
      exact (applyBlock_sound c b b₁ h₁).trans (runCerts_sound rest b₁ b' h)
    · cases h

/-- **Generic soundness of the pipeline validator.** -/
theorem applyPipeline_sound {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (p : List (PassKind × BlockCert)) (b b' : Block D V l Γ Λ Λ')
    (h : applyPipeline p b = some b') : BlockEquiv b b' := by
  unfold applyPipeline at h
  split at h
  · exact runCerts_sound p b b' h
  · cases h

/-- An accepted pipeline ran its passes in admitted order. -/
theorem applyPipeline_order {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (p : List (PassKind × BlockCert)) (b b' : Block D V l Γ Λ Λ')
    (h : applyPipeline p b = some b') : admittedOrder (p.map Prod.fst) = true := by
  unfold applyPipeline at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    exact hc.1
  · cases h
end Statements

/- CUTS (exactly what is NOT proved here):
   - No IR, by decision (594/606: direct lowering from the typed source,
     lane 287 superseded; OPTIMIZER.md §2): every rule acts on the real
     source syntax. GVN/CSE (V1/V2), dead code (D1/D2), alias motion
     (A1/A2), LICM (L1/L2), inlining (I1/I2), unrolling (U1/U2) and the
     peephole/allocation rules (P1–P4) need validator-recomputed dominators,
     footprints, effect summaries and the matching lowering rows, and are
     NOT here (§11.4: "only after the corresponding lowering rows and the
     source-cost/effect interface are accepted").
   - The block validator descends through `cons`/`bind`/`bindCall`/
     `pruefung`/`narrow` continuations, `ite` branches, `locks`/`breaking`
     bodies, both `on option` branches, the bodies of `traverse`/`retry`/
     `forever`, the `retry` overflow block and the `retry` exit condition.
     NOT reachable (a certificate pointing there is refused, never
     trusted): `on tag`/`on reason` arms, the other call binders,
     register/float binders, `exchange`/`awaits`, and the loop INVARIANTS of
     `traverse`/`forever` -- those are contract sites (§1.2 item 6, §7.4)
     whose obligations are reused from the unrewritten source, so no rule
     rewrites them.
   - Branch ELIMINATION for `ite` is not a block rewrite here: the condition
     folds to `true`/`false` (exact), and the branch-free lowering of a
     literal condition belongs to the x86 lowering lane.
   - A decided check or condition that READS a location is refused (its
     read event would vanish from the trace); a weaker refinement that may
     drop reads is not defined, because the race-freedom legs are stated
     over that trace.
   - Strength reduction certifies the target WORD operation (`shlW`,
     `shrW`, `&&& maskW`) against the source value; encoding, decoding,
     register allocation and the executed bytes stay with the lowering /
     image lanes (OPTIMIZER.md §8.7). The word is `SourceMemory.zahlWort`
     of the operand (`encodeNat` is that interface, not a second one).
     Products are recognised in both orders (`a * 2^k`, `2^k * b` with `b`
     not constant); division and remainder only with the constant divisor.
   - No floating-point rule exists (F1 literal folding included): F2–F4
     stay REFUSED by absence, `constBool?` answers `none` on `fllt`/`flle`.
   - No concurrency, TSO, budget/time or call-log transfer is CLAIMED
     beyond what exact `Ausgang` equality of single-thread `execBlock`
     already carries; the cross-thread (W/GX) and machine-work/time
     transfers stay OPEN (§§5, 6.4). In particular a dropped check or
     `narrow` removes a machine-G step (see `BlockEquiv`).
   - `foldInt`'s out-of-range refusal branch is unreachable for a sound
     `constInt?` (a value outside its type does not exist); it is kept as a
     recomputed check, and no poison probe can exercise it.
   - The pipeline order check is the order of §9; the rank table is the
     reviewed order of that section, not a measured choice.
-/

#print axioms constInt?_sound
#print axioms constInt?_orte
#print axioms bounds_sound
#print axioms constBool?_sound
#print axioms foldInt_sound
#print axioms foldBool_sound
#print axioms applyExpr_sound
#print axioms encodeNat_toNat
#print axioms shlW_encodeNat
#print axioms checkStrength_sound
#print axioms checkStrength_sound_zahlWort
#print axioms checkStrength_sdiv
#print axioms checkStrength_srem
#print axioms dropCheck_sound
#print axioms narrowEntailed_sound
#print axioms applyStmt_sound
#print axioms applyBlock_sound
#print axioms applyOrKeep_sound
#print axioms runCerts_sound
#print axioms applyPipeline_sound
#print axioms applyPipeline_order

end Gabbro.Grammatik.X86.OptimizationRules
