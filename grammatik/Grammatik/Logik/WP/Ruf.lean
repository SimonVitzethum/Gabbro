import Grammatik.Logik.WP.Kern
import Grammatik.Logik.Vertraege.HandlerKongruenz

/-!
# GabbroV over machine G: calls and recursion

A specification of the program's functions is any Lean relation `Spez f σ ρ out` between a call's entry world, its
arguments and its outcome -- not only the in-language `requires`/`ensures` expressions. Then

* `wpS_call`: a call statement meets `Q` when every outcome the specification allows does;
* `ruf_induktion` (partial correctness): if every body meets the specification under callees that meet it, every
  depth of `rufAt` meets it;
* `ruf_mass` (total correctness): with a measure that falls at every call, every call whose measure lies below the
  depth meets it -- so a specification demanding a normal answer is reached;
* `rufAt_succ_wp`: one step of `rufAt` as the weakest precondition of the body.

Together with the structural rules of `Kern.lean` this is the procedure logic: modular (each body is proved once,
against the specifications of its callees), sound and complete (the specification `fun f σ ρ out => out = rufAt …`
satisfies every premise).
-/

namespace Gabbro.Grammatik.WP

open Gabbro.Grammatik

variable {D : Deklaration}

/-- A specification of every function: which outcomes a call may have, given its entry world and arguments. -/
abbrev Spez (D : Deklaration) := ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f → Prop

/-- A call meaning meets a specification. -/
def Erfuellt (S : Spez D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ f σ ρ, S f σ ρ (R f σ ρ)

/-- What a call statement makes of the callee's outcome (`execStmt`'s `.call` clause). -/
def rufZuAusgang {V : Vertrag D} {l : Bool} {Γ : Ctx} {f : D.Fn} (hr : D.gruende f = 0) (ρ : Env D Γ) :
    RufAusgang f → Ausgang V l Γ
  | .ok σ' _ => .ok σ' ρ
  | .why _ r => keinGrund hr r
  | .logik e => .logik e
  | .hardware e => .hardware e

section Aufruf

variable (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- **The call statement**, exactly: it meets `Q` when the callee's outcome, seen by the caller, does. -/
theorem wpS_call_exakt {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (f : D.Fn)
    (args : Args D Γ Λ (D.params f)) (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0)
    (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpS O passes R (.call f args hp hr) Q σ ρ ↔
      Q (rufZuAusgang hr ρ (R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ))) := by
  unfold wpS
  simp only [execStmt]
  cases R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) <;> rfl

/-- **The call rule against a specification**: if the callee meets `S`, the call meets `Q` whenever every outcome `S`
    allows at these arguments meets `Q`. -/
theorem wpS_call {S : Spez D} (hR : Erfuellt S R) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (f : D.Fn) (args : Args D Γ Λ (D.params f)) (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0)
    (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ)
    (h : ∀ out, S f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) out →
      Q (rufZuAusgang hr ρ out)) :
    wpS O passes R (.call f args hp hr) Q σ ρ :=
  (wpS_call_exakt O passes R f args hp hr Q σ ρ).2 (h _ (hR f _ _))

end Aufruf

/-! ## One step of `rufAt` as the body's weakest precondition -/

/-- What `rufAt` makes of the body's end: the `ensures` test (its `old` side at the entry world `σ`), the owed
    invariants, the answer. -/
def rufNach (P : Programm D) (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) :
    EndAusgang (vertragVon D f) false (D.params f) → RufAusgang f
  | EndAusgang.zurueck σ' v =>
      let σ' := σ'.lese (vertragVon D f).ende (P.ensures f).orte
      if wahr? (eval σ (P.ensures f) σ' (ergEnv (D.erg f) v ρ)) = false then
        .logik (.nachbedingung f)
      else
        let σ' := (D.invs.filter (schuldet f)).foldl
          (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte) σ'
        match D.invs.find? (fun i => schuldet f i && !wahr? (eval σ' (P.invariante i) σ' .nil)) with
        | Option.some i => .logik (.invariante i)
        | Option.none => .ok σ' v
  | .why σ' r => .why σ' r
  | .leave h _ _ => absurd h (by decide)
  | .next h _ _ => absurd h (by decide)
  | .logik e => .logik e
  | .hardware e => .hardware e

/-- The entry world of a call: the `requires` read recorded. -/
def rufEintritt (P : Programm D) (f : D.Fn) (σ : World D) : World D :=
  σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte

/-- `rufSchritt` with its parts named: the entry gate, then the body's end post-processed. -/
theorem rufSchritt_eq (P : Programm D) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (f : D.Fn) (σ : World D)
    (ρ : Env D (D.params f)) :
    rufSchritt P O passes R f σ ρ =
      if wahr? (eval (rufEintritt P f σ) (P.requires f) (rufEintritt P f σ) ρ) = false then
        .logik (.vorbedingung f)
      else rufNach P f (rufEintritt P f σ) ρ (execEnd (V := vertragVon D f) O passes R (P.rumpf f) (rufEintritt P f σ) ρ) := by
  unfold rufSchritt rufEintritt
  dsimp only
  by_cases hq : wahr? (eval (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) (P.requires f)
      (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ) = false
  · rw [if_pos hq, if_pos hq]
  · rw [if_neg hq, if_neg hq]
    generalize execEnd (V := vertragVon D f) O passes R (P.rumpf f)
      (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ = eo
    cases eo <;> rfl

/-- **One step of `rufAt`**: a failing `requires` is the precondition stop; otherwise the call's outcome is the body's
    end, post-processed. So a specification of `rufAt (n+1)` is the weakest precondition of the body for it. -/
theorem rufAt_succ_wp (P : Programm D) (O : Orakel D) (passes n : Nat) (f : D.Fn) (σ : World D)
    (ρ : Env D (D.params f)) (Q : RufAusgang f → Prop)
    (hVor : wahr? (eval (rufEintritt P f σ) (P.requires f) (rufEintritt P f σ) ρ) = false →
      Q (.logik (.vorbedingung f)))
    (hRumpf : wahr? (eval (rufEintritt P f σ) (P.requires f) (rufEintritt P f σ) ρ) = true →
      wpE (V := vertragVon D f) O passes (rufAt P O passes n) (P.rumpf f)
        (fun eo => Q (rufNach P f (rufEintritt P f σ) ρ eo)) (rufEintritt P f σ) ρ) :
    Q (rufAt P O passes (n + 1) f σ ρ) := by
  rw [rufAt_succ_eq, rufSchritt_eq]
  split
  · rename_i hq; exact hVor hq
  · rename_i hq; exact hRumpf (by simpa using hq)

/-- **Recursion, partial correctness.** A specification that allows the depth stop (`abstieg`), and that every body
    meets under callees meeting it, is met by every depth of `rufAt`. -/
theorem ruf_induktion (P : Programm D) (O : Orakel D) (passes : Nat) (S : Spez D)
    (hAbstieg : ∀ f σ ρ, S f σ ρ (.logik (.abstieg f)))
    (hSchritt : ∀ n, Erfuellt S (rufAt P O passes n) → Erfuellt S (rufAt P O passes (n + 1))) :
    ∀ n, Erfuellt S (rufAt P O passes n) := by
  intro n
  induction n with
  | zero => intro f σ ρ; exact hAbstieg f σ ρ
  | succ n ih => exact hSchritt n ih

/-- **Recursion, total correctness.** A measure `μ` on calls; if every body meets the specification at depth `n + 1`
    for every call of measure below `n + 1`, given that callees of measure below `n` meet it at depth `n`, then every
    call of measure below the depth meets it -- the depth stop is never reached. -/
theorem ruf_mass (P : Programm D) (O : Orakel D) (passes : Nat) (S : Spez D)
    (μ : ∀ f : D.Fn, World D → Env D (D.params f) → Nat)
    (hSchritt : ∀ n, (∀ g σ ρ, μ g σ ρ < n → S g σ ρ (rufAt P O passes n g σ ρ)) →
      ∀ f σ ρ, μ f σ ρ < n + 1 → S f σ ρ (rufAt P O passes (n + 1) f σ ρ)) :
    ∀ n f σ ρ, μ f σ ρ < n → S f σ ρ (rufAt P O passes n f σ ρ) := by
  intro n
  induction n with
  | zero => intro f σ ρ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih => exact hSchritt n ih

/-- **The procedure logic is complete**: the specification "the outcome IS `rufAt n`'s" meets the premise of
    `ruf_induktion` at every depth -- every true statement about the calls follows from it by consequence. -/
theorem ruf_vollstaendig (P : Programm D) (O : Orakel D) (passes n : Nat) :
    Erfuellt (fun f σ ρ out => out = rufAt P O passes n f σ ρ) (rufAt P O passes n) :=
  fun _ _ _ => rfl

end Gabbro.Grammatik.WP
