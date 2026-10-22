/-
  File:      Grammatik/Logik/Terminierung/Mass.lean
  Subject:   T2 -- THE RECURSION MEASURE IN THE MODEL (2026-10-22).

  The language's `decreases` becomes a measure in the model: per function a LEXICOGRAPHIC tuple of natural-number
  expressions over its parameters (`Mass`), so that measures like Ackermann's `(m, n)` are expressible. It is a
  parameter beside the program, like the order specification of the leg `folge`: the exporter fills it from the
  `decreases` clauses, and a function without one has the empty tuple.

  * `Mass.wert` -- the tuple's value at a world and the arguments; `lexLt` -- the strict lexicographic order;
    `lexLt_wf` -- it is well-founded on tuples of one length (`T4` uses it).
  * `massTor` -- the call handler that checks the measure at every call into the caller's own cycle: a call of `g`
    whose measure does not fall below the caller's entry value answers `logik (abstieg g)`, the outcome machine G's
    big-step semantics already uses for a recursion whose depth runs out. It is `torRuf`'s shape (the `requires`
    gate), so the replay that carries `requires` to every logged entry carries the measure the same way.
  * `MassPflicht` -- the user's duty: the body, run against every frame-respecting handler behind `massTor`, never
    ends in `abstieg`. The checker only checks THAT every recursion cycle that is not a tail-call cycle carries a
    measure (`Klasse.lean`); that the measure falls is the user's logic, as `ensures` is.
-/
import Grammatik.Logik.Terminierung.Klasse
import Grammatik.Speichermodell.Atomar.AtomarRec

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Measures and their order -/

/-- **A measure**: per function a lexicographic tuple of natural-number expressions over its parameters. -/
def Mass (D : Deklaration) : Type :=
  ∀ f : D.Fn, List (Σ hi : Int, Expr D (D.params f) (Signatur.anfang D (D.signatur f)) (.int 0 hi))

/-- No function carries a measure. -/
def Mass.leer : Mass D := fun _ => []

/-- `f` carries a measure. -/
def Mass.hat (m : Mass D) (f : D.Fn) : Bool := !(m f).isEmpty

/-- The measure's value at the world `σ` and the arguments `ρ`. -/
def Mass.wert (m : Mass D) (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) : List Nat :=
  (m f).map fun e => ((eval σ e.2 σ ρ : Zahl 0 e.1)).n.toNat

/-- The strict lexicographic order. -/
def lexLt : List Nat → List Nat → Bool
  | a :: as, b :: bs => a < b || (a == b && lexLt as bs)
  | _, _ => false

theorem lexLt_laenge : ∀ {a b : List Nat}, lexLt a b = true → a ≠ [] ∧ b ≠ []
  | _ :: _, _ :: _, _ => ⟨List.cons_ne_nil _ _, List.cons_ne_nil _ _⟩
  | [], _, h => by simp [lexLt] at h
  | _ :: _, [], h => by simp [lexLt] at h

/-- The order restricted to tuples of length `n`. -/
def lexLtN (n : Nat) (a b : List Nat) : Prop := a.length = n ∧ b.length = n ∧ lexLt a b = true

/-- **The lexicographic order is well-founded on tuples of one length.** -/
theorem lexLt_wf : ∀ n, WellFounded (lexLtN n)
  | 0 => ⟨fun a => ⟨a, fun b ⟨_, hb, h⟩ => by
      have := (lexLt_laenge h).2; exact absurd (List.eq_nil_of_length_eq_zero hb) this⟩⟩
  | n + 1 => by
      have ih := lexLt_wf n
      -- a tuple `a :: as` is reached by induction on `a`, then on `as`
      refine ⟨fun x => ?_⟩
      suffices H : ∀ (a : Nat) (as : List Nat), as.length = n → Acc (lexLtN (n + 1)) (a :: as) by
        refine ⟨_, fun y ⟨hy, hx, _⟩ => ?_⟩
        cases y with
        | nil => simp at hy
        | cons b bs => exact H b bs (by simpa using hy)
      intro a
      induction a using Nat.strongRecOn with
      | _ a iha =>
      intro as has
      induction (ih.apply as) with
      | intro as _ ihas =>
      refine ⟨_, fun y ⟨hy, _, hlt⟩ => ?_⟩
      cases y with
      | nil => simp at hy
      | cons b bs =>
          simp only [lexLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hlt
          have hbs : bs.length = n := by simpa using hy
          rcases hlt with hlt | ⟨rfl, hlt⟩
          · exact iha b hlt bs hbs
          · exact ihas bs ⟨hbs, by simpa using has, hlt⟩ hbs

/-! ## 2. The measure gate and the user's duty -/

section Pflicht

variable [DecidableEq D.Fn] (P : Programm D) (fs : List D.Fn)

/-- `g` lies on a cycle with `f` (both reach each other). -/
def zyklusMit (f g : D.Fn) : Bool := reachB P fs f g && reachB P fs g f

/-- **The measure gate**: a call of `g` on the caller's cycle (`zyk`) whose measure does not fall below `w`
    answers `logik (abstieg g)`; every other call is `R`'s. -/
def massTor (m : Mass D) (zyk : D.Fn → Bool) (w : List Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) :
    ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f :=
  fun g σ ρ => if zyk g && !(lexLt (m.wert g σ ρ) w) then .logik (.abstieg g) else R g σ ρ

/-- **The user's duty for the measure of `f`**: run against every frame-respecting handler behind the measure gate,
    from every entry where `requires f` holds, the body never ends in `abstieg` -- every call back into `f`'s
    cycle has a smaller measure than `f`'s entry. Vacuous for a function without a measure. -/
def MassPflicht (passes : Nat) (Q : AxEns D) (S : SperrInv D) (T : D.Tab ⊕ D.Glob → Prop) (m : Mass D)
    (f : D.Fn) : Prop :=
  m.hat f = true →
  ∀ O' : Orakel D, RahmenO O' → RegLokal O' → AxVertragO Q O' →
    ∀ U : Umwelt D, HavocOk S U → ∀ A : AUmwelt D, HavocA T A →
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
      RespektiertRahmen P R → OhneLogik R →
      ∀ (σ : World D) (ρ : Env D (D.params f)), ReqAmEintritt P f σ ρ →
        ∀ g : D.Fn, execEndHA (V := vertragVon D f) S O' U A passes
          (massTor m (zyklusMit P fs f) (m.wert f σ ρ) R) (P.rumpf f) σ ρ ≠
          EndAusgang.logik (Logik.abstieg g)

end Pflicht

end Gabbro.Grammatik
