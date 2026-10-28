import Grammatik.Bausteine.Arena.Ownership.Borrow
import Grammatik.Logik.Vertraege.ObjektRahmen.T1

/-! Source provenance uses the existing bottom-based variable positions.
Copies share an origin. Consuming an origin invalidates every copy at once;
numeric equality of a later index cannot manufacture its provenance. -/

namespace Gabbro.Grammatik.ArenaOwnership.Source

variable {D : Deklaration}

structure Context where
  references : List (Option Nat)
  rights : Nat → Option PassingMode
  next : Nat

def Context.empty (Γ : Ctx) : Context := ⟨List.replicate Γ.length none, fun _ => none, 0⟩

def Context.reference (c : Context) {Γ : Ctx} {τ : Ty} (x : Var Γ τ) : Option Nat :=
  (c.references[x.unten]?).getD none

def Context.kill (c : Context) (origin : Nat) : Context :=
  { c with rights := fun i => if i = origin then none else c.rights i }

def Context.bind (c : Context) (origin : Option Nat) : Context :=
  { c with references := c.references ++ [origin] }

def Context.bindFresh (c : Context) : Context :=
  ⟨c.references ++ [some c.next], fun i => if i = c.next then some .owned else c.rights i, c.next + 1⟩

def Context.drop (c : Context) : Context := { c with references := c.references.dropLast }

def Context.bounded (c : Context) : Prop :=
  (∀ i, c.next ≤ i → c.rights i = none) ∧
  ∀ ref ∈ c.references, ∀ i, ref = some i → i < c.next

abbrev Ghost := Nat → Option Handle

def References (c : Context) (g : Ghost) {Γ : Ctx} (ρ : Env D Γ) : Prop :=
  c.references.length = Γ.length ∧
  ∀ {τ : Ty} (x : Var Γ τ) origin, c.reference x = some origin →
    ∃ h, g origin = some h ∧ intVon τ (ρ.get x) = some h.slot

def Rights (c : Context) (g : Ghost) (s : State) (frame : Frame) : Prop :=
  (∀ origin mode, c.rights origin = some mode →
    ∃ h, g origin = some h ∧ mode.permits s frame h) ∧
  (∀ i j p q, c.rights i = some p → c.rights j = some q → i ≠ j →
    (p = .owned ∨ q = .owned) →
      ∀ h k, g i = some h → g j = some k → h.slot ≠ k.slot)

def Realizes (c : Context) (g : Ghost) (A : FreiForm D) (frame : Frame)
    (s : State) (σ : World D) {Γ : Ctx} (ρ : Env D Γ) : Prop :=
  s.agrees A σ ∧ A.FreiOk σ ∧ c.bounded ∧ References c g ρ ∧ Rights c g s frame

/-- Only copying or widening a reference transports its identity. -/
def expressionOrigin {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (references : List (Option Nat)) : Expr D Γ Λ τ → Option Nat
  | .var x => (references[x.unten]?).getD none
  | .widen _ _ e => expressionOrigin references e
  | _ => none

abbrev origin {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (c : Context) (e : Expr D Γ Λ τ) : Option Nat :=
  expressionOrigin c.references e

theorem origin_sound {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (c : Context) (g : Ghost) (ρ : Env D Γ) (hr : References c g ρ)
    (e : Expr D Γ Λ τ) (i : Nat) (hi : origin c e = some i) (σ0 σ : World D) :
    ∃ h, g i = some h ∧ intVon τ (eval σ0 e σ ρ) = some h.slot := by
  induction e using Expr.rec (motive_2 := fun _ _ _ _ => True) with
  | var x => exact hr.2 x i hi
  | widen h0 h1 e ih =>
    obtain ⟨h, hg, hv⟩ := ih ρ hr hi
    exact ⟨h, hg, hv⟩
  | empty => trivial
  | num _ _ => trivial
  | _ => simp only [origin, expressionOrigin, reduceCtorEq] at hi

@[simp] theorem Context.kill_reference (c : Context) (i : Nat) {Γ : Ctx} {τ : Ty} (x : Var Γ τ) :
    (c.kill i).reference x = c.reference x := rfl

@[simp] theorem Context.kill_at (c : Context) (i : Nat) : (c.kill i).rights i = none := by simp only [kill, ↓reduceIte]

@[simp] theorem Context.kill_other (c : Context) (i j : Nat) (h : j ≠ i) :
    (c.kill i).rights j = c.rights j := by simp only [kill, h, ↓reduceIte]

theorem Context.kill_bounded {c : Context} (hc : c.bounded) (i : Nat) : (c.kill i).bounded := by
  refine ⟨?_, hc.2⟩
  intro j hj
  by_cases he : j = i
  · simp only [kill, he, ↓reduceIte]
  · simpa [Context.kill, he] using hc.1 j hj

theorem Context.kill_references {c : Context} {g : Ghost} {Γ : Ctx} {ρ : Env D Γ}
    (hc : References c g ρ) (i : Nat) : References (c.kill i) g ρ := hc

theorem Context.kill_rights {c : Context} {g : Ghost} {s : State} {frame : Frame}
    (hc : Rights c g s frame) (i : Nat) : Rights (c.kill i) g s frame := by
  constructor
  · intro j mode hj
    by_cases he : j = i
    · simp only [kill, he, ↓reduceIte, reduceCtorEq] at hj
    · exact hc.1 j mode (by simpa [Context.kill, he] using hj)
  · intro j k p q hj hk hne hown h h' hg hg'
    have hjne : j ≠ i := by intro he; simp only [kill, he, ↓reduceIte, reduceCtorEq] at hj
    have hkne : k ≠ i := by intro he; simp only [kill, he, ↓reduceIte, reduceCtorEq] at hk
    exact hc.2 j k p q (by simpa [Context.kill, hjne] using hj)
      (by simpa [Context.kill, hkne] using hk) hne hown h h' hg hg'

theorem Context.kill_aliases {c : Context} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ) (i : Nat) (hi : origin c e = some i) :
    origin (c.kill i) e = some i ∧ (c.kill i).rights i = none := ⟨hi, Context.kill_at c i⟩

end Gabbro.Grammatik.ArenaOwnership.Source
