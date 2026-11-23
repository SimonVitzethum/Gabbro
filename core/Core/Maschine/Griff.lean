/-
  File:      core/Core/Maschine/Griff.lean
  Subject:   AUTHORITY AND LIFETIME (PERFECT-MODEL §3.4, step M4): a handle names an object and the
             generation it was issued for; the authority state records per object whether it lives and its
             current generation. A handle is valid exactly when its object lives in its generation.
             Revoking an object bumps its generation, so every handle issued before is stale for ever --
             also after the object is brought back to life (`widerrufen_ungueltig`,
             `alter_griff_bleibt_ungueltig`). A rule whose step uses a handle demands `Gueltig`, so a stale
             handle or a revoked capability has no step.
-/
module

@[expose] public section

namespace Gabbro.Core.Maschine

/-- **A handle**: an object and the generation it was issued for. -/
structure Griff where
  objekt : Nat
  gen : Nat
  deriving DecidableEq, Repr

/-- **The authority state**: per object whether it lives and its current generation. -/
structure Rechte where
  lebt : Nat → Bool
  gen : Nat → Nat

namespace Rechte

/-- A handle is valid: its object lives in the handle's generation. -/
def Gueltig (r : Rechte) (g : Griff) : Prop := r.lebt g.objekt = true ∧ r.gen g.objekt = g.gen

/-- Revoking an object: it no longer lives and its generation moves on. -/
def widerrufen (r : Rechte) (o : Nat) : Rechte where
  lebt := fun j => if j = o then false else r.lebt j
  gen := fun j => if j = o then r.gen j + 1 else r.gen j

/-- Bringing an object (back) to life in its current generation. -/
def beleben (r : Rechte) (o : Nat) : Rechte where
  lebt := fun j => if j = o then true else r.lebt j
  gen := r.gen

/-- The handle issued for a living object now. -/
def ausgeben (r : Rechte) (o : Nat) : Griff := ⟨o, r.gen o⟩

theorem ausgeben_gueltig (r : Rechte) (o : Nat) : (r.beleben o).Gueltig ((r.beleben o).ausgeben o) := by
  simp only [Gueltig, beleben, ausgeben, ↓reduceIte, and_self]

/-- **A revoked handle is invalid.** -/
theorem widerrufen_ungueltig (r : Rechte) (g : Griff) : ¬ (r.widerrufen g.objekt).Gueltig g := by
  intro h
  have h1 := h.1
  simp only [widerrufen, ↓reduceIte, Bool.false_eq_true] at h1

/-- **A handle valid before a revocation stays invalid after the object lives again.** -/
theorem alter_griff_bleibt_ungueltig (r : Rechte) (g : Griff) (hg : r.Gueltig g) :
    ¬ ((r.widerrufen g.objekt).beleben g.objekt).Gueltig g := by
  intro h
  have h2 := h.2
  simp only [beleben, widerrufen, ↓reduceIte] at h2
  rw [hg.2] at h2
  exact Nat.succ_ne_self g.gen h2

/-- Other objects are not touched by a revocation. -/
theorem widerrufen_anders (r : Rechte) {g : Griff} {o : Nat} (hne : g.objekt ≠ o) :
    (r.widerrufen o).Gueltig g ↔ r.Gueltig g := by
  simp only [Gueltig, widerrufen, hne, ↓reduceIte]

end Rechte

end Gabbro.Core.Maschine
