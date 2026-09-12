/-
  Audit probe F5: `hinv_aus_disziplin` ignores its `LockFrei` premise (pattern b);
  `interferenceFree_wo_frei` therefore proves `Q`-preservation without using
  lock-freedom at either end.

  Claim: `hinv_aus_disziplin ... (h : LockFrei L σ) : I.inv (.inl t₀) σ` is
  proved by `intro k σ h _; exact hinv_kette_aus_disziplin ...`, i.e. the
  lock-freedom hypothesis is bound to `_` and never used. The conclusion
  "lock free implies invariant" is really "invariant, unconditionally" (at
  every chain world). Below: the same conclusion with the `LockFrei`
  hypothesis erased, plus the corollary that `interferenceFree_wo_frei`'s
  `hFreiVor`/`hFreiNach` are dead premises.
-/
import Grammatik.InterferenzAllgemein

namespace Gabbro.Grammatik

open Gabbro.Grammatik

variable {D : Deklaration}

/-- `hinv_aus_disziplin` minus `LockFrei`: identical proof, `_` made explicit. -/
theorem audit_hinv_ohne_frei
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (t₀ : D.Tab) (L : D.Lock)
    (Wc : D.Tab → Bool) (Gc : D.Glob → Bool)
    (hAb : HaengtAb Wc Gc (I.inv (.inl t₀)))
    (hFrameT : ∀ t : D.Tab, Wc t = true → (.inl t₀ : D.Tab ⊕ D.Glob) = .inl t)
    (hFrameG : ∀ x : D.Glob, Gc x = true → (.inl t₀ : D.Tab ⊕ D.Glob) = .inr x)
    (hGuardT : Sum.inl L ∈ D.braucht t₀)
    (hEntry : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → I.inv (.inl t₀) σ₀)
    (hReturn : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → J.schrittFaden[k]? = some g → J.welten[k]? = some vor →
        J.welten[k + 1]? = some nach → TraegerSchreibt (J.code g) (.inl t₀) = true →
          L ∈ D.haelt (J.code g) → I.inv (.inl t₀) nach)
    (hCov : ∀ (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i) :
    ∀ (k : Nat) (σ : World D), J.welten[k]? = some σ → I.inv (.inl t₀) σ := by
  intro k σ h
  exact hinv_kette_aus_disziplin Nb J I (.inl t₀) L Wc Gc hAb hFrameT hFrameG
    hGuardT hEntry hReturn
    (fun k g vor nach hgm hkg hkv hkn hW =>
      wache_aus_schuld Nb J t₀ L hGuardT g hgm hW (hCov g hgm hW))
    k σ h

/-- The original follows by ignoring the freedom hypothesis. -/
theorem audit_hinv_forget_frei
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (t₀ : D.Tab) (L : D.Lock)
    (Wc : D.Tab → Bool) (Gc : D.Glob → Bool)
    (hAb : HaengtAb Wc Gc (I.inv (.inl t₀)))
    (hFrameT : ∀ t : D.Tab, Wc t = true → (.inl t₀ : D.Tab ⊕ D.Glob) = .inl t)
    (hFrameG : ∀ x : D.Glob, Gc x = true → (.inl t₀ : D.Tab ⊕ D.Glob) = .inr x)
    (hGuardT : Sum.inl L ∈ D.braucht t₀)
    (hEntry : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → I.inv (.inl t₀) σ₀)
    (hReturn : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → J.schrittFaden[k]? = some g → J.welten[k]? = some vor →
        J.welten[k + 1]? = some nach → TraegerSchreibt (J.code g) (.inl t₀) = true →
          L ∈ D.haelt (J.code g) → I.inv (.inl t₀) nach)
    (hCov : ∀ (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i) :
    ∀ (k : Nat) (σ : World D), J.welten[k]? = some σ → LockFrei (D := D) L σ →
      I.inv (.inl t₀) σ :=
  fun k σ h _ => audit_hinv_ohne_frei Nb J I t₀ L Wc Gc hAb hFrameT hFrameG
    hGuardT hEntry hReturn hCov k σ h

/-- Consequence: `interferenceFree_wo_frei` concludes `Q`-preservation while
    its `LockFrei` premises at both ends are dead -- the "WHERE THE LOCK IS
    FREE" in the docstring restricts nothing. -/
example (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Q : Faden → World D → Prop)
    (t₀ : D.Tab) (L : D.Lock)
    (Wc : D.Tab → Bool) (Gc : D.Glob → Bool)
    (hAb : HaengtAb Wc Gc (I.inv (.inl t₀)))
    (hFrameT : ∀ t : D.Tab, Wc t = true → (.inl t₀ : D.Tab ⊕ D.Glob) = .inl t)
    (hFrameG : ∀ x : D.Glob, Gc x = true → (.inl t₀ : D.Tab ⊕ D.Glob) = .inr x)
    (hGuardT : Sum.inl L ∈ D.braucht t₀)
    (hEntry : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → I.inv (.inl t₀) σ₀)
    (hReturn : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → J.schrittFaden[k]? = some g → J.welten[k]? = some vor →
        J.welten[k + 1]? = some nach → TraegerSchreibt (J.code g) (.inl t₀) = true →
          L ∈ D.haelt (J.code g) → I.inv (.inl t₀) nach)
    (hCov : ∀ (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i)
    (hFormU : ∀ (f : Faden), f ∈ J.faeden → ∀ (σ : World D),
      Q f σ ↔ I.inv (.inl t₀) σ) :
    ∀ (f : Faden), f ∈ J.faeden → ∀ (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → g ≠ f →
        J.schrittFaden[k]? = some g → J.welten[k]? = some vor →
          J.welten[k + 1]? = some nach → (Q f vor ↔ Q f nach) := by
  intro f hf k g vor nach _ _ _ hkv hkn
  have hInv := audit_hinv_ohne_frei Nb J I t₀ L Wc Gc hAb hFrameT hFrameG hGuardT
    hEntry hReturn hCov
  rw [hFormU f hf vor, hFormU f hf nach]
  exact ⟨fun _ => hInv _ nach hkn, fun _ => hInv _ vor hkv⟩

/-
CUTS:
- The finding is about the `LockFrei` premise specifically (pattern b/d:
  docstring "lock free implies invariant" over a proof that never reads it).
  Whether `hReturn`/`hCov`/`hEntry` hold for ordinary programs is a separate
  (pattern e) question, not demonstrated here.
-/
#print axioms Gabbro.Grammatik.audit_hinv_ohne_frei
#print axioms Gabbro.Grammatik.audit_hinv_forget_frei
