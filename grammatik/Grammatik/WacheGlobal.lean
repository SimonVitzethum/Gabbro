/-
  File:      Grammatik/WacheGlobal.lean
  Subject:   D6 -- WATCHES FOR GLOBALS (lane 103).

  Mirror of `wache_aus_schuld` (InterferenzAllgemein.lean) for globals:
  a writer of global `x` holds every guard in its watch list, from the
  checker's per-thread touch discipline plus the guard fact. U003
  (`D.invarianten_gehalten`) is table-only, so the mirror routes via
  the touch rule (`WaechterGehalten`) instead of `J.hSchuld`.
-/
import Grammatik.InterferenzAllgemein

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **The watch, discharged for globals.** A writer of global `x₀` holds
    every guard in `x₀`'s watch list: the touch discipline gives the
    held ceramony (`WaechterGehalten`) at `.inr x₀`, the guard fact picks
    `L`, and the `held`-membership in the signature holdings is exactly
    the declared hold. Tables route via `J.hSchuld` (`wache_aus_schuld`);
    globals have no `schuldet` coverage, so the discipline travels here
    as the explicit per-thread premise `hTouch`. -/
theorem wache_global_aus_schuld (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (x₀ : D.Glob) (L : D.Lock)
    (hGuardG : Sum.inl L ∈ D.gbraucht x₀)
    (g : Faden) (hg : g ∈ J.faeden)
    (hW : TraegerSchreibt (J.code g) (.inr x₀) = true)
    (hTouch : ∀ f ∈ J.faeden, TraegerSchreibt (J.code f) (.inr x₀) = true →
      WaechterGehalten (J.code f) (.inr x₀)) :
    L ∈ D.haelt (J.code g) := by
  have hWG : ∀ w ∈ D.gbraucht x₀,
      Res.von D w ∈ Signatur.anfang D (D.signatur (J.code g)) :=
    hTouch g hg hW
  have hmem := hWG (Sum.inl L) hGuardG
  change Res.held (D := D) L ∈ _ at hmem
  simp only [Signatur.anfang] at hmem
  rcases List.mem_append.mp hmem with hleft | hright
  · obtain ⟨L', hL', heq⟩ := List.mem_map.mp hleft
    cases heq
    exact hL'
  · obtain ⟨⟨m, s⟩, _, heq⟩ := List.mem_map.mp hright
    simp only [Res.vonMarke] at heq
    cases heq

/-! ## CUTS:
  - Witness `wache_global_aus_schuld_zeuge` on a local one-global
    declaration: pending (next step).
-/

#print axioms Gabbro.Grammatik.wache_global_aus_schuld

end Gabbro.Grammatik
