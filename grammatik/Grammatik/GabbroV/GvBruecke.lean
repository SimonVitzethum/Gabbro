/-
   File:      Grammatik/GabbroV/GvBruecke.lean
   Subject:   Agent 04 follow-up-4: the store-bridge base -- `Semantik.kette`
              (the accepted model, `Semantik.lean:203-209`) agrees with the
              `ketteNext` mirror on in-range indices.

   This closes the "projection documented, not formalised" gap for the
   single-chain case: every `kette_schranke` premise (`hrand`) and every
   `ketteNext` run is a statement about a `Semantik.kette` run, via the
   edge-map mirror `spiegel`. What stays open (CUTS): whole-`World`
   stores to edge maps (per-table projection), the `chain`-domain
   bridge, fuel completeness past slot count.
-/
import Grammatik.Kern.Semantik.Semantik
import Grammatik.GabbroV.GvVerkettung

namespace Gabbro.Grammatik.GabbroV

open Gabbro.Grammatik

/-- Mirror a `kette` edge map to naturals: `none` stays `none`, a bound
    index travels through `Int.toNat` (faithful on non-negative indices;
    the `Zahl 0 (n-1)` type already forces every answer non-negative). -/
def spiegel (n : Int) (weiter : Int → Option (Zahl 0 (n - 1))) :
    Nat → Option Nat
  | k =>
    match weiter (k : Int) with
    | none => none
    | some z => some z.n.toNat

/-- Agreement: on non-negative indices the accepted `kette` and the
    `ketteNext` mirror answer alike. The `Zahl` answers need no extra
    premise -- `z.lo_le` already says they are non-negative. -/
theorem kette_gleicht (n : Int) (weiter : Int → Option (Zahl 0 (n - 1)))
    (fuel : Nat) (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    kette weiter fuel a b
      = ketteNext (spiegel n weiter) fuel a.toNat b.toNat := by
  induction fuel generalizing a with
  | zero =>
      by_cases hab : a = b
      · subst hab
        have eL : kette weiter 0 a a = true := by simp [kette]
        have eR : ketteNext (spiegel n weiter) 0 a.toNat a.toNat = true := by
          simp [ketteNext]
        rw [eL, eR]
      · have hne : a.toNat ≠ b.toNat := by omega
        have eL : kette weiter 0 a b = false := by simp [kette, hab]
        have eR : ketteNext (spiegel n weiter) 0 a.toNat b.toNat = false := by
          simp [ketteNext, hne]
        rw [eL, eR]
  | succ fuel ih =>
      by_cases hab : a = b
      · subst hab
        have eL : kette weiter (fuel + 1) a a = true := by simp [kette]
        have eR : ketteNext (spiegel n weiter) (fuel + 1) a.toNat a.toNat
            = true := by
          simp [ketteNext]
        rw [eL, eR]
      · have hne : a.toNat ≠ b.toNat := by omega
        simp only [kette, ketteNext, if_neg hab, if_neg hne]
        cases hma : weiter a with
        | none =>
            have hsp : spiegel n weiter a.toNat = none := by
              have hc : ((a.toNat : Nat) : Int) = a := by omega
              rw [spiegel, hc, hma]
            rw [hsp]
        | some m =>
            have hsp : spiegel n weiter a.toNat = some (m.n.toNat) := by
              have hc : ((a.toNat : Nat) : Int) = a := by omega
              rw [spiegel, hc, hma]
            rw [hsp]
            exact ih m.n m.lo_le

/-! ## Witness: the three-chain on both sides -/

/-- Three-slot chain 0 → 1 → 2 → end as a model edge map. The `Zahl`
    proofs are discharged by `omega`; out-of-range targets are
    unrepresentable -- that is what `D006`-`D008` buy. -/
def kette3W : Int → Option (Zahl 0 (3 - 1))
  | 0 => some ⟨1, by omega, by omega⟩
  | 1 => some ⟨2, by omega, by omega⟩
  | _ => none

/-- Witness (non-degenerate): the bridge fires on a real three-chain --
    every premise (`0 ≤ 0`, `0 ≤ 2`) discharges by `decide`. -/
theorem kette_bruecke_zeuge :
    kette kette3W 3 0 2 = ketteNext (spiegel 3 kette3W) 3 0 2 := by
  exact kette_gleicht 3 kette3W 3 0 2 (by decide) (by decide)

/-- Fuel witness: one step of fuel does not cross two edges. -/
theorem kette_braucht_treibstoff :
    kette kette3W 1 0 2 = false := by
  decide

/-
   CUTS: what is not proved.
   - Proved: `spiegel` mirrors a model edge map to naturals; `kette_gleicht`
     (agreement on non-negative indices, by fuel induction); the bridge
     fires on `kette3W` (`kette_bruecke_zeuge`); fuel matters
     (`kette_braucht_treibstoff`).
   - Only stated: `kette3W` as the fixture shape.
   - Not modelled: whole-`World` stores to edge maps (per-table
     projection of `σ.slots`); the `chain`-domain bridge; fuel
     completeness past slot count; `GvTraversal`/`GvSplits`/
     `GvParserFragment` (not in this clone) reconciliation.
   - No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` anywhere; every
     premise is used; no premise has type `Prop` itself.
-/

#print axioms kette_gleicht
#print axioms kette_bruecke_zeuge

end Gabbro.Grammatik.GabbroV
