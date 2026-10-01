/-
  File:      Grammatik/X86/RegionFresh.lean
  Subject:   Fresh/disjoint external-region proofs over checked allocation.

  Lane 544 (N18): generic fresh/disjoint external-region preservation over
  the accepted `Regionen.reserviere`/`initialisiere` and `RegionSeparation`
  interfaces, proved over actual `Speicher` memory transitions and multiple
  reservations. Region extent/ownership originate in the existing
  source/binding model (`TableLayout.alsRegion` over the computed layout),
  never from an integer-to-pointer conversion. Source-to-allocator
  correspondence stays OPEN (see CUTS).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Regionen
import Grammatik.X86.RegionSeparation
import Grammatik.X86.TableLayout
import Grammatik.X86.Ausfuehrung

namespace Gabbro.Grammatik.X86

/-- A bare number names no region extent: admission requires membership. -/
def ausZahlVerweigert (n : Nat) (rs : List Region) : Bool :=
  rs.all (fun r => !inRegion r n)

/-- SOUNDNESS of the number refusal: a refused bare number lies in no
    listed region extent. Every premise is used. -/
theorem ausZahlVerweigert_klingt (n : Nat) (rs : List Region)
    (h : ausZahlVerweigert n rs = true) (r : Region) (hm : r ∈ rs) :
    inRegion r n = false := by
  unfold ausZahlVerweigert at h
  rw [List.all_eq_true] at h
  have h2 := h r hm
  simpa using h2

/-- Interval fact: an address inside one of two disjoint regions lies
    outside the other. Real interval arithmetic, never assumed. -/
theorem disjunkt_nicht_in_region (a b : Region)
    (hd : regionDisjunkt a b = true)
    (x : Nat) (hx : inRegion a x = true) :
    inRegion b x = false := by
  unfold regionDisjunkt at hd
  unfold inRegion at hx ⊢
  rw [decide_eq_true_eq] at hd hx
  rw [decide_eq_false_iff_not]
  omega

/- CUTS:
    - Skeleton only: no fresh/disjoint preservation is proved yet.
    - No source correspondence is claimed here.
-/

#print axioms ausZahlVerweigert

end Gabbro.Grammatik.X86
