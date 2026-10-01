/-
  File:      Grammatik/X86/AccessExecution.lean
  Subject:   Executed pilot instruction to realised access footprint.

  Lane 568: connects `Zugriffe.zugriff` (a checked POTENTIAL footprint from
  the pre-state) to ACTUAL successful `Ausfuehrung.schritt` and
  `Byteschritt.byteschritt` for all 14 pilot forms. Every footprint fact
  below is derived from a successful step premise (`schritt d s = some s'`
  or `byteschritt s = .weiter s'`); a computed list alone is never a
  realised trace. Reuses the `Speicher` read/write frame lemmas through
  the `Zugriffe` linkage theorems. The eight `Fuss` addresses stay a byte
  set, not one atomic TSO event; the full W/GX mapping stays OPEN.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Zugriffe
import Grammatik.X86.Byteschritt

namespace Gabbro.Grammatik.X86

/-- A realised step: the actual `schritt` succeeded. -/
def istRealisiert (d : Decodiert) (s s' : Zustand) : Prop :=
  schritt d s = some s'

/-- A realised byte step: actual fetch, decode and `schritt` succeeded. -/
def byteRealisiert (s s' : Zustand) : Prop :=
  byteschritt s = .weiter s'

/-- A realised step had a valid decode length. -/
theorem realisiert_laenge_ok (d : Decodiert) (s s' : Zustand)
    (hstep : istRealisiert d s s') : laengeOk d.laenge = true := by
  unfold istRealisiert at hstep
  match hm : laengeOk d.laenge with
  | true => rfl
  | false =>
    rw [schritt_laenge_verweigert d s hm] at hstep
    cases hstep

/-! ## 1. Byte-step decomposition: a realised byte step is a fetched `schritt`. -/

/-- A realised byte step runs the existing `schritt` on a fetched instruction. -/
theorem byte_aus_weiter (s s' : Zustand)
    (h : byteRealisiert s s') :
    ∃ d rest, fetchDekodiert s = some (d, rest) ∧ schritt d s = some s' := by
  unfold byteRealisiert byteschritt at h
  match hf : fetchDekodiert s with
  | none =>
    simp only [hf] at h
    cases h
  | some pr =>
    obtain ⟨d, rest⟩ := pr
    match hs : schritt d s with
    | none =>
      simp only [hf, hs] at h
      cases h
    | some s'' =>
      simp only [hf, hs] at h
      cases h
      exact ⟨d, rest, rfl, hs⟩

/- CUTS:
    - Skeleton only: realised predicates plus the length fact.
-/

#print axioms realisiert_laenge_ok
#print axioms byte_aus_weiter

end Gabbro.Grammatik.X86
