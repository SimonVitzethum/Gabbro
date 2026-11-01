module

public import Grammatik.Bausteine.Schablonen.ZeugeTorModell
public import Grammatik.Kern.Semantik.Syscall.Syscall
public import Grammatik.Bausteine.Schablonen.SchablonenOhneLibc.Teil1
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section

namespace Gabbro.Grammatik
namespace OhneLibc
section Region

/-- **What `N571` makes of the contract.** An index `i` the checker admits through the bound
    name (`i + 1 <= n`, `passt(i, 1, clause)` in `m1.rs`) addresses a byte inside the handed-over
    region, and a byte of NO other region live at the call -- the store `r[i] = v` the emitter
    writes touches the new memory and nothing else. -/
theorem region_zugriff (lebend : List Region) (n : Nat) (r : Region)
    (h : RegionVertrag lebend n r) (i : Nat) (hi : i + 1 ≤ n) :
    r.enthaelt (r.basis + i) ∧ ∀ s ∈ lebend, ¬ s.enthaelt (r.basis + i) := by
  obtain ⟨hn, hd⟩ := h
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  intro s hs ⟨h1, h2⟩
  rcases hd s hs with h3 | h3 <;> omega

/-- The premise `hi` is not decoration: the byte just past the extent may belong to the next
    region -- a region of 4096 bytes at 4096 and one right behind it at 8192. -/
theorem region_zugriff_grenze :
    RegionVertrag [⟨8192, 4096⟩] 4096 ⟨4096, 4096⟩ ∧
    (⟨8192, 4096⟩ : Region).enthaelt (4096 + 4096) := by
  refine ⟨⟨Nat.le_refl _, ?_⟩, ⟨Nat.le_refl _, by decide⟩⟩
  intro s hs
  simp only [List.mem_singleton] at hs
  subst hs
  left; decide

/-! ### The witness: a mapping gate's table (`ENOMEM = 12`, `EINVAL = 22`), one word of each kind,
    and a 4096-byte region beside a live one -/

def regionTab : FehlerTabelle (Fin 2) := [(12, 0), (22, 1)]

/-- **Witness for `tor_region`, `tor_region_adresse`, `tor_region_fehler_kein_zeiger` and
    `region_zugriff`**, ALL premises jointly: the word `0x7f0000000000` is that address, `-12`
    is reason `0`, `0` and `-13` (an errno the table does not admit) are the stop; and the byte
    at index 4095 of a 4096-byte region at `0x7f0000000000` lies inside it and outside a live
    region just below it. -/
theorem tor_region_zeuge :
    regionStumpf regionTab 0x7f0000000000 = .ok 0x7f0000000000 ∧
    regionStumpf regionTab (-12) = .why 0 ∧
    regionStumpf regionTab 0 = .unerwartet 0 ∧
    regionStumpf regionTab (-13) = .unerwartet (-13) ∧
    regionStumpf regionTab 0x7f0000000000 =
      alsAdresse (dekodiere regionTab 1 wortMax 0x7f0000000000) ∧
    ((0x7f0000000000 : Nat) : Int) = 0x7f0000000000 ∧ 1 ≤ (0x7f0000000000 : Nat) ∧
    regionStumpf regionTab (-12) ≠ .ok 0 ∧
    ((⟨0x7f0000000000, 4096⟩ : Region).enthaelt (0x7f0000000000 + 4095) ∧
      ∀ s ∈ [(⟨0x7effffff0000, 0x10000⟩ : Region)],
        ¬ s.enthaelt (0x7f0000000000 + 4095)) := by
  have hv : RegionVertrag [⟨0x7effffff0000, 0x10000⟩] 4096 ⟨0x7f0000000000, 4096⟩ := by
    refine ⟨Nat.le_refl _, ?_⟩
    intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    right; decide
  exact ⟨by decide, by decide, by decide, by decide,
    tor_region regionTab _ (by decide),
    (tor_region_adresse regionTab 0x7f0000000000 0x7f0000000000 (by decide)).1,
    (tor_region_adresse regionTab 0x7f0000000000 0x7f0000000000 (by decide)).2,
    tor_region_fehler_kein_zeiger regionTab (-12) (by decide) 0,
    region_zugriff _ 4096 _ hv 4095 (by decide)⟩

end Region

end OhneLibc

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.OhneLibc.nie_tor_kehrt_nicht_zurueck
#print axioms Gabbro.Grammatik.OhneLibc.nie_tor_halt_benannt
#print axioms Gabbro.Grammatik.OhneLibc.nie_tor_zeuge
#print axioms Gabbro.Grammatik.OhneLibc.start_nolibc
#print axioms Gabbro.Grammatik.OhneLibc.start_nolibc_zeuge
#print axioms Gabbro.Grammatik.OhneLibc.tor_fehlbar
#print axioms Gabbro.Grammatik.OhneLibc.tor_fehlbar_zeuge
#print axioms Gabbro.Grammatik.OhneLibc.tor_region
#print axioms Gabbro.Grammatik.OhneLibc.tor_region_adresse
#print axioms Gabbro.Grammatik.OhneLibc.region_zugriff
#print axioms Gabbro.Grammatik.OhneLibc.tor_region_zeuge
#print axioms Gabbro.Grammatik.OhneLibc.start_nolibc_haken
#print axioms Gabbro.Grammatik.OhneLibc.start_nolibc_haken_zeuge
