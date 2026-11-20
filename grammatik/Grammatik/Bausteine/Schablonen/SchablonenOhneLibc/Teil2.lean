module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetSem
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem
public import Grammatik.Nebenlaeufigkeit.Sperren.Sources
public import Grammatik.Zielsatz.Kern.Akzeptiert
public import Grammatik.Zielsatz.Kern.Beweis
public import Grammatik.Zielsatz.Atomar.BeweisAtomar
public import Grammatik.Zielsatz.Kern.Spec
public import Grammatik.Kern.Semantik.Syscall.Syscall
public import Grammatik.Bausteine.Schablonen.SchablonenOhneLibc.Teil1
public import Grammatik.Bausteine.Schablonen.SchablonenOhneLibc.Teil1a
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

end Region

end OhneLibc

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.OhneLibc.nie_tor_kehrt_nicht_zurueck
#print axioms Gabbro.Grammatik.OhneLibc.nie_tor_halt_benannt
#print axioms Gabbro.Grammatik.OhneLibc.start_nolibc
#print axioms Gabbro.Grammatik.OhneLibc.tor_fehlbar
#print axioms Gabbro.Grammatik.OhneLibc.tor_region
#print axioms Gabbro.Grammatik.OhneLibc.tor_region_adresse
#print axioms Gabbro.Grammatik.OhneLibc.region_zugriff
#print axioms Gabbro.Grammatik.OhneLibc.start_nolibc_haken
