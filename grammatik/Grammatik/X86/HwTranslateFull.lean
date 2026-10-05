/-
  File:      Grammatik/X86/HwTranslateFull.lean
  Subject:   Full translation: large pages and per-access SMEP/SMAP inside the walk-or-TLB join.

  Lane 1321: follow-up of lanes 1297 (`HwPagingLarge.lean`) and 1299 (`HwTranslate.lean`).
  The join of 1299 refuses large pages and SMEP/SMAP per-access semantics; per-entry
  permission caching stays a stated exception there. This file instantiates the walk-or-TLB
  join with the full walk `seitenGangGross` (large pages, per-access SMEP/SMAP+EFLAGS.AC),
  proves the flat-model bridge for it, and closes permission caching exactly: a hit reuses
  the cached rights until INVLPG/CR3-write. Non-canonical addresses resolve to none before
  any walk. Reuses the accepted definitions unchanged (lifted, never redefined).
-/
import Grammatik.X86.HwPagingLarge
import Grammatik.X86.HwTranslate

namespace Gabbro.Grammatik.X86

/-! ## 1. The full join: canonical-first walk-or-TLB over `seitenGangGross`.

  A hit answers from the cache with NO rights re-check (this IS the caching rule, closed
  exactly in §3); a miss runs the request's OWN walk, so per-access SMEP/SMAP and large-page
  rules apply inside the join. Non-canonical addresses answer `none` before any walk or
  cache look-up: #GP precedes translation (silicon: canonical check first, named assumption).
-/

/-- Joined full resolution: canonical first, hit from cache, miss from the full walk. -/
def uebersetzeVoll (gst : GrossSteuerung) (tab : Nat → Wort)
    (tlb : List TlbEintrag) (q : SeitenAnfrage) : Option Nat :=
  if !istKanonischNat q.linear then none
  else
    match tlbSuche tlb (q.linear / 4096) with
    | some r => some (r * 4096 + q.linear % 4096)
    | none =>
      match (seitenGangGross gst tab q).1 with
      | .ok phys => some phys
      | _ => none

/- CUTS:
   Skeleton: the joined resolution `uebersetzeVoll` only. Fresh/stale agreement, INVLPG/CR3
   effects, flat bridge, permission-caching closure, machine connection and witness follow.
   NOT proved: everything above; no hardware correspondence beyond self-consistency.
-/

#print axioms uebersetzeVoll

end Gabbro.Grammatik.X86
