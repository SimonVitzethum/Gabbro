/-
  File:      Grammatik/X86/HwTranslate.lean
  Subject:   Page walk joined with the TLB and the flat memory model.

  Lane 1299: follow-up of lane 1283 (`HwPaging.lean`, the 4-level walk
  with no TLB) and lane 1285 (`HwSegTlb.lean`, the TLB over a walk
  PARAMETER). Join them: the TLB instantiated with the page walk as
  its translation function, INVLPG and CR3-write effects over it, the
  stale-entry rule stated as in 1285, and the bridge to the flat
  byte-permission model of `Speicher.lean` (fresh walk-or-TLB access
  agrees with the flat permission; the stale TLB hit is the proved
  exception). Reuses the accepted definitions unchanged (lifted,
  never redefined). No silicon correspondence is claimed (see CUTS).

  Silicon provenance (Intel SDM 325462-093US, Sept 2026, clone-local
  text extract): INVLPG invalidates the TLB entries for the page of
  its operand (Vol 2 INVLPG; Vol 3A Section 5.10.4.1); with
  CR4.PCIDE = 0 the current PCID is 000H; MOV to CR3 then
  invalidates all TLB entries for PCID 000H except global pages
  (Vol 3A Section 5.10.4.1). The model runs with PCID off and no
  global entries (lane 1285 `tlbGlobal`), so a CR3 write empties the
  core TLB.
-/
import Grammatik.X86.HwPaging
import Grammatik.X86.HwSegTlb

namespace Gabbro.Grammatik.X86

/-- The page walk as a TLB translation function (owned by lane 1283,
    instantiated here): page `s` is read through its first byte as a
    user read; success names the frame, any other outcome is a walk
    miss (`none`). Permission checks stay inside `seitenGang`. -/
def walkLesen (st : SeitenSteuerung) (tab : Nat → Wort) :
    SeitenDurchlauf :=
  fun s =>
    match (seitenGang st tab ⟨s * 4096, false, true, false⟩).1 with
    | .ok phys => some (phys / 4096)
    | _ => none

/-- Joined resolution: the lane-1285 TLB instantiated with the
    lane-1283 page walk. A hit answers from the cache (even a stale
    one); a miss runs the walk. -/
def uebersetzeMitTlb (st : SeitenSteuerung) (tab : Nat → Wort)
    (tlb : List TlbEintrag) (a : Adresse) : Option Adresse :=
  tlbAufloesung tlb (walkLesen st tab) a

/- CUTS (skeleton):
   Proved here: the join definitions `walkLesen`/`uebersetzeMitTlb`.
   NOT proved yet: stale/fresh agreement, INVLPG/CR3 effects, flat
   bridge, adapter plug, extended steps, witness.
-/

#print axioms walkLesen
#print axioms uebersetzeMitTlb

end Gabbro.Grammatik.X86
