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

/-! ## 1. The join agrees with both accepted evaluators.

  The stale-entry rule of lane 1285 (`tlbAufloesung_trifft`) and the
  miss rule (`tlbAufloesung_verfehlt`) lift unchanged: the walk is
  only instantiated, never redefined. -/

/-- A walk success answers through the instantiated function. -/
theorem walkLesen_ok (st : SeitenSteuerung) (tab : Nat → Wort)
    (s phys : Nat)
    (h : (seitenGang st tab ⟨s * 4096, false, true, false⟩).1 =
      .ok phys) :
    walkLesen st tab s = some (phys / 4096) := by
  simp [walkLesen, h]

/-- A walk without success is a TLB miss (`none`). -/
theorem walkLesen_keinOk (st : SeitenSteuerung) (tab : Nat → Wort)
    (s : Nat)
    (h : ¬ ∃ phys,
      (seitenGang st tab ⟨s * 4096, false, true, false⟩).1 =
        .ok phys) :
    walkLesen st tab s = none := by
  simp only [walkLesen]
  cases e : (seitenGang st tab ⟨s * 4096, false, true, false⟩).1 with
  | ok phys => exact absurd ⟨phys, e⟩ h
  | seitenFehler a c => rfl
  | gpFehler a => rfl
  | grossVerweigert a => rfl
  | steuerVerweigert => rfl

/-- STALE (lane-1285 rule, joined): a hit answers from the cache,
    whatever the walk (and the tables) now say. -/
theorem uebersetze_trifft (st : SeitenSteuerung) (tab : Nat → Wort)
    (tlb : List TlbEintrag) (a : Adresse) (r : Nat)
    (hHit : tlbSuche tlb (seitenNr a) = some r) :
    uebersetzeMitTlb st tab tlb a = some (physAddr r a) :=
  tlbAufloesung_trifft tlb (walkLesen st tab) a r hHit

/-- FRESH (lane-1285 rule, joined): a miss runs the walk. -/
theorem uebersetze_verfehlt (st : SeitenSteuerung) (tab : Nat → Wort)
    (tlb : List TlbEintrag) (a : Adresse) (r : Nat)
    (hMiss : tlbSuche tlb (seitenNr a) = none)
    (hWalk : walkLesen st tab (seitenNr a) = some r) :
    uebersetzeMitTlb st tab tlb a = some (physAddr r a) :=
  tlbAufloesung_verfehlt tlb (walkLesen st tab) a r hMiss hWalk

/-! ## 2. Fresh accesses run the walk; stale hits ignore it.

  The instantiated walk probes the page base (`s * 4096`); a
  page-aligned address names the same linear byte there. -/

/-- A page-aligned address is its page number times the base. -/
theorem seitenNr_mal_basis (a : Adresse) (h : seitenOffset a = 0) :
    a.toNat = seitenNr a * 4096 := by
  simp only [seitenNr, seitenOffset, tlbSeitenGroesse] at h ⊢
  omega

/-- The instantiated walk answers a page-aligned user read. -/
theorem walkLesen_ausgerichtet (st : SeitenSteuerung)
    (tab : Nat → Wort) (a : Adresse) (phys : Nat)
    (hAlign : seitenOffset a = 0)
    (h : (seitenGang st tab ⟨a.toNat, false, true, false⟩).1 =
      .ok phys) :
    walkLesen st tab (seitenNr a) = some (phys / 4096) := by
  have hlin : seitenNr a * 4096 = a.toNat :=
    (seitenNr_mal_basis a hAlign).symm
  rw [← hlin] at h
  exact walkLesen_ok st tab (seitenNr a) phys h

/-- FRESH joined access: miss plus walk success is the walk frame. -/
theorem uebersetze_frisch_ok (st : SeitenSteuerung) (tab : Nat → Wort)
    (tlb : List TlbEintrag) (a : Adresse) (phys : Nat)
    (hAlign : seitenOffset a = 0)
    (hMiss : tlbSuche tlb (seitenNr a) = none)
    (h : (seitenGang st tab ⟨a.toNat, false, true, false⟩).1 =
      .ok phys) :
    uebersetzeMitTlb st tab tlb a = some (physAddr (phys / 4096) a) :=
  uebersetze_verfehlt st tab tlb a (phys / 4096) hMiss
    (walkLesen_ausgerichtet st tab a phys hAlign h)

/-- FRESH inversion: an admitted fresh access comes from the walk. -/
theorem uebersetze_frisch_braucht_gang (st : SeitenSteuerung)
    (tab : Nat → Wort) (tlb : List TlbEintrag) (a p : Adresse)
    (hMiss : tlbSuche tlb (seitenNr a) = none)
    (h : uebersetzeMitTlb st tab tlb a = some p) :
    ∃ r, walkLesen st tab (seitenNr a) = some r ∧
      p = physAddr r a := by
  simp only [uebersetzeMitTlb, tlbAufloesung, hMiss] at h
  cases e : walkLesen st tab (seitenNr a) with
  | some r =>
    simp only [e] at h
    cases h
    exact ⟨r, rfl, rfl⟩
  | none =>
    simp only [e] at h
    cases h

/-- STALE independence: on a hit the tables are never consulted --
    two table states resolve identically. -/
theorem uebersetze_stal_unabhaengig (st : SeitenSteuerung)
    (tab tab' : Nat → Wort) (tlb : List TlbEintrag) (a : Adresse)
    (r : Nat) (hHit : tlbSuche tlb (seitenNr a) = some r) :
    uebersetzeMitTlb st tab tlb a =
      uebersetzeMitTlb st tab' tlb a := by
  rw [uebersetze_trifft st tab tlb a r hHit,
    uebersetze_trifft st tab' tlb a r hHit]

/-! ## 3. INVLPG and CR3-write effects over the joined resolution.

  Both lift lane 1285 unchanged (Vol 3A Section 5.10.4.1: INVLPG
  drops the page of its operand; MOV to CR3 with PCIDE = 0 drops
  every non-global entry, which here is every entry). -/

/-- After INVLPG of its page the joined access re-walks. -/
theorem uebersetze_nach_invlpg (st : SeitenSteuerung)
    (tab : Nat → Wort) (tlb : List TlbEintrag) (a : Adresse)
    (r : Nat)
    (hWalk : walkLesen st tab (seitenNr a) = some r) :
    uebersetzeMitTlb st tab (tlbEntfernen tlb (seitenNr a)) a =
      some (physAddr r a) :=
  tlbNachEntfernen_geht_durch tlb (walkLesen st tab) a r hWalk

/-- A CR3 write empties the joined core TLB (PCID off). -/
theorem uebersetze_cr3_leert (tlb : List TlbEintrag) :
    tlbCr3Spuelung tlb = [] :=
  tlbCr3Spuelung_leert tlb

/-- LOCALITY: invalidating on core `c` leaves core `d` alone
    (software shootdown stays a user-logic duty). -/
theorem uebersetze_invlpg_lokal (tlb : Nat → List TlbEintrag)
    (c d s : Nat) (h : d ≠ c) :
    (fun e => if e = c then tlbEntfernen (tlb c) s else tlb e) d =
      tlb d :=
  tlbEntfernen_lokal tlb c d s h

/-! ## 4. Bridge to the flat byte-permission model.

  A FRESH walk-or-TLB admission meets the flat permission of the
  physical byte (the lane-1283 obligation `FlachStimmt`, which the OS
  establishes as user logic when it installs its tables). The STALE
  hit is the proved exception: §2 shows it never consults the walk,
  and §6 exhibits tables where the walk faults while the stale entry
  still admits. -/

/-- FRESH read: miss plus walk success resolves through the walk
    AND meets the flat read permission. -/
theorem uebersetze_frisch_flach_lesbar (st : SeitenSteuerung)
    (tab : Nat → Wort) (m : Speicher) (tlb : List TlbEintrag)
    (a : Adresse) (phys : Nat)
    (hAlign : seitenOffset a = 0)
    (hMiss : tlbSuche tlb (seitenNr a) = none)
    (h : (seitenGang st tab ⟨a.toNat, false, true, false⟩).1 =
      .ok phys)
    (hcons : FlachStimmt st tab m) :
    uebersetzeMitTlb st tab tlb a = some (physAddr (phys / 4096) a) ∧
      m.lesbar (BitVec.ofNat 64 phys) = true :=
  ⟨uebersetze_frisch_ok st tab tlb a phys hAlign hMiss h,
    gangOk_flach_lesbar st tab m _ phys hcons h rfl⟩

/-- FRESH write: miss plus walk success resolves through the walk
    AND meets the flat write permission. The resolution runs the
    read probe at the page base; the permission comes from the write
    walk itself (the two may differ; both premises are stated). -/
theorem uebersetze_frisch_flach_schreibbar (st : SeitenSteuerung)
    (tab : Nat → Wort) (m : Speicher) (tlb : List TlbEintrag)
    (a : Adresse) (physR phys : Nat)
    (hAlign : seitenOffset a = 0)
    (hMiss : tlbSuche tlb (seitenNr a) = none)
    (hRead : (seitenGang st tab ⟨a.toNat, false, true, false⟩).1 =
      .ok physR)
    (h : (seitenGang st tab ⟨a.toNat, true, true, false⟩).1 =
      .ok phys)
    (hcons : FlachStimmt st tab m) :
    uebersetzeMitTlb st tab tlb a = some (physAddr (physR / 4096) a) ∧
      m.schreibbar (BitVec.ofNat 64 phys) = true :=
  ⟨uebersetze_frisch_ok st tab tlb a physR hAlign hMiss hRead,
    gangOk_flach_schreibbar st tab m _ phys hcons h rfl⟩

/- CUTS (skeleton):
   Proved here: the join definitions `walkLesen`/`uebersetzeMitTlb`.
   NOT proved yet: stale/fresh agreement, INVLPG/CR3 effects, flat
   bridge, adapter plug, extended steps, witness.
-/

#print axioms walkLesen
#print axioms uebersetzeMitTlb

end Gabbro.Grammatik.X86
