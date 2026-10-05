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

/-! ## 2. Fresh runs the full walk; stale hits ignore it.

  The hit case reuses the lane-1285 shape (lifted to requests); the miss case runs the
  request's OWN full walk, so large-page and per-access SMEP/SMAP rules apply inside
  the join. Non-canonical requests resolve to none before any walk or cache look-up.
-/

/-- HIT (stale rule, full walk): a hit answers from the cache, whatever the walk and the
    tables now say. No rights are re-checked: this IS the permission-caching rule. -/
theorem uebersetzeVoll_trifft (gst : GrossSteuerung) (tab : Nat → Wort)
    (tlb : List TlbEintrag) (q : SeitenAnfrage) (r : Nat)
    (hkan : istKanonischNat q.linear = true)
    (hHit : tlbSuche tlb (q.linear / 4096) = some r) :
    uebersetzeVoll gst tab tlb q = some (r * 4096 + q.linear % 4096) := by
  unfold uebersetzeVoll
  rw [hkan]
  simp [hHit]

/-- STALE independence: on a hit the tables AND the control are never consulted --
    two table states and two control states resolve identically. -/
theorem uebersetzeVoll_stal_unabhaengig (gst gst' : GrossSteuerung)
    (tab tab' : Nat → Wort) (tlb : List TlbEintrag) (q : SeitenAnfrage)
    (r : Nat)
    (hkan : istKanonischNat q.linear = true)
    (hHit : tlbSuche tlb (q.linear / 4096) = some r) :
    uebersetzeVoll gst tab tlb q = uebersetzeVoll gst' tab' tlb q := by
  rw [uebersetzeVoll_trifft gst tab tlb q r hkan hHit,
    uebersetzeVoll_trifft gst' tab' tlb q r hkan hHit]

/-- FRESH: miss plus full-walk success is the walk frame. -/
theorem uebersetzeVoll_frisch_ok (gst : GrossSteuerung) (tab : Nat → Wort)
    (tlb : List TlbEintrag) (q : SeitenAnfrage) (phys : Nat)
    (hkan : istKanonischNat q.linear = true)
    (hMiss : tlbSuche tlb (q.linear / 4096) = none)
    (h : (seitenGangGross gst tab q).1 = .ok phys) :
    uebersetzeVoll gst tab tlb q = some phys := by
  unfold uebersetzeVoll
  rw [hkan]
  simp [hMiss, h]

/-- FRESH inversion: an admitted fresh resolution comes from the full walk. -/
theorem uebersetzeVoll_frisch_braucht_gang (gst : GrossSteuerung)
    (tab : Nat → Wort) (tlb : List TlbEintrag) (q : SeitenAnfrage)
    (phys : Nat)
    (hkan : istKanonischNat q.linear = true)
    (hMiss : tlbSuche tlb (q.linear / 4096) = none)
    (h : uebersetzeVoll gst tab tlb q = some phys) :
    (seitenGangGross gst tab q).1 = .ok phys := by
  unfold uebersetzeVoll at h
  rw [hkan] at h
  simp [hMiss] at h
  generalize heq : (seitenGangGross gst tab q).1 = e at h ⊢
  cases e with
  | ok p =>
    simp at h
    cases h
    rfl
  | seitenFehler a c => simp at h
  | gpFehler a => simp at h
  | grossVerweigert a => simp at h
  | steuerVerweigert => simp at h

/-- #GP BEFORE ANY WALK (pure): a non-canonical request resolves to none, even on a
    hit. The cache is never consulted. -/
theorem uebersetzeVoll_nichtkanonisch (gst : GrossSteuerung)
    (tab : Nat → Wort) (tlb : List TlbEintrag) (q : SeitenAnfrage)
    (hk : istKanonischNat q.linear = false) :
    uebersetzeVoll gst tab tlb q = none := by
  unfold uebersetzeVoll
  rw [hk]
  simp

/-- The dispatcher faults #GP on a non-canonical address before any table is read. -/
theorem gangGross_nichtkanonisch_gp (gst : GrossSteuerung) (q : SeitenAnfrage)
    (e3 e2 e1 e0 : SeitenEintrag)
    (hk : istKanonischNat q.linear = false) :
    gangGross gst q e3 e2 e1 e0 = .gpFehler q.linear := by
  cases hg : e2.gross with
  | true =>
    rw [gangGross_bei_1G gst q e3 e2 e1 e0 hg]
    simp [gangGross1G, hk]
  | false =>
    rw [gangGross_bei_2M gst q e3 e2 e1 e0 hg]
    simp [gangGross2M, hk]

/-- The full walk faults #GP on a non-canonical address whatever the tables say:
    two table states agree without consulting either. -/
theorem seitenGangGross_nichtkanonisch_gp (gst : GrossSteuerung)
    (tab tab' : Nat → Wort) (q : SeitenAnfrage)
    (hk : istKanonischNat q.linear = false) :
    (seitenGangGross gst tab q).1 = .gpFehler q.linear ∧
      (seitenGangGross gst tab' q).1 = .gpFehler q.linear := by
  simp only [seitenGangGross_fst]
  exact ⟨gangGross_nichtkanonisch_gp gst q _ _ _ _ hk,
    gangGross_nichtkanonisch_gp gst q _ _ _ _ hk⟩

/-- Where lane 1299 applied (no large leaves, SMEP/SMAP disarmed), the full walk IS the
    lane-1299 walk probe: the instantiated `walkLesen` answers the same frame. The old
    walk is lifted, never redefined. -/
theorem voll_walkLesen_gleich (st : SeitenSteuerung) (ac : Bool)
    (tab : Nat → Wort) (s phys : Nat)
    (h1 : st.smep = false) (h2 : st.smap = false)
    (hg2 : (seitenTabEintrag tab
        (seitenTabEintrag tab st.cr3 (gangIndexPML4 (s * 4096))).rahmen
        (gangIndexPDPT (s * 4096))).gross = false)
    (hg1 : (seitenTabEintrag tab
        (seitenTabEintrag tab
          (seitenTabEintrag tab st.cr3 (gangIndexPML4 (s * 4096))).rahmen
          (gangIndexPDPT (s * 4096))).rahmen
        (gangIndexPD (s * 4096))).gross = false)
    (h : (seitenGangGross ⟨st, ac⟩ tab ⟨s * 4096, false, true, false⟩).1 =
      .ok phys) :
    walkLesen st tab s = some (phys / 4096) := by
  have hg : (seitenGangGross ⟨st, ac⟩ tab ⟨s * 4096, false, true, false⟩).1 =
      (seitenGang st tab ⟨s * 4096, false, true, false⟩).1 :=
    seitenGangGross_gleich ⟨st, ac⟩ tab ⟨s * 4096, false, true, false⟩
      h1 h2 hg2 hg1
  rw [hg] at h
  exact walkLesen_ok st tab s phys h

/- CUTS:
   Proved: §1 joined resolution; §2 fresh/stale agreement, #GP-before-walk (pure and
   walk-level), 1299 probe correspondence where the walks agree.
   Follow: INVLPG/CR3 effects, flat bridge, permission-caching closure, machine
   connection, joint witness.
   NOT proved: everything above; no hardware correspondence beyond self-consistency.
-/

#print axioms uebersetzeVoll
#print axioms uebersetzeVoll_trifft
#print axioms uebersetzeVoll_stal_unabhaengig
#print axioms uebersetzeVoll_frisch_ok
#print axioms uebersetzeVoll_frisch_braucht_gang
#print axioms uebersetzeVoll_nichtkanonisch
#print axioms gangGross_nichtkanonisch_gp
#print axioms seitenGangGross_nichtkanonisch_gp
#print axioms voll_walkLesen_gleich

end Gabbro.Grammatik.X86
