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

/-! ## 3. Permission caching closed exactly.

  The precise closure is three proved facts: (1) a hit reuses the cached frame and its
  rights for EVERY current table and control state, including states whose walk now
  faults (`uebersetzeVoll_stal_unabhaengig`); (2) INVLPG and CR3-write remove the entry
  on the acting core only; (3) after removal the current walk decides again. The stale
  exceptions of lane 1299 become the closed rule plus its reached witnesses below:
  a revoked mapping and armed SMAP/SMEP fault while the stale hit still admits.
-/

/-- After INVLPG of its page the full resolution re-walks into the walk success. -/
theorem uebersetzeVoll_nach_invlpg (gst : GrossSteuerung) (tab : Nat → Wort)
    (tlb : List TlbEintrag) (q : SeitenAnfrage) (phys : Nat)
    (hkan : istKanonischNat q.linear = true)
    (h : (seitenGangGross gst tab q).1 = .ok phys) :
    uebersetzeVoll gst tab (tlbEntfernen tlb (q.linear / 4096)) q =
      some phys := by
  have hMiss : tlbSuche (tlbEntfernen tlb (q.linear / 4096))
      (q.linear / 4096) = none :=
    tlbEntfernen_sucht_verfehlt tlb (q.linear / 4096)
  exact uebersetzeVoll_frisch_ok gst tab _ q phys hkan hMiss h

/-- After INVLPG of its page a walk fault resolves to none. -/
theorem uebersetzeVoll_nach_invlpg_fehl (gst : GrossSteuerung)
    (tab : Nat → Wort) (tlb : List TlbEintrag) (q : SeitenAnfrage)
    (a : Nat) (code : PfFehlerCode)
    (hkan : istKanonischNat q.linear = true)
    (h : (seitenGangGross gst tab q).1 = .seitenFehler a code) :
    uebersetzeVoll gst tab (tlbEntfernen tlb (q.linear / 4096)) q = none := by
  have hMiss : tlbSuche (tlbEntfernen tlb (q.linear / 4096))
      (q.linear / 4096) = none :=
    tlbEntfernen_sucht_verfehlt tlb (q.linear / 4096)
  unfold uebersetzeVoll
  rw [hkan]
  simp [hMiss, h]

/-- A CR3 write empties the joined core TLB (PCID off): lifted unchanged. -/
theorem uebersetzeVoll_cr3_leert (tlb : List TlbEintrag) :
    tlbCr3Spuelung tlb = [] :=
  tlbCr3Spuelung_leert tlb

/-- LOCALITY: invalidating on core `c` leaves core `d` alone (software shootdown
    stays a user-logic duty). -/
theorem uebersetzeVoll_invlpg_lokal (tlb : Nat → List TlbEintrag)
    (c d s : Nat) (h : d ≠ c) :
    (fun e => if e = c then tlbEntfernen (tlb c) s else tlb e) d =
      tlb d :=
  tlbEntfernen_lokal tlb c d s h

/-! ### Stale-rights witnesses: the walk faults, the cached rights still admit.

  Changed tables: `witGrossTab` with the PD[0] 2 MiB leaf cleared (the mapping
  revocation, mirroring the lane-1299 witness shape on the large page). -/

/-- Witness tables: the large-page mapping revoked (PD[0] leaf cleared). -/
def witVollTab1 : Nat → Wort :=
  fun n => if n = 42 * 512 + 0 then 0 else witGrossTab n

/-- The revoked walk faults non-present on a supervisor read. -/
theorem witVollTab1_pf :
    (seitenGangGross witGrossSteuer witVollTab1 ⟨0, false, false, false⟩).1 =
      .seitenFehler 0 ⟨false, false, false, false, false⟩ := by
  decide

/-- STALE RIGHTS 1 (revoked mapping): the walk faults, the cached frame still admits. -/
theorem witVoll_stal_revoke :
    uebersetzeVoll witGrossSteuer witVollTab1 [⟨0, 512⟩]
      ⟨0, false, false, false⟩ = some 2097152 := by
  decide

/-- STALE RIGHTS 2 (SMAP): the supervisor read faults under armed SMAP
    (`wit_gross_smap`), the stale hit still admits with cached rights. -/
theorem witVoll_stal_smap :
    uebersetzeVoll witGrossSteuerSmap witGrossTab [⟨0, 512⟩]
      ⟨0, false, false, false⟩ = some 2097152 := by
  decide

/-- STALE RIGHTS 3 (SMEP): the supervisor fetch faults under armed SMEP
    (`wit_gross_smep`), the stale hit still admits with cached rights. -/
theorem witVoll_stal_smep :
    uebersetzeVoll witGrossSteuerSmep witGrossTab [⟨0, 512⟩]
      ⟨0, false, false, true⟩ = some 2097152 := by
  decide

/-- After INVLPG the revoked mapping re-faults: the stale use is over. -/
theorem witVoll_nach_invlpg_fehl :
    uebersetzeVoll witGrossSteuer witVollTab1 (tlbEntfernen [⟨0, 512⟩] 0)
      ⟨0, false, false, false⟩ = none := by
  decide

/-- #GP beats a hit: a cached entry for the non-canonical page never answers. -/
theorem witVoll_nichtkanonisch_hit :
    uebersetzeVoll witGrossSteuer witGrossTab [⟨2 ^ 35, 7⟩]
      ⟨2 ^ 47, false, true, false⟩ = none := by
  decide

/-! ## 4. Bridge to the flat byte-permission model, for the full walk.

  `FlachStimmtGross` is the OS obligation for the FULL walk (user logic, as in lane
  1283): every full-walk-admitted access -- 4 KiB, 2 MiB and 1 GiB leaves,
  SMEP/SMAP-gated -- meets its flat permission at the physical byte. Where the full
  walk agrees with the accepted 4 KiB walk, the lane-1283 obligation transfers
  pointwise; fresh full-join admission meets the flat permission in both directions.
-/

/-- Flat consistency for the full walk: every full-walk-admitted read meets `lesbar`,
    every full-walk-admitted write meets `schreibbar`, at the physical byte -- for
    every leaf size and under armed SMEP/SMAP. -/
def FlachStimmtGross (gst : GrossSteuerung) (tab : Nat → Wort)
    (m : Speicher) : Prop :=
  ∀ (q : SeitenAnfrage) (phys : Nat),
    (seitenGangGross gst tab q).1 = .ok phys →
    (q.schreiben = true → m.schreibbar (BitVec.ofNat 64 phys) = true) ∧
    (q.schreiben = false → m.lesbar (BitVec.ofNat 64 phys) = true)

/-- A full-walk-admitted write meets the flat write permission. -/
theorem gangGross_flach_schreibbar (gst : GrossSteuerung) (tab : Nat → Wort)
    (m : Speicher) (q : SeitenAnfrage) (phys : Nat)
    (hcons : FlachStimmtGross gst tab m)
    (h : (seitenGangGross gst tab q).1 = .ok phys)
    (hs : q.schreiben = true) :
    m.schreibbar (BitVec.ofNat 64 phys) = true :=
  (hcons q phys h).1 hs

/-- A full-walk-admitted read meets the flat read permission. -/
theorem gangGross_flach_lesbar (gst : GrossSteuerung) (tab : Nat → Wort)
    (m : Speicher) (q : SeitenAnfrage) (phys : Nat)
    (hcons : FlachStimmtGross gst tab m)
    (h : (seitenGangGross gst tab q).1 = .ok phys)
    (hs : q.schreiben = false) :
    m.lesbar (BitVec.ofNat 64 phys) = true :=
  (hcons q phys h).2 hs

/-- TRANSFER (write): where the full walk agrees with the accepted 4 KiB walk, the
    lane-1283 obligation covers the full walk pointwise. Large leaves keep their own
    obligation side. -/
theorem flachGross_aus_flach_schreibbar (st : SeitenSteuerung) (ac : Bool)
    (tab : Nat → Wort) (m : Speicher) (q : SeitenAnfrage) (phys : Nat)
    (hcons : FlachStimmt st tab m)
    (h1 : st.smep = false) (h2 : st.smap = false)
    (hg2 : (seitenTabEintrag tab
        (seitenTabEintrag tab st.cr3 (gangIndexPML4 q.linear)).rahmen
        (gangIndexPDPT q.linear)).gross = false)
    (hg1 : (seitenTabEintrag tab
        (seitenTabEintrag tab
          (seitenTabEintrag tab st.cr3 (gangIndexPML4 q.linear)).rahmen
          (gangIndexPDPT q.linear)).rahmen
        (gangIndexPD q.linear)).gross = false)
    (h : (seitenGangGross ⟨st, ac⟩ tab q).1 = .ok phys)
    (hs : q.schreiben = true) :
    m.schreibbar (BitVec.ofNat 64 phys) = true := by
  have hg : (seitenGangGross ⟨st, ac⟩ tab q).1 =
      (seitenGang st tab q).1 :=
    seitenGangGross_gleich ⟨st, ac⟩ tab q h1 h2 hg2 hg1
  rw [hg] at h
  exact gangOk_flach_schreibbar st tab m q phys hcons h hs

/-- TRANSFER (read): the same for reads. -/
theorem flachGross_aus_flach_lesbar (st : SeitenSteuerung) (ac : Bool)
    (tab : Nat → Wort) (m : Speicher) (q : SeitenAnfrage) (phys : Nat)
    (hcons : FlachStimmt st tab m)
    (h1 : st.smep = false) (h2 : st.smap = false)
    (hg2 : (seitenTabEintrag tab
        (seitenTabEintrag tab st.cr3 (gangIndexPML4 q.linear)).rahmen
        (gangIndexPDPT q.linear)).gross = false)
    (hg1 : (seitenTabEintrag tab
        (seitenTabEintrag tab
          (seitenTabEintrag tab st.cr3 (gangIndexPML4 q.linear)).rahmen
          (gangIndexPDPT q.linear)).rahmen
        (gangIndexPD q.linear)).gross = false)
    (h : (seitenGangGross ⟨st, ac⟩ tab q).1 = .ok phys)
    (hs : q.schreiben = false) :
    m.lesbar (BitVec.ofNat 64 phys) = true := by
  have hg : (seitenGangGross ⟨st, ac⟩ tab q).1 =
      (seitenGang st tab q).1 :=
    seitenGangGross_gleich ⟨st, ac⟩ tab q h1 h2 hg2 hg1
  rw [hg] at h
  exact gangOk_flach_lesbar st tab m q phys hcons h hs

/-- FRESH full-join read: miss plus full-walk success resolves through the walk
    AND meets the flat read permission. -/
theorem uebersetzeVoll_frisch_flach_lesbar (gst : GrossSteuerung)
    (tab : Nat → Wort) (m : Speicher) (tlb : List TlbEintrag)
    (q : SeitenAnfrage) (phys : Nat)
    (hkan : istKanonischNat q.linear = true)
    (hMiss : tlbSuche tlb (q.linear / 4096) = none)
    (h : (seitenGangGross gst tab q).1 = .ok phys)
    (hs : q.schreiben = false)
    (hcons : FlachStimmtGross gst tab m) :
    uebersetzeVoll gst tab tlb q = some phys ∧
      m.lesbar (BitVec.ofNat 64 phys) = true :=
  ⟨uebersetzeVoll_frisch_ok gst tab tlb q phys hkan hMiss h,
    gangGross_flach_lesbar gst tab m q phys hcons h hs⟩

/-- FRESH full-join write: miss plus full-walk success resolves through the walk
    AND meets the flat write permission. -/
theorem uebersetzeVoll_frisch_flach_schreibbar (gst : GrossSteuerung)
    (tab : Nat → Wort) (m : Speicher) (tlb : List TlbEintrag)
    (q : SeitenAnfrage) (phys : Nat)
    (hkan : istKanonischNat q.linear = true)
    (hMiss : tlbSuche tlb (q.linear / 4096) = none)
    (h : (seitenGangGross gst tab q).1 = .ok phys)
    (hs : q.schreiben = true)
    (hcons : FlachStimmtGross gst tab m) :
    uebersetzeVoll gst tab tlb q = some phys ∧
      m.schreibbar (BitVec.ofNat 64 phys) = true :=
  ⟨uebersetzeVoll_frisch_ok gst tab tlb q phys hkan hMiss h,
    gangGross_flach_schreibbar gst tab m q phys hcons h hs⟩

/-- The obligation is inhabited: the all-permissive flat memory meets every full walk,
    so the bridge is never vacuous. -/
theorem flachStimmtGross_allwahr (gst : GrossSteuerung) (tab : Nat → Wort) :
    FlachStimmtGross gst tab allWahrSpeicher := by
  intro q phys h
  exact ⟨fun _ => rfl, fun _ => rfl⟩

/-! ### Witness flat memory: the large pages with their permissions.

  Frames 512..1023 (the 2 MiB page) and frame 262144 (the 1 GiB page) are readable
  and writable; nothing else is. The witnessed large mappings meet it pointwise. -/

/-- Witness flat memory: exactly the two large witness pages permit access. -/
def witVollFlach : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0
    lesbar := fun a =>
      decide (512 ≤ a.toNat / 4096 ∧ a.toNat / 4096 < 1024 ∨
        a.toNat / 4096 = 262144)
    schreibbar := fun a =>
      decide (512 ≤ a.toNat / 4096 ∧ a.toNat / 4096 < 1024 ∨
        a.toNat / 4096 = 262144)
    ausfuehrbar := fun _ => false }

/-- The 2 MiB witness page is flat-readable at its base. -/
theorem witVoll_flach_liest :
    witVollFlach.lesbar (BitVec.ofNat 64 2097152) = true := by
  decide

/-- The 2 MiB witness page is flat-writable at its base. -/
theorem witVoll_flach_schreibt :
    witVollFlach.schreibbar (BitVec.ofNat 64 2097152) = true := by
  decide

/-- The 1 GiB witness page is flat-readable at its base. -/
theorem witVoll_flach_liest_1G :
    witVollFlach.lesbar (BitVec.ofNat 64 (2 ^ 30)) = true := by
  decide

/-! ## 5. Machine connection: adapter plug and extended steps.

  No full translation admits a `HwMaschine` successor: faults have none by construction,
  and accessed/dirty updates touch the tables, which live outside `HwMaschine` (the same
  reason both predecessors refuse). Translation behaviour lives in `HwVollSchritt` over
  machine-plus-extended-control-plus-tables-plus-TLBs, embedding `HwSchritt` exactly.
  Canonicality is a step premise for every table or cache access (fresh, stale, fault):
  #GP precedes the walk AND the cache. Large pages are admitted here (no wholesale
  `grossVerweigert` refusal); a misplaced large page refuses as in lane 1299.
-/

/-- The full-translation adapter: the refused default. No translation admits a machine
    successor state. -/
def adapterVoll : HwAdapter SeitenAnfrage := verweigertAdapter _

/-- The full-translation adapter admits nothing. -/
theorem adapterVoll_verweigert (m : HwMaschine) (c : Nat)
    (q : SeitenAnfrage) :
    adapterVoll.schritt m c q = none := rfl

/-- Full joined state: the coherent machine plus extended control, tables,
    and per-core TLBs. -/
structure VollZustand where
  hw : HwMaschine
  steuer : GrossSteuerung
  tabellen : Nat → Wort
  tlb : Nat → List TlbEintrag

/-- Full joined events: the old events, INVLPG, CR3 write, a fresh walk-through
    access, a stale TLB-hit use, a walk fault, and a non-canonical #GP. -/
inductive VollEreignis where
  | alt : HwEreignis → VollEreignis
  | invlpg : Nat → Adresse → VollEreignis
  | cr3 : Nat → VollEreignis
  | zugriffOk : Nat → SeitenAnfrage → Nat → VollEreignis
  | zugriffAlt : Nat → SeitenAnfrage → Nat → VollEreignis
  | zugriffPf : Nat → SeitenAnfrage → Nat → PfFehlerCode →
      VollEreignis
  | zugriffGp : Nat → SeitenAnfrage → Nat → VollEreignis
  deriving DecidableEq, Repr

/-- One full joined step: the embedded old step (translation state kept), INVLPG /
    CR3 write on one core's TLB, a fresh access (canonical, miss: the full walk runs
    and writes back accessed/dirty), a stale use (canonical, hit: the walk is not
    consulted, tables kept), a walk fault (canonical, miss, self-loop), or a
    non-canonical #GP (the walk equation, self-loop -- the cache is never consulted). -/
inductive HwVollSchritt :
    VollZustand → VollZustand → VollEreignis → Prop where
  | einbettet {s : VollZustand} {m' : HwMaschine} {e : HwEreignis}
      (h : HwSchritt s.hw m' e) :
      HwVollSchritt s ⟨m', s.steuer, s.tabellen, s.tlb⟩ (.alt e)
  | invlpg {s : VollZustand} (c : Nat) (a : Adresse) :
      HwVollSchritt s
        ⟨s.hw, s.steuer, s.tabellen,
          fun d => if d = c then tlbEntfernen (s.tlb c) (seitenNr a)
            else s.tlb d⟩
        (.invlpg c a)
  | cr3 {s : VollZustand} (c : Nat) :
      HwVollSchritt s
        ⟨s.hw, s.steuer, s.tabellen,
          fun d => if d = c then tlbCr3Spuelung (s.tlb c)
            else s.tlb d⟩
        (.cr3 c)
  | frisch {s : VollZustand} {c : Nat} {q : SeitenAnfrage}
      {phys : Nat} {tab' : Nat → Wort}
      (hkan : istKanonischNat q.linear = true)
      (hMiss : tlbSuche (s.tlb c) (q.linear / 4096) = none)
      (h : (seitenGangGross s.steuer s.tabellen q).1 = .ok phys)
      (ht : (seitenGangGross s.steuer s.tabellen q).2 = tab') :
      HwVollSchritt s ⟨s.hw, s.steuer, tab', s.tlb⟩
        (.zugriffOk c q phys)
  | veraltet {s : VollZustand} {c : Nat} {q : SeitenAnfrage}
      {r : Nat}
      (hkan : istKanonischNat q.linear = true)
      (hHit : tlbSuche (s.tlb c) (q.linear / 4096) = some r) :
      HwVollSchritt s s (.zugriffAlt c q r)
  | fehler {s : VollZustand} {c : Nat} {q : SeitenAnfrage}
      {a : Nat} {code : PfFehlerCode}
      (hkan : istKanonischNat q.linear = true)
      (hMiss : tlbSuche (s.tlb c) (q.linear / 4096) = none)
      (h : (seitenGangGross s.steuer s.tabellen q).1 =
        .seitenFehler a code) :
      HwVollSchritt s s (.zugriffPf c q a code)
  | gp {s : VollZustand} {c : Nat} {q : SeitenAnfrage} {a : Nat}
      (h : (seitenGangGross s.steuer s.tabellen q).1 = .gpFehler a) :
      HwVollSchritt s s (.zugriffGp c q a)

/-- FORWARD embedding: every old step is a full joined step. -/
theorem hwVollSchritt_einbettung_vor (s : VollZustand)
    (m' : HwMaschine) (e : HwEreignis)
    (h : HwSchritt s.hw m' e) :
    HwVollSchritt s ⟨m', s.steuer, s.tabellen, s.tlb⟩ (.alt e) :=
  .einbettet h

/-- BACKWARD embedding, exact: an `.alt` step comes only from the old step
    with the same event. -/
theorem hwVollSchritt_alt_invert (s t : VollZustand)
    (e : HwEreignis) (h : HwVollSchritt s t (.alt e)) :
    ∃ m', t.hw = m' ∧ t.tabellen = s.tabellen ∧
      HwSchritt s.hw m' e := by
  cases h with
  | einbettet hstep => exact ⟨_, rfl, rfl, hstep⟩

/-- An `.alt` step over the reached target is the old step. -/
theorem hwVollSchritt_einbettung_zurueck (s : VollZustand)
    (m' : HwMaschine) (e : HwEreignis)
    (h : HwVollSchritt s ⟨m', s.steuer, s.tabellen, s.tlb⟩
      (.alt e)) :
    HwSchritt s.hw m' e := by
  obtain ⟨m'', hm, _, hstep⟩ := hwVollSchritt_alt_invert s _ e h
  subst hm
  exact hstep

/-- A fresh step carries its walk equation. -/
theorem vollZugriffOk_invert_gang (s t : VollZustand) (c : Nat)
    (q : SeitenAnfrage) (phys : Nat)
    (h : HwVollSchritt s t (.zugriffOk c q phys)) :
    (seitenGangGross s.steuer s.tabellen q).1 = .ok phys := by
  cases h with
  | frisch hkan hMiss h ht => exact h

/-- A fresh step carries its miss. -/
theorem vollZugriffOk_invert_miss (s t : VollZustand) (c : Nat)
    (q : SeitenAnfrage) (phys : Nat)
    (h : HwVollSchritt s t (.zugriffOk c q phys)) :
    tlbSuche (s.tlb c) (q.linear / 4096) = none := by
  cases h with
  | frisch hkan hMiss h ht => exact hMiss

/-- A fresh step carries its canonicality. -/
theorem vollZugriffOk_invert_kanon (s t : VollZustand) (c : Nat)
    (q : SeitenAnfrage) (phys : Nat)
    (h : HwVollSchritt s t (.zugriffOk c q phys)) :
    istKanonischNat q.linear = true := by
  cases h with
  | frisch hkan hMiss h ht => exact hkan

/-- A stale step carries its hit: the walk equation is absent. -/
theorem vollZugriffAlt_invert_hit (s t : VollZustand) (c : Nat)
    (q : SeitenAnfrage) (r : Nat)
    (h : HwVollSchritt s t (.zugriffAlt c q r)) :
    tlbSuche (s.tlb c) (q.linear / 4096) = some r := by
  cases h with
  | veraltet hkan hHit => exact hHit

/-- A stale step carries its canonicality: #GP precedes the cache. -/
theorem vollZugriffAlt_invert_kanon (s t : VollZustand) (c : Nat)
    (q : SeitenAnfrage) (r : Nat)
    (h : HwVollSchritt s t (.zugriffAlt c q r)) :
    istKanonischNat q.linear = true := by
  cases h with
  | veraltet hkan hHit => exact hkan

/-- A stale step never moves the state. -/
theorem hwVollSchritt_veraltet_still (s s' : VollZustand)
    (c : Nat) (q : SeitenAnfrage) (r : Nat)
    (h : HwVollSchritt s s' (.zugriffAlt c q r)) : s' = s := by
  cases h
  rfl

/-- A fault step carries its walk equation. -/
theorem vollZugriffPf_invert_gang (s t : VollZustand) (c : Nat)
    (q : SeitenAnfrage) (a : Nat) (code : PfFehlerCode)
    (h : HwVollSchritt s t (.zugriffPf c q a code)) :
    (seitenGangGross s.steuer s.tabellen q).1 = .seitenFehler a code := by
  cases h with
  | fehler hkan hMiss h => exact h

/-- A fault step carries its miss. -/
theorem vollZugriffPf_invert_miss (s t : VollZustand) (c : Nat)
    (q : SeitenAnfrage) (a : Nat) (code : PfFehlerCode)
    (h : HwVollSchritt s t (.zugriffPf c q a code)) :
    tlbSuche (s.tlb c) (q.linear / 4096) = none := by
  cases h with
  | fehler hkan hMiss h => exact hMiss

/-- A fault step carries its canonicality. -/
theorem vollZugriffPf_invert_kanon (s t : VollZustand) (c : Nat)
    (q : SeitenAnfrage) (a : Nat) (code : PfFehlerCode)
    (h : HwVollSchritt s t (.zugriffPf c q a code)) :
    istKanonischNat q.linear = true := by
  cases h with
  | fehler hkan hMiss h => exact hkan

/-- A fault step never moves the state. -/
theorem hwVollSchritt_fehler_still (s s' : VollZustand)
    (c : Nat) (q : SeitenAnfrage) (a : Nat) (code : PfFehlerCode)
    (h : HwVollSchritt s s' (.zugriffPf c q a code)) :
    s' = s := by
  cases h
  rfl

/-- A #GP step carries its walk equation. -/
theorem vollZugriffGp_invert_gang (s t : VollZustand) (c : Nat)
    (q : SeitenAnfrage) (a : Nat)
    (h : HwVollSchritt s t (.zugriffGp c q a)) :
    (seitenGangGross s.steuer s.tabellen q).1 = .gpFehler a := by
  cases h with
  | gp h => exact h

/-- A #GP step never moves the state. -/
theorem hwVollSchritt_gp_still (s s' : VollZustand)
    (c : Nat) (q : SeitenAnfrage) (a : Nat)
    (h : HwVollSchritt s s' (.zugriffGp c q a)) :
    s' = s := by
  cases h
  rfl

/-- Every full joined step preserves machine well-formedness: old steps by the
    accepted preservation, all family steps because the machine is kept. -/
theorem hwVollSchritt_wf (s s' : VollZustand)
    (e : VollEreignis) (h : HwVollSchritt s s' e)
    (hwf : HwWf s.hw) : HwWf s'.hw := by
  cases h with
  | einbettet hstep => exact hwSchritt_wf _ _ _ hstep hwf
  | invlpg c a => exact hwf
  | cr3 c => exact hwf
  | frisch hkan hMiss h ht => exact hwf
  | veraltet hkan hHit => exact hwf
  | fehler hkan hMiss h => exact hwf
  | gp h => exact hwf

/-! ### Refusals and the canonical boundary.

  A non-canonical request admits no fresh, stale or fault step (only #GP): the
  canonical check precedes the walk AND the cache. A misplaced large page and a
  wholesale-refused configuration admit no fresh or fault step. A stale hit admits
  no fresh step (the walk is not run twice); a miss admits no stale step.
-/

/-- A non-canonical request admits no fresh, stale or fault step: only #GP. -/
theorem vollGp_verweigert (s s' : VollZustand) (c : Nat)
    (q : SeitenAnfrage)
    (hk : istKanonischNat q.linear = false) :
    (∀ phys, ¬ HwVollSchritt s s' (.zugriffOk c q phys)) ∧
      (∀ r, ¬ HwVollSchritt s s' (.zugriffAlt c q r)) ∧
      (∀ a code, ¬ HwVollSchritt s s' (.zugriffPf c q a code)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro phys hstep
    have hkan := vollZugriffOk_invert_kanon s s' c q phys hstep
    rw [hk] at hkan
    cases hkan
  · intro r hstep
    have hkan := vollZugriffAlt_invert_kanon s s' c q r hstep
    rw [hk] at hkan
    cases hkan
  · intro a code hstep
    have hkan := vollZugriffPf_invert_kanon s s' c q a code hstep
    rw [hk] at hkan
    cases hkan

/-- A misplaced large page admits no fresh or fault step. -/
theorem vollGross_verweigert (s s' : VollZustand)
    (c : Nat) (q : SeitenAnfrage) (a phys : Nat) (a' : Nat)
    (code : PfFehlerCode)
    (hg : (seitenGangGross s.steuer s.tabellen q).1 = .grossVerweigert a) :
    ¬ HwVollSchritt s s' (.zugriffOk c q phys) ∧
      ¬ HwVollSchritt s s' (.zugriffPf c q a' code) := by
  refine ⟨?_, ?_⟩
  · intro hstep
    have hok := vollZugriffOk_invert_gang s s' c q phys hstep
    rw [hg] at hok
    cases hok
  · intro hstep
    have hpf := vollZugriffPf_invert_gang s s' c q a' code hstep
    rw [hg] at hpf
    cases hpf

/-- A wholesale-refused configuration admits no fresh or fault step. -/
theorem vollSteuer_verweigert (s s' : VollZustand)
    (c : Nat) (q : SeitenAnfrage) (phys : Nat) (a' : Nat)
    (code : PfFehlerCode)
    (hg : (seitenGangGross s.steuer s.tabellen q).1 = .steuerVerweigert) :
    ¬ HwVollSchritt s s' (.zugriffOk c q phys) ∧
      ¬ HwVollSchritt s s' (.zugriffPf c q a' code) := by
  refine ⟨?_, ?_⟩
  · intro hstep
    have hok := vollZugriffOk_invert_gang s s' c q phys hstep
    rw [hg] at hok
    cases hok
  · intro hstep
    have hpf := vollZugriffPf_invert_gang s s' c q a' code hstep
    rw [hg] at hpf
    cases hpf

/-- A stale hit admits no FRESH step: the walk is not run twice. -/
theorem vollSchritt_frisch_braucht_miss (s t : VollZustand)
    (c : Nat) (q : SeitenAnfrage) (phys r : Nat)
    (hHit : tlbSuche (s.tlb c) (q.linear / 4096) = some r) :
    ¬ HwVollSchritt s t (.zugriffOk c q phys) := by
  intro hstep
  have hMiss := vollZugriffOk_invert_miss s t c q phys hstep
  rw [hHit] at hMiss
  cases hMiss

/-- A miss admits no STALE step: without a hit nothing is stale. -/
theorem vollSchritt_veraltet_braucht_treffer (s t : VollZustand)
    (c : Nat) (q : SeitenAnfrage) (r : Nat)
    (hMiss : tlbSuche (s.tlb c) (q.linear / 4096) = none) :
    ¬ HwVollSchritt s t (.zugriffAlt c q r) := by
  intro hstep
  have hHit := vollZugriffAlt_invert_hit s t c q r hstep
  rw [hMiss] at hHit
  cases hHit

/-- AGREEMENT: an INVLPG step drops exactly the page on its core and keeps
    machine, control and tables. -/
theorem voll_invlpg_vereinbarung (s : VollZustand)
    (c : Nat) (a : Adresse) :
    ∃ t, HwVollSchritt s t (.invlpg c a) ∧
      t.tlb c = tlbEntfernen (s.tlb c) (seitenNr a) ∧
      t.hw = s.hw ∧ t.tabellen = s.tabellen := by
  refine ⟨⟨s.hw, s.steuer, s.tabellen,
    fun d => if d = c then tlbEntfernen (s.tlb c) (seitenNr a)
      else s.tlb d⟩, .invlpg c a, ?_, rfl, rfl⟩
  simp

/-- AGREEMENT: a CR3 step flushes exactly its core and keeps the rest. -/
theorem voll_cr3_vereinbarung (s : VollZustand) (c : Nat) :
    ∃ t, HwVollSchritt s t (.cr3 c) ∧
      t.tlb c = tlbCr3Spuelung (s.tlb c) ∧
      t.hw = s.hw ∧ t.tabellen = s.tabellen := by
  refine ⟨⟨s.hw, s.steuer, s.tabellen,
    fun d => if d = c then tlbCr3Spuelung (s.tlb c) else s.tlb d⟩,
    .cr3 c, ?_, rfl, rfl⟩
  simp

/-! ## 6. Joint witness: large mappings, stale rights, INVLPG, faults, two cores.

  Core 0 holds the stale 2 MiB entry (it still admits the revoked page while core 1
  faults on it); core 1 walks fresh and writes back accessed/dirty. Beside the
  accepted two-core TSO run (owner-only forwarding, drain 0 -> 42 observed from both
  cores) and the flat permissions of the witnessed large pages. Non-degenerate: two
  page sizes, two cores, real table changes and a real memory change.
-/

/-- Witness TLBs: core 0 holds the stale 2 MiB entry, core 1 walks fresh. -/
def witVollTlbs : Nat → List TlbEintrag :=
  fun c => if c = 0 then [⟨0, 512⟩] else []

/-- Core 0 really holds the stale entry. -/
theorem witVollTlbs_null : witVollTlbs 0 = [⟨0, 512⟩] := by
  simp [witVollTlbs]

/-- Witness full state: coherent witness machine, large-page control, witness
    tables, stale TLB on core 0. -/
def witVollM : VollZustand :=
  ⟨hwWitStart, witGrossSteuer, witGrossTab, witVollTlbs⟩

/-- The witness state is machine-well-formed. -/
theorem witVollM_wf : HwWf witVollM.hw := hwWitStart_wf

/-- The stale-use step is reached on core 0 (a self-loop on the witness). -/
theorem witVoll_veraltet_schritt :
    HwVollSchritt witVollM witVollM
      (.zugriffAlt 0 ⟨0, false, false, false⟩ 512) := by
  apply HwVollSchritt.veraltet
  · exact kanonischNat_null
  · decide

/-- Witness address for INVLPG: linear zero. -/
def witVollAdr : Adresse := BitVec.ofNat 64 0

/-- The witness address lives on page 0. -/
theorem witVollAdr_seite : seitenNr witVollAdr = 0 := by
  decide

/-- The INVLPG step is reached and its page misses afterwards. -/
theorem witVoll_invlpg_schritt :
    ∃ t, HwVollSchritt witVollM t (.invlpg 0 witVollAdr) ∧
      tlbSuche (t.tlb 0) (seitenNr witVollAdr) = none := by
  obtain ⟨t, hstep, htlb, _, _⟩ :=
    voll_invlpg_vereinbarung witVollM 0 witVollAdr
  refine ⟨t, hstep, ?_⟩
  rw [htlb]
  show tlbSuche (tlbEntfernen (witVollTlbs 0) (seitenNr witVollAdr))
    (seitenNr witVollAdr) = none
  rw [witVollAdr_seite, witVollTlbs_null]
  exact tlbEntfernen_sucht_verfehlt [⟨0, 512⟩] 0

/-- INVLPG on core 0 leaves core 1 alone on the witness. -/
theorem witVoll_invlpg_lokal :
    (fun d => if d = 0 then tlbEntfernen (witVollTlbs 0) 0
      else witVollTlbs d) 1 = witVollTlbs 1 := by
  decide

/-- The witness user write walks to the 2 MiB page. -/
theorem witVoll_schreib_ok :
    (seitenGangGross witGrossSteuer witGrossTab ⟨0, true, true, false⟩).1 =
      .ok 2097152 := by
  decide

/-- Witness state after the fresh user write: tables gain accessed/dirty. -/
def witVollM1 : VollZustand :=
  ⟨hwWitStart, witGrossSteuer,
    (seitenGangGross witGrossSteuer witGrossTab ⟨0, true, true, false⟩).2,
    witVollTlbs⟩

/-- The fresh write step is reached on core 1 (empty TLB: miss). -/
theorem witVoll_frisch_schritt :
    HwVollSchritt witVollM witVollM1
      (.zugriffOk 1 ⟨0, true, true, false⟩ 2097152) := by
  have hMiss : tlbSuche (witVollM.tlb 1) (0 / 4096) = none := by
    decide
  exact HwVollSchritt.frisch kanonischNat_null hMiss witVoll_schreib_ok rfl

/-- The non-canonical #GP step is reached (self-loop, cache never consulted). -/
theorem witVoll_gp_schritt :
    HwVollSchritt witVollM witVollM
      (.zugriffGp 0 ⟨2 ^ 47, false, true, false⟩ (2 ^ 47)) := by
  exact HwVollSchritt.gp wit_gross_nichtkanonisch_gp

/-- Witness revoked state: the mapping revoked, the stale entry still cached. -/
def witVollMrev : VollZustand :=
  ⟨hwWitStart, witGrossSteuer, witVollTab1, witVollTlbs⟩

/-- The revoked page faults on core 1 (empty TLB) while core 0 still admits it
    (`witVoll_veraltet_schritt` runs on the same tables): the stale-rights
    divergence as reached steps on two cores. -/
theorem witVoll_pf_schritt :
    HwVollSchritt witVollMrev witVollMrev
      (.zugriffPf 1 ⟨0, false, false, false⟩ 0
        ⟨false, false, false, false, false⟩) := by
  apply HwVollSchritt.fehler
  · exact kanonischNat_null
  · decide
  · exact witVollTab1_pf

/-- The CR3 step is reached and its core TLB is empty afterwards. -/
theorem witVoll_cr3_schritt :
    ∃ t, HwVollSchritt witVollM t (.cr3 0) ∧ t.tlb 0 = [] := by
  obtain ⟨t, hstep, htlb, _, _⟩ := voll_cr3_vereinbarung witVollM 0
  refine ⟨t, hstep, ?_⟩
  rw [htlb]
  show tlbCr3Spuelung (witVollTlbs 0) = []
  rw [witVollTlbs_null]
  exact tlbCr3Spuelung_leert [⟨0, 512⟩]

/-- Two-step chain: the stale use self-loops, then INVLPG drops the entry. -/
theorem witVoll_kette :
    ∃ t, HwVollSchritt witVollM witVollM
      (.zugriffAlt 0 ⟨0, false, false, false⟩ 512) ∧
      HwVollSchritt witVollM t (.invlpg 0 witVollAdr) ∧
      tlbSuche (t.tlb 0) (seitenNr witVollAdr) = none := by
  obtain ⟨t, hstep, hmiss⟩ := witVoll_invlpg_schritt
  exact ⟨t, witVoll_veraltet_schritt, hstep, hmiss⟩

/- CUTS:
   Proved: §§1-6a (all of the above; witness states and reached steps).
   Follow: joint witness `voll_zeuge` (§6b).
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
#print axioms uebersetzeVoll_nach_invlpg
#print axioms uebersetzeVoll_nach_invlpg_fehl
#print axioms uebersetzeVoll_cr3_leert
#print axioms uebersetzeVoll_invlpg_lokal
#print axioms witVollTab1
#print axioms witVollTab1_pf
#print axioms witVoll_stal_revoke
#print axioms witVoll_stal_smap
#print axioms witVoll_stal_smep
#print axioms witVoll_nach_invlpg_fehl
#print axioms witVoll_nichtkanonisch_hit
#print axioms FlachStimmtGross
#print axioms gangGross_flach_schreibbar
#print axioms gangGross_flach_lesbar
#print axioms flachGross_aus_flach_schreibbar
#print axioms flachGross_aus_flach_lesbar
#print axioms uebersetzeVoll_frisch_flach_lesbar
#print axioms uebersetzeVoll_frisch_flach_schreibbar
#print axioms flachStimmtGross_allwahr
#print axioms witVollFlach
#print axioms witVoll_flach_liest
#print axioms witVoll_flach_schreibt
#print axioms witVoll_flach_liest_1G
#print axioms adapterVoll
#print axioms adapterVoll_verweigert
#print axioms VollZustand
#print axioms VollEreignis
#print axioms HwVollSchritt
#print axioms hwVollSchritt_einbettung_vor
#print axioms hwVollSchritt_alt_invert
#print axioms hwVollSchritt_einbettung_zurueck
#print axioms vollZugriffOk_invert_gang
#print axioms vollZugriffOk_invert_miss
#print axioms vollZugriffOk_invert_kanon
#print axioms vollZugriffAlt_invert_hit
#print axioms vollZugriffAlt_invert_kanon
#print axioms hwVollSchritt_veraltet_still
#print axioms vollZugriffPf_invert_gang
#print axioms vollZugriffPf_invert_miss
#print axioms vollZugriffPf_invert_kanon
#print axioms hwVollSchritt_fehler_still
#print axioms vollZugriffGp_invert_gang
#print axioms hwVollSchritt_gp_still
#print axioms hwVollSchritt_wf
#print axioms vollGp_verweigert
#print axioms vollGross_verweigert
#print axioms vollSteuer_verweigert
#print axioms vollSchritt_frisch_braucht_miss
#print axioms vollSchritt_veraltet_braucht_treffer
#print axioms voll_invlpg_vereinbarung
#print axioms voll_cr3_vereinbarung
#print axioms witVollTlbs
#print axioms witVollTlbs_null
#print axioms witVollM
#print axioms witVollM_wf
#print axioms witVoll_veraltet_schritt
#print axioms witVollAdr
#print axioms witVollAdr_seite
#print axioms witVoll_invlpg_schritt
#print axioms witVoll_invlpg_lokal
#print axioms witVoll_schreib_ok
#print axioms witVollM1
#print axioms witVoll_frisch_schritt
#print axioms witVoll_gp_schritt
#print axioms witVollMrev
#print axioms witVoll_pf_schritt
#print axioms witVoll_cr3_schritt
#print axioms witVoll_kette

end Gabbro.Grammatik.X86
