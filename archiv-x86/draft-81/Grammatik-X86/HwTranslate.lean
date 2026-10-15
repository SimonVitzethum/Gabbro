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

/-! ## 5. Machine connection: adapter plug and extended steps.

  No translation admits a `HwMaschine` successor: faults have none
  by construction (the same reason `adapterFehler1123` refuses), and
  accessed/dirty updates touch the tables, which live outside
  `HwMaschine`. Translation behaviour lives in
  `HwUebersetzSchritt` over machine-plus-tables-plus-TLBs,
  embedding `HwSchritt` exactly. -/

/-- The translation adapter: the refused default. No translation
    admits a machine successor state. -/
def adapterUebersetz : HwAdapter SeitenAnfrage := verweigertAdapter _

/-- The translation adapter admits nothing. -/
theorem adapterUebersetz_verweigert (m : HwMaschine) (c : Nat)
    (q : SeitenAnfrage) :
    adapterUebersetz.schritt m c q = none := rfl

/-- Joined state: the coherent machine plus control state, tables,
    and per-core TLBs. -/
structure UebersetzZustand where
  hw : HwMaschine
  steuer : SeitenSteuerung
  tabellen : Nat → Wort
  tlb : Nat → List TlbEintrag

/-- Joined events: the old events, INVLPG, CR3 write, a fresh
    walk-through access, a stale TLB-hit use, and a walk fault. -/
inductive UebersetzEreignis where
  | alt : HwEreignis → UebersetzEreignis
  | invlpg : Nat → Adresse → UebersetzEreignis
  | cr3 : Nat → UebersetzEreignis
  | zugriffOk : Nat → SeitenAnfrage → Nat → UebersetzEreignis
  | zugriffAlt : Nat → SeitenAnfrage → Nat → UebersetzEreignis
  | zugriffPf : Nat → SeitenAnfrage → Nat → PfFehlerCode →
      UebersetzEreignis
  deriving DecidableEq, Repr

/-- One joined step: the embedded old step (translation state kept),
    INVLPG / CR3 write on one core's TLB, a fresh access (miss: the
    walk runs and writes back accessed/dirty), a stale use (hit:
    the walk is not consulted, tables kept), or a walk fault
    (a self-loop carrying address and error code). -/
inductive HwUebersetzSchritt :
    UebersetzZustand → UebersetzZustand → UebersetzEreignis → Prop where
  | einbettet {s : UebersetzZustand} {m' : HwMaschine} {e : HwEreignis}
      (h : HwSchritt s.hw m' e) :
      HwUebersetzSchritt s ⟨m', s.steuer, s.tabellen, s.tlb⟩ (.alt e)
  | invlpg {s : UebersetzZustand} (c : Nat) (a : Adresse) :
      HwUebersetzSchritt s
        ⟨s.hw, s.steuer, s.tabellen,
          fun d => if d = c then tlbEntfernen (s.tlb c) (seitenNr a)
            else s.tlb d⟩
        (.invlpg c a)
  | cr3 {s : UebersetzZustand} (c : Nat) :
      HwUebersetzSchritt s
        ⟨s.hw, s.steuer, s.tabellen,
          fun d => if d = c then tlbCr3Spuelung (s.tlb c)
            else s.tlb d⟩
        (.cr3 c)
  | frisch {s : UebersetzZustand} {c : Nat} {q : SeitenAnfrage}
      {phys : Nat} {tab' : Nat → Wort}
      (hMiss : tlbSuche (s.tlb c) (q.linear / 4096) = none)
      (h : (seitenGang s.steuer s.tabellen q).1 = .ok phys)
      (ht : (seitenGang s.steuer s.tabellen q).2 = tab') :
      HwUebersetzSchritt s ⟨s.hw, s.steuer, tab', s.tlb⟩
        (.zugriffOk c q phys)
  | veraltet {s : UebersetzZustand} {c : Nat} {q : SeitenAnfrage}
      {r : Nat}
      (hHit : tlbSuche (s.tlb c) (q.linear / 4096) = some r) :
      HwUebersetzSchritt s s (.zugriffAlt c q r)
  | fehler {s : UebersetzZustand} {c : Nat} {q : SeitenAnfrage}
      {a : Nat} {code : PfFehlerCode}
      (hMiss : tlbSuche (s.tlb c) (q.linear / 4096) = none)
      (h : (seitenGang s.steuer s.tabellen q).1 = .seitenFehler a code) :
      HwUebersetzSchritt s s (.zugriffPf c q a code)

/-- FORWARD embedding: every old step is a joined step. -/
theorem hwUebersetzSchritt_einbettung_vor (s : UebersetzZustand)
    (m' : HwMaschine) (e : HwEreignis)
    (h : HwSchritt s.hw m' e) :
    HwUebersetzSchritt s ⟨m', s.steuer, s.tabellen, s.tlb⟩ (.alt e) :=
  .einbettet h

/-- BACKWARD embedding, exact: an `.alt` step comes only from the
    old step with the same event. -/
theorem hwUebersetzSchritt_alt_invert (s t : UebersetzZustand)
    (e : HwEreignis) (h : HwUebersetzSchritt s t (.alt e)) :
    ∃ m', t.hw = m' ∧ t.tabellen = s.tabellen ∧
      HwSchritt s.hw m' e := by
  cases h with
  | einbettet hstep => exact ⟨_, rfl, rfl, hstep⟩

/-- An `.alt` step over the reached target is the old step. -/
theorem hwUebersetzSchritt_einbettung_zurueck (s : UebersetzZustand)
    (m' : HwMaschine) (e : HwEreignis)
    (h : HwUebersetzSchritt s ⟨m', s.steuer, s.tabellen, s.tlb⟩
      (.alt e)) :
    HwSchritt s.hw m' e := by
  obtain ⟨m'', hm, _, hstep⟩ := hwUebersetzSchritt_alt_invert s _ e h
  subst hm
  exact hstep

/-- A fresh step carries its walk equation. -/
theorem zugriffOk_invert_gang (s t : UebersetzZustand) (c : Nat)
    (q : SeitenAnfrage) (phys : Nat)
    (h : HwUebersetzSchritt s t (.zugriffOk c q phys)) :
    (seitenGang s.steuer s.tabellen q).1 = .ok phys := by
  cases h with
  | frisch hMiss h ht => exact h

/-- A fresh step carries its miss. -/
theorem zugriffOk_invert_miss (s t : UebersetzZustand) (c : Nat)
    (q : SeitenAnfrage) (phys : Nat)
    (h : HwUebersetzSchritt s t (.zugriffOk c q phys)) :
    tlbSuche (s.tlb c) (q.linear / 4096) = none := by
  cases h with
  | frisch hMiss h ht => exact hMiss

/-- A stale step carries its hit: the walk equation is absent. -/
theorem zugriffAlt_invert_hit (s t : UebersetzZustand) (c : Nat)
    (q : SeitenAnfrage) (r : Nat)
    (h : HwUebersetzSchritt s t (.zugriffAlt c q r)) :
    tlbSuche (s.tlb c) (q.linear / 4096) = some r := by
  cases h with
  | veraltet hHit => exact hHit

/-- A stale step never moves the state. -/
theorem hwUebersetzSchritt_veraltet_still (s s' : UebersetzZustand)
    (c : Nat) (q : SeitenAnfrage) (r : Nat)
    (h : HwUebersetzSchritt s s' (.zugriffAlt c q r)) : s' = s := by
  cases h
  rfl

/-- A fault step carries its walk equation. -/
theorem zugriffPf_invert_gang (s t : UebersetzZustand) (c : Nat)
    (q : SeitenAnfrage) (a : Nat) (code : PfFehlerCode)
    (h : HwUebersetzSchritt s t (.zugriffPf c q a code)) :
    (seitenGang s.steuer s.tabellen q).1 = .seitenFehler a code := by
  cases h with
  | fehler hMiss h => exact h

/-- A fault step carries its miss. -/
theorem zugriffPf_invert_miss (s t : UebersetzZustand) (c : Nat)
    (q : SeitenAnfrage) (a : Nat) (code : PfFehlerCode)
    (h : HwUebersetzSchritt s t (.zugriffPf c q a code)) :
    tlbSuche (s.tlb c) (q.linear / 4096) = none := by
  cases h with
  | fehler hMiss h => exact hMiss

/-- A fault step never moves the state. -/
theorem hwUebersetzSchritt_fehler_still (s s' : UebersetzZustand)
    (c : Nat) (q : SeitenAnfrage) (a : Nat) (code : PfFehlerCode)
    (h : HwUebersetzSchritt s s' (.zugriffPf c q a code)) :
    s' = s := by
  cases h
  rfl

/-- Every joined step preserves machine well-formedness: old steps
    by the accepted preservation, all family steps because the
    machine profiles are kept. -/
theorem hwUebersetzSchritt_wf (s s' : UebersetzZustand)
    (e : UebersetzEreignis) (h : HwUebersetzSchritt s s' e)
    (hwf : HwWf s.hw) : HwWf s'.hw := by
  cases h with
  | einbettet hstep => exact hwSchritt_wf _ _ _ hstep hwf
  | invlpg c a => exact hwf
  | cr3 c => exact hwf
  | frisch hMiss h ht => exact hwf
  | veraltet hHit => exact hwf
  | fehler hMiss h => exact hwf

/-- A refused large page admits no joined access step at all. -/
theorem uebersetzGross_verweigert (s s' : UebersetzZustand)
    (c : Nat) (q : SeitenAnfrage) (a phys : Nat) (a' : Nat)
    (code : PfFehlerCode)
    (hg : (seitenGang s.steuer s.tabellen q).1 = .grossVerweigert a) :
    ¬ HwUebersetzSchritt s s' (.zugriffOk c q phys) ∧
      ¬ HwUebersetzSchritt s s' (.zugriffPf c q a' code) := by
  refine ⟨?_, ?_⟩
  · intro hstep
    have hok := zugriffOk_invert_gang s s' c q phys hstep
    rw [hg] at hok
    cases hok
  · intro hstep
    have hpf := zugriffPf_invert_gang s s' c q a' code hstep
    rw [hg] at hpf
    cases hpf

/-- An armed SMEP/SMAP configuration admits no joined access step. -/
theorem uebersetzSteuer_verweigert (s s' : UebersetzZustand)
    (c : Nat) (q : SeitenAnfrage) (phys : Nat) (a' : Nat)
    (code : PfFehlerCode)
    (hg : (seitenGang s.steuer s.tabellen q).1 = .steuerVerweigert) :
    ¬ HwUebersetzSchritt s s' (.zugriffOk c q phys) ∧
      ¬ HwUebersetzSchritt s s' (.zugriffPf c q a' code) := by
  refine ⟨?_, ?_⟩
  · intro hstep
    have hok := zugriffOk_invert_gang s s' c q phys hstep
    rw [hg] at hok
    cases hok
  · intro hstep
    have hpf := zugriffPf_invert_gang s s' c q a' code hstep
    rw [hg] at hpf
    cases hpf

/-- A noncanonical address admits no joined access step. -/
theorem uebersetzGp_verweigert (s s' : UebersetzZustand) (c : Nat)
    (q : SeitenAnfrage) (a phys : Nat) (a' : Nat) (code : PfFehlerCode)
    (hg : (seitenGang s.steuer s.tabellen q).1 = .gpFehler a) :
    ¬ HwUebersetzSchritt s s' (.zugriffOk c q phys) ∧
      ¬ HwUebersetzSchritt s s' (.zugriffPf c q a' code) := by
  refine ⟨?_, ?_⟩
  · intro hstep
    have hok := zugriffOk_invert_gang s s' c q phys hstep
    rw [hg] at hok
    cases hok
  · intro hstep
    have hpf := zugriffPf_invert_gang s s' c q a' code hstep
    rw [hg] at hpf
    cases hpf

/-- A stale hit admits no FRESH step: the walk is not run twice. -/
theorem uebersetzSchritt_frisch_braucht_miss (s t : UebersetzZustand)
    (c : Nat) (q : SeitenAnfrage) (phys r : Nat)
    (hHit : tlbSuche (s.tlb c) (q.linear / 4096) = some r) :
    ¬ HwUebersetzSchritt s t (.zugriffOk c q phys) := by
  intro hstep
  have hMiss := zugriffOk_invert_miss s t c q phys hstep
  rw [hHit] at hMiss
  cases hMiss

/-- A miss admits no STALE step: without a hit nothing is stale. -/
theorem uebersetzSchritt_veraltet_braucht_treffer (s t : UebersetzZustand)
    (c : Nat) (q : SeitenAnfrage) (r : Nat)
    (hMiss : tlbSuche (s.tlb c) (q.linear / 4096) = none) :
    ¬ HwUebersetzSchritt s t (.zugriffAlt c q r) := by
  intro hstep
  have hHit := zugriffAlt_invert_hit s t c q r hstep
  rw [hMiss] at hHit
  cases hHit

/-- AGREEMENT: an INVLPG step drops exactly the page on its core
    and keeps machine, control and tables. -/
theorem uebersetz_invlpg_vereinbarung (s : UebersetzZustand)
    (c : Nat) (a : Adresse) :
    ∃ t, HwUebersetzSchritt s t (.invlpg c a) ∧
      t.tlb c = tlbEntfernen (s.tlb c) (seitenNr a) ∧
      t.hw = s.hw ∧ t.tabellen = s.tabellen := by
  refine ⟨⟨s.hw, s.steuer, s.tabellen,
    fun d => if d = c then tlbEntfernen (s.tlb c) (seitenNr a)
      else s.tlb d⟩, .invlpg c a, ?_, rfl, rfl⟩
  simp

/-- AGREEMENT: a CR3 step flushes exactly its core and keeps the
    rest. -/
theorem uebersetz_cr3_vereinbarung (s : UebersetzZustand) (c : Nat) :
    ∃ t, HwUebersetzSchritt s t (.cr3 c) ∧
      t.tlb c = tlbCr3Spuelung (s.tlb c) ∧
      t.hw = s.hw ∧ t.tabellen = s.tabellen := by
  refine ⟨⟨s.hw, s.steuer, s.tabellen,
    fun d => if d = c then tlbCr3Spuelung (s.tlb c) else s.tlb d⟩,
    .cr3 c, ?_, rfl, rfl⟩
  simp

/-! ## 6. Witness: mapping changed, stale use, INVLPG, fault.

  Linear page 1 (address 4096) maps read-write onto frame 32 in the
  lane-1283 witness tables. The witness clears that leaf in memory
  (the mapping change), keeps the old frame cached (the stale
  entry), accesses through it, then invalidates and faults. -/

/-- Changed tables: the RW leaf of page 1 cleared in memory. -/
def witUebersetzTab1 : Nat → Wort :=
  fun n => if n = 16 * 512 + 1 then 0 else witTab n

/-- Stale entry: page 1 still cached to frame 32. -/
def witUebersetzTlb : List TlbEintrag := [⟨1, 32⟩]

/-- Witness address: first byte of linear page 1. -/
def witUebersetzAdr : Adresse := BitVec.ofNat 64 4096

/-- The witness address lives on page 1. -/
theorem witUebersetz_seite : seitenNr witUebersetzAdr = 1 := by
  decide

/-- The witness address is page-aligned. -/
theorem witUebersetz_offset_null : seitenOffset witUebersetzAdr = 0 := by
  decide

/-- The cached frame with zero offset names 131072. -/
theorem witUebersetz_phys :
    physAddr 32 witUebersetzAdr = BitVec.ofNat 64 131072 := by
  decide

/-- STALE USE: the changed tables are never consulted -- the cached
    frame 32 still answers. -/
theorem witUebersetz_veraltet :
    uebersetzeMitTlb witSeitenSteuer witUebersetzTab1 witUebersetzTlb
      witUebersetzAdr =
      some (physAddr 32 witUebersetzAdr) := by
  decide

/-- The stale use IS the lifted lane-1285 hit rule. -/
theorem witUebersetz_veraltet_ist_trifft :
    uebersetzeMitTlb witSeitenSteuer witUebersetzTab1 witUebersetzTlb
      witUebersetzAdr =
      some (physAddr 32 witUebersetzAdr) :=
  uebersetze_trifft witSeitenSteuer witUebersetzTab1 witUebersetzTlb
    witUebersetzAdr 32 (by decide)

/-- The fresh walk through the changed tables faults non-present
    with the access bits. -/
theorem witUebersetz_neu_pf :
    (seitenGang witSeitenSteuer witUebersetzTab1
      ⟨4096, false, true, false⟩).1 =
      .seitenFehler 4096 ⟨false, false, true, false, false⟩ := by
  decide

/-- The instantiated walk misses page 1 after the change. -/
theorem witUebersetz_walk_fehl :
    walkLesen witSeitenSteuer witUebersetzTab1 1 = none := by
  apply walkLesen_keinOk
  intro hEx
  obtain ⟨phys, hok⟩ := hEx
  have hok4096 :
      (seitenGang witSeitenSteuer witUebersetzTab1
        ⟨4096, false, true, false⟩).1 = .ok phys := hok
  rw [witUebersetz_neu_pf] at hok4096
  cases hok4096

/-- After INVLPG the joined access re-walks into the fault. -/
theorem witUebersetz_nach_invlpg_fehl :
    uebersetzeMitTlb witSeitenSteuer witUebersetzTab1
      (tlbEntfernen witUebersetzTlb 1) witUebersetzAdr = none := by
  decide

/-! ## 7. Joint witness: changed mapping, stale use, INVLPG, fault.

  Beside the accepted two-core TSO run: owner-only forwarding, a
  drain that changes actual shared memory, and the flat agreement
  on the lane-1283 shared page. -/

/-- Witness TLBs: core 0 holds the stale entry, core 1 is empty. -/
def witUebersetzTlbs : Nat → List TlbEintrag :=
  fun c => if c = 0 then witUebersetzTlb else []

/-- Core 0 really holds the stale entry. -/
theorem witUebersetzTlbs_null :
    witUebersetzTlbs 0 = witUebersetzTlb := by
  simp [witUebersetzTlbs]

/-- Witness joined state: coherent witness machine, witness
    control, changed tables, stale TLB on core 0. -/
def witUebersetzM : UebersetzZustand :=
  ⟨hwWitStart, witSeitenSteuer, witUebersetzTab1, witUebersetzTlbs⟩

/-- The witness joined state is machine-well-formed. -/
theorem witUebersetzM_wf : HwWf witUebersetzM.hw := hwWitStart_wf

/-- The stale-use step is reached (a self-loop on the witness). -/
theorem witUebersetz_veraltet_schritt :
    HwUebersetzSchritt witUebersetzM witUebersetzM
      (.zugriffAlt 0 ⟨4096, false, true, false⟩ 32) := by
  apply HwUebersetzSchritt.veraltet
  decide

/-- The INVLPG step is reached and its page misses afterwards. -/
theorem witUebersetz_invlpg_schritt :
    ∃ t, HwUebersetzSchritt witUebersetzM t
      (.invlpg 0 witUebersetzAdr) ∧
      tlbSuche (t.tlb 0) (seitenNr witUebersetzAdr) = none := by
  obtain ⟨t, hstep, htlb, _, _⟩ :=
    uebersetz_invlpg_vereinbarung witUebersetzM 0 witUebersetzAdr
  refine ⟨t, hstep, ?_⟩
  rw [htlb]
  show tlbSuche
    (tlbEntfernen (witUebersetzTlbs 0) (seitenNr witUebersetzAdr))
    (seitenNr witUebersetzAdr) = none
  rw [witUebersetz_seite, witUebersetzTlbs_null]
  exact tlbEntfernen_sucht_verfehlt witUebersetzTlb 1

/-- INVLPG on core 0 leaves core 1 alone on the witness. -/
theorem witUebersetz_invlpg_lokal :
    (fun d => if d = 0 then
      tlbEntfernen (witUebersetzTlbs 0) (seitenNr witUebersetzAdr)
      else witUebersetzTlbs d) 1 = witUebersetzTlbs 1 := by
  decide

/-- JOINT WITNESS: the old mapping admits, the changed mapping
    faults, the stale entry still admits, INVLPG re-faults (both as
    pure resolution and as reached steps), beside owner-only
    forwarding and the memory-changing drain on two cores.
    Non-degenerate: a real mapping change in memory, a real memory
    change through the drain. -/
theorem hwUebersetz_zeuge :
    HwWf witUebersetzM.hw ∧
      (seitenGang witSeitenSteuer witTab
        ⟨4096, false, true, false⟩).1 = .ok 131072 ∧
      (seitenGang witSeitenSteuer witUebersetzTab1
        ⟨4096, false, true, false⟩).1 =
        .seitenFehler 4096 ⟨false, false, true, false, false⟩ ∧
      uebersetzeMitTlb witSeitenSteuer witUebersetzTab1
        witUebersetzTlb witUebersetzAdr =
        some (physAddr 32 witUebersetzAdr) ∧
      uebersetzeMitTlb witSeitenSteuer witUebersetzTab1
        (tlbEntfernen witUebersetzTlb 1) witUebersetzAdr = none ∧
      HwUebersetzSchritt witUebersetzM witUebersetzM
        (.zugriffAlt 0 ⟨4096, false, true, false⟩ 32) ∧
      (∃ t, HwUebersetzSchritt witUebersetzM t
        (.invlpg 0 witUebersetzAdr) ∧
        tlbSuche (t.tlb 0) (seitenNr witUebersetzAdr) = none) ∧
      hwWitLoadEigen = some (some (BitVec.ofNat 8 42)) ∧
      hwWitLoadFremd = some (some (BitVec.ofNat 8 0)) ∧
      hwWitNachFlush = some (some (BitVec.ofNat 8 42)) := by
  exact ⟨witUebersetzM_wf, wit_lese_rw_ok, witUebersetz_neu_pf,
    witUebersetz_veraltet, witUebersetz_nach_invlpg_fehl,
    witUebersetz_veraltet_schritt, witUebersetz_invlpg_schritt,
    hwWit_weiterleitung, hwWit_fremd_alt,
    hwWit_spülung_aendert_speicher⟩

/- CUTS:
   Proved here (all over the REUSED accepted definitions -- the
   lane-1283 walk, the lane-1285 TLB rules, the coherent machine and
   its two-core TSO run -- lifted, never redefined):
   - §1: the walk as a TLB function `walkLesen` with its unfolding
     (`walkLesen_ok`, `walkLesen_keinOk`); the joined resolution
     `uebersetzeMitTlb` with the lifted stale rule
     (`uebersetze_trifft`, from `tlbAufloesung_trifft`) and miss rule
     (`uebersetze_verfehlt`, from `tlbAufloesung_verfehlt`).
   - §2: page-alignment bridge (`seitenNr_mal_basis`,
     `walkLesen_ausgerichtet`); fresh access runs the walk
     (`uebersetze_frisch_ok`) and every admitted fresh access comes
     from it (`uebersetze_frisch_braucht_gang`); on a hit the tables
     are never consulted (`uebersetze_stal_unabhaengig`).
   - §3: INVLPG re-walk (`uebersetze_nach_invlpg`, from
     `tlbNachEntfernen_geht_durch`), CR3 flush
     (`uebersetze_cr3_leert`, from `tlbCr3Spuelung_leert`), core
     locality (`uebersetze_invlpg_lokal`, from
     `tlbEntfernen_lokal`).
   - §4: flat bridge -- fresh walk-or-TLB admission meets the flat
     byte permission in both directions
     (`uebersetze_frisch_flach_lesbar`,
     `uebersetze_frisch_flach_schreibbar` over the lane-1283
     obligation `FlachStimmt`); the stale hit is the proved
     exception (§2 independence plus the §6 exhibit).
   - §5: machine connection -- the refused adapter plug
     (`adapterUebersetz`), the extended step `HwUebersetzSchritt`
     with the EXACT two-way `HwSchritt` embedding, inversion and
     stillness facts, `HwWf` preservation, planted refusals for
     large pages, armed SMEP/SMAP, noncanonical addresses, and the
     hit-vs-fresh / miss-vs-stale exclusions, plus forward INVLPG /
     CR3 agreements.
   - §§6-7: closed `decide` pins (page, offset, cached frame, stale
     use as the lifted hit rule, changed-walk fault, walk miss,
     post-INVLPG fault) and the reached two-core joint witness
     `hwUebersetz_zeuge` (old walk admits, changed walk faults,
     stale entry admits, INVLPG re-faults as pure resolution and as
     reached steps, owner-only forwarding, drain 0 -> 42).
   Named silicon assumptions (never discharged here, no hardware
   correspondence claimed): INVLPG invalidates the TLB entries for
   the page of its operand (Intel SDM 325462-093US Vol 2 INVLPG;
   Vol 3A Section 5.10.4.1); with CR4.PCIDE = 0 the current PCID is
   000H; MOV to CR3 then invalidates all non-global entries for
   PCID 000H (Vol 3A Section 5.10.4.1) -- hence the model runs with
   PCID off and no global entries (lane-1285 `tlbGlobal`), so a CR3
   write empties the core TLB. Page-table bit layout, error-code
   meanings and the 48-bit canonical width are lane-1283
   assumptions, reused here. Cross-core shootdown stays a
   user-logic (OS) duty.
   NOT proved here, and not claimed:
   - No write-probe walk: `walkLesen` probes pages as user reads;
     write permission comes from the write walk plus `FlachStimmt`.
   - No per-entry permission caching: a hit reuses the frame with
     no rights re-check (this IS the stale exception, stated).
   - No large pages (refused, from lane 1283), no SMEP/SMAP
     per-access semantics (refused wholesale), no fault DELIVERY
     (address plus error code only, no IDT path).
   - `FlachStimmt` for a REAL OS is user logic (only the bridge
     directions are proved here).
   - No per-access target-to-W/GX simulation, no timing, no source
     stop-class transfer; axioms stay within the standard goal set
     (propext, Classical.choice, Quot.sound).
-/

#print axioms walkLesen
#print axioms uebersetzeMitTlb
#print axioms walkLesen_ok
#print axioms walkLesen_keinOk
#print axioms uebersetze_trifft
#print axioms uebersetze_verfehlt
#print axioms seitenNr_mal_basis
#print axioms walkLesen_ausgerichtet
#print axioms uebersetze_frisch_ok
#print axioms uebersetze_frisch_braucht_gang
#print axioms uebersetze_stal_unabhaengig
#print axioms uebersetze_nach_invlpg
#print axioms uebersetze_cr3_leert
#print axioms uebersetze_invlpg_lokal
#print axioms uebersetze_frisch_flach_lesbar
#print axioms uebersetze_frisch_flach_schreibbar
#print axioms adapterUebersetz
#print axioms adapterUebersetz_verweigert
#print axioms UebersetzZustand
#print axioms UebersetzEreignis
#print axioms HwUebersetzSchritt
#print axioms hwUebersetzSchritt_einbettung_vor
#print axioms hwUebersetzSchritt_alt_invert
#print axioms hwUebersetzSchritt_einbettung_zurueck
#print axioms zugriffOk_invert_gang
#print axioms zugriffOk_invert_miss
#print axioms zugriffAlt_invert_hit
#print axioms hwUebersetzSchritt_veraltet_still
#print axioms zugriffPf_invert_gang
#print axioms zugriffPf_invert_miss
#print axioms hwUebersetzSchritt_fehler_still
#print axioms hwUebersetzSchritt_wf
#print axioms uebersetzGross_verweigert
#print axioms uebersetzSteuer_verweigert
#print axioms uebersetzGp_verweigert
#print axioms uebersetzSchritt_frisch_braucht_miss
#print axioms uebersetzSchritt_veraltet_braucht_treffer
#print axioms uebersetz_invlpg_vereinbarung
#print axioms uebersetz_cr3_vereinbarung
#print axioms witUebersetzTab1
#print axioms witUebersetzTlb
#print axioms witUebersetzAdr
#print axioms witUebersetz_seite
#print axioms witUebersetz_offset_null
#print axioms witUebersetz_phys
#print axioms witUebersetz_veraltet
#print axioms witUebersetz_veraltet_ist_trifft
#print axioms witUebersetz_neu_pf
#print axioms witUebersetz_walk_fehl
#print axioms witUebersetz_nach_invlpg_fehl
#print axioms witUebersetzTlbs
#print axioms witUebersetzTlbs_null
#print axioms witUebersetzM
#print axioms witUebersetzM_wf
#print axioms witUebersetz_veraltet_schritt
#print axioms witUebersetz_invlpg_schritt
#print axioms witUebersetz_invlpg_lokal
#print axioms hwUebersetz_zeuge

end Gabbro.Grammatik.X86
