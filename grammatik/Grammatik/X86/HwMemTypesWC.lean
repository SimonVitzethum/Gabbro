/-
  File:      Grammatik/X86/HwMemTypesWC.lean
  Subject:   WC/WT/WP memory types and cache-control instructions on the
              coherent machine.

  Lane 1287: follow-up of lane 1133 (`HwDevices.lean`): its CUTS state NO
  WC/WT/WP and no cache-control forms. This file adds the memory types
  (PAT/MTRR combination reduced to a stated per-region type function, as
  lane 1133 does for UC), the ordering rules per type as the SDM states
  them (WB: TSO as modelled; WT/WP: reads cached, writes go through;
  WC: stores weakly ordered in a per-core write-combining buffer drained
  by fences, reusing `SfenceStoreNarrow.lean` and `MfenceDrainOwn.lean`),
  PREFETCHh as an architectural NOP with no fault, and CLFLUSH as a
  store-ordered flush of one line with byte-read fault rules.

  Manual provenance (official Intel SDM 325462-093US, September 2026,
  local `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`):
  - Vol.1 10.4.6.3/Table 10-1 (PREFETCHh hints do not affect function);
  - PREFETCHh entry: "merely a hint and does not affect program
    behavior", #UD only with LOCK; prefetches from UC/WC ignored;
  - CLFLUSH entry: NP 0F AE /7, ordered wrt writes/locked/fences and
    other CLFLUSH, faults as a byte load (plus execute-only allowed);
  - Vol.1 10.4.6.5/WC semantics: weakly ordered, no write allocate,
    stores may combine; fencing gives global visibility;
  - Vol.3A 14.3.2/WP: reads cached, writes go through and invalidate.
  AMD retrieval failed; no AMD provenance or silicon proof is claimed.
  Every ordering claim below is stated as the SDM's and named as an
  assumption; silicon behaviour is never proved.
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.MemoryTypeHardwareExecution
import Grammatik.X86.SfenceStoreNarrow
import Grammatik.X86.MfenceDrainOwn

namespace Gabbro.Grammatik.X86

namespace HwMemWC1287

/-- Memory types of one region: WB default, WT/WP go-through, WC
    buffered, UC owned by lane 1133 (named here, never stepped). -/
inductive SpeicherTypWC where
  | wb
  | wt
  | wp
  | wc
  | uc
  deriving DecidableEq, Repr

/-- Software-established type profile: the PAT/MTRR/page-table
    combination reduced to an explicit list. First covering region
    wins; establishing it is software user logic, never trusted. -/
abbrev TypProfil := List (Region × SpeicherTypWC)

/-- One typed region covers `[start, start+len)`: inside, no wrap. -/
def decktTyp (r : Region) (start len : Nat) : Bool :=
  decide (r.basis ≤ start ∧ start + len ≤ r.basis + r.len ∧
    start + len ≤ 2 ^ 64)

/-- Effective type of an `n`-byte access at `a`: first covering region
    wins; WB is the default wherever no region covers. -/
def speicherTyp : TypProfil → Adresse → Nat → SpeicherTypWC
  | [], _, _ => .wb
  | (r, t) :: rest, a, n =>
    if decktTyp r a.toNat n then t else speicherTyp rest a n

/-- The empty profile admits no special type: WB is the default. -/
theorem speicherTyp_leer (a : Adresse) (n : Nat) :
    speicherTyp [] a n = .wb := rfl

/-- A covering head region decides the type. -/
theorem speicherTyp_kopf (r : Region) (t : SpeicherTypWC)
    (rest : TypProfil) (a : Adresse) (n : Nat)
    (hd : decktTyp r a.toNat n = true) :
    speicherTyp ((r, t) :: rest) a n = t := by
  simp [speicherTyp, hd]

/-- A non-covering head region is skipped: lookup continues. -/
theorem speicherTyp_ueberspringe (q : Region × SpeicherTypWC)
    (rest : TypProfil) (a : Adresse) (n : Nat)
    (hmiss : decktTyp q.1 a.toNat n = false) :
    speicherTyp (q :: rest) a n = speicherTyp rest a n := by
  simp [speicherTyp, hmiss]

/-! ## 1. Ordering rules per type, as the SDM states them.

  Stated model content (proved below by `decide` on the table): only
  WC stores are buffered outside the WB TSO buffer; WT/WP stores go
  through. That the PINS show the drained order is silicon and stays
  a named assumption (`WcBusAnnahme`); that WB behaves as TSO is the
  accepted `TSO.lean` model, reused, never restated. -/

/-- Which types buffer stores outside the WB TSO buffer: WC only. -/
def typGepuffert : SpeicherTypWC → Bool
  | .wc => true
  | _ => false

/-- Which types write through to memory on retire: WT and WP. -/
def typDurchschreib : SpeicherTypWC → Bool
  | .wt => true
  | .wp => true
  | _ => false

/-- MODEL (SDM WC semantics): only WC stores are buffered. -/
theorem wc_allein_gepuffert :
    typGepuffert .wc = true ∧ typGepuffert .wb = false ∧
      typGepuffert .wt = false ∧ typGepuffert .wp = false ∧
      typGepuffert .uc = false := by
  decide

/-- MODEL (SDM WT/WP): WT and WP write through; WB/WC/UC do not. -/
theorem wtwp_schreiben_durch :
    typDurchschreib .wt = true ∧ typDurchschreib .wp = true ∧
      typDurchschreib .wb = false ∧ typDurchschreib .wc = false ∧
      typDurchschreib .uc = false := by
  decide

/-- The per-type store path the steps below discharge: buffered WC
    stores reach memory only through the fence drain; WT/WP stores
    reach memory on retire; WB rides the accepted TSO buffer. -/
def typPfad (t : SpeicherTypWC) : Bool × Bool :=
  (typGepuffert t, typDurchschreib t)

/-! ## 2. Machine: coherent machine plus per-core WC buffer.

  The WB TSO buffers stay inside `masch`; WC stores combine in a
  per-core SECOND buffer (`wc`) drained by fences. WT/WP stores write
  memory on retire. UC addresses never step here (lane 1133 owns UC);
  memory-type aliasing (one address under two types) is reserved per
  the SDM and stays OPEN (see CUTS). -/

/-- PREFETCHh data hints (T0/T1/T2/NTA). -/
inductive PrefetchHinweis where
  | nta
  | t0
  | t1
  | t2
  deriving DecidableEq, Repr

/-- Observable events: typed retirements, line flush, hint NOP, fence.
    The acting core rides the event wherever the effect is per-core
    (WC buffering, line drain, fence drain), as in `HwEreignis`.
    Silicon bits ride the event where the manual gates on them
    (CLFLUSH needs its CPUID bit); PREFETCHh needs none (a NOP
    everywhere; its encodings stay NOPs even without enumeration). -/
inductive WcEreignis1287 where
  | wcSpeichern : Nat → Adresse → Byte → WcEreignis1287
  | wtSpeichern : Adresse → Byte → WcEreignis1287
  | wpSpeichern : Adresse → Byte → WcEreignis1287
  | clflush : Nat → Bool → Adresse → WcEreignis1287
  | prefetch : PrefetchHinweis → Adresse → WcEreignis1287
  | zaun : Nat → WcEreignis1287
  deriving DecidableEq, Repr

/-- The extended coherent WC machine: the coherent machine plus the
    software-established type profile, the per-core write-combining
    buffers, and the WC-side program-order log. -/
structure HwWcMaschine1287 where
  masch : HwMaschine
  profil : TypProfil
  wc : Nat → List TSOEintrag
  wcLog : List WcEreignis1287

/-- One WC entry into canonical memory (one chunk of the drain). -/
def wcSpeicherSchreibe (mem : Speicher) (e : TSOEintrag) : Speicher :=
  { mem with bytes := fun x => if x = e.addr then e.wert else mem.bytes x }

/-- Drain a WC entry list into memory, oldest first. -/
def wcLeere (mem : Speicher) (l : List TSOEintrag) : Speicher :=
  l.foldl wcSpeicherSchreibe mem

/-- Stated cache line size (the CPUID CLFLUSH line size; 64 on the
    selected profile, named, never proved). -/
def clflushLinie : Nat := 64

/-- Line base of an address under the stated size. -/
def linienBasis (a : Adresse) : Nat :=
  (a.toNat / clflushLinie) * clflushLinie

/-- Same stated line as `a`. -/
def inLinie (a : Adresse) (x : Adresse) : Bool :=
  decide (linienBasis x = linienBasis a)

/-- Byte load with own-buffer forwarding: youngest own WC entry wins,
    then youngest own WB entry (accepted TSO forwarding), then
    canonical memory. Foreign WC/WB entries never forward (no core
    reads another core's buffer). -/
def wcLesbar (w : HwWcMaschine1287) (c : Nat) (a : Adresse) :
    Option Byte :=
  if w.masch.mem.lesbar a then
    some (match neuestens (w.wc c) a with
      | some v => v
      | none =>
        match neuestens (w.masch.puffer c) a with
        | some v => v
        | none => w.masch.mem.bytes a)
  else none

/-- PREFETCHh byte decode: `0F 18` with a MEMORY ModRM; the reg field
    is the hint (0 NTA, 1 T0, 2 T1, 3 T2). Register forms (mod = 3,
    the HINT-NOP shapes) and the LOCK prefix refuse here: LOCK on a
    prefetch is the manual's #UD, and this machine has no fault
    vocabulary on the bare path, so denial is absence of a step. -/
def decodePrefetch1287 :
    List Byte → Option (PrefetchHinweis × List Byte)
  | [b0, b1, m] =>
    if byteNat b0 == 15 && byteNat b1 == 24 &&
        byteNat m / 64 != 3 then
      match (byteNat m / 8) % 8 with
      | 0 => some (.nta, [])
      | 1 => some (.t0, [])
      | 2 => some (.t1, [])
      | 3 => some (.t2, [])
      | _ => none
    else none
  | _ => none

/-- CLFLUSH byte decode: `NP 0F AE /7` with a MEMORY ModRM. The mod=3
    row (F8..FF) is SFENCE's (`SfenceStoreNarrow.lean`) and refuses
    here; no accepted row is shadowed either way. -/
def decodeClflush1287 : List Byte → Option (List Byte)
  | [b0, b1, m] =>
    if byteNat b0 == 15 && byteNat b1 == 174 &&
        (byteNat m / 8) % 8 == 7 && byteNat m / 64 != 3 then some []
    else none
  | _ => none

/-- Canonical PREFETCHT0 bytes decode to the T0 hint. -/
theorem pin_prefetch_t0 :
    decodePrefetch1287 [natByte 15, natByte 24, natByte 8] =
      some (.t0, []) := by
  decide

/-- Canonical PREFETCHNTA bytes decode to the NTA hint. -/
theorem pin_prefetch_nta :
    decodePrefetch1287 [natByte 15, natByte 24, natByte 0] =
      some (.nta, []) := by
  decide

/-- Canonical CLFLUSH bytes (mod=0, reg=7) decode. -/
theorem pin_clflush :
    decodeClflush1287 [natByte 15, natByte 174, natByte 56] =
      some [] := by
  decide

/-- The SFENCE row (mod=3, reg=7) is no CLFLUSH. -/
theorem pin_clflush_kein_sfence :
    decodeClflush1287 [natByte 15, natByte 174, natByte 248] =
      none := by
  decide

/-- The register form (mod=3) is no PREFETCHh memory hint. -/
theorem pin_prefetch_register_verweigert :
    decodePrefetch1287 [natByte 15, natByte 24, natByte 200] =
      none := by
  decide

/-- The LOCK prefix refuses on both decoders (exact-length shapes;
    the manual's #UD has no step here). -/
theorem pin_lock_praefix_verweigert :
    decodePrefetch1287
      [natByte 240, natByte 15, natByte 24, natByte 8] = none ∧
    decodeClflush1287
      [natByte 240, natByte 15, natByte 174, natByte 56] = none := by
  decide

/-- NAMED ASSUMPTION (WC bus order): the pins present the drained WC
    log content in order. The model retires in program order and
    drains FIFO (proved below); the bus appearance itself is
    hardware (SDM: WC propagation order is guaranteed only through
    fencing and transaction atomicity). -/
def WcBusAnnahme (log pins : List WcEreignis1287) : Prop := pins = log

/-- From the named bus assumption, pins and log run together. -/
theorem wcPinsLaenge (log pins : List WcEreignis1287)
    (h : WcBusAnnahme log pins) :
    pins.length = log.length := by rw [h]

/-- NAMED ASSUMPTION (WT/WP go-through): a retired WT/WP store is
    visible in memory before any later fence on the acting core. The
    model writes memory on retire (proved below); cache update and
    bus appearance are hardware (SDM Vol.3A 14.3.2: WT/WP writes are
    propagated to the system bus). -/
def WtWpBusAnnahme (w : HwWcMaschine1287) (a : Adresse) (v : Byte) :
    Prop :=
  w.masch.mem.bytes a = v

/-- From the named go-through assumption, the memory byte reads back. -/
theorem wtWpBus_liest (w : HwWcMaschine1287) (a : Adresse) (v : Byte)
    (h : WtWpBusAnnahme w a v) :
    w.masch.mem.bytes a = v := h

/-- Well-formedness: admitted features have silicon behind them --
    exactly `HwWf` of the coherent machine (profiles are shared). -/
def HwWcWf (w : HwWcMaschine1287) : Prop := HwWf w.masch

/-! ## 3. Steps on the extended coherent machine.

  Each case is a function on checked gates; denial at any gate is
  `none` (the absence of a step, never a silent skip). UC addresses
  never step here: no case admits `.uc` (lane 1133 owns UC). -/

/-- WC store retire: typed WC with write permission. The coherent
    bytes, the WB buffers and other cores' WC buffers are untouched;
    the entry combines in the own WC buffer (SDM: no write allocate,
    stores may collapse -- the buffer holds them youngest-last). -/
def wcStoreZugriff (w : HwWcMaschine1287) (c : Nat) (a : Adresse)
    (v : Byte) : Option HwWcMaschine1287 :=
  if speicherTyp w.profil a 1 == .wc && w.masch.mem.schreibbar a then
    some ⟨w.masch, w.profil, pufferSetze w.wc c (w.wc c ++ [⟨a, v⟩]),
      w.wcLog ++ [.wcSpeichern c a v]⟩
  else none

/-- WT store retire: typed WT with write permission. Memory is
    written on retire (go-through); no buffer grows. -/
def wtStoreZugriff (w : HwWcMaschine1287) (a : Adresse)
    (v : Byte) : Option HwWcMaschine1287 :=
  if speicherTyp w.profil a 1 == .wt && w.masch.mem.schreibbar a then
    some ⟨{ w.masch with mem :=
        { w.masch.mem with bytes := fun x =>
          if x = a then v else w.masch.mem.bytes x } },
      w.profil, w.wc, w.wcLog ++ [.wtSpeichern a v]⟩
  else none

/-- WP store retire: typed WP with write permission. Memory is
    written on retire and cached copies are invalidated; with no data
    cache modelled the memory effect is the WT one, and the event
    records which rule retired it. -/
def wpStoreZugriff (w : HwWcMaschine1287) (a : Adresse)
    (v : Byte) : Option HwWcMaschine1287 :=
  if speicherTyp w.profil a 1 == .wp && w.masch.mem.schreibbar a then
    some ⟨{ w.masch with mem :=
        { w.masch.mem with bytes := fun x =>
          if x = a then v else w.masch.mem.bytes x } },
      w.profil, w.wc, w.wcLog ++ [.wpSpeichern a v]⟩
  else none

/-- Line-scoped drain of one core's WC buffer: entries in the stated
    line of `a` go to memory oldest-first; the rest stays pending. -/
def wcLinieSpuele (mem : Speicher) (l : List TSOEintrag)
    (a : Adresse) : Speicher × List TSOEintrag :=
  (wcLeere mem (l.filter (fun e => inLinie a e.addr)),
    l.filter (fun e => !(inLinie a e.addr)))

/-- CLFLUSH retire: named silicon bit plus byte-read fault rules
    (readable, or execute-only which a plain load would refuse --
    the SDM's stated allowance). The acting core's line entries drain
    to memory; foreign WC entries for the same line stay pending
    (cross-core WC eviction order is OPEN, see CUTS). -/
def clflushZugriff (w : HwWcMaschine1287) (c : Nat) (silizium : Bool)
    (a : Adresse) : Option HwWcMaschine1287 :=
  if silizium && (w.masch.mem.lesbar a || w.masch.mem.ausfuehrbar a) then
    let (mem', rest) := wcLinieSpuele w.masch.mem (w.wc c) a
    some ⟨{ w.masch with mem := mem' }, w.profil,
      pufferSetze w.wc c rest, w.wcLog ++ [.clflush c silizium a]⟩
  else none

/-- PREFETCHh retire: architecturally a NOP with no fault -- admitted
    at every address with no permission check; machine, buffers and
    memory are unchanged and only the log records the hint. -/
def prefetchZugriff (w : HwWcMaschine1287) (h : PrefetchHinweis)
    (a : Adresse) : Option HwWcMaschine1287 :=
  some ⟨w.masch, w.profil, w.wc, w.wcLog ++ [.prefetch h a]⟩

/-- Fence drain (SFENCE/MFENCE/LOCK retired): the own WB buffer
    through the accepted `drainVoll`, then the own WC buffer
    oldest-first into memory. Foreign buffers are untouched by
    construction (`pufferSetze` elsewhere, `drain_fremd_puffer`). -/
def wcZaunZustand (w : HwWcMaschine1287) (c : Nat) :
    Option HwWcMaschine1287 :=
  match drainVoll ⟨w.masch.mem, w.masch.puffer⟩ c with
  | none => none
  | some s =>
    some ⟨⟨wcLeere s.mem (w.wc c), w.masch.kerne, s.puffer,
        w.masch.hw, w.masch.bereit⟩,
      w.profil, pufferSetze w.wc c [], w.wcLog ++ [.zaun c]⟩

/-- One extended step, each case from its function above. -/
inductive HwWcSchritt :
    HwWcMaschine1287 → HwWcMaschine1287 → WcEreignis1287 → Prop where
  | wcSpeichern (w : HwWcMaschine1287) (c : Nat) (a : Adresse)
      (v : Byte) (w' : HwWcMaschine1287)
      (h : wcStoreZugriff w c a v = some w') :
      HwWcSchritt w w' (.wcSpeichern c a v)
  | wtSpeichern (w : HwWcMaschine1287) (a : Adresse) (v : Byte)
      (w' : HwWcMaschine1287)
      (h : wtStoreZugriff w a v = some w') :
      HwWcSchritt w w' (.wtSpeichern a v)
  | wpSpeichern (w : HwWcMaschine1287) (a : Adresse) (v : Byte)
      (w' : HwWcMaschine1287)
      (h : wpStoreZugriff w a v = some w') :
      HwWcSchritt w w' (.wpSpeichern a v)
  | clflush (w : HwWcMaschine1287) (c : Nat) (silizium : Bool)
      (a : Adresse) (w' : HwWcMaschine1287)
      (h : clflushZugriff w c silizium a = some w') :
      HwWcSchritt w w' (.clflush c silizium a)
  | prefetch (w : HwWcMaschine1287) (h0 : PrefetchHinweis)
      (a : Adresse) (w' : HwWcMaschine1287)
      (h : prefetchZugriff w h0 a = some w') :
      HwWcSchritt w w' (.prefetch h0 a)
  | zaun (w : HwWcMaschine1287) (c : Nat) (w' : HwWcMaschine1287)
      (h : wcZaunZustand w c = some w') :
      HwWcSchritt w w' (.zaun c)

/-- Every extended step preserves well-formedness: profiles are never
    touched; only memory and buffers move, and `HwWf` sees neither. -/
theorem hwWcSchritt_wf (w w' : HwWcMaschine1287)
    (e : WcEreignis1287) (h : HwWcSchritt w w' e)
    (hwf : HwWcWf w) : HwWcWf w' := by
  cases h with
  | wcSpeichern c a v w' h =>
    unfold wcStoreZugriff at h
    by_cases hg : (speicherTyp w.profil a 1 == .wc &&
      w.masch.mem.schreibbar a) = true
    · rw [if_pos hg] at h
      cases h
      exact hwf
    · rw [if_neg hg] at h
      cases h
  | wtSpeichern a v w' h =>
    unfold wtStoreZugriff at h
    by_cases hg : (speicherTyp w.profil a 1 == .wt &&
      w.masch.mem.schreibbar a) = true
    · rw [if_pos hg] at h
      cases h
      exact hwf
    · rw [if_neg hg] at h
      cases h
  | wpSpeichern a v w' h =>
    unfold wpStoreZugriff at h
    by_cases hg : (speicherTyp w.profil a 1 == .wp &&
      w.masch.mem.schreibbar a) = true
    · rw [if_pos hg] at h
      cases h
      exact hwf
    · rw [if_neg hg] at h
      cases h
  | clflush c s a w' h =>
    unfold clflushZugriff at h
    by_cases hg : (s &&
      (w.masch.mem.lesbar a || w.masch.mem.ausfuehrbar a)) = true
    · rw [if_pos hg] at h
      cases h
      exact hwf
    · rw [if_neg hg] at h
      cases h
  | prefetch h0 a w' h =>
    unfold prefetchZugriff at h
    cases h
    exact hwf
  | zaun c w' h =>
    unfold wcZaunZustand at h
    cases hs : drainVoll ⟨w.masch.mem, w.masch.puffer⟩ c with
    | none => simp [hs] at h
    | some s =>
      simp only [hs] at h
      cases h
      exact hwf

/-! ## 4. Step agreement: the functions discharge the stated rules.

  BYPASS (WC): a retired WC store touches no coherent byte, no WB
  buffer and no foreign WC buffer -- the own WC buffer and the log
  each grow by exactly the new event. GO-THROUGH (WT/WP): memory is
  written on retire and no buffer grows. NOP (PREFETCHh): nothing
  moves but the log. LINE (CLFLUSH): the acting core's line entries
  drain; everything else is kept. FENCE: both own buffers empty
  afterwards, foreign buffers byte-identical. -/

/-- BYPASS: a WC-store step leaves machine bytes, WB buffers and
    foreign WC buffers alone and appends exactly one WC entry. -/
theorem hwWcStore_bypass (w w' : HwWcMaschine1287)
    (c : Nat) (a : Adresse) (v : Byte)
    (h : HwWcSchritt w w' (.wcSpeichern c a v)) :
    w'.masch = w.masch ∧
      w'.wc c = w.wc c ++ [⟨a, v⟩] ∧
      w'.wcLog = w.wcLog ++ [.wcSpeichern c a v] ∧
      ∀ d : Nat, d ≠ c → w'.wc d = w.wc d := by
  cases h with
  | wcSpeichern c a v w' h =>
    unfold wcStoreZugriff at h
    by_cases hg : (speicherTyp w.profil a 1 == .wc &&
      w.masch.mem.schreibbar a) = true
    · rw [if_pos hg] at h
      cases h
      refine ⟨rfl, ?_, rfl, ?_⟩
      · exact pufferSetze_gleich _ _ _
      · intro d hd
        exact pufferSetze_anders _ _ hd
    · rw [if_neg hg] at h
      cases h

/-- GO-THROUGH (WT): memory is written on retire; both buffer kinds
    and the profile are kept; the log grows by the event. -/
theorem hwWtStore_durch (w w' : HwWcMaschine1287)
    (a : Adresse) (v : Byte)
    (h : HwWcSchritt w w' (.wtSpeichern a v)) :
    w'.masch.mem.bytes a = v ∧
      w'.masch.puffer = w.masch.puffer ∧
      w'.wc = w.wc ∧
      w'.wcLog = w.wcLog ++ [.wtSpeichern a v] := by
  cases h with
  | wtSpeichern a v w' h =>
    unfold wtStoreZugriff at h
    by_cases hg : (speicherTyp w.profil a 1 == .wt &&
      w.masch.mem.schreibbar a) = true
    · rw [if_pos hg] at h
      cases h
      refine ⟨?_, rfl, rfl, rfl⟩
      simp
    · rw [if_neg hg] at h
      cases h

/-- GO-THROUGH (WP): same memory effect as WT, recorded as WP. -/
theorem hwWpStore_durch (w w' : HwWcMaschine1287)
    (a : Adresse) (v : Byte)
    (h : HwWcSchritt w w' (.wpSpeichern a v)) :
    w'.masch.mem.bytes a = v ∧
      w'.masch.puffer = w.masch.puffer ∧
      w'.wc = w.wc ∧
      w'.wcLog = w.wcLog ++ [.wpSpeichern a v] := by
  cases h with
  | wpSpeichern a v w' h =>
    unfold wpStoreZugriff at h
    by_cases hg : (speicherTyp w.profil a 1 == .wp &&
      w.masch.mem.schreibbar a) = true
    · rw [if_pos hg] at h
      cases h
      refine ⟨?_, rfl, rfl, rfl⟩
      simp
    · rw [if_neg hg] at h
      cases h

/-- NOP: a PREFETCHh step changes nothing but the log. -/
theorem hwPrefetch_nop (w w' : HwWcMaschine1287)
    (h0 : PrefetchHinweis) (a : Adresse)
    (h : HwWcSchritt w w' (.prefetch h0 a)) :
    w'.masch = w.masch ∧ w'.wc = w.wc ∧
      w'.wcLog = w.wcLog ++ [.prefetch h0 a] := by
  cases h with
  | prefetch h0 a w' h =>
    unfold prefetchZugriff at h
    cases h
    exact ⟨rfl, rfl, rfl⟩

/-- FENCE (WB half, reused): the fence drains the own WB buffer, so
    it is empty and fence-ready afterwards. -/
theorem hwWcZaun_wbLeer (w w' : HwWcMaschine1287) (c : Nat)
    (h : HwWcSchritt w w' (.zaun c)) :
    w'.masch.puffer c = [] ∧
      zaunBereit ⟨w'.masch.mem, w'.masch.puffer⟩ c = true := by
  cases h with
  | zaun c w' h =>
    unfold wcZaunZustand at h
    cases hs : drainVoll ⟨w.masch.mem, w.masch.puffer⟩ c with
    | none => simp [hs] at h
    | some s =>
      simp only [hs] at h
      cases h
      refine ⟨?_, ?_⟩
      · exact drain_voll_leer _ s c hs
      · exact drain_voll_bereit _ s c hs

/-- FENCE (WC half): the own WC buffer is empty afterwards. -/
theorem hwWcZaun_wcLeer (w w' : HwWcMaschine1287) (c : Nat)
    (h : HwWcSchritt w w' (.zaun c)) :
    w'.wc c = [] := by
  cases h with
  | zaun c w' h =>
    unfold wcZaunZustand at h
    cases hs : drainVoll ⟨w.masch.mem, w.masch.puffer⟩ c with
    | none => simp [hs] at h
    | some s =>
      simp only [hs] at h
      cases h
      exact pufferSetze_gleich _ _ _

/-- FENCE (foreign frame, WB half reused): no foreign WB entry is
    discharged -- no fence-everywhere. -/
theorem hwWcZaun_fremdWb (w w' : HwWcMaschine1287) (c : Nat)
    {d : Nat} (hd : d ≠ c)
    (h : HwWcSchritt w w' (.zaun c)) :
    w'.masch.puffer d = w.masch.puffer d := by
  cases h with
  | zaun c w' h =>
    unfold wcZaunZustand at h
    cases hs : drainVoll ⟨w.masch.mem, w.masch.puffer⟩ c with
    | none => simp [hs] at h
    | some s =>
      simp only [hs] at h
      cases h
      exact mfenceDrain_fremd ⟨w.masch.mem, w.masch.puffer⟩ s c hd hs

/-- FENCE (foreign frame, WC half): no foreign WC entry moves. -/
theorem hwWcZaun_fremdWc (w w' : HwWcMaschine1287) (c : Nat)
    {d : Nat} (hd : d ≠ c)
    (h : HwWcSchritt w w' (.zaun c)) :
    w'.wc d = w.wc d := by
  cases h with
  | zaun c w' h =>
    unfold wcZaunZustand at h
    cases hs : drainVoll ⟨w.masch.mem, w.masch.puffer⟩ c with
    | none => simp [hs] at h
    | some s =>
      simp only [hs] at h
      cases h
      exact pufferSetze_anders _ _ hd

/-! ## 5. The family plug as an `HwAdapter`, with planted refusals.

  The type profile rides the event as checked input data (as 1133's
  `UcZugriff1133` carries its `UcProfil`). WC stores are admitted
  under their gate with the machine unchanged (the bypass content --
  the WC buffer itself rides the extended relation of §3); WT/WP
  stores write the memory byte on the bare machine (the go-through
  content, in full); PREFETCHh is always a NOP. CLFLUSH and the fence
  have no bare-machine plug: their effects need buffer state the
  adapter cannot carry, so their machine-visible content rides §3
  alone (documented, never silently admitted). -/

/-- Access request on the bare coherent machine. -/
inductive WcZugriff1287 where
  | wcSpeichere : Adresse → Byte → TypProfil → WcZugriff1287
  | wtSpeichere : Adresse → Byte → TypProfil → WcZugriff1287
  | wpSpeichere : Adresse → Byte → TypProfil → WcZugriff1287
  | holeVor : PrefetchHinweis → Adresse → WcZugriff1287

/-- Adapter step on the bare machine. -/
def wcAdapterSchritt (m : HwMaschine) (_ : Nat) :
    WcZugriff1287 → Option HwMaschine
  | .wcSpeichere a _ profil =>
    if speicherTyp profil a 1 == .wc && m.mem.schreibbar a then some m
    else none
  | .wtSpeichere a v profil =>
    if speicherTyp profil a 1 == .wt && m.mem.schreibbar a then
      some { m with mem :=
        { m.mem with bytes := fun x =>
          if x = a then v else m.mem.bytes x } }
    else none
  | .wpSpeichere a v profil =>
    if speicherTyp profil a 1 == .wp && m.mem.schreibbar a then
      some { m with mem :=
        { m.mem with bytes := fun x =>
          if x = a then v else m.mem.bytes x } }
    else none
  | .holeVor _ _ => some m

/-- The plug as a coherent-machine adapter. -/
def adapterWc1287 : HwAdapter WcZugriff1287 := ⟨wcAdapterSchritt⟩

/-- ADMITTED: a WC store under its gate steps to the same machine
    (bypass, machine-visible content). -/
theorem wcAdapter_wc_ok (m : HwMaschine) (c : Nat) (a : Adresse)
    (v : Byte) (profil : TypProfil)
    (ht : speicherTyp profil a 1 = .wc)
    (hw : m.mem.schreibbar a = true) :
    wcAdapterSchritt m c (.wcSpeichere a v profil) = some m := by
  have e1 : (speicherTyp profil a 1 == .wc) = true := by simp [ht]
  have hgate : (speicherTyp profil a 1 == .wc &&
    m.mem.schreibbar a) = true := by simp [e1, hw]
  show (if speicherTyp profil a 1 == .wc && m.mem.schreibbar a
    then some m else none) = some m
  exact if_pos hgate

/-- ADMITTED: a WT store under its gate writes the memory byte. -/
theorem wcAdapter_wt_mem (m : HwMaschine) (c : Nat) (a : Adresse)
    (v : Byte) (profil : TypProfil)
    (ht : speicherTyp profil a 1 = .wt)
    (hw : m.mem.schreibbar a = true) :
    ∃ m' : HwMaschine,
      wcAdapterSchritt m c (.wtSpeichere a v profil) = some m' ∧
        m'.mem.bytes a = v ∧ m'.puffer = m.puffer := by
  have e1 : (speicherTyp profil a 1 == .wt) = true := by simp [ht]
  have hgate : (speicherTyp profil a 1 == .wt &&
    m.mem.schreibbar a) = true := by simp [e1, hw]
  refine ⟨{ m with mem :=
      { m.mem with bytes := fun x =>
        if x = a then v else m.mem.bytes x } }, ?_, ?_, rfl⟩
  · show (if speicherTyp profil a 1 == .wt && m.mem.schreibbar a
      then some _ else none) = some _
    rw [if_pos hgate]
  · simp

/-- ADMITTED: PREFETCHh is a NOP at every address -- no permission
    check, no fault, machine unchanged. -/
theorem wcAdapter_prefetch_nop (m : HwMaschine) (c : Nat)
    (h0 : PrefetchHinweis) (a : Adresse) :
    wcAdapterSchritt m c (.holeVor h0 a) = some m := rfl

/-- REFUSED: a WC request at a WT address is no WC access. -/
theorem wcAdapter_wc_falscherTyp (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Byte) (profil : TypProfil)
    (ht : speicherTyp profil a 1 = .wt) :
    wcAdapterSchritt m c (.wcSpeichere a v profil) = none := by
  have hne : (speicherTyp profil a 1 == .wc) = false := by simp [ht]
  have hgate : ¬(speicherTyp profil a 1 == .wc &&
    m.mem.schreibbar a) = true := by simp [hne]
  show (if speicherTyp profil a 1 == .wc && m.mem.schreibbar a
    then (some m) else none) = none
  exact if_neg hgate

/-- REFUSED: a WC request at a UC address is no WC access (lane
    1133 owns UC). -/
theorem wcAdapter_wc_nichtUc (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Byte) (profil : TypProfil)
    (ht : speicherTyp profil a 1 = .uc) :
    wcAdapterSchritt m c (.wcSpeichere a v profil) = none := by
  have hne : (speicherTyp profil a 1 == .wc) = false := by simp [ht]
  have hgate : ¬(speicherTyp profil a 1 == .wc &&
    m.mem.schreibbar a) = true := by simp [hne]
  show (if speicherTyp profil a 1 == .wc && m.mem.schreibbar a
    then (some m) else none) = none
  exact if_neg hgate

/-- REFUSED: without write permission no typed store is admitted. -/
theorem wcAdapter_ohneSchreibrecht (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Byte) (profil : TypProfil)
    (hw : m.mem.schreibbar a = false) :
    wcAdapterSchritt m c (.wcSpeichere a v profil) = none ∧
      wcAdapterSchritt m c (.wtSpeichere a v profil) = none ∧
      wcAdapterSchritt m c (.wpSpeichere a v profil) = none := by
  have g1 : ¬(speicherTyp profil a 1 == .wc &&
    m.mem.schreibbar a) = true := by simp [hw]
  have g2 : ¬(speicherTyp profil a 1 == .wt &&
    m.mem.schreibbar a) = true := by simp [hw]
  have g3 : ¬(speicherTyp profil a 1 == .wp &&
    m.mem.schreibbar a) = true := by simp [hw]
  refine ⟨?_, ?_, ?_⟩
  · show (if speicherTyp profil a 1 == .wc && m.mem.schreibbar a
      then (some m) else none) = none
    exact if_neg g1
  · show (if speicherTyp profil a 1 == .wt && m.mem.schreibbar a
      then (some _) else none) = none
    exact if_neg g2
  · show (if speicherTyp profil a 1 == .wp && m.mem.schreibbar a
      then (some _) else none) = none
    exact if_neg g3

/-- The plug preserves well-formedness: WC/prefetch keep the machine,
    WT/WP move memory only (profiles untouched). -/
theorem adapterWc1287_wf (m m' : HwMaschine) (c : Nat)
    (e : WcZugriff1287)
    (h : (adapterWc1287).schritt m c e = some m')
    (hwf : HwWf m) : HwWf m' := by
  cases e with
  | wcSpeichere a v profil =>
    have h' : wcAdapterSchritt m c (.wcSpeichere a v profil) =
        some m' := h
    simp only [wcAdapterSchritt] at h'
    by_cases hg : (speicherTyp profil a 1 == .wc &&
      m.mem.schreibbar a) = true
    · rw [if_pos hg] at h'
      cases h'
      exact hwf
    · rw [if_neg hg] at h'
      cases h'
  | wtSpeichere a v profil =>
    have h' : wcAdapterSchritt m c (.wtSpeichere a v profil) =
        some m' := h
    simp only [wcAdapterSchritt] at h'
    by_cases hg : (speicherTyp profil a 1 == .wt &&
      m.mem.schreibbar a) = true
    · rw [if_pos hg] at h'
      cases h'
      exact hwf
    · rw [if_neg hg] at h'
      cases h'
  | wpSpeichere a v profil =>
    have h' : wcAdapterSchritt m c (.wpSpeichere a v profil) =
        some m' := h
    simp only [wcAdapterSchritt] at h'
    by_cases hg : (speicherTyp profil a 1 == .wp &&
      m.mem.schreibbar a) = true
    · rw [if_pos hg] at h'
      cases h'
      exact hwf
    · rw [if_neg hg] at h'
      cases h'
  | holeVor h0 a =>
    have h' : wcAdapterSchritt m c (.holeVor h0 a) = some m' := h
    have h'' : (some m : Option HwMaschine) = some m' := h'
    cases h''
    exact hwf

/-- AGREEMENT (WT): the plug step is exactly the extended WT function
    projected to the bare machine. -/
theorem adapterWt_stimmt_ueberein (w : HwWcMaschine1287) (c : Nat)
    (a : Adresse) (v : Byte) :
    wcAdapterSchritt w.masch c (.wtSpeichere a v w.profil) =
      (wtStoreZugriff w a v).map (fun w' => w'.masch) := by
  simp only [wcAdapterSchritt, wtStoreZugriff]
  by_cases hg : (speicherTyp w.profil a 1 == .wt &&
    w.masch.mem.schreibbar a) = true <;> simp [hg]

/-- AGREEMENT (WC): the plug step is exactly the extended WC function
    projected to the bare machine (bypass: the machine is unchanged). -/
theorem adapterWc_stimmt_ueberein (w : HwWcMaschine1287) (c : Nat)
    (a : Adresse) (v : Byte) :
    wcAdapterSchritt w.masch c (.wcSpeichere a v w.profil) =
      (wcStoreZugriff w c a v).map (fun w' => w'.masch) := by
  simp only [wcAdapterSchritt, wcStoreZugriff]
  by_cases hg : (speicherTyp w.profil a 1 == .wc &&
    w.masch.mem.schreibbar a) = true <;> simp [hg]

/-- ADMITTED: a WP store under its gate writes the memory byte
    (go-through, recorded as WP). -/
theorem wcAdapter_wp_mem (m : HwMaschine) (c : Nat) (a : Adresse)
    (v : Byte) (profil : TypProfil)
    (ht : speicherTyp profil a 1 = .wp)
    (hw : m.mem.schreibbar a = true) :
    ∃ m' : HwMaschine,
      wcAdapterSchritt m c (.wpSpeichere a v profil) = some m' ∧
        m'.mem.bytes a = v ∧ m'.puffer = m.puffer := by
  have e1 : (speicherTyp profil a 1 == .wp) = true := by simp [ht]
  have hgate : (speicherTyp profil a 1 == .wp &&
    m.mem.schreibbar a) = true := by simp [e1, hw]
  refine ⟨{ m with mem :=
      { m.mem with bytes := fun x =>
        if x = a then v else m.mem.bytes x } }, ?_, ?_, rfl⟩
  · show (if speicherTyp profil a 1 == .wp && m.mem.schreibbar a
      then some _ else none) = some _
    rw [if_pos hgate]
  · simp

/-! ## 6. Step frame for CLFLUSH: log and kept entries.

  The line drain keeps every entry outside the stated line pending
  and records the flush; the drained bytes themselves enter the
  connection of §7 as computed facts. -/

/-- LINE FRAME: a CLFLUSH step keeps exactly the entries outside the
    stated line pending and records the flush in the log. -/
theorem hwClflush_rahmen (w w' : HwWcMaschine1287) (c : Nat)
    (s : Bool) (a : Adresse)
    (h : HwWcSchritt w w' (.clflush c s a)) :
    w'.wc c =
        (w.wc c).filter (fun e => !(inLinie a e.addr)) ∧
      w'.wcLog = w.wcLog ++ [.clflush c s a] := by
  cases h with
  | clflush c s a w' h =>
    unfold clflushZugriff at h
    by_cases hg : (s &&
      (w.masch.mem.lesbar a || w.masch.mem.ausfuehrbar a)) = true
    · rw [if_pos hg] at h
      cases h
      refine ⟨?_, rfl⟩
      show (pufferSetze w.wc c _) c = _
      simp [pufferSetze]
    · rw [if_neg hg] at h
      cases h

/-! ## 7. Joint witness: buffer, flush, go-through, hint, fence.

  Two cores touch typed memory: core 0 buffers two WC stores -- one
  flushed store-ordered by CLFLUSH, one drained by the fence -- while
  core 1 still reads the old bytes; a WT store goes through at once;
  PREFETCHh is a NOP even at an unreadable address. Non-degenerate:
  canonical memory changes twice (the CLFLUSH line drain and the
  fence drain), on two cores, beside planted refusals. -/

/-- Witness WC region: two bytes at 8192 (one stated line). -/
def witWcReg1287 : Region := ⟨8192, 2, true, true, false⟩

/-- Witness WT region: one byte at 8194. -/
def witWtReg1287 : Region := ⟨8194, 1, true, true, false⟩

/-- Witness WP region: one byte at 8195. -/
def witWpReg1287 : Region := ⟨8195, 1, true, true, false⟩

/-- Witness type profile: disjoint typed regions over the accepted
    witness image (data cells 8192..8199 stay readable/writable). -/
def witProfil1287 : TypProfil :=
  [(witWcReg1287, .wc), (witWtReg1287, .wt), (witWpReg1287, .wp)]

/-- Witness addresses: two WC cells on one stated line, the WT cell,
    and an unreadable address for the hint NOP. -/
def witWc1287 : Adresse := BitVec.ofNat 64 8192
def witWcB1287 : Adresse := BitVec.ofNat 64 8193
def witWt1287 : Adresse := BitVec.ofNat 64 8194
def witNo1287 : Adresse := BitVec.ofNat 64 0

/-- The profile types the WC cells WC. -/
theorem witTyp_wc1287 : speicherTyp witProfil1287 witWc1287 1 = .wc := by
  decide

/-- The profile types the WT cell WT. -/
theorem witTyp_wt1287 : speicherTyp witProfil1287 witWt1287 1 = .wt := by
  decide

/-- The profile types 8195 WP. -/
theorem witTyp_wp1287 :
    speicherTyp witProfil1287 (BitVec.ofNat 64 8195) 1 = .wp := by
  decide

/-- Off-profile addresses stay WB. -/
theorem witTyp_wb1287 :
    speicherTyp witProfil1287 (BitVec.ofNat 64 8196) 1 = .wb := by
  decide

/-- Witness start: shared image, empty buffers, empty log. -/
def witW01287 : HwWcMaschine1287 :=
  ⟨hwWitStart, witProfil1287, fun _ => [], []⟩

/-- The witness start is well-formed. -/
theorem witW01287_wf : HwWcWf witW01287 := hwWitStart_wf

/-- After the first WC store: core 0 buffers 42 at 8192. -/
def witW11287 : HwWcMaschine1287 :=
  ⟨witW01287.masch, witW01287.profil,
    pufferSetze witW01287.wc 0
      (witW01287.wc 0 ++ [⟨witWc1287, natByte 42⟩]),
    witW01287.wcLog ++ [.wcSpeichern 0 witWc1287 (natByte 42)]⟩

/-- Stage 1: the WC store retires (buffered, machine untouched). -/
theorem wit_schritt11287 :
    HwWcSchritt witW01287 witW11287
      (.wcSpeichern 0 witWc1287 (natByte 42)) := by
  have hgate : (speicherTyp witW01287.profil witWc1287 1 == .wc &&
    witW01287.masch.mem.schreibbar witWc1287) = true := by decide
  exact HwWcSchritt.wcSpeichern witW01287 0 witWc1287 (natByte 42)
    witW11287 (by unfold wcStoreZugriff witW11287; rw [if_pos hgate])

/-- After the CLFLUSH: the stated line drains to memory. -/
def witW21287 : HwWcMaschine1287 :=
  let (mem', rest) :=
    wcLinieSpuele witW11287.masch.mem (witW11287.wc 0) witWc1287
  ⟨{ witW11287.masch with mem := mem' }, witW11287.profil,
    pufferSetze witW11287.wc 0 rest,
    witW11287.wcLog ++ [.clflush 0 true witWc1287]⟩

/-- Stage 2: CLFLUSH retires store-ordered over the line. -/
theorem wit_schritt21287 :
    HwWcSchritt witW11287 witW21287
      (.clflush 0 true witWc1287) := by
  have hgate : (true &&
    (witW11287.masch.mem.lesbar witWc1287 ||
      witW11287.masch.mem.ausfuehrbar witWc1287)) = true := by decide
  exact HwWcSchritt.clflush witW11287 0 true witWc1287
    witW21287 (by unfold clflushZugriff witW21287; rw [if_pos hgate])

/-- After the second WC store: core 0 buffers 43 at 8193. -/
def witW31287 : HwWcMaschine1287 :=
  ⟨witW21287.masch, witW21287.profil,
    pufferSetze witW21287.wc 0
      (witW21287.wc 0 ++ [⟨witWcB1287, natByte 43⟩]),
    witW21287.wcLog ++ [.wcSpeichern 0 witWcB1287 (natByte 43)]⟩

/-- Stage 3: the second WC store retires (buffered). -/
theorem wit_schritt31287 :
    HwWcSchritt witW21287 witW31287
      (.wcSpeichern 0 witWcB1287 (natByte 43)) := by
  have hgate : (speicherTyp witW21287.profil witWcB1287 1 == .wc &&
    witW21287.masch.mem.schreibbar witWcB1287) = true := by decide
  exact HwWcSchritt.wcSpeichern witW21287 0 witWcB1287 (natByte 43)
    witW31287 (by unfold wcStoreZugriff witW31287; rw [if_pos hgate])

/-- After the WT store: memory carries 9 at 8194 at once. -/
def witW41287 : HwWcMaschine1287 :=
  ⟨{ witW31287.masch with mem :=
      { witW31287.masch.mem with bytes := fun x =>
        if x = witWt1287 then natByte 9
        else witW31287.masch.mem.bytes x } },
    witW31287.profil, witW31287.wc,
    witW31287.wcLog ++ [.wtSpeichern witWt1287 (natByte 9)]⟩

/-- Stage 4: the WT store retires (go-through). -/
theorem wit_schritt41287 :
    HwWcSchritt witW31287 witW41287
      (.wtSpeichern witWt1287 (natByte 9)) := by
  have hgate : (speicherTyp witW31287.profil witWt1287 1 == .wt &&
    witW31287.masch.mem.schreibbar witWt1287) = true := by decide
  exact HwWcSchritt.wtSpeichern witW31287 witWt1287 (natByte 9)
    witW41287 (by unfold wtStoreZugriff witW41287; rw [if_pos hgate])

/-- After the hint: nothing moves but the log. -/
def witW51287 : HwWcMaschine1287 :=
  ⟨witW41287.masch, witW41287.profil, witW41287.wc,
    witW41287.wcLog ++ [.prefetch .t0 witNo1287]⟩

/-- Stage 5: PREFETCHh retires as a NOP at an unreadable address. -/
theorem wit_schritt51287 :
    HwWcSchritt witW41287 witW51287
      (.prefetch .t0 witNo1287) := by
  exact HwWcSchritt.prefetch witW41287 .t0 witNo1287
    witW51287 (by unfold prefetchZugriff; rfl)

/-- After the fence: both own buffers drain to memory. -/
def witW61287 : HwWcMaschine1287 :=
  match drainVoll ⟨witW51287.masch.mem, witW51287.masch.puffer⟩ 0 with
  | none => witW51287
  | some s =>
    ⟨⟨wcLeere s.mem (witW51287.wc 0), witW51287.masch.kerne, s.puffer,
      witW51287.masch.hw, witW51287.masch.bereit⟩,
    witW51287.profil, pufferSetze witW51287.wc 0 [],
    witW51287.wcLog ++ [.zaun 0]⟩

/-- Stage 6: the fence drains the second WC store to memory. -/
theorem wit_schritt61287 :
    HwWcSchritt witW51287 witW61287 (.zaun 0) := by
  exact HwWcSchritt.zaun witW51287 0
    witW61287 (by unfold wcZaunZustand; rfl)

/-- Owner forwarding after stage 1: core 0 reads its own WC byte. -/
theorem wit_eigen11287 :
    wcLesbar witW11287 0 witWc1287 = some (natByte 42) := by
  decide

/-- No foreign forwarding after stage 1: core 1 reads the old byte. -/
theorem wit_fremd11287 :
    wcLesbar witW11287 1 witWc1287 = some (natByte 0) := by
  decide

/-- The first cell is still zero after stage 1 (buffered, bypassed). -/
theorem wit_still11287 :
    witW11287.masch.mem.bytes witWc1287 = natByte 0 := by
  decide

/-- The CLFLUSH installs the line byte into memory. -/
theorem wit_spuelung21287 :
    witW21287.masch.mem.bytes witWc1287 = natByte 42 := by
  decide

/-- Owner forwarding after stage 3: core 0 reads its second WC byte. -/
theorem wit_eigen31287 :
    wcLesbar witW31287 0 witWcB1287 = some (natByte 43) := by
  decide

/-- No foreign forwarding after stage 3: core 1 reads the old byte. -/
theorem wit_fremd31287 :
    wcLesbar witW31287 1 witWcB1287 = some (natByte 0) := by
  decide

/-- The WT store is visible in memory: the go-through assumption. -/
theorem wit_durch41287 :
    WtWpBusAnnahme witW41287 witWt1287 (natByte 9) := by
  show witW41287.masch.mem.bytes witWt1287 = natByte 9
  decide

/-- The second cell is still zero before the fence (buffered). -/
theorem wit_null51287 :
    witW51287.masch.mem.bytes witWcB1287 = natByte 0 := by
  decide

/-- The fence installs the second WC byte into memory. -/
theorem wit_spuelung61287 :
    witW61287.masch.mem.bytes witWcB1287 = natByte 43 := by
  decide

end HwMemWC1287

end Gabbro.Grammatik.X86
