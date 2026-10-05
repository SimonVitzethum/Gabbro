/-
  File:      Grammatik/X86/HwWcOrdering.lean
  Subject:   WC eviction order and CLFLUSHOPT/CLWB on the lifted WC machine.

  Lane 1301: follow-up of lane 1287 (`HwMemTypesWC.lean`): its CUTS leave
  OPEN cross-core WC same-line eviction order, WC read ordering, and
  CLFLUSHOPT/CLWB. This file lifts the accepted 1287 machine
  (`HwWcMaschine1287`) unchanged -- never copied -- and adds: WC buffer
  eviction as a nondeterministic oldest-first drain step, a same-core WC
  read observation after a WC store, CLFLUSHOPT (weakly ordered, ordered
  by SFENCE/MFENCE) and CLWB (no invalidation requirement).

  Manual provenance (official Intel SDM 325462-093US, September 2026,
  local `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`):
  - CLFLUSHOPT entry: `NFx 66 0F AE /7`, ordered wrt fences, locked
    RMW and older writes to the line; NOT ordered wrt other
    CLFLUSHOPT/CLFLUSH/CLWB or younger writes; SFENCE orders it;
    byte-load faults (execute-only allowed); #UD without the CPUID bit.
  - CLWB entry: `66 0F AE /6`, same fence/older-write ordering, same
    non-ordering, writes back and MAY retain the line (no invalidation);
    byte-load faults; #UD without the CPUID bit.
  - Vol.1 12.8/WC buffer: separate from caches and store buffer, not
    snooped (no coherency); eviction protocol is implementation
    dependent; WC weakly ordered; buffer 2 may appear before buffer 1
    on the bus; partial writes possible.
  The memory-ordering chapter is NOT supplied in the clone: every
  ordering rule below is a NAMED assumption (`WcEvictOrdAnnahme1301`,
  `ClflushoptZaunAnnahme1301`, `ClwbKeepAnnahme1301`); silicon behaviour
  is never proved.
-/
import Grammatik.X86.Hw.Speicher.HwMemTypesWC

namespace Gabbro.Grammatik.X86

namespace HwWcOrd1301

/-- Observable events on the lifted WC machine: a retired WC store, a
    spontaneous eviction drain, a same-core WC read observation, the two
    weakly ordered flushes (each carrying its stated CPUID bit), and a
    fence drain. The acting core rides the event wherever the effect is
    per-core, as in `HwEreignis` and `WcEreignis1287`. -/
inductive WcOrdEreignis1301 where
  | wcGepuffert : Nat → Adresse → Byte → WcOrdEreignis1301
  | evict : Nat → Adresse → Byte → WcOrdEreignis1301
  | wcGelesen : Nat → Adresse → Byte → WcOrdEreignis1301
  | clflushopt : Nat → Bool → Adresse → WcOrdEreignis1301
  | clwb : Nat → Bool → Adresse → WcOrdEreignis1301
  | zaun : Nat → WcOrdEreignis1301
  deriving DecidableEq, Repr

/-! ## 1. Machine: the accepted 1287 WC machine, lifted unchanged.

  Buffers, memory and the type profile ride inside `wc`; this file adds
  only the ordering-side program-order log. Nothing is copied. -/

/-- The lifted ordering machine: the accepted 1287 WC machine plus the
    ordering-side program-order log. -/
structure HwWcOrdMaschine1301 where
  wc : HwMemWC1287.HwWcMaschine1287
  ordLog : List WcOrdEreignis1301

/-- Well-formedness is exactly the lifted 1287 well-formedness. -/
def HwWcOrdWf1301 (m : HwWcOrdMaschine1301) : Prop :=
  HwMemWC1287.HwWcWf m.wc

/-! ## 2. Steps on the lifted machine.

  WC-store and fence cases reuse the accepted 1287 functions BY
  REFERENCE (`wcStoreZugriff`, `wcZaunZustand`); eviction drains the
  oldest pending entry of the acting core (MODEL of the
  implementation-dependent eviction: per-core FIFO here, cross-core
  same-line order is the named assumption `WcEvictOrdAnnahme1301`). -/

/-- Spontaneous WC eviction: the oldest pending entry of core `c`
    drains to memory. Empty buffer refuses (`none`). -/
def wcEvictZugriff1301 (m : HwWcOrdMaschine1301) (c : Nat) :
    Option HwWcOrdMaschine1301 :=
  match m.wc.wc c with
  | [] => none
  | e :: rest =>
    some ⟨{ m.wc with
      masch := { m.wc.masch with
        mem := HwMemWC1287.wcSpeicherSchreibe m.wc.masch.mem e },
      wc := pufferSetze m.wc.wc c rest },
      m.ordLog ++ [.evict c e.addr e.wert]⟩

/-- WC-store retire on the lifted machine: the accepted 1287 function,
    with the ordering log recording the retirement. -/
def wcStoreZugriff1301 (m : HwWcOrdMaschine1301) (c : Nat)
    (a : Adresse) (v : Byte) : Option HwWcOrdMaschine1301 :=
  match HwMemWC1287.wcStoreZugriff m.wc c a v with
  | none => none
  | some w' => some ⟨w', m.ordLog ++ [.wcGepuffert c a v]⟩

/-- Fence drain (SFENCE/MFENCE/LOCK retired) on the lifted machine: the
    accepted 1287 function, with the ordering log recording the fence. -/
def wcZaunZustand1301 (m : HwWcOrdMaschine1301) (c : Nat) :
    Option HwWcOrdMaschine1301 :=
  match HwMemWC1287.wcZaunZustand m.wc c with
  | none => none
  | some w' => some ⟨w', m.ordLog ++ [.zaun c]⟩

/-- CLFLUSHOPT retire: named silicon bit plus byte-read fault rules
    (readable, or execute-only -- the SDM's stated allowance, as for
    1287's CLFLUSH). The acting core's line entries drain to memory
    through the accepted `wcLinieSpuele`; foreign WC entries for the
    same line stay pending (cross-core order is the named assumption).
    ORDERING (never a step effect): weakly ordered; SFENCE/MFENCE order
    it -- the named assumption `ClflushoptZaunAnnahme1301`. -/
def clflushoptZugriff1301 (m : HwWcOrdMaschine1301) (c : Nat)
    (silizium : Bool) (a : Adresse) : Option HwWcOrdMaschine1301 :=
  if silizium &&
      (m.wc.masch.mem.lesbar a || m.wc.masch.mem.ausfuehrbar a) then
    let (mem', rest) :=
      HwMemWC1287.wcLinieSpuele m.wc.masch.mem (m.wc.wc c) a
    some ⟨⟨{ m.wc.masch with mem := mem' }, m.wc.profil,
      pufferSetze m.wc.wc c rest, m.wc.wcLog⟩,
      m.ordLog ++ [.clflushopt c silizium a]⟩
  else none

/-- CLWB retire: named silicon bit plus the same byte-read fault rules.
    The line drains through the accepted `wcLinieSpuele`; with no data
    cache modelled the memory effect is the CLFLUSHOPT one, and the
    NO-INVALIDATION content (the line MAY stay cached) is the named
    assumption `ClwbKeepAnnahme1301`. -/
def clwbZugriff1301 (m : HwWcOrdMaschine1301) (c : Nat)
    (silizium : Bool) (a : Adresse) : Option HwWcOrdMaschine1301 :=
  if silizium &&
      (m.wc.masch.mem.lesbar a || m.wc.masch.mem.ausfuehrbar a) then
    let (mem', rest) :=
      HwMemWC1287.wcLinieSpuele m.wc.masch.mem (m.wc.wc c) a
    some ⟨⟨{ m.wc.masch with mem := mem' }, m.wc.profil,
      pufferSetze m.wc.wc c rest, m.wc.wcLog⟩,
      m.ordLog ++ [.clwb c silizium a]⟩
  else none

/-- Same-core WC read observation: admitted exactly where the acting
    core reads `v` through the accepted `wcLesbar` (own WC entry first,
    then own WB entry, then memory; never a foreign buffer). The machine
    is unchanged; only the log records the observation. -/
def wcReadZugriff1301 (m : HwWcOrdMaschine1301) (c : Nat)
    (a : Adresse) (v : Byte) : Option HwWcOrdMaschine1301 :=
  if HwMemWC1287.wcLesbar m.wc c a = some v then
    some ⟨m.wc, m.ordLog ++ [.wcGelesen c a v]⟩
  else none

/-- One ordering step, each case from its function above. -/
inductive HwWcOrdSchritt1301 :
    HwWcOrdMaschine1301 → HwWcOrdMaschine1301 → WcOrdEreignis1301 → Prop where
  | wcSpeichern (m : HwWcOrdMaschine1301) (c : Nat) (a : Adresse)
      (v : Byte) (m' : HwWcOrdMaschine1301)
      (h : wcStoreZugriff1301 m c a v = some m') :
      HwWcOrdSchritt1301 m m' (.wcGepuffert c a v)
  | evict (m : HwWcOrdMaschine1301) (c : Nat) (m' : HwWcOrdMaschine1301)
      (e : TSOEintrag)
      (h : wcEvictZugriff1301 m c = some m')
      (hkopf : (m.wc.wc c).head? = some e) :
      HwWcOrdSchritt1301 m m' (.evict c e.addr e.wert)
  | wcLesen (m : HwWcOrdMaschine1301) (c : Nat) (a : Adresse)
      (v : Byte) (m' : HwWcOrdMaschine1301)
      (h : wcReadZugriff1301 m c a v = some m') :
      HwWcOrdSchritt1301 m m' (.wcGelesen c a v)
  | clflushopt (m : HwWcOrdMaschine1301) (c : Nat) (silizium : Bool)
      (a : Adresse) (m' : HwWcOrdMaschine1301)
      (h : clflushoptZugriff1301 m c silizium a = some m') :
      HwWcOrdSchritt1301 m m' (.clflushopt c silizium a)
  | clwb (m : HwWcOrdMaschine1301) (c : Nat) (silizium : Bool)
      (a : Adresse) (m' : HwWcOrdMaschine1301)
      (h : clwbZugriff1301 m c silizium a = some m') :
      HwWcOrdSchritt1301 m m' (.clwb c silizium a)
  | zaun (m : HwWcOrdMaschine1301) (c : Nat) (m' : HwWcOrdMaschine1301)
      (h : wcZaunZustand1301 m c = some m') :
      HwWcOrdSchritt1301 m m' (.zaun c)

/-! ## 3. Preservation and agreement: the lifted content.

  Profiles are never touched; only memory and the WC buffer move, and
  `HwWf` sees neither. -/

/-- Every ordering step preserves well-formedness: WC-store and fence
    steps reuse the accepted 1287 preservation; eviction and the flushes
    move memory and the WC buffer only; the read changes nothing. -/
theorem hwWcOrdSchritt_wf1301 (m m' : HwWcOrdMaschine1301)
    (e : WcOrdEreignis1301) (h : HwWcOrdSchritt1301 m m' e)
    (hwf : HwWcOrdWf1301 m) : HwWcOrdWf1301 m' := by
  cases h with
  | wcSpeichern c a v m' h =>
    unfold wcStoreZugriff1301 at h
    cases hs : HwMemWC1287.wcStoreZugriff m.wc c a v with
    | none => simp [hs] at h
    | some w' =>
      simp only [hs] at h
      cases h
      exact HwMemWC1287.hwWcSchritt_wf m.wc w' _
        (.wcSpeichern m.wc c a v w' hs) hwf
  | evict c m' e h hkopf =>
    unfold wcEvictZugriff1301 at h
    cases hb : m.wc.wc c with
    | nil => simp [hb] at h
    | cons e' rest =>
      simp only [hb] at h
      cases h
      exact hwf
  | wcLesen c a v m' h =>
    unfold wcReadZugriff1301 at h
    by_cases hg : HwMemWC1287.wcLesbar m.wc c a = some v
    · rw [if_pos hg] at h
      cases h
      exact hwf
    · rw [if_neg hg] at h
      cases h
  | clflushopt c s a m' h =>
    unfold clflushoptZugriff1301 at h
    by_cases hg : (s &&
      (m.wc.masch.mem.lesbar a ||
        m.wc.masch.mem.ausfuehrbar a)) = true
    · rw [if_pos hg] at h
      cases h
      exact hwf
    · rw [if_neg hg] at h
      cases h
  | clwb c s a m' h =>
    unfold clwbZugriff1301 at h
    by_cases hg : (s &&
      (m.wc.masch.mem.lesbar a ||
        m.wc.masch.mem.ausfuehrbar a)) = true
    · rw [if_pos hg] at h
      cases h
      exact hwf
    · rw [if_neg hg] at h
      cases h
  | zaun c m' h =>
    unfold wcZaunZustand1301 at h
    cases hs : HwMemWC1287.wcZaunZustand m.wc c with
    | none => simp [hs] at h
    | some w' =>
      simp only [hs] at h
      cases h
      exact HwMemWC1287.hwWcSchritt_wf m.wc w' _
        (.zaun m.wc c w' hs) hwf

/-- BYPASS (lifted): a WC-store step leaves the coherent machine
    alone and appends exactly one WC entry; the ordering log records
    the retirement. -/
theorem hwWcOrdStore_bypass1301 (m m' : HwWcOrdMaschine1301)
    (c : Nat) (a : Adresse) (v : Byte)
    (h : HwWcOrdSchritt1301 m m' (.wcGepuffert c a v)) :
    m'.wc.masch = m.wc.masch ∧
      m'.wc.wc c = m.wc.wc c ++ [⟨a, v⟩] ∧
      m'.ordLog = m.ordLog ++ [.wcGepuffert c a v] := by
  cases h with
  | wcSpeichern c a v m' h =>
    unfold wcStoreZugriff1301 at h
    cases hs : HwMemWC1287.wcStoreZugriff m.wc c a v with
    | none => simp [hs] at h
    | some w' =>
      simp only [hs] at h
      cases h
      have hb := HwMemWC1287.hwWcStore_bypass m.wc w' c a v
        (HwMemWC1287.HwWcSchritt.wcSpeichern m.wc c a v w' hs)
      exact ⟨hb.1, hb.2.1, rfl⟩

/-- WC READ ORDERING (same core): after a retired WC store the acting
    core reads the stored byte back (own-buffer forwarding, reused from
    the accepted table through `neuestens_angehaengt`). Foreign cores
    never forward (1287's `wcLesbar`: only the own buffers are read). -/
theorem hwWcOrdLesen_nach_speichern1301
    (w w' : HwMemWC1287.HwWcMaschine1287)
    (c : Nat) (a : Adresse) (v : Byte)
    (h : HwMemWC1287.wcStoreZugriff w c a v = some w')
    (hrd : w.masch.mem.lesbar a = true) :
    HwMemWC1287.wcLesbar w' c a = some v := by
  have hb := HwMemWC1287.hwWcStore_bypass w w' c a v
    (HwMemWC1287.HwWcSchritt.wcSpeichern w c a v w' h)
  unfold HwMemWC1287.wcLesbar
  simp [hb.1, hb.2.1, hrd, neuestens_angehaengt]

/-- READ FRAME: a WC-read step changes nothing but the ordering log,
    and the observed value is exactly the accepted `wcLesbar` value. -/
theorem hwWcOrdLesen_rahmen1301 (m m' : HwWcOrdMaschine1301)
    (c : Nat) (a : Adresse) (v : Byte)
    (h : HwWcOrdSchritt1301 m m' (.wcGelesen c a v)) :
    m'.wc = m.wc ∧
      m'.ordLog = m.ordLog ++ [.wcGelesen c a v] ∧
      HwMemWC1287.wcLesbar m.wc c a = some v := by
  cases h with
  | wcLesen c a v m' h =>
    unfold wcReadZugriff1301 at h
    by_cases hg : HwMemWC1287.wcLesbar m.wc c a = some v
    · rw [if_pos hg] at h
      cases h
      exact ⟨rfl, rfl, hg⟩
    · rw [if_neg hg] at h
      cases h

/-- EVICTION FRAME: an eviction step installs the buffer head into
    memory, drops exactly that entry, records the drain, and leaves
    foreign buffers alone. -/
theorem hwWcOrdEvict_rahmen1301 (m m' : HwWcOrdMaschine1301)
    (c : Nat) (a : Adresse) (v : Byte)
    (h : HwWcOrdSchritt1301 m m' (.evict c a v)) :
    m'.wc.masch.mem.bytes a = v ∧
      m'.wc.wc c = (m.wc.wc c).drop 1 ∧
      m'.ordLog = m.ordLog ++ [.evict c a v] ∧
      ∀ d : Nat, d ≠ c → m'.wc.wc d = m.wc.wc d := by
  cases h with
  | evict c m' e h hk =>
    unfold wcEvictZugriff1301 at h
    cases hb : m.wc.wc c with
    | nil =>
      rw [hb] at hk
      cases hk
    | cons e' rest =>
      simp only [hb] at h
      cases h
      rw [hb] at hk
      have heq : e' = e := Option.some_inj.mp hk
      rw [heq]
      refine ⟨?_, ?_, rfl, ?_⟩
      · simp [HwMemWC1287.wcSpeicherSchreibe]
      · simp [pufferSetze]
      · intro d hd
        simp [pufferSetze, hd]

/-- FENCE FRAME (lifted): after a fence step both own buffers are
    empty and fence-ready, the fence is recorded, and no foreign
    buffer moved. -/
theorem hwWcOrdZaun_leer1301 (m m' : HwWcOrdMaschine1301) (c : Nat)
    (h : HwWcOrdSchritt1301 m m' (.zaun c)) :
    m'.wc.masch.puffer c = [] ∧
      m'.wc.wc c = [] ∧
      zaunBereit ⟨m'.wc.masch.mem, m'.wc.masch.puffer⟩ c = true ∧
      m'.ordLog = m.ordLog ++ [.zaun c] ∧
      ∀ d : Nat, d ≠ c →
        m'.wc.masch.puffer d = m.wc.masch.puffer d ∧
          m'.wc.wc d = m.wc.wc d := by
  cases h with
  | zaun c m' h =>
    unfold wcZaunZustand1301 at h
    cases hs : HwMemWC1287.wcZaunZustand m.wc c with
    | none => simp [hs] at h
    | some w' =>
      simp only [hs] at h
      cases h
      have hz := HwMemWC1287.HwWcSchritt.zaun m.wc c w' hs
      have hwb := HwMemWC1287.hwWcZaun_wbLeer m.wc w' c hz
      have hwc := HwMemWC1287.hwWcZaun_wcLeer m.wc w' c hz
      refine ⟨hwb.1, hwc, hwb.2, rfl, ?_⟩
      intro d hd
      exact ⟨HwMemWC1287.hwWcZaun_fremdWb m.wc w' c hd hz,
        HwMemWC1287.hwWcZaun_fremdWc m.wc w' c hd hz⟩

/-- LINE FRAME (CLFLUSHOPT): the acting core keeps exactly the
    entries outside the stated line pending and records the flush;
    foreign WC entries for the same line stay pending (their order
    against this drain is the named eviction assumption). -/
theorem hwWcOrdFlushopt_rahmen1301 (m m' : HwWcOrdMaschine1301)
    (c : Nat) (s : Bool) (a : Adresse)
    (h : HwWcOrdSchritt1301 m m' (.clflushopt c s a)) :
    m'.wc.wc c =
        (m.wc.wc c).filter
          (fun e => !(HwMemWC1287.inLinie a e.addr)) ∧
      m'.ordLog = m.ordLog ++ [.clflushopt c s a] := by
  cases h with
  | clflushopt c s a m' h =>
    unfold clflushoptZugriff1301 at h
    by_cases hg : (s &&
      (m.wc.masch.mem.lesbar a ||
        m.wc.masch.mem.ausfuehrbar a)) = true
    · rw [if_pos hg] at h
      cases h
      refine ⟨?_, rfl⟩
      show (pufferSetze m.wc.wc c _) c = _
      simp [pufferSetze]
    · rw [if_neg hg] at h
      cases h

/-- LINE FRAME (CLWB): same kept-pending frame as CLFLUSHOPT, recorded
    as CLWB; the no-invalidation content rides the named assumption
    `ClwbKeepAnnahme1301`. -/
theorem hwWcOrdClwb_rahmen1301 (m m' : HwWcOrdMaschine1301)
    (c : Nat) (s : Bool) (a : Adresse)
    (h : HwWcOrdSchritt1301 m m' (.clwb c s a)) :
    m'.wc.wc c =
        (m.wc.wc c).filter
          (fun e => !(HwMemWC1287.inLinie a e.addr)) ∧
      m'.ordLog = m.ordLog ++ [.clwb c s a] := by
  cases h with
  | clwb c s a m' h =>
    unfold clwbZugriff1301 at h
    by_cases hg : (s &&
      (m.wc.masch.mem.lesbar a ||
        m.wc.masch.mem.ausfuehrbar a)) = true
    · rw [if_pos hg] at h
      cases h
      refine ⟨?_, rfl⟩
      show (pufferSetze m.wc.wc c _) c = _
      simp [pufferSetze]
    · rw [if_neg hg] at h
      cases h

/-! ## 4. Planted refusals: empty eviction, missing silicon bit,
    wrong type, missing permission. -/

/-- REFUSED: eviction from an empty WC buffer is no step. -/
theorem hwWcOrdEvict_leer_verweigert1301 (m : HwWcOrdMaschine1301)
    (c : Nat) (h : m.wc.wc c = []) :
    wcEvictZugriff1301 m c = none := by
  unfold wcEvictZugriff1301
  simp [h]

/-- REFUSED: without the stated CPUID bit neither weakly ordered flush
    is admitted (the manual's #UD has no step here). -/
theorem hwWcOrdFlush_ohneBit1301 (m : HwWcOrdMaschine1301) (c : Nat)
    (a : Adresse) :
    clflushoptZugriff1301 m c false a = none ∧
      clwbZugriff1301 m c false a = none := by
  have g : ¬(false &&
    (m.wc.masch.mem.lesbar a ||
      m.wc.masch.mem.ausfuehrbar a)) = true := by simp
  refine ⟨?_, ?_⟩
  · unfold clflushoptZugriff1301
    rw [if_neg g]
  · unfold clwbZugriff1301
    rw [if_neg g]

/-- REFUSED: without any permission (neither readable nor executable)
    neither weakly ordered flush is admitted. -/
theorem hwWcOrdFlush_ohneRecht1301 (m : HwWcOrdMaschine1301) (c : Nat)
    (s : Bool) (a : Adresse)
    (hnoRd : m.wc.masch.mem.lesbar a = false)
    (hnoEx : m.wc.masch.mem.ausfuehrbar a = false) :
    clflushoptZugriff1301 m c s a = none ∧
      clwbZugriff1301 m c s a = none := by
  have g : ¬(s &&
    (m.wc.masch.mem.lesbar a ||
      m.wc.masch.mem.ausfuehrbar a)) = true := by simp [hnoRd, hnoEx]
  refine ⟨?_, ?_⟩
  · unfold clflushoptZugriff1301
    rw [if_neg g]
  · unfold clwbZugriff1301
    rw [if_neg g]

/-- REFUSED: a WC store at a non-WC address is no WC retirement
    (the accepted gate, lifted). -/
theorem hwWcOrdStore_falscherTyp1301 (m : HwWcOrdMaschine1301)
    (c : Nat) (a : Adresse) (v : Byte)
    (ht : HwMemWC1287.speicherTyp m.wc.profil a 1 =
      HwMemWC1287.SpeicherTypWC.wt) :
    wcStoreZugriff1301 m c a v = none := by
  have hne : (HwMemWC1287.speicherTyp m.wc.profil a 1 ==
    HwMemWC1287.SpeicherTypWC.wc) = false := by simp [ht]
  have hg : ¬(HwMemWC1287.speicherTyp m.wc.profil a 1 ==
    HwMemWC1287.SpeicherTypWC.wc &&
    m.wc.masch.mem.schreibbar a) = true := by simp [hne]
  unfold wcStoreZugriff1301
  have hs : HwMemWC1287.wcStoreZugriff m.wc c a v = none := by
    unfold HwMemWC1287.wcStoreZugriff
    rw [if_neg hg]
  simp [hs]

/-! ## 5. Byte decoders: CLFLUSHOPT and CLWB.

  CLFLUSHOPT is `NFx 66 0F AE /7` and CLWB is `66 0F AE /6`, each with
  a MEMORY ModRM (provenance in the file header). The mod=3 row
  refuses on both (register form has no memory operand); the plain
  CLFLUSH bytes (no 66 prefix) refuse on both; the LOCK prefix refuses
  on both (the manual's #UD has no step here). -/

/-- CLFLUSHOPT byte decode: `66 0F AE /7` with a MEMORY ModRM. -/
def decodeClflushopt1301 : List Byte → Option (List Byte)
  | [b66, b0, b1, m] =>
    if byteNat b66 == 102 && byteNat b0 == 15 && byteNat b1 == 174 &&
        (byteNat m / 8) % 8 == 7 && byteNat m / 64 != 3 then some []
    else none
  | _ => none

/-- CLWB byte decode: `66 0F AE /6` with a MEMORY ModRM. -/
def decodeClwb1301 : List Byte → Option (List Byte)
  | [b66, b0, b1, m] =>
    if byteNat b66 == 102 && byteNat b0 == 15 && byteNat b1 == 174 &&
        (byteNat m / 8) % 8 == 6 && byteNat m / 64 != 3 then some []
    else none
  | _ => none

/-- Canonical CLFLUSHOPT bytes (mod=0, reg=7) decode. -/
theorem pin_clflushopt1301 :
    decodeClflushopt1301
      [natByte 102, natByte 15, natByte 174, natByte 56] =
      some [] := by
  decide

/-- Canonical CLWB bytes (mod=0, reg=6) decode. -/
theorem pin_clwb1301 :
    decodeClwb1301
      [natByte 102, natByte 15, natByte 174, natByte 48] =
      some [] := by
  decide

/-- The two forms never shadow each other: CLWB bytes are no
    CLFLUSHOPT and CLFLUSHOPT bytes are no CLWB. -/
theorem pin_opt_nicht_wb1301 :
    decodeClflushopt1301
      [natByte 102, natByte 15, natByte 174, natByte 48] = none ∧
    decodeClwb1301
      [natByte 102, natByte 15, natByte 174, natByte 56] = none := by
  decide

/-- The register row (mod=3) is neither form. -/
theorem pin_flush_register_verweigert1301 :
    decodeClflushopt1301
      [natByte 102, natByte 15, natByte 174, natByte 248] = none ∧
    decodeClwb1301
      [natByte 102, natByte 15, natByte 174, natByte 240] = none := by
  decide

/-- The plain CLFLUSH bytes (no 66 prefix) are neither form. -/
theorem pin_clflush_kein_opt_wb1301 :
    decodeClflushopt1301
      [natByte 15, natByte 174, natByte 56] = none ∧
    decodeClwb1301
      [natByte 15, natByte 174, natByte 56] = none := by
  decide

/-- The LOCK prefix refuses on both decoders (exact-length shapes). -/
theorem pin_flush_lock_verweigert1301 :
    decodeClflushopt1301
      [natByte 240, natByte 102, natByte 15, natByte 174,
        natByte 56] = none ∧
    decodeClwb1301
      [natByte 240, natByte 102, natByte 15, natByte 174,
        natByte 48] = none := by
  decide

/-! ## 6. Named ordering assumptions.

  The memory-ordering chapter is NOT supplied in the clone, so every
  ordering rule is a NAMED assumption here (never a proved silicon
  claim). What the STEPS guarantee (FIFO per-core drains, log order,
  kept-pending frames) is proved in §3; what the PINS show is assumed. -/

/-- NAMED ASSUMPTION (WC eviction order): every retired WC drain
    appears on the pins -- no loss, no duplication. ORDER is
    deliberately NOT claimed: the SDM states that buffer 2 may appear
    before buffer 1 on the system bus. -/
def WcEvictOrdAnnahme1301 (log pins : List WcOrdEreignis1301) : Prop :=
  pins.length = log.length

/-- From the named eviction assumption, pins and log run together. -/
theorem wcEvictPinsLaenge1301 (log pins : List WcOrdEreignis1301)
    (h : WcEvictOrdAnnahme1301 log pins) :
    pins.length = log.length := h

/-- NAMED ASSUMPTION (CLFLUSHOPT fence order): the pins honor the
    fence-separated order in the log -- a CLFLUSHOPT retired before an
    SFENCE/MFENCE on the same core is ordered by it (SDM: SFENCE
    orders CLFLUSHOPT; CLFLUSHOPT is unordered against other flushes
    and younger writes, which the log never orders either). -/
def ClflushoptZaunAnnahme1301 (log pins : List WcOrdEreignis1301) :
    Prop :=
  pins = log

/-- From the named fence-order assumption, pins run with the log. -/
theorem clflushoptZaunPinsLaenge1301 (log pins : List WcOrdEreignis1301)
    (h : ClflushoptZaunAnnahme1301 log pins) :
    pins.length = log.length := by rw [h]

/-- PROGRAM ORDER (proved): a CLFLUSHOPT step followed by a fence step
    on the same core leaves the flush before the fence in the log --
    the order the named assumption lifts to the pins. -/
theorem clflushoptVorZaun1301 (m1 m2 m3 : HwWcOrdMaschine1301)
    (c : Nat) (a : Adresse)
    (h1 : HwWcOrdSchritt1301 m1 m2 (.clflushopt c true a))
    (h2 : HwWcOrdSchritt1301 m2 m3 (.zaun c)) :
    m2.ordLog = m1.ordLog ++ [.clflushopt c true a] ∧
      m3.ordLog = m2.ordLog ++ [.zaun c] ∧
      (.clflushopt c true a) ∈ m3.ordLog ∧
      (.zaun c) ∈ m3.ordLog := by
  have hf := hwWcOrdFlushopt_rahmen1301 m1 m2 c true a h1
  have hz2 : m3.ordLog = m2.ordLog ++ [.zaun c] := by
    cases h2 with
    | zaun c m' h =>
      unfold wcZaunZustand1301 at h
      cases hs : HwMemWC1287.wcZaunZustand m2.wc c with
      | none => simp [hs] at h
      | some w' =>
        simp only [hs] at h
        cases h
        rfl
  refine ⟨hf.2, hz2, ?_, ?_⟩
  · rw [hz2, hf.2]
    simp
  · rw [hz2]
    simp

/-- NAMED ASSUMPTION (CLWB no invalidation): a retired CLWB leaves the
    line's memory byte readable back -- the model drains the line, and
    silicon MAY retain it cached (SDM: CLWB may retain the line in a
    non-modified state). -/
def ClwbKeepAnnahme1301 (m : HwWcOrdMaschine1301) (a : Adresse)
    (v : Byte) : Prop :=
  m.wc.masch.mem.bytes a = v

/-- From the named keep assumption, the memory byte reads back. -/
theorem clwbKeep_liest1301 (m : HwWcOrdMaschine1301) (a : Adresse)
    (v : Byte) (h : ClwbKeepAnnahme1301 m a v) :
    m.wc.masch.mem.bytes a = v := h

/-! ## 7. The family plug as an `HwAdapter`.

  The type profile rides the event as checked input data (as 1287's
  `WcZugriff1287` carries its profile). An eviction drain is admitted
  under its gate with the machine-visible content (the drained byte in
  memory); a same-core WC read is admitted under its gate as a NOP.
  CLFLUSHOPT and CLWB have no bare-machine plug: their effects need
  WC-buffer state the adapter cannot carry, so their machine-visible
  content rides §2-§3 alone (documented, never silently admitted). -/

/-- Access request on the bare coherent machine. -/
inductive WcOrdZugriff1301 where
  | evictEin : Adresse → Byte → HwMemWC1287.TypProfil → WcOrdZugriff1301
  | liesWC : Adresse → HwMemWC1287.TypProfil → WcOrdZugriff1301

/-- Adapter step on the bare machine. -/
def wcOrdAdapterSchritt1301 (m : HwMaschine) (_ : Nat) :
    WcOrdZugriff1301 → Option HwMaschine
  | .evictEin a v profil =>
    if HwMemWC1287.speicherTyp profil a 1 ==
        HwMemWC1287.SpeicherTypWC.wc &&
        m.mem.schreibbar a then
      some { m with mem :=
        { m.mem with bytes := fun x =>
          if x = a then v else m.mem.bytes x } }
    else none
  | .liesWC a profil =>
    if HwMemWC1287.speicherTyp profil a 1 ==
        HwMemWC1287.SpeicherTypWC.wc &&
        m.mem.lesbar a then some m
    else none

/-- The plug as a coherent-machine adapter. -/
def adapterWcOrd1301 : HwAdapter WcOrdZugriff1301 :=
  ⟨wcOrdAdapterSchritt1301⟩

/-- ADMITTED: an eviction drain under its gate writes the memory byte. -/
theorem wcOrdAdapter_evict_mem1301 (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Byte) (profil : HwMemWC1287.TypProfil)
    (ht : HwMemWC1287.speicherTyp profil a 1 =
      HwMemWC1287.SpeicherTypWC.wc)
    (hw : m.mem.schreibbar a = true) :
    ∃ m' : HwMaschine,
      wcOrdAdapterSchritt1301 m c (.evictEin a v profil) = some m' ∧
        m'.mem.bytes a = v ∧ m'.puffer = m.puffer := by
  have e1 : (HwMemWC1287.speicherTyp profil a 1 ==
    HwMemWC1287.SpeicherTypWC.wc) = true := by simp [ht]
  have hgate : (HwMemWC1287.speicherTyp profil a 1 ==
    HwMemWC1287.SpeicherTypWC.wc &&
    m.mem.schreibbar a) = true := by simp [e1, hw]
  refine ⟨{ m with mem :=
      { m.mem with bytes := fun x =>
        if x = a then v else m.mem.bytes x } }, ?_, ?_, rfl⟩
  · show (if HwMemWC1287.speicherTyp profil a 1 ==
      HwMemWC1287.SpeicherTypWC.wc &&
      m.mem.schreibbar a
      then some _ else none) = some _
    rw [if_pos hgate]
  · simp

/-- ADMITTED: a same-core WC read under its gate is a NOP. -/
theorem wcOrdAdapter_liest_ok1301 (m : HwMaschine) (c : Nat)
    (a : Adresse) (profil : HwMemWC1287.TypProfil)
    (ht : HwMemWC1287.speicherTyp profil a 1 =
      HwMemWC1287.SpeicherTypWC.wc)
    (hrd : m.mem.lesbar a = true) :
    wcOrdAdapterSchritt1301 m c (.liesWC a profil) = some m := by
  have e1 : (HwMemWC1287.speicherTyp profil a 1 ==
    HwMemWC1287.SpeicherTypWC.wc) = true := by simp [ht]
  have hgate : (HwMemWC1287.speicherTyp profil a 1 ==
    HwMemWC1287.SpeicherTypWC.wc &&
    m.mem.lesbar a) = true := by simp [e1, hrd]
  show (if HwMemWC1287.speicherTyp profil a 1 ==
    HwMemWC1287.SpeicherTypWC.wc &&
    m.mem.lesbar a
    then (some m) else none) = some m
  exact if_pos hgate

/-- REFUSED: an eviction request at a non-WC address is no drain. -/
theorem wcOrdAdapter_evict_falscherTyp1301 (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Byte) (profil : HwMemWC1287.TypProfil)
    (ht : HwMemWC1287.speicherTyp profil a 1 =
      HwMemWC1287.SpeicherTypWC.wt) :
    wcOrdAdapterSchritt1301 m c (.evictEin a v profil) = none := by
  have hne : (HwMemWC1287.speicherTyp profil a 1 ==
    HwMemWC1287.SpeicherTypWC.wc) = false := by simp [ht]
  have hgate : ¬(HwMemWC1287.speicherTyp profil a 1 ==
    HwMemWC1287.SpeicherTypWC.wc &&
    m.mem.schreibbar a) = true := by simp [hne]
  show (if HwMemWC1287.speicherTyp profil a 1 ==
    HwMemWC1287.SpeicherTypWC.wc &&
    m.mem.schreibbar a
    then (some _) else none) = none
  exact if_neg hgate

/-- REFUSED: without write permission no eviction drain is admitted,
    and without read permission no WC read is admitted. -/
theorem wcOrdAdapter_ohneRecht1301 (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Byte) (profil : HwMemWC1287.TypProfil)
    (hw : m.mem.schreibbar a = false)
    (hrd : m.mem.lesbar a = false) :
    wcOrdAdapterSchritt1301 m c (.evictEin a v profil) = none ∧
      wcOrdAdapterSchritt1301 m c (.liesWC a profil) = none := by
  have g1 : ¬(HwMemWC1287.speicherTyp profil a 1 ==
    HwMemWC1287.SpeicherTypWC.wc &&
    m.mem.schreibbar a) = true := by simp [hw]
  have g2 : ¬(HwMemWC1287.speicherTyp profil a 1 ==
    HwMemWC1287.SpeicherTypWC.wc &&
    m.mem.lesbar a) = true := by simp [hrd]
  refine ⟨?_, ?_⟩
  · show (if HwMemWC1287.speicherTyp profil a 1 ==
      HwMemWC1287.SpeicherTypWC.wc &&
      m.mem.schreibbar a
      then (some _) else none) = none
    exact if_neg g1
  · show (if HwMemWC1287.speicherTyp profil a 1 ==
      HwMemWC1287.SpeicherTypWC.wc &&
      m.mem.lesbar a
      then (some _) else none) = none
    exact if_neg g2

/-- The plug preserves well-formedness: eviction moves memory only
    and the read keeps the machine (profiles untouched). -/
theorem adapterWcOrd1301_wf (m m' : HwMaschine) (c : Nat)
    (e : WcOrdZugriff1301)
    (h : (adapterWcOrd1301).schritt m c e = some m')
    (hwf : HwWf m) : HwWf m' := by
  cases e with
  | evictEin a v profil =>
    have h' : wcOrdAdapterSchritt1301 m c (.evictEin a v profil) =
        some m' := h
    simp only [wcOrdAdapterSchritt1301] at h'
    by_cases hg : (HwMemWC1287.speicherTyp profil a 1 ==
      HwMemWC1287.SpeicherTypWC.wc &&
      m.mem.schreibbar a) = true
    · rw [if_pos hg] at h'
      cases h'
      exact hwf
    · rw [if_neg hg] at h'
      cases h'
  | liesWC a profil =>
    have h' : wcOrdAdapterSchritt1301 m c (.liesWC a profil) =
        some m' := h
    simp only [wcOrdAdapterSchritt1301] at h'
    by_cases hg : (HwMemWC1287.speicherTyp profil a 1 ==
      HwMemWC1287.SpeicherTypWC.wc &&
      m.mem.lesbar a) = true
    · rw [if_pos hg] at h'
      cases h'
      exact hwf
    · rw [if_neg hg] at h'
      cases h'

/-- AGREEMENT: on a singleton WC buffer the plug's eviction drain is
    exactly the extended eviction projected to the bare machine. -/
theorem adapterEvict_stimmt_ueberein1301 (m : HwWcOrdMaschine1301)
    (c : Nat) (a : Adresse) (v : Byte)
    (hbuf : m.wc.wc c = [⟨a, v⟩])
    (hgate : (HwMemWC1287.speicherTyp m.wc.profil a 1 ==
      HwMemWC1287.SpeicherTypWC.wc &&
      m.wc.masch.mem.schreibbar a) = true) :
    wcOrdAdapterSchritt1301 m.wc.masch c
        (.evictEin a v m.wc.profil) =
      (wcEvictZugriff1301 m c).map (fun m' => m'.wc.masch) := by
  have e1 : wcOrdAdapterSchritt1301 m.wc.masch c
      (.evictEin a v m.wc.profil) =
      some { m.wc.masch with mem :=
        (HwMemWC1287.wcSpeicherSchreibe m.wc.masch.mem ⟨a, v⟩) } := by
    show (if (HwMemWC1287.speicherTyp m.wc.profil a 1 ==
      HwMemWC1287.SpeicherTypWC.wc &&
      m.wc.masch.mem.schreibbar a)
      then some _ else none) = some _
    rw [if_pos hgate]
    rfl
  have e2 : (wcEvictZugriff1301 m c).map (fun m' => m'.wc.masch) =
      some { m.wc.masch with mem :=
        (HwMemWC1287.wcSpeicherSchreibe m.wc.masch.mem ⟨a, v⟩) } := by
    simp only [wcEvictZugriff1301, hbuf]
    rfl
  rw [e1, e2]

/-! ## 8. Joint witness: store, SFENCE drain, ordered CLFLUSHOPT,
    CLWB without invalidation, second store, spontaneous eviction.

  Two cores touch typed WC memory: core 0 buffers a WC store (owner
  reads it back, core 1 still reads the old byte), an SFENCE/MFENCE
  drains it to memory, a CLFLUSHOPT retires ordered after that fence,
  a CLWB retires without invalidating the byte, and a second WC store
  drains through spontaneous eviction. Non-degenerate: canonical
  memory changes twice, on two cores, beside planted refusals. -/

/-- Witness start: the accepted 1287 start, empty ordering log. -/
def witM0_1301 : HwWcOrdMaschine1301 :=
  ⟨HwMemWC1287.witW01287, []⟩

/-- The witness start is well-formed. -/
theorem witM0_wf1301 : HwWcOrdWf1301 witM0_1301 :=
  HwMemWC1287.witW01287_wf

/-- After the WC store: core 0 buffers 42 at 8192 (accepted state). -/
def witM1_1301 : HwWcOrdMaschine1301 :=
  ⟨HwMemWC1287.witW11287,
    witM0_1301.ordLog ++
      [.wcGepuffert 0 HwMemWC1287.witWc1287 (natByte 42)]⟩

/-- Stage 1: the WC store retires (buffered, machine untouched). -/
theorem wit_schritt1_1301 :
    HwWcOrdSchritt1301 witM0_1301 witM1_1301
      (.wcGepuffert 0 HwMemWC1287.witWc1287 (natByte 42)) := by
  have hgate : (HwMemWC1287.speicherTyp HwMemWC1287.witW01287.profil
      HwMemWC1287.witWc1287 1 ==
      HwMemWC1287.SpeicherTypWC.wc &&
      HwMemWC1287.witW01287.masch.mem.schreibbar
        HwMemWC1287.witWc1287) = true := by decide
  have hs : HwMemWC1287.wcStoreZugriff HwMemWC1287.witW01287 0
      HwMemWC1287.witWc1287 (natByte 42) =
      some HwMemWC1287.witW11287 := by
    unfold HwMemWC1287.wcStoreZugriff HwMemWC1287.witW11287
    rw [if_pos hgate]
  have hstep : wcStoreZugriff1301 witM0_1301 0 HwMemWC1287.witWc1287
      (natByte 42) = some witM1_1301 := by
    unfold wcStoreZugriff1301
    cases hs2 : HwMemWC1287.wcStoreZugriff witM0_1301.wc 0
        HwMemWC1287.witWc1287 (natByte 42) with
    | none =>
      have h0 : witM0_1301.wc = HwMemWC1287.witW01287 := rfl
      rw [h0, hs] at hs2
      cases hs2
    | some w' =>
      dsimp only
      have h0 : witM0_1301.wc = HwMemWC1287.witW01287 := rfl
      have h2 : witM1_1301 = ⟨HwMemWC1287.witW11287,
          witM0_1301.ordLog ++ [WcOrdEreignis1301.wcGepuffert 0
            HwMemWC1287.witWc1287 (natByte 42)]⟩ := rfl
      have hw' : w' = HwMemWC1287.witW11287 := by
        rw [h0, hs] at hs2
        exact (Option.some_inj.mp hs2).symm
      rw [hw', h2]
  exact HwWcOrdSchritt1301.wcSpeichern witM0_1301 0 _ _ witM1_1301
    hstep

/-- Owner forwarding after stage 1: core 0 reads its own WC byte. -/
theorem wit_eigen1_1301 :
    HwMemWC1287.wcLesbar witM1_1301.wc 0
      HwMemWC1287.witWc1287 = some (natByte 42) := by
  decide

/-- No foreign forwarding after stage 1: core 1 reads the old byte. -/
theorem wit_fremd1_1301 :
    HwMemWC1287.wcLesbar witM1_1301.wc 1
      HwMemWC1287.witWc1287 = some (natByte 0) := by
  decide

/-- The first cell is still zero after stage 1 (buffered, bypassed). -/
theorem wit_still1_1301 :
    witM1_1301.wc.masch.mem.bytes HwMemWC1287.witWc1287 =
      natByte 0 := by
  decide

/-- After the fence: the SFENCE/MFENCE drains the WC store to
    memory. The state shares the match structure of
    `wcZaunZustand1301`, so the step below closes by `rfl`. -/
def witM2_1301 : HwWcOrdMaschine1301 :=
  match HwMemWC1287.wcZaunZustand HwMemWC1287.witW11287 0 with
  | none => ⟨HwMemWC1287.witW11287, witM1_1301.ordLog ++ [.zaun 0]⟩
  | some w' => ⟨w', witM1_1301.ordLog ++ [.zaun 0]⟩

/-- Stage 2: the fence drains the WC store to memory. -/
theorem wit_schritt2_1301 :
    HwWcOrdSchritt1301 witM1_1301 witM2_1301 (.zaun 0) := by
  exact HwWcOrdSchritt1301.zaun witM1_1301 0 witM2_1301
    (by unfold wcZaunZustand1301; rfl)

/-- The fence installs the WC byte into memory. -/
theorem wit_zaun2_1301 :
    witM2_1301.wc.masch.mem.bytes HwMemWC1287.witWc1287 =
      natByte 42 := by
  decide

/-- After the CLFLUSHOPT: the line is flushed, ordered after the
    fence (accepted line drain, computed). -/
def witM3_1301 : HwWcOrdMaschine1301 :=
  let (mem', rest) := HwMemWC1287.wcLinieSpuele
    witM2_1301.wc.masch.mem (witM2_1301.wc.wc 0)
    HwMemWC1287.witWc1287
  ⟨⟨{ witM2_1301.wc.masch with mem := mem' },
    witM2_1301.wc.profil,
    pufferSetze witM2_1301.wc.wc 0 rest, witM2_1301.wc.wcLog⟩,
    witM2_1301.ordLog ++
      [.clflushopt 0 true HwMemWC1287.witWc1287]⟩

/-- Stage 3: CLFLUSHOPT retires, ordered after the fence. -/
theorem wit_schritt3_1301 :
    HwWcOrdSchritt1301 witM2_1301 witM3_1301
      (.clflushopt 0 true HwMemWC1287.witWc1287) := by
  have hgate : (true &&
      (witM2_1301.wc.masch.mem.lesbar HwMemWC1287.witWc1287 ||
        witM2_1301.wc.masch.mem.ausfuehrbar
          HwMemWC1287.witWc1287)) = true := by decide
  have hstep : clflushoptZugriff1301 witM2_1301 0 true
      HwMemWC1287.witWc1287 = some witM3_1301 := by
    unfold clflushoptZugriff1301
    unfold witM3_1301
    rw [if_pos hgate]
  exact HwWcOrdSchritt1301.clflushopt witM2_1301 0 true _ witM3_1301
    hstep

/-- The flushed byte stays 42 in memory. -/
theorem wit_flush3_1301 :
    witM3_1301.wc.masch.mem.bytes HwMemWC1287.witWc1287 =
      natByte 42 := by
  decide

/-- After the CLWB: the line is written back and NOT invalidated
    (accepted line drain, computed; the byte reads back). -/
def witM4_1301 : HwWcOrdMaschine1301 :=
  let (mem', rest) := HwMemWC1287.wcLinieSpuele
    witM3_1301.wc.masch.mem (witM3_1301.wc.wc 0)
    HwMemWC1287.witWc1287
  ⟨⟨{ witM3_1301.wc.masch with mem := mem' },
    witM3_1301.wc.profil,
    pufferSetze witM3_1301.wc.wc 0 rest, witM3_1301.wc.wcLog⟩,
    witM3_1301.ordLog ++
      [.clwb 0 true HwMemWC1287.witWc1287]⟩

/-- Stage 4: CLWB retires without invalidating the byte. -/
theorem wit_schritt4_1301 :
    HwWcOrdSchritt1301 witM3_1301 witM4_1301
      (.clwb 0 true HwMemWC1287.witWc1287) := by
  have hgate : (true &&
      (witM3_1301.wc.masch.mem.lesbar HwMemWC1287.witWc1287 ||
        witM3_1301.wc.masch.mem.ausfuehrbar
          HwMemWC1287.witWc1287)) = true := by decide
  have hstep : clwbZugriff1301 witM3_1301 0 true
      HwMemWC1287.witWc1287 = some witM4_1301 := by
    unfold clwbZugriff1301
    unfold witM4_1301
    rw [if_pos hgate]
  exact HwWcOrdSchritt1301.clwb witM3_1301 0 true _ witM4_1301 hstep

/-- The CLWB keeps the byte: the no-invalidation assumption holds. -/
theorem wit_keep4_1301 :
    ClwbKeepAnnahme1301 witM4_1301 HwMemWC1287.witWc1287
      (natByte 42) := by
  show witM4_1301.wc.masch.mem.bytes _ = _
  decide

/-- After the second WC store: core 0 buffers 43 at 8193. -/
def witM5under1301 : HwMemWC1287.HwWcMaschine1287 :=
  ⟨witM4_1301.wc.masch, witM4_1301.wc.profil,
    pufferSetze witM4_1301.wc.wc 0
      (witM4_1301.wc.wc 0 ++
        [⟨HwMemWC1287.witWcB1287, natByte 43⟩]),
    witM4_1301.wc.wcLog ++
      [HwMemWC1287.WcEreignis1287.wcSpeichern 0
        HwMemWC1287.witWcB1287 (natByte 43)]⟩

/-- Lifted second-store state. -/
def witM5_1301 : HwWcOrdMaschine1301 :=
  ⟨witM5under1301,
    witM4_1301.ordLog ++
      [.wcGepuffert 0 HwMemWC1287.witWcB1287 (natByte 43)]⟩

/-- Stage 5: the second WC store retires (buffered). -/
theorem wit_schritt5_1301 :
    HwWcOrdSchritt1301 witM4_1301 witM5_1301
      (.wcGepuffert 0 HwMemWC1287.witWcB1287 (natByte 43)) := by
  have hgate : (HwMemWC1287.speicherTyp witM4_1301.wc.profil
      HwMemWC1287.witWcB1287 1 ==
      HwMemWC1287.SpeicherTypWC.wc &&
      witM4_1301.wc.masch.mem.schreibbar
        HwMemWC1287.witWcB1287) = true := by decide
  have hs : HwMemWC1287.wcStoreZugriff witM4_1301.wc 0
      HwMemWC1287.witWcB1287 (natByte 43) =
      some witM5under1301 := by
    unfold HwMemWC1287.wcStoreZugriff witM5under1301
    rw [if_pos hgate]
  have hstep : wcStoreZugriff1301 witM4_1301 0
      HwMemWC1287.witWcB1287 (natByte 43) = some witM5_1301 := by
    unfold wcStoreZugriff1301
    cases hs2 : HwMemWC1287.wcStoreZugriff witM4_1301.wc 0
        HwMemWC1287.witWcB1287 (natByte 43) with
    | none =>
      rw [hs] at hs2
      cases hs2
    | some w' =>
      dsimp only
      have h2 : witM5_1301 = ⟨witM5under1301,
          witM4_1301.ordLog ++ [WcOrdEreignis1301.wcGepuffert 0
            HwMemWC1287.witWcB1287 (natByte 43)]⟩ := rfl
      have hw' : w' = witM5under1301 := by
        rw [hs] at hs2
        exact (Option.some_inj.mp hs2).symm
      rw [hw', h2]
  exact HwWcOrdSchritt1301.wcSpeichern witM4_1301 0 _ _ witM5_1301
    hstep

/-- Owner forwarding after stage 5: core 0 reads its second WC byte. -/
theorem wit_eigen5_1301 :
    HwMemWC1287.wcLesbar witM5_1301.wc 0
      HwMemWC1287.witWcB1287 = some (natByte 43) := by
  decide

/-- No foreign forwarding after stage 5: core 1 reads the old byte. -/
theorem wit_fremd5_1301 :
    HwMemWC1287.wcLesbar witM5_1301.wc 1
      HwMemWC1287.witWcB1287 = some (natByte 0) := by
  decide

/-- The second cell is still zero before the eviction (buffered). -/
theorem wit_null5_1301 :
    witM5_1301.wc.masch.mem.bytes HwMemWC1287.witWcB1287 =
      natByte 0 := by
  decide

/-- After the spontaneous eviction: the oldest entry drains to memory.
    The state shares the match structure of `wcEvictZugriff1301`, so
    the step below closes by `rfl`. -/
def witM6_1301 : HwWcOrdMaschine1301 :=
  match witM5_1301.wc.wc 0 with
  | [] => witM5_1301
  | e :: rest =>
    ⟨⟨{ witM5_1301.wc.masch with mem :=
      (HwMemWC1287.wcSpeicherSchreibe witM5_1301.wc.masch.mem e) },
      witM5_1301.wc.profil,
      pufferSetze witM5_1301.wc.wc 0 rest, witM5_1301.wc.wcLog⟩,
      witM5_1301.ordLog ++ [.evict 0 e.addr e.wert]⟩

/-- Stage 6: spontaneous eviction drains the second WC store. -/
theorem wit_schritt6_1301 :
    HwWcOrdSchritt1301 witM5_1301 witM6_1301
      (.evict 0 HwMemWC1287.witWcB1287 (natByte 43)) := by
  have hkopf : (witM5_1301.wc.wc 0).head? =
      some ⟨HwMemWC1287.witWcB1287, natByte 43⟩ := by rfl
  exact HwWcOrdSchritt1301.evict witM5_1301 0 witM6_1301 _
    (by unfold wcEvictZugriff1301; rfl) hkopf

/-- The eviction installs the second WC byte into memory. -/
theorem wit_spuel6_1301 :
    witM6_1301.wc.masch.mem.bytes HwMemWC1287.witWcB1287 =
      natByte 43 := by
  decide

/-- The start buffer is empty: eviction refuses there. -/
theorem wit_leer0_1301 : witM0_1301.wc.wc 0 = [] := rfl

/-- The hint address is unreadable at the start. -/
theorem wit_nord0_1301 :
    witM0_1301.wc.masch.mem.lesbar HwMemWC1287.witNo1287 =
      false := by
  decide

/-- The hint address is unexecutable at the start. -/
theorem wit_noex0_1301 :
    witM0_1301.wc.masch.mem.ausfuehrbar HwMemWC1287.witNo1287 =
      false := by
  decide

/-! ## 9. Connection: WC eviction order and CLFLUSHOPT/CLWB end to end.

  On a reached six-step run -- WC store with owner-only forwarding,
  SFENCE/MFENCE drain, CLFLUSHOPT ordered after the fence, CLWB
  without invalidation, second WC store with owner-only forwarding,
  spontaneous eviction -- the model discharges: bypass (machine kept,
  own buffer grown), the owner/foreign observation split, the fence
  frame with the memory change, the fence-before-flush log order, the
  flush line frames, the wrong-type refusal, the CLWB byte equality,
  the eviction frame with the memory change, the empty-eviction, the
  missing-bit and the permission refusals, pins running with the logs,
  and preserved well-formedness. Every silicon correspondence stays a
  named assumption (`WcEvictOrdAnnahme1301`,
  `ClflushoptZaunAnnahme1301`, `ClwbKeepAnnahme1301`). -/

/-- **Connection (WC eviction order, CLFLUSHOPT/CLWB, end to end).** -/
theorem hwWcOrd_verbindung1301
    (m0 m1 m2 m3 m4 m5 m6 : HwWcOrdMaschine1301)
    (pins pins2 : List WcOrdEreignis1301)
    (hbus : WcEvictOrdAnnahme1301 m6.ordLog pins)
    (hzaunA : ClflushoptZaunAnnahme1301 m4.ordLog pins2)
    (hwf : HwWcOrdWf1301 m0)
    (h1 : HwWcOrdSchritt1301 m0 m1
      (.wcGepuffert 0 HwMemWC1287.witWc1287 (natByte 42)))
    (heigen1 : HwMemWC1287.wcLesbar m1.wc 0 HwMemWC1287.witWc1287 =
      some (natByte 42))
    (hfremd1 : HwMemWC1287.wcLesbar m1.wc 1 HwMemWC1287.witWc1287 =
      some (natByte 0))
    (hstill1 : m1.wc.masch.mem.bytes HwMemWC1287.witWc1287 =
      natByte 0)
    (h2 : HwWcOrdSchritt1301 m1 m2 (.zaun 0))
    (hzaun : m2.wc.masch.mem.bytes HwMemWC1287.witWc1287 =
      natByte 42)
    (h3 : HwWcOrdSchritt1301 m2 m3
      (.clflushopt 0 true HwMemWC1287.witWc1287))
    (hflush3 : m3.wc.masch.mem.bytes HwMemWC1287.witWc1287 =
      natByte 42)
    (h4 : HwWcOrdSchritt1301 m3 m4
      (.clwb 0 true HwMemWC1287.witWc1287))
    (hkeep : ClwbKeepAnnahme1301 m4 HwMemWC1287.witWc1287
      (natByte 42))
    (h5 : HwWcOrdSchritt1301 m4 m5
      (.wcGepuffert 0 HwMemWC1287.witWcB1287 (natByte 43)))
    (heigen5 : HwMemWC1287.wcLesbar m5.wc 0 HwMemWC1287.witWcB1287 =
      some (natByte 43))
    (hfremd5 : HwMemWC1287.wcLesbar m5.wc 1 HwMemWC1287.witWcB1287 =
      some (natByte 0))
    (hnull5 : m5.wc.masch.mem.bytes HwMemWC1287.witWcB1287 =
      natByte 0)
    (h6 : HwWcOrdSchritt1301 m5 m6
      (.evict 0 HwMemWC1287.witWcB1287 (natByte 43)))
    (hspuel6 : m6.wc.masch.mem.bytes HwMemWC1287.witWcB1287 =
      natByte 43)
    (htypWt : HwMemWC1287.speicherTyp m0.wc.profil
      HwMemWC1287.witWt1287 1 = HwMemWC1287.SpeicherTypWC.wt)
    (hempty : m0.wc.wc 0 = [])
    (hnoRd : m0.wc.masch.mem.lesbar HwMemWC1287.witNo1287 = false)
    (hnoEx : m0.wc.masch.mem.ausfuehrbar HwMemWC1287.witNo1287 =
      false) :
    (m1.wc.masch = m0.wc.masch ∧
      m1.wc.wc 0 = m0.wc.wc 0 ++
        [⟨HwMemWC1287.witWc1287, natByte 42⟩]) ∧
    (HwMemWC1287.wcLesbar m1.wc 0 HwMemWC1287.witWc1287 ≠
      HwMemWC1287.wcLesbar m1.wc 1 HwMemWC1287.witWc1287) ∧
    (m2.wc.masch.puffer 0 = [] ∧ m2.wc.wc 0 = [] ∧
      zaunBereit ⟨m2.wc.masch.mem, m2.wc.masch.puffer⟩ 0 = true ∧
      m2.ordLog = m1.ordLog ++ [.zaun 0]) ∧
    (m2.wc.masch.mem.bytes HwMemWC1287.witWc1287 ≠
      m1.wc.masch.mem.bytes HwMemWC1287.witWc1287) ∧
    (m3.ordLog = (m1.ordLog ++ [.zaun 0]) ++
      [.clflushopt 0 true HwMemWC1287.witWc1287]) ∧
    (m3.wc.wc 0 = (m2.wc.wc 0).filter (fun e =>
      !(HwMemWC1287.inLinie HwMemWC1287.witWc1287 e.addr))) ∧
    (wcStoreZugriff1301 m0 0 HwMemWC1287.witWt1287 (natByte 9) =
      none) ∧
    (m4.ordLog = m3.ordLog ++
      [.clwb 0 true HwMemWC1287.witWc1287] ∧
      m4.wc.wc 0 = (m3.wc.wc 0).filter (fun e =>
        !(HwMemWC1287.inLinie HwMemWC1287.witWc1287 e.addr)) ∧
      m4.wc.masch.mem.bytes HwMemWC1287.witWc1287 =
        m3.wc.masch.mem.bytes HwMemWC1287.witWc1287) ∧
    (m5.wc.masch = m4.wc.masch ∧
      m5.wc.wc 0 = m4.wc.wc 0 ++
        [⟨HwMemWC1287.witWcB1287, natByte 43⟩]) ∧
    (HwMemWC1287.wcLesbar m5.wc 0 HwMemWC1287.witWcB1287 ≠
      HwMemWC1287.wcLesbar m5.wc 1 HwMemWC1287.witWcB1287) ∧
    (m6.wc.masch.mem.bytes HwMemWC1287.witWcB1287 ≠
      m5.wc.masch.mem.bytes HwMemWC1287.witWcB1287) ∧
    (m6.wc.wc 0 = (m5.wc.wc 0).drop 1 ∧
      ∀ d : Nat, d ≠ 0 → m6.wc.wc d = m5.wc.wc d) ∧
    (wcEvictZugriff1301 m0 0 = none) ∧
    (clflushoptZugriff1301 m0 0 false HwMemWC1287.witWc1287 = none ∧
      clwbZugriff1301 m0 0 false HwMemWC1287.witWc1287 = none) ∧
    (clflushoptZugriff1301 m0 0 true HwMemWC1287.witNo1287 = none ∧
      clwbZugriff1301 m0 0 true HwMemWC1287.witNo1287 = none) ∧
    (pins.length = m6.ordLog.length) ∧
    (pins2.length = m4.ordLog.length) ∧
    (HwWcOrdWf1301 m6) := by
  have hbypass1 := hwWcOrdStore_bypass1301 m0 m1 0
    HwMemWC1287.witWc1287 (natByte 42) h1
  have hzaunF := hwWcOrdZaun_leer1301 m1 m2 0 h2
  have hrahmen3 := hwWcOrdFlushopt_rahmen1301 m2 m3 0 true
    HwMemWC1287.witWc1287 h3
  have hrahmen4 := hwWcOrdClwb_rahmen1301 m3 m4 0 true
    HwMemWC1287.witWc1287 h4
  have hbypass5 := hwWcOrdStore_bypass1301 m4 m5 0
    HwMemWC1287.witWcB1287 (natByte 43) h5
  have hevict6 := hwWcOrdEvict_rahmen1301 m5 m6 0
    HwMemWC1287.witWcB1287 (natByte 43) h6
  have hgift1 : wcStoreZugriff1301 m0 0 HwMemWC1287.witWt1287
      (natByte 9) = none :=
    hwWcOrdStore_falscherTyp1301 m0 0 HwMemWC1287.witWt1287
      (natByte 9) htypWt
  have hgift2 : wcEvictZugriff1301 m0 0 = none :=
    hwWcOrdEvict_leer_verweigert1301 m0 0 hempty
  have hgift3 := hwWcOrdFlush_ohneBit1301 m0 0
    HwMemWC1287.witWc1287
  have hgift4 := hwWcOrdFlush_ohneRecht1301 m0 0 true
    HwMemWC1287.witNo1287 hnoRd hnoEx
  have k4 : m4.wc.masch.mem.bytes HwMemWC1287.witWc1287 =
      natByte 42 :=
    clwbKeep_liest1301 m4 HwMemWC1287.witWc1287 (natByte 42) hkeep
  have hord : m3.ordLog = (m1.ordLog ++ [.zaun 0]) ++
      [.clflushopt 0 true HwMemWC1287.witWc1287] := by
    rw [hrahmen3.2, hzaunF.2.2.2.1]
  have hbytes : m4.wc.masch.mem.bytes HwMemWC1287.witWc1287 =
      m3.wc.masch.mem.bytes HwMemWC1287.witWc1287 := by
    rw [k4, hflush3]
  have hwf1 := hwWcOrdSchritt_wf1301 m0 m1 _ h1 hwf
  have hwf2 := hwWcOrdSchritt_wf1301 m1 m2 _ h2 hwf1
  have hwf3 := hwWcOrdSchritt_wf1301 m2 m3 _ h3 hwf2
  have hwf4 := hwWcOrdSchritt_wf1301 m3 m4 _ h4 hwf3
  have hwf5 := hwWcOrdSchritt_wf1301 m4 m5 _ h5 hwf4
  have hwf6 := hwWcOrdSchritt_wf1301 m5 m6 _ h6 hwf5
  refine ⟨⟨hbypass1.1, hbypass1.2.1⟩, ?_,
    ⟨hzaunF.1, hzaunF.2.1, hzaunF.2.2.1, hzaunF.2.2.2.1⟩, ?_,
    hord, hrahmen3.1, hgift1, ⟨hrahmen4.2, hrahmen4.1, hbytes⟩,
    ⟨hbypass5.1, hbypass5.2.1⟩, ?_, ?_,
    ⟨hevict6.2.1, hevict6.2.2.2⟩, hgift2, hgift3, hgift4,
    wcEvictPinsLaenge1301 m6.ordLog pins hbus,
    clflushoptZaunPinsLaenge1301 m4.ordLog pins2 hzaunA, hwf6⟩
  · rw [heigen1, hfremd1]
    decide
  · rw [hzaun, hstill1]
    decide
  · rw [heigen5, hfremd5]
    decide
  · rw [hspuel6, hnull5]
    decide

/-- Joint witness for `hwWcOrd_verbindung1301`: all twenty-three
    premises together on the reached non-degenerate two-core run -- a
    WC store with owner-only forwarding, an SFENCE/MFENCE drain
    installing the byte, a CLFLUSHOPT ordered after the fence, a CLWB
    keeping the byte, a second WC store with owner-only forwarding and
    a memory-changing spontaneous eviction, beside the kind and
    permission refusals, with all three named assumptions discharged.
    Non-degenerate: canonical memory changes twice, on two cores. -/
theorem hwWcOrd_verbindung1301_zeuge :
    ∃ (m0 m1 m2 m3 m4 m5 m6 : HwWcOrdMaschine1301)
      (pins pins2 : List WcOrdEreignis1301),
      WcEvictOrdAnnahme1301 m6.ordLog pins ∧
      ClflushoptZaunAnnahme1301 m4.ordLog pins2 ∧
      HwWcOrdWf1301 m0 ∧
      HwWcOrdSchritt1301 m0 m1
        (.wcGepuffert 0 HwMemWC1287.witWc1287 (natByte 42)) ∧
      HwMemWC1287.wcLesbar m1.wc 0 HwMemWC1287.witWc1287 =
        some (natByte 42) ∧
      HwMemWC1287.wcLesbar m1.wc 1 HwMemWC1287.witWc1287 =
        some (natByte 0) ∧
      m1.wc.masch.mem.bytes HwMemWC1287.witWc1287 = natByte 0 ∧
      HwWcOrdSchritt1301 m1 m2 (.zaun 0) ∧
      m2.wc.masch.mem.bytes HwMemWC1287.witWc1287 = natByte 42 ∧
      HwWcOrdSchritt1301 m2 m3
        (.clflushopt 0 true HwMemWC1287.witWc1287) ∧
      m3.wc.masch.mem.bytes HwMemWC1287.witWc1287 = natByte 42 ∧
      HwWcOrdSchritt1301 m3 m4
        (.clwb 0 true HwMemWC1287.witWc1287) ∧
      ClwbKeepAnnahme1301 m4 HwMemWC1287.witWc1287 (natByte 42) ∧
      HwWcOrdSchritt1301 m4 m5
        (.wcGepuffert 0 HwMemWC1287.witWcB1287 (natByte 43)) ∧
      HwMemWC1287.wcLesbar m5.wc 0 HwMemWC1287.witWcB1287 =
        some (natByte 43) ∧
      HwMemWC1287.wcLesbar m5.wc 1 HwMemWC1287.witWcB1287 =
        some (natByte 0) ∧
      m5.wc.masch.mem.bytes HwMemWC1287.witWcB1287 = natByte 0 ∧
      HwWcOrdSchritt1301 m5 m6
        (.evict 0 HwMemWC1287.witWcB1287 (natByte 43)) ∧
      m6.wc.masch.mem.bytes HwMemWC1287.witWcB1287 = natByte 43 ∧
      HwMemWC1287.speicherTyp m0.wc.profil HwMemWC1287.witWt1287 1 =
        HwMemWC1287.SpeicherTypWC.wt ∧
      m0.wc.wc 0 = [] ∧
      m0.wc.masch.mem.lesbar HwMemWC1287.witNo1287 = false ∧
      m0.wc.masch.mem.ausfuehrbar HwMemWC1287.witNo1287 = false := by
  refine ⟨witM0_1301, witM1_1301, witM2_1301, witM3_1301, witM4_1301,
    witM5_1301, witM6_1301, witM6_1301.ordLog, witM4_1301.ordLog,
    rfl, rfl, witM0_wf1301, wit_schritt1_1301, wit_eigen1_1301,
    wit_fremd1_1301, wit_still1_1301, wit_schritt2_1301,
    wit_zaun2_1301, wit_schritt3_1301, wit_flush3_1301,
    wit_schritt4_1301, wit_keep4_1301, wit_schritt5_1301,
    wit_eigen5_1301, wit_fremd5_1301, wit_null5_1301,
    wit_schritt6_1301, wit_spuel6_1301, HwMemWC1287.witTyp_wt1287,
    wit_leer0_1301, wit_nord0_1301, wit_noex0_1301⟩

/- CUTS:
   Proved here, over the REUSED accepted vocabulary
   (`HardwareExecution`: `HwMaschine/HwWf/HwAdapter/pufferSetze`,
   `hwWitStart`; `TSO`: `TSOEintrag/neuestens_angehaengt`;
   `FenceDrain`: `drainVoll/zaunBereit`; lane 1287 `HwMemTypesWC`:
   `HwWcMaschine1287/HwWcWf/HwWcSchritt`, `wcStoreZugriff`,
   `wcZaunZustand`, `wcLinieSpuele`, `wcLesbar`,
   `wcSpeicherSchreibe`, `inLinie`, the store/fence preservation and
   frame lemmas, the witness image/profile/addresses and their
   type/permission facts -- no copied model, no redefined evaluator):
   - the lifted ordering machine (accepted 1287 machine plus the
     ordering-side program-order log) with six step functions and the
     `HwWcOrdSchritt1301` relation, `HwWf` preservation, and
     bypass/read/eviction/fence/line-frame agreement;
   - WC buffer eviction as a nondeterministic oldest-first drain step
     (empty buffer refuses; foreign buffers untouched);
   - WC read ordering for the same core (a retired WC store reads
     back through the accepted forwarding; foreign cores never
     forward);
   - CLFLUSHOPT (`66 0F AE /7` memory form) and CLWB (`66 0F AE /6`
     memory form) byte decoders with pins (canonical bytes decode;
     register row, plain-CLFLUSH bytes and LOCK refuse; the forms
     never shadow each other);
   - the three NAMED ordering assumptions (`WcEvictOrdAnnahme1301`:
     every retired drain appears on the pins, order NOT claimed per
     the SDM's buffer-reordering statement; `ClflushoptZaunAnnahme1301`:
     the pins honor the fence-separated log order;
     `ClwbKeepAnnahme1301`: the retired CLWB byte reads back) with
     their length/readback consequences and the proved program-order
     fact (CLFLUSHOPT before its fence in the log);
   - the family plug as an `HwAdapter` (eviction drain, WC read NOP)
     with wf preservation, planted refusals (wrong type, missing
     permission, missing silicon bit) and exact plug agreement on a
     singleton WC buffer (CLFLUSHOPT/CLWB have no bare-machine plug:
     their effects need buffer state);
   - a reached joint witness (WC store with owner-only forwarding,
     SFENCE/MFENCE drain installing the byte, CLFLUSHOPT ordered
     after the fence, CLWB keeping the byte, second WC store with
     owner-only forwarding, memory-changing spontaneous eviction)
     with all three named assumptions discharged and canonical memory
     changed twice on two cores.
   NOT proved here, and not claimed:
   - No hardware correspondence beyond the cited Intel SDM entries
     (provenance in the file header, not proofs); the stated line
     size (64, reused) and the CLFLUSHOPT/CLWB CPUID bits are named,
     never probed; profile population (MTRR/PAT/page tables) is
     software user logic.
   - No cross-core WC same-line eviction ORDER beyond the named
     count assumption (the SDM states buffers may appear out of
     order on the bus); no WC read ordering beyond same-core
     forwarding (no cross-type ordering, no streaming-load
     reordering); no non-temporal store forms, no PREFETCHW,
     no CLDEMOTE.
   - No per-access target-to-W/GX simulation, no
     source/checker/Spec/goal/emitter correspondence, no
     syscall/interrupt scope, no timing/fairness/progress claim.
-/

#print axioms hwWcOrdSchritt_wf1301
#print axioms hwWcOrdStore_bypass1301
#print axioms hwWcOrdLesen_nach_speichern1301
#print axioms hwWcOrdLesen_rahmen1301
#print axioms hwWcOrdEvict_rahmen1301
#print axioms hwWcOrdZaun_leer1301
#print axioms hwWcOrdFlushopt_rahmen1301
#print axioms hwWcOrdClwb_rahmen1301
#print axioms hwWcOrdEvict_leer_verweigert1301
#print axioms hwWcOrdFlush_ohneBit1301
#print axioms hwWcOrdFlush_ohneRecht1301
#print axioms hwWcOrdStore_falscherTyp1301
#print axioms pin_clflushopt1301
#print axioms pin_clwb1301
#print axioms pin_opt_nicht_wb1301
#print axioms pin_flush_register_verweigert1301
#print axioms pin_clflush_kein_opt_wb1301
#print axioms pin_flush_lock_verweigert1301
#print axioms wcEvictPinsLaenge1301
#print axioms clflushoptZaunPinsLaenge1301
#print axioms clflushoptVorZaun1301
#print axioms clwbKeep_liest1301
#print axioms wcOrdAdapter_evict_mem1301
#print axioms wcOrdAdapter_liest_ok1301
#print axioms wcOrdAdapter_evict_falscherTyp1301
#print axioms wcOrdAdapter_ohneRecht1301
#print axioms adapterWcOrd1301_wf
#print axioms adapterEvict_stimmt_ueberein1301
#print axioms witM0_wf1301
#print axioms wit_schritt1_1301
#print axioms wit_eigen1_1301
#print axioms wit_fremd1_1301
#print axioms wit_still1_1301
#print axioms wit_schritt2_1301
#print axioms wit_zaun2_1301
#print axioms wit_schritt3_1301
#print axioms wit_flush3_1301
#print axioms wit_schritt4_1301
#print axioms wit_keep4_1301
#print axioms wit_schritt5_1301
#print axioms wit_eigen5_1301
#print axioms wit_fremd5_1301
#print axioms wit_null5_1301
#print axioms wit_schritt6_1301
#print axioms wit_spuel6_1301
#print axioms wit_leer0_1301
#print axioms wit_nord0_1301
#print axioms wit_noex0_1301
#print axioms hwWcOrd_verbindung1301
#print axioms hwWcOrd_verbindung1301_zeuge

end HwWcOrd1301

end Gabbro.Grammatik.X86
