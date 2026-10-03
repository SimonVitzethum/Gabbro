/-
  File:      Grammatik/X86/LfenceLoadNarrow.lean
  Subject:   LFENCE load-only ordering, narrower than MFENCE, over the
             canonical byte TSO model with byte-facing fetch discipline.

  Lane 782 (hardware completion): LFENCE orders loads only and never
  drains the own store buffer, unlike MFENCE (`LockedOps.lockSchritt`
  `.mfence`, admitted only on an empty own buffer). The TSO step below
  is total (always admitted); narrowness is the proved refusal gap:
  a nonempty own buffer refuses MFENCE and admits LFENCE.

  Manual provenance (local snapshot `.tmp/HARDWARE-REFERENCES/`):
  - Intel SDM combined volumes 1-4, edition 325462-093US, September 2026
    (`REFERENCES.json`: official index intel.com, content delivery URL,
    sha256-verified 2026-10-02; AMD retrieval failed, no AMD claim).
  - Vol. 2 instruction reference entries LFENCE (opcode 0F AE /5, form
    0F AE E8) and MFENCE (opcode 0F AE /6, form 0F AE F0).
  - LFENCE orders load-from-memory operations only; it does not order
    stores (no store-buffer drain). MFENCE orders both loads and stores.
  Silicon correspondence stays OPEN (see CUTS); proved here are the
  stated canonical bytes, their disjointness, and the TSO-level
  load-ordering distinction.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Codec
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Byteschritt
import Grammatik.X86.TSO
import Grammatik.X86.LockedOps
import Grammatik.X86.LockedInstructionExecution
import Grammatik.X86.FenceDrain

namespace Gabbro.Grammatik.X86

/-- LFENCE event: fence-only, load-ordering shape. `istMfence` is false
    by construction: this event never claims the full barrier. -/
structure LfenceEreignis where
  kern : Nat
  istZaun : Bool
  istMfence : Bool
  deriving DecidableEq, Repr

/-- LFENCE TSO step: total and state-preserving. Loads are ordered but
    no store is drained and no buffer changes: the successor state is
    the input state, with the narrow fence event. -/
def lfenceSchritt (s : TSOZustand) (c : Nat) : TSOZustand × LfenceEreignis :=
  (s, ⟨c, true, false⟩)

/-! ## 1. TSO-level load ordering: buffers and memory unchanged. -/

/-- LFENCE leaves every core buffer unchanged. -/
theorem lfence_erhaelt_puffer (s : TSOZustand) (c : Nat) :
    (lfenceSchritt s c).1.puffer = s.puffer := rfl

/-- LFENCE leaves every canonical byte unchanged. -/
theorem lfence_erhaelt_speicher (s : TSOZustand) (c : Nat) :
    (lfenceSchritt s c).1.mem.bytes = s.mem.bytes := rfl

/-- Load-load ordering, observed: every load on the acting core reads
    the same value before and after LFENCE. Uses the state identity. -/
theorem lfence_lasten_bleiben (s : TSOZustand) (c : Nat) (a : Adresse) :
    loadByte (lfenceSchritt s c).1 c a = loadByte s c a := rfl

/-- The LFENCE event is fence-only and never a full barrier. -/
theorem lfence_ereignis_schmal (s : TSOZustand) (c : Nat) :
    (lfenceSchritt s c).2.istZaun = true ∧
      (lfenceSchritt s c).2.istMfence = false ∧
      (lfenceSchritt s c).2.kern = c := by
  refine ⟨rfl, rfl, rfl⟩

/-- MFENCE refuses a nonempty own buffer: the exact admitted
    elimination gap. LFENCE (total above) admits the same state. -/
theorem mfence_verweigert_bei_vollem_puffer (s : TSOZustand) (c : Nat)
    (hne : s.puffer c ≠ []) :
    lockSchritt .mfence c s = none := by
  cases hbuf : s.puffer c with
  | nil => exact absurd hbuf hne
  | cons e rest => simp [lockSchritt, hbuf]

/-! ## 2. Canonical bytes: LFENCE is `0F AE E8`, length 3. -/

/-- Canonical LFENCE bytes: `0F AE E8` (ModRM `/5`, register-direct). -/
def lfenceBytes : List Byte := [natByte 15, natByte 174, natByte 232]

/-- LFENCE decoder: only `0F AE E8` is accepted; SFENCE (`F8`),
    MFENCE (`F0`), CLFLUSH rows and truncations refuse with `none`. -/
def decodeLfence : List Byte → Option (Unit × List Byte)
  | b0 :: b1 :: m :: rest =>
    if byteNat b0 == 15 && byteNat b1 == 174 && byteNat m == 232 then
      some ((), rest)
    else none
  | _ => none

/-- Round trip: the canonical bytes decode over any suffix. -/
theorem roundtrip_lfence (suffix : List Byte) :
    decodeLfence (lfenceBytes ++ suffix) = some ((), suffix) := by
  have h15 : byteNat (natByte 15) = 15 :=
    byteNat_natByte_of_lt 15 (by decide)
  have h174 : byteNat (natByte 174) = 174 :=
    byteNat_natByte_of_lt 174 (by decide)
  have h232 : byteNat (natByte 232) = 232 :=
    byteNat_natByte_of_lt 232 (by decide)
  simp [decodeLfence, lfenceBytes, h15, h174, h232]

/-- Canonical LFENCE bytes are 3 long. -/
theorem lfenceBytes_len : lfenceBytes.length = 3 := rfl

/-- The LFENCE length passes the decode-length guard. -/
theorem lfenceLaenge_ok : laengeOk lfenceBytes.length = true := by
  rw [lfenceBytes_len]
  decide

/-- The pilot decoder refuses the LFENCE row: no pilot form is
    shadowed by the new fence bytes. -/
theorem pilot_weist_lfence_zurueck : decode lfenceBytes = none := by
  decide

/-- The locked decoder refuses the LFENCE row without a LOCK prefix:
    ModRM reg field 5 is not the MFENCE row (reg field 6). -/
theorem lock_weist_lfence_zurueck : decodeLock lfenceBytes = none := by
  decide

/-! ## 3. Byte-facing fetch and step from actual executable memory.

  The fetched window is the state's ACTUAL bytes at `rip`
  (`Byteschritt.geholt`: executable prefix only, capped at 15).
  Admission checks the consumed length against the fetched window, the
  decode-length guard, and execute permission of the consumed prefix --
  exactly the `fetchDekodiert` discipline. No caller-supplied value
  ever becomes a trusted fetch. -/

/-- LFENCE byte outcome: success carries the successor, refusal is
    explicit. No halt and no fault constructor: LFENCE itself raises
    no fault at this layer (see CUTS). -/
inductive LfenceByteAusgang where
  | weiter : Zustand → LfenceByteAusgang
  | verweigert : LfenceByteAusgang

/-- Unified admission: consumed length plus remaining suffix is the
    fetched window, the length passes the guard, and the consumed
    prefix is executable. -/
def lfenceZugelassen (s : Zustand) (fenster rest : List Byte) : Bool :=
  decide (lfenceBytes.length + rest.length = fenster.length) &&
    laengeOk lfenceBytes.length &&
    ausfuehrbarN s.speicher s.rip lfenceBytes.length

/-- Fetch and decode LFENCE from the given window, gated by admission. -/
def fetchLfence (s : Zustand) : Option (Unit × List Byte) :=
  match decodeLfence (geholt s) with
  | none => none
  | some (u, rest) =>
    if lfenceZugelassen s (geholt s) rest then some (u, rest) else none

/-- One LFENCE byte step from actual memory: fetch, then advance RIP
    by 3 with registers, flags and memory unchanged. No data memory is
    read or written; no flag is defined or cleared; no store is
    drained. -/
def lfenceByteschritt (s : Zustand) : LfenceByteAusgang :=
  match fetchLfence s with
  | none => .verweigert
  | some _ => .weiter { s with rip := s.rip + BitVec.ofNat 64 3 }

/-- A successful fetch decodes the canonical bytes with full admission:
    length equation, length guard and execute permission all hold. -/
theorem fetchLfence_erfolg (s : Zustand) (rest : List Byte)
    (h : fetchLfence s = some ((), rest)) :
    decodeLfence (geholt s) = some ((), rest) ∧
      lfenceBytes.length + rest.length = (geholt s).length ∧
      laengeOk lfenceBytes.length = true ∧
      ausfuehrbarN s.speicher s.rip lfenceBytes.length = true := by
  unfold fetchLfence at h
  cases hdec : decodeLfence (geholt s) with
  | none =>
    rw [hdec] at h
    cases h
  | some p =>
    obtain ⟨u, rest'⟩ := p
    simp only [hdec] at h
    by_cases hz : lfenceZugelassen s (geholt s) rest' = true
    · rw [if_pos hz] at h
      have hpair : (u, rest') = ((), rest) := by cases h; rfl
      have hrr : rest' = rest := congrArg Prod.snd hpair
      have huu : u = () := congrArg Prod.fst hpair
      rw [huu] at hdec ⊢
      rw [hrr] at hdec hz ⊢
      unfold lfenceZugelassen at hz
      simp only [Bool.and_eq_true] at hz
      obtain ⟨⟨hsum, hlen⟩, hexe⟩ := hz
      exact ⟨rfl, of_decide_eq_true hsum, hlen, hexe⟩
    · rw [if_neg hz] at h
      cases h

/-- Selection: a fetched LFENCE advances RIP by 3, preserving
    registers, flags and every memory byte. -/
theorem lfenceByteschritt_weiter (s : Zustand) (rest : List Byte)
    (hf : fetchLfence s = some ((), rest)) :
    ∃ s' : Zustand,
      lfenceByteschritt s = .weiter s' ∧
        s'.rip = s.rip + BitVec.ofNat 64 3 ∧
        s'.register = s.register ∧ s'.flags = s.flags ∧
        s'.speicher.bytes = s.speicher.bytes := by
  refine ⟨{ s with rip := s.rip + BitVec.ofNat 64 3 }, ?_, rfl, rfl, rfl, rfl⟩
  unfold lfenceByteschritt
  rw [hf]

/-- Selection: fetch refusal is byte-step refusal. -/
theorem lfenceByteschritt_verweigert (s : Zustand)
    (hf : fetchLfence s = none) :
    lfenceByteschritt s = .verweigert := by
  unfold lfenceByteschritt
  rw [hf]

/-- Neighbour refusal: the SFENCE row (`F8`) is not LFENCE. -/
theorem lfence_nachbar_sfence :
    decodeLfence [natByte 15, natByte 174, natByte 248] = none := by
  decide

/-- Neighbour refusal: the MFENCE row (`F0`) is not LFENCE. -/
theorem lfence_nachbar_mfence :
    decodeLfence [natByte 15, natByte 174, natByte 240] = none := by
  decide

/-- Truncation refusal: two bytes are not an LFENCE. -/
theorem lfence_abgeschnitten :
    decodeLfence [natByte 15, natByte 174] = none := by
  decide

/-- Empty input is refused. -/
theorem lfence_leer : decodeLfence [] = none := by
  decide

/-! ## 4. Reached witnesses: fetched LFENCE plus a memory-changing run. -/

/-- Witness code bytes: the canonical LFENCE triple at 4096. -/
def lfWitBytes (a : Adresse) : Byte :=
  if a.toNat = 4096 then natByte 15
  else if a.toNat = 4097 then natByte 174
  else if a.toNat = 4098 then natByte 232
  else BitVec.ofNat 8 0

/-- Witness execute permission: exactly the three fence bytes. -/
def lfWitExec (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4099)

/-- Witness memory: fence bytes executable, data fully permitted. -/
def lfWitSpeicher : Speicher :=
  { bytes := lfWitBytes, lesbar := fun _ => true,
    schreibbar := fun _ => true, ausfuehrbar := lfWitExec }

/-- Witness state: fence at RIP 4096. -/
def lfWitZustand : Zustand :=
  { register := zeugeReg, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := lfWitSpeicher }

/-- The witness fetch succeeds with no remaining suffix. -/
theorem lf_fetch : fetchLfence lfWitZustand = some ((), []) := by
  decide

/-- Past the fence bytes there is nothing executable: fetch refuses. -/
theorem lf_fetch_nachBild :
    fetchLfence
      { lfWitZustand with rip := BitVec.ofNat 64 4099 } = none := by
  decide

/-- Past the fence bytes the step refuses. -/
theorem lf_nachBild_verweigert :
    lfenceByteschritt
      { lfWitZustand with rip := BitVec.ofNat 64 4099 } =
      .verweigert :=
  lfenceByteschritt_verweigert _ lf_fetch_nachBild

/-- After core 0 flushes its single pending byte. -/
def lfGespült : TSOZustand :=
  ⟨{ zeugenSpeicher with
      bytes := fun x =>
        if x = sbX then sbEins else zeugenSpeicher.bytes x },
    pufferSetze sbNach1.puffer 0 []⟩

/-- The flush step computes as claimed. -/
theorem lf_flush : flushKern sbNach1 0 = some lfGespült := by
  rfl

/-- The flush observably changes the canonical byte at `sbX`. -/
theorem lf_speicher_aendert :
    sbNach1.mem.bytes sbX ≠ lfGespült.mem.bytes sbX := by
  decide

/-- Core 0 holds a pending store: MFENCE would refuse here. -/
theorem lf_puffer_voll : sbNach1.puffer 0 ≠ [] := by
  decide

/-- MFENCE refuses the witness state; LFENCE admits it. -/
theorem lf_mfence_verweigert :
    lockSchritt .mfence 0 sbNach1 = none :=
  mfence_verweigert_bei_vollem_puffer _ _ lf_puffer_voll

/-- The witness state is reached by a real issue step. -/
theorem lf_erreichbar : TSOErreichbar sbStart sbNach1 :=
  .schritt .start (.issue _ _ _ _ _ sb_schritt1)

/-! ## 5. The narrow connection: LFENCE admits what MFENCE refuses. -/

/-- **LFENCE load narrowness.** On a state whose own buffer is
    nonempty, LFENCE preserves every buffer and every canonical byte
    (hence every load on the acting core), carries the narrow
    fence-only event -- and MFENCE refuses the very same state. Every
    premise is used: `s`, `c`, `a` in the preservation conjuncts,
    `hne` for the MFENCE refusal. -/
theorem LfenceLoadNarrow_verbindung (s : TSOZustand) (c : Nat)
    (a : Adresse) (hne : s.puffer c ≠ []) :
    (lfenceSchritt s c).1.puffer = s.puffer ∧
    (lfenceSchritt s c).1.mem.bytes = s.mem.bytes ∧
    loadByte (lfenceSchritt s c).1 c a = loadByte s c a ∧
    (lfenceSchritt s c).2.istZaun = true ∧
    (lfenceSchritt s c).2.istMfence = false ∧
    lockSchritt .mfence c s = none := by
  refine ⟨rfl, rfl, rfl, rfl, rfl,
    mfence_verweigert_bei_vollem_puffer s c hne⟩

/-- **Joint witness.** All premises of `LfenceLoadNarrow_verbindung`
    hold together on `sbNach1` (reached by a real issue, flushed to a
    memory change), while the canonical bytes fetch and step from
    actual executable memory past RIP 4096 to 4099 with memory
    unchanged. Non-degenerate: a buffered store, a memory-changing
    flush, and a real fetched step. -/
theorem LfenceLoadNarrow_verbindung_zeuge :
    ∃ (s : TSOZustand) (c : Nat) (a : Adresse),
      s.puffer c ≠ [] ∧
      (lfenceSchritt s c).1.puffer = s.puffer ∧
      (lfenceSchritt s c).1.mem.bytes = s.mem.bytes ∧
      loadByte (lfenceSchritt s c).1 c a = loadByte s c a ∧
      (lfenceSchritt s c).2.istZaun = true ∧
      (lfenceSchritt s c).2.istMfence = false ∧
      lockSchritt .mfence c s = none ∧
      TSOErreichbar sbStart s ∧
      (∃ s3 : TSOZustand, flushKern s c = some s3 ∧
        s.mem.bytes sbX ≠ s3.mem.bytes sbX) ∧
      fetchLfence lfWitZustand = some ((), []) ∧
      (∃ z' : Zustand,
        lfenceByteschritt lfWitZustand = .weiter z' ∧
        z'.rip = BitVec.ofNat 64 4099 ∧
        z'.speicher.bytes = lfWitZustand.speicher.bytes) := by
  refine ⟨sbNach1, 0, sbX, lf_puffer_voll, rfl, rfl, rfl, rfl, rfl,
    lf_mfence_verweigert, lf_erreichbar,
    ⟨lfGespült, lf_flush, lf_speicher_aendert⟩, lf_fetch, ?_⟩
  obtain ⟨z', hz', hrip, _, _, hmem⟩ :=
    lfenceByteschritt_weiter lfWitZustand [] lf_fetch
  have hziel : z'.rip = BitVec.ofNat 64 4099 := by
    rw [hrip]
    decide
  exact ⟨z', hz', hziel, hmem⟩

/- CUTS:
    - Proved here: LFENCE as load-only ordering over the ONE canonical
      `TSOZustand` (total `lfenceSchritt`: buffers and canonical bytes
      unchanged, every acting-core load preserved), its narrowness gap
      against MFENCE (`mfence_verweigert_bei_vollem_puffer`,
      `LfenceLoadNarrow_verbindung`: MFENCE refuses exactly where
      LFENCE admits), canonical bytes `0F AE E8` with round trip,
      length guard, pilot/locked-codec disjointness, neighbour and
      truncation refusals, and byte-facing fetch/step from actual
      executable memory under the `fetchDekodiert` admission
      discipline with a reached memory-changing joint witness.
    - No silicon correspondence: the `0F AE E8` form and the load-only
      ordering are stated from the Intel SDM entries LFENCE/MFENCE
      (edition 325462-093US); no claim that silicon implements them.
    - No store ordering and no drain: LFENCE never flushes any buffer
      (`lfence_erhaelt_puffer`); a program needing publication still
      needs a flush or MFENCE. Store→load forwarding (`loadByte`)
      passes through LFENCE unchanged by construction.
    - No dispatch-serializing variant: the MSR-controlled
      dispatch-serializing LFENCE behaviour and any CPUID feature gate
      are OPEN; this layer admits unconditionally and raises no fault.
    - No fault claim: LFENCE raises no #UD/#GP/#PF at this layer;
      fault delivery, canonical-address checks and descriptor gates
      stay with their owners.
    - No TSO/W/GX bridge: no per-access linearisation, no run
      induction into W runs; `TSOErreichbar` is target-only.
    - No timing, fairness or progress claim: drain liveness, load
      latency and any `FortschrittG`/`ZeitAbX` transfer are OPEN.
    - No interrupt, device, MMIO or DMA model; no source, checker,
      contract, budget or goal change.
-/

#print axioms lfence_erhaelt_puffer
#print axioms lfence_erhaelt_speicher
#print axioms lfence_lasten_bleiben
#print axioms lfence_ereignis_schmal
#print axioms mfence_verweigert_bei_vollem_puffer
#print axioms roundtrip_lfence
#print axioms lfenceBytes_len
#print axioms lfenceLaenge_ok
#print axioms pilot_weist_lfence_zurueck
#print axioms lock_weist_lfence_zurueck
#print axioms fetchLfence_erfolg
#print axioms lfenceByteschritt_weiter
#print axioms lfenceByteschritt_verweigert
#print axioms lfence_nachbar_sfence
#print axioms lfence_nachbar_mfence
#print axioms lfence_abgeschnitten
#print axioms lfence_leer
#print axioms lf_fetch
#print axioms lf_fetch_nachBild
#print axioms lf_nachBild_verweigert
#print axioms lf_flush
#print axioms lf_speicher_aendert
#print axioms lf_puffer_voll
#print axioms lf_mfence_verweigert
#print axioms lf_erreichbar
#print axioms LfenceLoadNarrow_verbindung
#print axioms LfenceLoadNarrow_verbindung_zeuge

end Gabbro.Grammatik.X86
