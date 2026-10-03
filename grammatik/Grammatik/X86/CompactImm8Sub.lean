/-
  File:      Grammatik/X86/CompactImm8Sub.lean
  Subject:   Connection for the REX.W 83/5 imm8 row (SUB r/m64, imm8).

  Lane 749: exactly one row -- REX.W + 83 /5 ib, SUB r/m64, imm8,
  register-direct (mod=3) -- with borrow/flag identity, pinned bytes
  and refusal outside the signed byte. Reuses the accepted producers
  (`IntegerHardwareForms`: encode/decode/step/fetch; `Wort.sub64`;
  canonical `Zustand`/`Speicher`; pilot `schritt` for the witness
  store). No new syntax, decoder, evaluator or state type.

  Manual: Intel SDM 325462-093US (Sep 2026), Vol. 2B 4-685/4-686,
  heading SUB-Subtract: row "REX.W + 83 /5 ib  SUB r/m64, imm8  MI
  Valid N.E. Subtract sign-extended imm8 from r/m64"; Operation
  DEST := (DEST - SRC); immediates sign-extended to the destination
  width; flags OF SF ZF AF PF CF set according to the result.
  Bundle: .tmp/HARDWARE-REFERENCES (REFERENCES.json + intel txt).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.NarrowOps
import Grammatik.X86.RelocatedExecution
import Grammatik.X86.IntegerHardwareForms

namespace Gabbro.Grammatik.X86

/-- Pinned compact bytes: `sub rax, 1` is REX.W, 83, E8, 01. -/
theorem pin_sub_kompakt :
    encodeIntHwImm (.subI .rax 1) =
      [natByte 72, natByte 131, natByte 232, natByte 1] := by
  decide

/-! ## 1. Compact choice and imm8 fit: the row refuses outside i8.

    The encoder emits the 4-byte compact form (REX.W, 83, /5, ib)
    exactly for immediates fitting the signed byte; anything else
    takes the 7-byte wide form (REX.W, 81, /5, id). Dually, every
    byte the compact decoder reads sign-extends into the signed
    byte, so a compact decode can never smuggle a wide value. -/

/-- The compact SUB choice fires exactly on fitting values. -/
theorem kompakt_sub_feuert (dst : Register) (imm : BitVec 32) :
    (encodeIntHwImm (.subI dst imm)).length = 4 ↔ immPasst8 imm = true := by
  unfold encodeIntHwImm
  by_cases h : immPasst8 imm = true
  · simp [h]
  · have hf : immPasst8 imm = false := by
      cases he : immPasst8 imm with
      | true => simp [he] at h
      | false => rfl
    simp [hf, length_leBytes32]

/-- Every byte sign-extends into the signed byte: compact decodes fit.
    Case split at 128 with the reused truncation bridge
    (`narrowTruncMod`) and the bit-31 boundary (`bit31_equiv`). -/
theorem imm8Erweitern_passt (n : Nat) (h : n < 256) :
    immPasst8 (imm8Erweitern n) = true := by
  unfold immPasst8 imm8Erweitern
  by_cases hg : n ≥ 128
  · rw [if_pos hg]
    have hbound : 0xFFFFFF00 + n < 2 ^ 32 := by omega
    have hto : (BitVec.ofNat 32 (0xFFFFFF00 + n)).toNat =
        0xFFFFFF00 + n := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hbound
    have hto64 : (BitVec.ofNat 64
        (BitVec.ofNat 32 (0xFFFFFF00 + n)).toNat).toNat =
        0xFFFFFF00 + n := by
      rw [hto, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have htr : (trunc .b32 (BitVec.ofNat 64
        (BitVec.ofNat 32 (0xFFFFFF00 + n)).toNat)).toNat =
        0xFFFFFF00 + n := by
      rw [narrowTruncMod, hto64]
      exact Nat.mod_eq_of_lt hbound
    have hneg : negB .b32 (BitVec.ofNat 64
        (BitVec.ofNat 32 (0xFFFFFF00 + n)).toNat) = true := by
      unfold negB
      rw [htr, show signBit .b32 = 31 from rfl,
        bit31_equiv _ (by omega)]
      exact decide_eq_true (by omega)
    have hbits : Breite.bits .b32 = 32 := rfl
    have hval : sVal .b32 (BitVec.ofNat 64
        (BitVec.ofNat 32 (0xFFFFFF00 + n)).toNat) =
        (((0xFFFFFF00 + n : Nat)) : Int) - (((2 ^ 32 : Nat)) : Int) := by
      have e0 : sVal .b32 (BitVec.ofNat 64
          (BitVec.ofNat 32 (0xFFFFFF00 + n)).toNat) =
          if negB .b32 (BitVec.ofNat 64
            (BitVec.ofNat 32 (0xFFFFFF00 + n)).toNat)
          then ((trunc .b32 (BitVec.ofNat 64
            (BitVec.ofNat 32 (0xFFFFFF00 + n)).toNat)).toNat : Int) -
            (((2 ^ Breite.bits .b32 : Nat)) : Int)
          else ((trunc .b32 (BitVec.ofNat 64
            (BitVec.ofNat 32 (0xFFFFFF00 + n)).toNat)).toNat : Int) := rfl
      simp only [e0, htr, hneg, hbits, if_true]
    rw [hval]
    exact decide_eq_true (by omega)
  · have hg' : ¬ n ≥ 128 := hg
    rw [if_neg hg']
    have hto : (BitVec.ofNat 32 n).toNat = n := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have hto64 : (BitVec.ofNat 64 (BitVec.ofNat 32 n).toNat).toNat =
        n := by
      rw [hto, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have htr : (trunc .b32
        (BitVec.ofNat 64 (BitVec.ofNat 32 n).toNat)).toNat = n := by
      have hbits : Breite.bits .b32 = 32 := rfl
      rw [narrowTruncMod, hto64, hbits]
      exact Nat.mod_eq_of_lt (by omega)
    have hneg : negB .b32
        (BitVec.ofNat 64 (BitVec.ofNat 32 n).toNat) = false := by
      unfold negB
      rw [htr, show signBit .b32 = 31 from rfl,
        bit31_equiv _ (by omega)]
      exact decide_eq_false (by omega)
    have hval : sVal .b32
        (BitVec.ofNat 64 (BitVec.ofNat 32 n).toNat) = ((n : Nat) : Int) := by
      have e0 : sVal .b32 (BitVec.ofNat 64 (BitVec.ofNat 32 n).toNat) =
          if negB .b32 (BitVec.ofNat 64 (BitVec.ofNat 32 n).toNat)
          then ((trunc .b32 (BitVec.ofNat 64
            (BitVec.ofNat 32 n).toNat)).toNat : Int) -
            (((2 ^ Breite.bits .b32 : Nat)) : Int)
          else ((trunc .b32 (BitVec.ofNat 64
            (BitVec.ofNat 32 n).toNat)).toNat : Int) := rfl
      simp only [e0, htr, hneg, Bool.false_eq_true, if_false]
    rw [hval]
    exact decide_eq_true (by omega)

/-- Pinned compact bytes: `sub rax, -1` signs through one byte. -/
theorem pin_sub_neg1 :
    encodeIntHwImm (.subI .rax 0xFFFFFFFF) =
      [natByte 72, natByte 131, natByte 232, natByte 255] := by
  decide

/-- Pinned compact bytes over an extended register: `sub r9, 1`. -/
theorem pin_sub_r9 :
    encodeIntHwImm (.subI .r9 1) =
      [natByte 73, natByte 131, natByte 233, natByte 1] := by
  decide

/-- Pinned wide bytes: `sub rax, 256` needs the imm32 form. -/
theorem pin_sub_weit :
    encodeIntHwImm (.subI .rax 256) =
      [natByte 72, natByte 129, natByte 232,
       natByte 0, natByte 1, natByte 0, natByte 0] := by
  decide

/-- Pinned decode: compact `sub rax, 1` (4 bytes). -/
theorem pin_sub_kompakt_dekode :
    decodeIntHwImm [natByte 72, natByte 131, natByte 232, natByte 1] =
      some ((⟨.subI .rax 1, 4⟩ : IntHwImmDec), []) := by
  decide

/-- Pinned decode: compact `sub rax, -1` (sign extension at decode). -/
theorem pin_sub_neg1_dekode :
    decodeIntHwImm
      [natByte 72, natByte 131, natByte 232, natByte 255] =
      some ((⟨.subI .rax 0xFFFFFFFF, 4⟩ : IntHwImmDec), []) := by
  decide

/-! ## 2. Per-width gates and planted neighbour refusals.

    The SUB-imm row executes at b64 only (the manual's REX.W row;
    no narrow arithmetic flag snapshot exists). The decoder admits
    no 32-bit SUB-imm at any digit-5 arm; SBB/ADC digits, missing
    or R-extended REX prefixes and truncated tails refuse loudly. -/

/-- The width gate admits SUB-imm exactly at b64. -/
theorem subImm_breite_nur_b64 (b : Breite) (dst : Register)
    (imm : BitVec 32) :
    immBreiteOk (.subI dst imm) b = (b == .b64) := by
  cases b <;> rfl

/-- Digit 5 at b32 refuses in every ModRM arm (wide and compact). -/
theorem subkompakt_32_verweigert (bBit : Nat) (m : Byte) (t : List Byte)
    (wide : Bool) (hmod : byteNat m / 64 == 3)
    (hdig : byteNat m / 8 % 8 = 5) :
    decodeIntHwImmModrm .b32 wide bBit (m :: t) = none := by
  simp only [decodeIntHwImmModrm]
  rw [if_pos hmod]
  cases hc : codeReg (bBit * 8 + byteNat m % 8) with
  | none => rfl
  | some rd =>
    rw [hdig]
    cases wide <;> rfl

/-- SBB digit /3 refuses on the compact opcode. -/
theorem subkompakt_sbb_verweigert :
    decodeIntHwImm
      [natByte 72, natByte 131, natByte 216, natByte 1] = none := by
  decide

/-- ADC digit /2 refuses on the compact opcode. -/
theorem subkompakt_adc_verweigert :
    decodeIntHwImm
      [natByte 72, natByte 131, natByte 208, natByte 1] = none := by
  decide

/-- No REX prefix, no row: a bare 83 /5 is refused. -/
theorem subkompakt_ohne_rex_verweigert :
    decodeIntHwImm [natByte 131, natByte 232, natByte 1] = none := by
  decide

/-- REX.R is not a canonical prefix of this row. -/
theorem subkompakt_rex_r_verweigert :
    decodeIntHwImm
      [natByte 76, natByte 131, natByte 232, natByte 1] = none := by
  decide

/-- W=0 compact bytes refuse: no 32-bit SUB-imm exists. -/
theorem subkompakt_w0_kompakt_verweigert :
    decodeIntHwImm
      [natByte 64, natByte 131, natByte 232, natByte 1] = none := by
  decide

/-- W=0 wide bytes refuse: no 32-bit SUB-imm exists. -/
theorem subkompakt_w0_weit_verweigert :
    decodeIntHwImm [natByte 64, natByte 129, natByte 232,
      natByte 1, natByte 0, natByte 0, natByte 0] = none := by
  decide

/-- A compact SUB without its immediate byte is truncated. -/
theorem subkompakt_kurz_verweigert :
    decodeIntHwImm [natByte 72, natByte 131, natByte 232] = none := by
  decide

/-! ## 3. Borrow/flag identity of the compact SUB step.

    A compact SUB-imm step IS the canonical `sub64` borrow: the
    destination takes the modular difference, CF is the borrow
    (`cfSub`), AF the nibble borrow (`afSub`, DEFINED like the
    manual's flag row), and RIP advances past the 4 compact bytes.
    Memory is untouched, so this row consults no data permission
    and raises no data fault. -/

/-- Borrow probe: `0 - 1` borrows, `5 - 1` does not. -/
theorem probe_sub_borgt :
    (sub64 0 1).1 = 0xFFFFFFFFFFFFFFFF ∧ (sub64 0 1).2.cf = true ∧
    (sub64 5 1).1 = 4 ∧ (sub64 5 1).2.cf = false ∧
    (sub64 5 1).2.af = some false := by
  decide

/-- The compact SUB step is the canonical borrow: value, full flag
    snapshot, borrow bit, defined nibble borrow and RIP advance. -/
theorem subkompakt_schritt (d : IntHwImmDec) (s s' : Zustand)
    (dst : Register) (imm : BitVec 32)
    (hok : laengeOk d.laenge = true)
    (hlen : d.laenge = immDecLaenge d.op)
    (hb : immDecBreiteOk d.op = true)
    (h : d.op = .subI dst imm)
    (hstep : stepIntHwImm d s = some s') :
    s'.register dst = s.register dst - immWort imm ∧
    s'.flags = (sub64 (s.register dst) (immWort imm)).2 ∧
    s'.flags.cf = cfSub (s.register dst) (immWort imm) ∧
    s'.flags.af = some (afSub (s.register dst) (immWort imm)) ∧
    s'.rip = ripNach s.rip d.laenge := by
  have e : stepIntHwImm d s =
      some (schrittRegister s (ripNach s.rip d.laenge)
        (sub64 (s.register dst) (immWort imm)).2 dst
        (sub64 (s.register dst) (immWort imm)).1) := by
    unfold stepIntHwImm
    rw [h] at hlen hb
    rw [hok, h, hlen, hb]
    simp
  rw [e] at hstep
  cases hstep
  refine ⟨by simp only [schrittRegister, regSet_gleich, sub64],
    schrittRegister_flags _ _ _ _ _,
    by simp only [schrittRegister_flags, sub64],
    by simp only [schrittRegister_flags, sub64],
    schrittRegister_rip _ _ _ _ _⟩

/-! ## 4. Fetched-byte connection: the admitted compact SUB row.

    From actual executable memory, the accepted immediate fetch
    (`fetchIntHwImm`) admits the compact SUB row and the accepted
    byte step (`intHwImmByteschritt`) executes it with the borrow
    identity above. No new dispatcher is invented. -/

/-- TARGET: a fetched compact SUB executes with borrow identity,
    advances past its 4 bytes and leaves memory untouched. -/
theorem CompactImm8Sub_verbindung (s s' : Zustand) (dst : Register)
    (imm : BitVec 32) (rest : List Byte)
    (hfetch : fetchIntHwImm s = some (⟨.subI dst imm, 4⟩, rest))
    (hfit : immPasst8 imm = true)
    (hstep : intHwImmByteschritt s = .weiter s') :
    s'.register dst = s.register dst - immWort imm ∧
    s'.flags.cf = cfSub (s.register dst) (immWort imm) ∧
    s'.flags.af = some (afSub (s.register dst) (immWort imm)) ∧
    s'.rip = ripNach s.rip 4 ∧
    s'.speicher = s.speicher := by
  have hlen4 : immDecLaenge (.subI dst imm) = 4 := by
    simp [immDecLaenge, hfit]
  cases hst : stepIntHwImm ⟨.subI dst imm, 4⟩ s with
  | none =>
    have hnone : intHwImmByteschritt s = .verweigert := by
      simp only [intHwImmByteschritt, hfetch, hst]
    rw [hnone] at hstep
    cases hstep
  | some t =>
    have hwt : intHwImmByteschritt s = .weiter t := by
      simp only [intHwImmByteschritt, hfetch, hst]
    rw [hwt] at hstep
    cases hstep
    have hsub := subkompakt_schritt _ s s' dst imm rfl hlen4.symm
      rfl rfl hst
    obtain ⟨hreg, _, hcf, haf, hrip⟩ := hsub
    refine ⟨hreg, hcf, haf, ?_, stepImm_speicher _ s s' hst⟩
    simpa using hrip

/-! ## 5. Joint witness: fetched compact SUB feeding a memory store.

    The image holds `sub rax, 1` (4 compact bytes) followed by the
    pilot `store [rbx], rax` (7 bytes) in actual code memory: the
    compact row steps `rax` from 5 to 4 with no borrow, and the
    fetched store writes the value into the data cell, observably
    changing its byte from zero to 4. -/

/-- Witness program: compact SUB bytes then the pilot store bytes. -/
def subkompaktProg : List Byte :=
  [natByte 72, natByte 131, natByte 232, natByte 1,
   natByte 72, natByte 137, natByte 131,
   natByte 0, natByte 0, natByte 0, natByte 0]

/-- Program bytes over addresses from 4096; zero elsewhere. -/
def subkompaktBytes (a : Adresse) : Byte :=
  if a.toNat < 4096 then BitVec.ofNat 8 0
  else subkompaktProg.getD (a.toNat - 4096) (BitVec.ofNat 8 0)

/-- Code window executable: the 11 image bytes at 4096. -/
def subkompaktExec (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4107)

/-- Data cell readable and writable: 8192..8200. -/
def subkompaktDaten (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8200)

/-- Witness registers: 5 in rax, the data cell in rbx. -/
def subkompaktReg : Register → Wort := fun q =>
  if q = Register.rax then 5
  else if q = Register.rbx then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness start state: compact SUB at 4096, data cell at 8192. -/
def subkompaktStart : Zustand :=
  { register := subkompaktReg, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096,
    speicher :=
      { bytes := subkompaktBytes, lesbar := subkompaktDaten,
        schreibbar := subkompaktDaten, ausfuehrbar := subkompaktExec } }

/-- Fetched suffix after the 4 SUB bytes: the 7 store bytes. -/
def subkompaktRest : List Byte :=
  [natByte 72, natByte 137, natByte 131,
   natByte 0, natByte 0, natByte 0, natByte 0]

/-- The program bytes are the canonical compact SUB plus the pilot
    store: the row's encoding composes with the common pilot. -/
theorem pin_subkette_bytes :
    subkompaktProg = encodeIntHwImm (.subI .rax 1) ++
      encode (.store64 .rbx .rax (BitVec.ofNat 32 0)) := by
  decide

/-- The executed bytes fetch to the compact SUB row with the store
    tail as the remaining suffix. -/
theorem subkompakt_holt :
    fetchIntHwImm subkompaktStart =
      some (⟨.subI .rax 1, 4⟩, subkompaktRest) := by
  decide

/-- Witness middle state: the SUB successor (rax holds 4, RIP past
    the 4 SUB bytes, borrow-free flags, memory untouched). -/
def subkompaktMitte : Zustand :=
  schrittRegister subkompaktStart
    (ripNach subkompaktStart.rip 4)
    (sub64 (subkompaktStart.register .rax) (immWort 1)).2 .rax
    (sub64 (subkompaktStart.register .rax) (immWort 1)).1

/-- The fetched SUB byte-step reaches the middle state. -/
theorem subkompakt_weiter :
    intHwImmByteschritt subkompaktStart = .weiter subkompaktMitte := by
  rfl

/-- The SUB step moves 5 to 4 without borrowing. -/
theorem subkompakt_mitte_wert :
    subkompaktMitte.register .rax = 4 ∧
    subkompaktMitte.flags.cf = false ∧
    subkompaktMitte.rip = BitVec.ofNat 64 4100 := by
  decide

/-- Two-step end: the SUB successor, then the pilot store of `rax`. -/
def subkompaktKette : Option Zustand :=
  schritt ⟨.store64 .rbx .rax (BitVec.ofNat 32 0), 7⟩ subkompaktMitte

/-- The value reaches memory: the data cell reads 4 and its byte
    observably changed from zero. -/
theorem subkompakt_kette_speicher :
    subkompaktKette.map (fun s =>
        s.speicher.bytes (BitVec.ofNat 64 8192)) =
        some (natByte 4) ∧
      subkompaktStart.speicher.bytes (BitVec.ofNat 64 8192) =
        BitVec.ofNat 8 0 := by
  decide

/-- The chain advances RIP past both instructions: 4096 + 4 + 7. -/
theorem subkompakt_kette_rip :
    subkompaktKette.map (fun s => s.rip) =
      some (BitVec.ofNat 64 4107) := by
  decide

/-- JOINT WITNESS: the fetched compact SUB executes with borrow
    identity (register 5 to 4, no borrow, defined nibble borrow,
    RIP past 4 bytes, memory untouched), the reached store step
    observably changes the data cell from zero to 4, and the SBB
    digit and the prefix-less neighbour refuse. Non-degenerate: a
    register-changing reached execution plus a store-changing
    reached run, jointly instantiated. -/
theorem CompactImm8Sub_verbindung_zeuge :
    ∃ (s s' : Zustand) (dst : Register) (imm : BitVec 32)
      (rest : List Byte),
      fetchIntHwImm s = some (⟨.subI dst imm, 4⟩, rest) ∧
      immPasst8 imm = true ∧
      intHwImmByteschritt s = .weiter s' ∧
      s'.register dst = s.register dst - immWort imm ∧
      s'.flags.cf = cfSub (s.register dst) (immWort imm) ∧
      s'.flags.af = some (afSub (s.register dst) (immWort imm)) ∧
      s'.rip = ripNach s.rip 4 ∧
      s'.speicher = s.speicher ∧
      s.register dst ≠ s'.register dst ∧
      (∃ s'' : Zustand,
        schritt ⟨.store64 .rbx .rax (BitVec.ofNat 32 0), 7⟩ s' =
          some s'' ∧
        s''.speicher.bytes (BitVec.ofNat 64 8192) ≠
          s'.speicher.bytes (BitVec.ofNat 64 8192)) ∧
      decodeIntHwImm
        [natByte 72, natByte 131, natByte 216, natByte 1] = none ∧
      decodeIntHwImm [natByte 131, natByte 232, natByte 1] =
        none := by
  refine ⟨subkompaktStart, subkompaktMitte, .rax, 1, subkompaktRest,
    subkompakt_holt, by decide, subkompakt_weiter, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, subkompakt_sbb_verweigert,
    subkompakt_ohne_rex_verweigert⟩
  · exact (CompactImm8Sub_verbindung subkompaktStart subkompaktMitte
      .rax 1 subkompaktRest subkompakt_holt (by decide)
      subkompakt_weiter).1
  · exact (CompactImm8Sub_verbindung subkompaktStart subkompaktMitte
      .rax 1 subkompaktRest subkompakt_holt (by decide)
      subkompakt_weiter).2.1
  · exact (CompactImm8Sub_verbindung subkompaktStart subkompaktMitte
      .rax 1 subkompaktRest subkompakt_holt (by decide)
      subkompakt_weiter).2.2.1
  · exact (CompactImm8Sub_verbindung subkompaktStart subkompaktMitte
      .rax 1 subkompaktRest subkompakt_holt (by decide)
      subkompakt_weiter).2.2.2.1
  · exact (CompactImm8Sub_verbindung subkompaktStart subkompaktMitte
      .rax 1 subkompaktRest subkompakt_holt (by decide)
      subkompakt_weiter).2.2.2.2
  · decide
  · cases hK : subkompaktKette with
    | none =>
      have hN := subkompakt_kette_speicher.1
      rw [hK] at hN
      cases hN
    | some s'' =>
      refine ⟨s'', ?_, ?_⟩
      · exact hK
      · have hmap := subkompakt_kette_speicher.1
        rw [hK] at hmap
        have hb4 : s''.speicher.bytes (BitVec.ofNat 64 8192) =
            natByte 4 := by
          simpa using hmap
        have hb0 : subkompaktMitte.speicher.bytes
            (BitVec.ofNat 64 8192) = BitVec.ofNat 8 0 :=
          subkompakt_kette_speicher.2
        rw [hb4, hb0]
        decide

/- CUTS:
    Proved here, reusing the ACCEPTED producers (`Typen`,
    `Wort.sub64`/`cfSub`/`afSub`, `Speicher` bytes, `Ausfuehrung`
    `laengeOk`/`ripNach`/`regSet`/`schrittRegister`/`schritt`,
    `Codec` bytes/helpers, `Byteschritt.geholt`/`ausfuehrbarN`/
    `ByteAusgang`, `NarrowOps.narrowTruncMod`,
    `RelocatedExecution.bit31_equiv` and the UNCHANGED
    `IntegerHardwareForms` immediate row (`encodeIntHwImm`,
    `decodeIntHwImm`, `stepIntHwImm`, `fetchIntHwImm`,
    `intHwImmByteschritt`, `immWort`, `immPasst8`,
    `imm8Erweitern`, `immDecLaenge`, `immDecBreiteOk`,
    `immBreiteOk`, `stepImm_speicher`):
    exactly one row -- REX.W + 83 /5 ib, SUB r/m64, imm8,
    register-direct (mod=3). Compact choice fires exactly on
    fitting values (`kompakt_sub_feuert`); every decoded imm8 byte
    sign-extends into the signed byte (`imm8Erweitern_passt`, so a
    compact decode never smuggles a wide value); pinned compact
    bytes for `sub rax, 1`, `sub rax, -1` and `sub r9, 1`, the
    wide `sub rax, 256` bytes, and both compact decodes; the
    b64-only width gate with a generic digit-5-at-b32 decoder
    refusal; planted refusals for the SBB/ADC digits, missing
    REX, REX.R, W=0 compact/wide and truncated tails; the
    borrow/flag identity step equation (value, full `sub64`
    snapshot, CF borrow, DEFINED AF nibble borrow, RIP advance);
    the fetched-byte connection through the accepted fetch and
    byte step with memory provably untouched; and the joint
    witness (fetched SUB 5 to 4, reached pilot store changing
    the data cell from zero to 4, neighbour refusals).
    Manual ground: Intel SDM 325462-093US (Sep 2026), Vol. 2B
    4-685/4-686, heading SUB-Subtract: row "REX.W + 83 /5 ib
    SUB r/m64, imm8 MI Valid N.E. Subtract sign-extended imm8
    from r/m64"; Operation DEST := (DEST - SRC); immediates
    sign-extended to the destination width; flags OF SF ZF AF
    PF CF set according to the result. Bundle:
    .tmp/HARDWARE-REFERENCES (REFERENCES.json + intel txt).
    NOT proved here, and not claimed:
    - No hardware correspondence: opcode, digit, REX discipline,
      borrow/flag rules and sign-extension semantics are STATED
      canonical subset choices with self-consistency only, not
      verified against silicon.
    - No memory-operand form: only mod=3 register-direct is
      covered; `SUB [mem], imm8` (addressing, permissions,
      faults, atomicity) stays OPEN.
    - No 16/32-bit 83 rows, no 81/80 rows, no LOCK prefix; the
      `ExtendedExecution` dispatcher does not cover this family,
      so dispatcher composition stays with its owner.
    - No TSO/GX bridge: every fact is sequential over one
      `Speicher`; the row emits no memory access (proved), hence
      no TSO event, but per-access granularity and the GX
      refinement stay with the TSO bridge (OPEN).
    - No source correspondence, no ABI/image/entry/relocation,
      no cost or time transfer, no new hardware or software
      assumptions and no checker rule: no diagnostic,
      poison-probe, example or CLI numbers are taken.
-/

#print axioms pin_sub_kompakt
#print axioms kompakt_sub_feuert
#print axioms imm8Erweitern_passt
#print axioms pin_sub_neg1
#print axioms pin_sub_r9
#print axioms pin_sub_weit
#print axioms pin_sub_kompakt_dekode
#print axioms pin_sub_neg1_dekode
#print axioms subImm_breite_nur_b64
#print axioms subkompakt_32_verweigert
#print axioms subkompakt_sbb_verweigert
#print axioms subkompakt_adc_verweigert
#print axioms subkompakt_ohne_rex_verweigert
#print axioms subkompakt_rex_r_verweigert
#print axioms subkompakt_w0_kompakt_verweigert
#print axioms subkompakt_w0_weit_verweigert
#print axioms subkompakt_kurz_verweigert
#print axioms probe_sub_borgt
#print axioms subkompakt_schritt
#print axioms CompactImm8Sub_verbindung
#print axioms pin_subkette_bytes
#print axioms subkompakt_holt
#print axioms subkompakt_weiter
#print axioms subkompakt_mitte_wert
#print axioms subkompakt_kette_speicher
#print axioms subkompakt_kette_rip
#print axioms CompactImm8Sub_verbindung_zeuge

end Gabbro.Grammatik.X86
