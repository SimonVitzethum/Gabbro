/-
  File:      Grammatik/X86/IntSignXchg.lean
  Subject:   Sign-extend-accumulator ops (CBW/CWDE/CDQE, CWD/CDQ/CQO),
             register XCHG and register MOVSXD, connected to the
             coherent machine and the unified byte dispatcher.

  Lane 1281: the 32/64-bit accumulator preparations reuse the
  accepted `vor98Schritt`/`vor99Schritt` (`MulDivWidthHardwareForms`)
  unchanged (lifted, never redefined); only the 16-bit CBW/CWD
  forms, the register XCHG forms and the register MOVSXD form are
  defined here, over the canonical `sext`/`trunc`/`mergeRegNarrow`.
  XCHG with a memory operand is implicitly LOCKed and stays with
  the locked families (refused here with a named reason). No flags
  change for any of these. No hardware correspondence beyond
  self-consistency is claimed (see CUTS).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.TSO
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.NarrowOps
import Grammatik.X86.MulDiv
import Grammatik.X86.MulDivWidthHardwareForms
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.FeatureProfile
import Grammatik.X86.Gleitprofil
import Grammatik.X86.ScalarFloat
import Grammatik.X86.HardwareExecution

namespace Gabbro.Grammatik.X86

/-- Admitted event forms. `cbw`/`cwd` are the 16-bit preparations
    (opcodes `66 98`/`66 99`); `cwde`/`cdqe`/`cdq`/`cqo` lift the
    accepted width preparations; `nop` is bare `90` (exactly the
    architectural NOP, never a zero-extending self-exchange);
    `xchgReg`/`xchgRax16`/`xchgRax32`/`xchgRax64` are the register
    exchanges at an explicit width (`90+r` has no 8-bit form, so the
    RAX-exchange comes in 16/32/64-bit variants);
    `movsxd` is the REX.W register move with doubleword
    sign-extension. -/
inductive SxBefehl where
  | cbw | cwde | cdqe | cwd | cdq | cqo | nop
  | xchgReg (b : Breite) (a c : Register)
  | xchgRax16 (r : Register)
  | xchgRax32 (r : Register)
  | xchgRax64 (r : Register)
  | movsxd (dst src : Register)
  deriving DecidableEq, Repr

/-- Decoded sign/xchg instruction: operation plus checked length. -/
structure SxDecodiert where
  befehl : SxBefehl
  laenge : Nat
  deriving DecidableEq, Repr

/-! ## 1. Value dispatch: fresh 16-bit preparations, exchanges and
    MOVSXD; the 32/64-bit preparations ARE the accepted ones.

    `cbwSchritt` sign-extends AL into AX and merges it (upper RAX
    bits kept, per the 16-bit write discipline of `mergeRegNarrow`).
    `cwdSchritt` broadcasts the sign of AX into DX the same way the
    accepted `vor99Schritt` broadcasts at 32/64 bits. `xchgSeite`
    states one side of an exchange at an explicit width (8/16-bit
    merge, 32-bit zero-extends, 64-bit whole); both sides read the
    OLD values, so a same-register 87-form exchange keeps the
    32-bit zero-extension while bare `90` stays `nop` (§3). -/

/-- CBW value: AX takes the sign-extension of AL, RAX upper kept. -/
def cbwWert (s : Zustand) : Wort :=
  mergeRegNarrow .b16 (s.register Register.rax)
    (sext .b8 (s.register Register.rax))

/-- CBW shape: only RAX moves (RIP advances at the caller). -/
def cbwSchritt (s : Zustand) : Zustand :=
  { s with register := regSet s.register Register.rax (cbwWert s) }

/-- CWD value: DX takes the broadcast sign of AX, RDX upper kept. -/
def cwdWert (s : Zustand) : Wort :=
  let v := if negB .b16 (s.register Register.rax) then
    BitVec.ofNat 64 65535 else BitVec.ofNat 64 0
  mergeRegNarrow .b16 (s.register Register.rdx) v

/-- CWD shape: only RDX moves (RIP advances at the caller). -/
def cwdSchritt (s : Zustand) : Zustand :=
  { s with register := regSet s.register Register.rdx (cwdWert s) }

/-- One side of a width exchange: what a register holding `old`
    shows after exchanging with `other` at width `b`. -/
def xchgSeite (b : Breite) (old other : Wort) : Wort :=
  match b with
  | .b8 => mergeRegNarrow .b8 old other
  | .b16 => mergeRegNarrow .b16 old other
  | .b32 => trunc .b32 other
  | .b64 => other

/-- Exchange shape: both sides read the OLD values, then RIP
    advances at the caller. -/
def xchgSchritt (b : Breite) (a c : Register) (s : Zustand) : Zustand :=
  let va := s.register a
  let vc := s.register c
  let r1 := regSet s.register a (xchgSeite b va vc)
  let r2 := regSet r1 c (xchgSeite b vc va)
  { s with register := r2 }

/-- MOVSXD shape: the destination takes the full sign-extension of
    the source low doubleword (a whole 64-bit write, no merge). -/
def movsxdSchritt (dst src : Register) (s : Zustand) : Zustand :=
  let v := sext .b32 (s.register src)
  { s with register := regSet s.register dst v }

/-- One family step over `MulDivErgebnis`: the fresh arms above,
    the 32/64-bit preparations ARE the accepted `wdSchritt` arms on
    the same length (lifted, never redefined). -/
def sxSchritt (d : SxDecodiert) (s : Zustand) : MulDivErgebnis :=
  match laengeOk d.laenge with
  | false => .misslungen
  | true =>
    let nach := ripNach s.rip d.laenge
    match d.befehl with
    | .cbw => .ok { (cbwSchritt s) with rip := nach }
    | .cwde => wdSchritt ⟨.vor98 .w32, d.laenge⟩ s
    | .cdqe => wdSchritt ⟨.vor98 .w64, d.laenge⟩ s
    | .cwd => .ok { (cwdSchritt s) with rip := nach }
    | .cdq => wdSchritt ⟨.vor99 .w32, d.laenge⟩ s
    | .cqo => wdSchritt ⟨.vor99 .w64, d.laenge⟩ s
    | .nop => .ok { s with rip := nach }
    | .xchgReg b a c => .ok { (xchgSchritt b a c s) with rip := nach }
    | .xchgRax16 r => .ok { (xchgSchritt .b16 Register.rax r s) with rip := nach }
    | .xchgRax32 r => .ok { (xchgSchritt .b32 Register.rax r s) with rip := nach }
    | .xchgRax64 r => .ok { (xchgSchritt .b64 Register.rax r s) with rip := nach }
    | .movsxd dst src => .ok { (movsxdSchritt dst src s) with rip := nach }

/-! ## 2. The old evaluator is lifted, never redefined.

    At 32/64 bits the family step IS the accepted width step on
    the same length. No competing preparation is defined here. -/

/-- CWDE is the accepted 32-bit `vor98` step. -/
theorem sx_cwde_ist_vor98 (l : Nat) (s : Zustand) :
    sxSchritt ⟨.cwde, l⟩ s = wdSchritt ⟨.vor98 .w32, l⟩ s := by
  cases h : laengeOk l <;> simp [sxSchritt, wdSchritt, h]

/-- CDQE is the accepted 64-bit `vor98` step. -/
theorem sx_cdqe_ist_vor98 (l : Nat) (s : Zustand) :
    sxSchritt ⟨.cdqe, l⟩ s = wdSchritt ⟨.vor98 .w64, l⟩ s := by
  cases h : laengeOk l <;> simp [sxSchritt, wdSchritt, h]

/-- CDQ is the accepted 32-bit `vor99` step. -/
theorem sx_cdq_ist_vor99 (l : Nat) (s : Zustand) :
    sxSchritt ⟨.cdq, l⟩ s = wdSchritt ⟨.vor99 .w32, l⟩ s := by
  cases h : laengeOk l <;> simp [sxSchritt, wdSchritt, h]

/-- CQO is the accepted 64-bit `vor99` step. -/
theorem sx_cqo_ist_vor99 (l : Nat) (s : Zustand) :
    sxSchritt ⟨.cqo, l⟩ s = wdSchritt ⟨.vor99 .w64, l⟩ s := by
  cases h : laengeOk l <;> simp [sxSchritt, wdSchritt, h]

/-! ## 3. Read-back, flag silence and memory silence of the fresh arms.

    No fresh arm changes flags (the manual rows for CBW/CWDE/CDQE,
    CWD/CDQ/CQO, XCHG and MOVSXD all read "Flags Affected: None")
    and no fresh arm touches memory. -/

/-- The exchange shape as nested register updates (old values). -/
theorem xchgSchritt_eq (b : Breite) (a c : Register) (s : Zustand) :
    (xchgSchritt b a c s).register =
      regSet (regSet s.register a (xchgSeite b (s.register a) (s.register c))) c
        (xchgSeite b (s.register c) (s.register a)) := by
  rfl

/-- Read-back at the first side (distinct registers). -/
theorem xchgSchritt_bei_a_neq (b : Breite) (a c : Register) (s : Zustand)
    (hne : a ≠ c) :
    (xchgSchritt b a c s).register a =
      xchgSeite b (s.register a) (s.register c) := by
  rw [xchgSchritt_eq]
  rw [regSet_fremd _ c a _ hne]
  exact regSet_gleich _ _ _

/-- Read-back at the second side (no side condition). -/
theorem xchgSchritt_bei_c (b : Breite) (a c : Register) (s : Zustand) :
    (xchgSchritt b a c s).register c =
      xchgSeite b (s.register c) (s.register a) := by
  rw [xchgSchritt_eq]
  exact regSet_gleich _ _ _

/-- CBW keeps the flags. -/
theorem cbwSchritt_flags (s : Zustand) : (cbwSchritt s).flags = s.flags := rfl

/-- CBW keeps the memory. -/
theorem cbwSchritt_memory (s : Zustand) : (cbwSchritt s).speicher = s.speicher := rfl

/-- CWD keeps the flags. -/
theorem cwdSchritt_flags (s : Zustand) : (cwdSchritt s).flags = s.flags := rfl

/-- CWD keeps the memory. -/
theorem cwdSchritt_memory (s : Zustand) : (cwdSchritt s).speicher = s.speicher := rfl

/-- Exchanges keep the flags. -/
theorem xchgSchritt_flags (b : Breite) (a c : Register) (s : Zustand) :
    (xchgSchritt b a c s).flags = s.flags := rfl

/-- Exchanges keep the memory. -/
theorem xchgSchritt_memory (b : Breite) (a c : Register) (s : Zustand) :
    (xchgSchritt b a c s).speicher = s.speicher := rfl

/-- MOVSXD keeps the flags. -/
theorem movsxdSchritt_flags (dst src : Register) (s : Zustand) :
    (movsxdSchritt dst src s).flags = s.flags := rfl

/-- MOVSXD keeps the memory. -/
theorem movsxdSchritt_memory (dst src : Register) (s : Zustand) :
    (movsxdSchritt dst src s).speicher = s.speicher := rfl

/-- Pinned CBW: `AL = 0xFF` (-1) extends to `AX = 0xFFFF`. -/
theorem probe_cbw_sext :
    mergeRegNarrow .b16 0 (sext .b8 0xFF) = 0xFFFF := by
  decide

/-- Pinned CWD merge: a broadcast `0xFFFF` lands in DX, RDX kept. -/
theorem probe_cwd_merge :
    mergeRegNarrow .b16 0xABCDEF1234560000 0xFFFF =
      0xABCDEF123456FFFF := by
  decide

/-- Pinned 32-bit exchange side: zero-extends the other word. -/
theorem probe_xchgSeite_32 :
    xchgSeite .b32 0xFFFFFFFFFFFFFFFF 0x11223344 = 0x11223344 := by
  decide

/-- Pinned 8-bit exchange side: merges the low byte, keeps upper. -/
theorem probe_xchgSeite_8 :
    xchgSeite .b8 0xABCDEF1234567890 0x11 = 0xABCDEF1234567811 := by
  decide

/-- Pinned MOVSXD: `-1` as doubleword extends to all ones. -/
theorem probe_movsxd_neg1 :
    sext .b32 0xFFFFFFFF = 0xFFFFFFFFFFFFFFFF := by
  decide

/-- Pinned MOVSXD: a positive doubleword is unchanged. -/
theorem probe_movsxd_pos :
    sext .b32 0x7FFFFFFF = 0x7FFFFFFF := by
  decide

/-! ## 4. Step-level flag and memory silence.

    Every successful family step keeps flags and memory: the fresh
    arms by their shapes (§3), the lifted arms by the accepted
    preparation shapes below. -/

/-- An accepted `vor98` success keeps the flags. -/
theorem wdVor98_flags (w : WdBreite) (l : Nat) (s s' : Zustand)
    (h : wdSchritt ⟨.vor98 w, l⟩ s = .ok s') : s'.flags = s.flags := by
  unfold wdSchritt at h
  cases hlen : laengeOk l with
  | false => simp [hlen] at h
  | true =>
    simp [hlen] at h
    cases h
    cases w <;> rfl

/-- An accepted `vor98` success keeps the memory. -/
theorem wdVor98_memory (w : WdBreite) (l : Nat) (s s' : Zustand)
    (h : wdSchritt ⟨.vor98 w, l⟩ s = .ok s') :
    s'.speicher = s.speicher := by
  unfold wdSchritt at h
  cases hlen : laengeOk l with
  | false => simp [hlen] at h
  | true =>
    simp [hlen] at h
    cases h
    cases w <;> rfl

/-- An accepted `vor99` success keeps the flags. -/
theorem wdVor99_flags (w : WdBreite) (l : Nat) (s s' : Zustand)
    (h : wdSchritt ⟨.vor99 w, l⟩ s = .ok s') : s'.flags = s.flags := by
  unfold wdSchritt at h
  cases hlen : laengeOk l with
  | false => simp [hlen] at h
  | true =>
    simp [hlen] at h
    cases h
    cases w <;> rfl

/-- An accepted `vor99` success keeps the memory. -/
theorem wdVor99_memory (w : WdBreite) (l : Nat) (s s' : Zustand)
    (h : wdSchritt ⟨.vor99 w, l⟩ s = .ok s') :
    s'.speicher = s.speicher := by
  unfold wdSchritt at h
  cases hlen : laengeOk l with
  | false => simp [hlen] at h
  | true =>
    simp [hlen] at h
    cases h
    cases w <;> rfl

/-- Every successful family step keeps the flags. -/
theorem sxSchritt_flags (d : SxDecodiert) (s s' : Zustand)
    (h : sxSchritt d s = .ok s') : s'.flags = s.flags := by
  unfold sxSchritt at h
  cases hlen : laengeOk d.laenge with
  | false =>
    simp [hlen] at h
  | true =>
    simp [hlen] at h
    cases hbef : d.befehl with
    | cbw =>
      simp [hbef] at h
      cases h
      rfl
    | cwde =>
      simp [hbef] at h
      exact wdVor98_flags _ _ _ _ h
    | cdqe =>
      simp [hbef] at h
      exact wdVor98_flags _ _ _ _ h
    | cwd =>
      simp [hbef] at h
      cases h
      rfl
    | cdq =>
      simp [hbef] at h
      exact wdVor99_flags _ _ _ _ h
    | cqo =>
      simp [hbef] at h
      exact wdVor99_flags _ _ _ _ h
    | nop =>
      simp [hbef] at h
      cases h
      rfl
    | xchgReg b a c =>
      simp [hbef] at h
      cases h
      rfl
    | xchgRax16 r =>
      simp [hbef] at h
      cases h
      rfl
    | xchgRax32 r =>
      simp [hbef] at h
      cases h
      rfl
    | xchgRax64 r =>
      simp [hbef] at h
      cases h
      rfl
    | movsxd dst src =>
      simp [hbef] at h
      cases h
      rfl

/-- Every successful family step keeps the memory. -/
theorem sxSchritt_memory (d : SxDecodiert) (s s' : Zustand)
    (h : sxSchritt d s = .ok s') : s'.speicher = s.speicher := by
  unfold sxSchritt at h
  cases hlen : laengeOk d.laenge with
  | false =>
    simp [hlen] at h
  | true =>
    simp [hlen] at h
    cases hbef : d.befehl with
    | cbw =>
      simp [hbef] at h
      cases h
      rfl
    | cwde =>
      simp [hbef] at h
      exact wdVor98_memory _ _ _ _ h
    | cdqe =>
      simp [hbef] at h
      exact wdVor98_memory _ _ _ _ h
    | cwd =>
      simp [hbef] at h
      cases h
      rfl
    | cdq =>
      simp [hbef] at h
      exact wdVor99_memory _ _ _ _ h
    | cqo =>
      simp [hbef] at h
      exact wdVor99_memory _ _ _ _ h
    | nop =>
      simp [hbef] at h
      cases h
      rfl
    | xchgReg b a c =>
      simp [hbef] at h
      cases h
      rfl
    | xchgRax16 r =>
      simp [hbef] at h
      cases h
      rfl
    | xchgRax32 r =>
      simp [hbef] at h
      cases h
      rfl
    | xchgRax64 r =>
      simp [hbef] at h
      cases h
      rfl
    | movsxd dst src =>
      simp [hbef] at h
      cases h
      rfl

/-! ## 5. No shadowing: the unified chain refuses the new rows.

    Each planned byte row is refused by the whole unified chain,
    so the family arm takes it exactly once. Checked by evaluation;
    a row accepted here would need a different encoding choice. -/

theorem ext_weist_sxcbw_zurueck :
    decodeExt [natByte 102, natByte 152] = none := by
  decide

theorem ext_weist_sxcwd_zurueck :
    decodeExt [natByte 102, natByte 153] = none := by
  decide

theorem ext_weist_sxnop_zurueck :
    decodeExt [natByte 144] = none := by
  decide

theorem ext_weist_sxxchg91_zurueck :
    decodeExt [natByte 145] = none := by
  decide

theorem ext_weist_sxxchg4890_zurueck :
    decodeExt [natByte 72, natByte 144] = none := by
  decide

theorem ext_weist_sxxchg6690_zurueck :
    decodeExt [natByte 102, natByte 144] = none := by
  decide

theorem ext_weist_sxxchg4891_zurueck :
    decodeExt [natByte 72, natByte 145] = none := by
  decide

theorem ext_weist_sxxchg86_zurueck :
    decodeExt [natByte 134, natByte 192] = none := by
  decide

theorem ext_weist_sxxchg87_zurueck :
    decodeExt [natByte 135, natByte 192] = none := by
  decide

theorem ext_weist_sxxchg6687_zurueck :
    decodeExt [natByte 102, natByte 135, natByte 192] = none := by
  decide

theorem ext_weist_sxxchg4887_zurueck :
    decodeExt [natByte 72, natByte 135, natByte 192] = none := by
  decide

theorem ext_weist_sxmovsxd_zurueck :
    decodeExt [natByte 72, natByte 99, natByte 192] = none := by
  decide

theorem ext_weist_sxmovsxdR_zurueck :
    decodeExt [natByte 76, natByte 99, natByte 193] = none := by
  decide

theorem ext_weist_sxlock90_zurueck :
    decodeExt [natByte 240, natByte 144] = none := by
  decide

theorem ext_weist_sxlock98_zurueck :
    decodeExt [natByte 240, natByte 152] = none := by
  decide

theorem ext_weist_sxxchg87mem_zurueck :
    decodeExt [natByte 135, natByte 0] = none := by
  decide

/-! ## 6. Decode: the accepted prefix parse, family opcodes after it.

    `decodeSx` reuses `nimmPraefix` (LOCK refusal, `66`/REX parse)
    and `wdBits`/`codeReg` unchanged. SIB (`xb == 1`) refuses
    everywhere (no addressed form lives here); every memory ModRM
    refuses (an XCHG memory operand is implicitly LOCKed and stays
    with the locked families; a MOVSXD memory source needs the TSO
    read path, still open). Bare `90` with no prefix at all
    (`npfx == 0`, which already forces `op16 = false`) is the
    architectural NOP, never a zero-extending self-exchange: the
    self-exchange event at 32 bits stays reachable through the
    redundant-REX encoding `[0x40, 0x90]`. -/

/-- Preparation dispatch after the prefix (`98`/`99`): 16-bit with
    `66`, 32-bit default, 64-bit with REX.W. REX.R/B name no field
    here and are ignored; `66`+REX.W refuses. -/
def decodeSx98 (op16 : Bool) (wb npfx : Nat) (is99 : Bool)
    (rest : List Byte) : Option (SxDecodiert × List Byte) :=
  if op16 && wb == 1 then none
  else if op16 then
    some (⟨if is99 then .cwd else .cbw, npfx + 1⟩, rest)
  else if wb == 1 then
    some (⟨if is99 then .cqo else .cdqe, npfx + 1⟩, rest)
  else
    some (⟨if is99 then .cdq else .cwde, npfx + 1⟩, rest)

/-- `90+r` dispatch after the prefix: bare `90` is NOP; otherwise
    the width follows the prefix (default 32, `66` 16, REX.W 64)
    and REX.B extends the opcode register. REX.R names no field
    and is ignored. -/
def decodeSx90 (op16 : Bool) (wb rb bb npfx : Nat) (op : Byte)
    (rest : List Byte) : Option (SxDecodiert × List Byte) :=
  let n := byteNat op
  if n < 144 || 151 < n then none
  else
    let lo := n - 144
    if lo == 0 && npfx == 0 then
      some (⟨.nop, 1⟩, rest)
    else if !op16 && wb == 0 then
      match codeReg (bb * 8 + lo) with
      | some r => some (⟨.xchgRax32 r, npfx + 1⟩, rest)
      | none => none
    else if op16 && wb == 0 then
      match codeReg (bb * 8 + lo) with
      | some r => some (⟨.xchgRax16 r, npfx + 1⟩, rest)
      | none => none
    else if !op16 && wb == 1 && rb == 0 then
      match codeReg (bb * 8 + lo) with
      | some r => some (⟨.xchgRax64 r, npfx + 1⟩, rest)
      | none => none
    else none

/-- `86` ModRM (`mod = 3`): the 8-bit register exchange. Operand
    size and REX.W name nothing at one byte and are ignored. -/
def decodeSx86 (rb bb npfx : Nat)
    (m : Byte) (rest : List Byte) : Option (SxDecodiert × List Byte) :=
  if byteNat m / 64 == 3 then
    match codeReg (rb * 8 + byteNat m / 8 % 8),
      codeReg (bb * 8 + byteNat m % 8) with
    | some a, some c => some (⟨.xchgReg .b8 a c, npfx + 2⟩, rest)
    | _, _ => none
  else none

/-- `87` ModRM (`mod = 3`): the 16/32/64-bit register exchange at
    the prefix width. `66`+REX.W refuses. -/
def decodeSx87 (op16 : Bool) (wb rb bb npfx : Nat)
    (m : Byte) (rest : List Byte) : Option (SxDecodiert × List Byte) :=
  if byteNat m / 64 == 3 then
    match codeReg (rb * 8 + byteNat m / 8 % 8),
      codeReg (bb * 8 + byteNat m % 8) with
    | some a, some c =>
      if !op16 && wb == 0 then
        some (⟨.xchgReg .b32 a c, npfx + 2⟩, rest)
      else if op16 && wb == 0 then
        some (⟨.xchgReg .b16 a c, npfx + 2⟩, rest)
      else if !op16 && wb == 1 then
        some (⟨.xchgReg .b64 a c, npfx + 2⟩, rest)
      else none
    | _, _ => none
  else none

/-- `63` ModRM (`mod = 3`): the REX.W register MOVSXD. Without
    REX.W, or with `66`, the form refuses. -/
def decodeSx63 (op16 : Bool) (wb rb bb npfx : Nat)
    (m : Byte) (rest : List Byte) : Option (SxDecodiert × List Byte) :=
  if op16 then none
  else if wb == 0 then none
  else if byteNat m / 64 == 3 then
    match codeReg (rb * 8 + byteNat m / 8 % 8),
      codeReg (bb * 8 + byteNat m % 8) with
    | some dst, some src =>
      some (⟨.movsxd dst src, npfx + 2⟩, rest)
    | _, _ => none
  else none

/-- Opcode dispatch after the prefix: `98`/`99`, `90+r`, `86`,
    `87`, `63`. Anything else refuses. -/
def decodeSxNachPraefix (op16 : Bool) (wb rb xb bb npfx : Nat) :
    List Byte → Option (SxDecodiert × List Byte)
  | [] => none
  | op :: rest =>
    if xb == 1 then none
    else if byteNat op == 152 then decodeSx98 op16 wb npfx false rest
    else if byteNat op == 153 then decodeSx98 op16 wb npfx true rest
    else if byteNat op == 134 then
      match rest with
      | [] => none
      | m :: rest2 => decodeSx86 rb bb npfx m rest2
    else if byteNat op == 135 then
      match rest with
      | [] => none
      | m :: rest2 => decodeSx87 op16 wb rb bb npfx m rest2
    else if byteNat op == 99 then
      match rest with
      | [] => none
      | m :: rest2 => decodeSx63 op16 wb rb bb npfx m rest2
    else if 144 ≤ byteNat op && byteNat op ≤ 151 then
      decodeSx90 op16 wb rb bb npfx op rest
    else none

/-- Full decode: the accepted prefix parse, then the family layer.
    The parser reads bytes and never compares against encoder
    output. -/
def decodeSx : List Byte → Option (SxDecodiert × List Byte)
  | [] => none
  | b :: rest =>
    match nimmPraefix (b :: rest) with
    | none => none
    | some (pfx, tail) =>
      let bits := wdBits pfx.rex
      decodeSxNachPraefix pfx.op16 bits.1 bits.2.1 bits.2.2.1
        bits.2.2.2 pfx.n tail

/-! ## 7. Encode: one canonical byte string per event.

    REX bytes reuse the accepted `wdRex` (empty exactly when no bit
    is needed). The 32-bit RAX self-exchange cannot use bare `90`
    (that IS the NOP), so its canonical encoding carries the
    redundant all-zero REX `[0x40, 0x90]`, which the decoder takes
    as the exchange arm. -/

/-- Canonical bytes of one family event. -/
def sxEncode : SxBefehl → List Byte
  | .cbw => [natByte 102, natByte 152]
  | .cwde => [natByte 152]
  | .cdqe => [natByte 72, natByte 152]
  | .cwd => [natByte 102, natByte 153]
  | .cdq => [natByte 153]
  | .cqo => [natByte 72, natByte 153]
  | .nop => [natByte 144]
  | .xchgReg .b8 a c =>
    wdRex .w32 (regHigh a) (regHigh c) ++
      [natByte 134, modrmReg (regLow a) (regLow c)]
  | .xchgReg .b16 a c =>
    [natByte 102] ++ wdRex .w32 (regHigh a) (regHigh c) ++
      [natByte 135, modrmReg (regLow a) (regLow c)]
  | .xchgReg .b32 a c =>
    wdRex .w32 (regHigh a) (regHigh c) ++
      [natByte 135, modrmReg (regLow a) (regLow c)]
  | .xchgReg .b64 a c =>
    wdRex .w64 (regHigh a) (regHigh c) ++
      [natByte 135, modrmReg (regLow a) (regLow c)]
  | .xchgRax16 r =>
    [natByte 102] ++ wdRex .w32 0 (regHigh r) ++
      [natByte (144 + regLow r)]
  | .xchgRax32 r =>
    if regHigh r == 0 && regLow r == 0 then
      [natByte 64, natByte 144]
    else
      wdRex .w32 0 (regHigh r) ++ [natByte (144 + regLow r)]
  | .xchgRax64 r =>
    wdRex .w64 0 (regHigh r) ++ [natByte (144 + regLow r)]
  | .movsxd dst src =>
    wdRex .w64 (regHigh dst) (regHigh src) ++
      [natByte 99, modrmReg (regLow dst) (regLow src)]

/-! ## 8. Pinned bytes: one canonical encoding per admitted form,
    planted refusals beside them. -/

/-- Pinned decode: CBW. -/
theorem pin_sxcbw_dekode :
    decodeSx [natByte 102, natByte 152] =
      some (⟨.cbw, 2⟩, []) := by
  decide

/-- Pinned decode: CWDE. -/
theorem pin_sxcwde_dekode :
    decodeSx [natByte 152] = some (⟨.cwde, 1⟩, []) := by
  decide

/-- Pinned decode: CDQE. -/
theorem pin_sxcdqe_dekode :
    decodeSx [natByte 72, natByte 152] = some (⟨.cdqe, 2⟩, []) := by
  decide

/-- Pinned decode: CWD. -/
theorem pin_sxcwd_dekode :
    decodeSx [natByte 102, natByte 153] = some (⟨.cwd, 2⟩, []) := by
  decide

/-- Pinned decode: CDQ. -/
theorem pin_sxcdq_dekode :
    decodeSx [natByte 153] = some (⟨.cdq, 1⟩, []) := by
  decide

/-- Pinned decode: CQO. -/
theorem pin_sxcqo_dekode :
    decodeSx [natByte 72, natByte 153] = some (⟨.cqo, 2⟩, []) := by
  decide

/-- Pinned decode: bare `90` is NOP (never a self-exchange). -/
theorem pin_sxnop_dekode :
    decodeSx [natByte 144] = some (⟨.nop, 1⟩, []) := by
  decide

/-- Pinned decode: `91` exchanges ECX with EAX at 32 bits. -/
theorem pin_sxxchg91_dekode :
    decodeSx [natByte 145] = some (⟨.xchgRax32 .rcx, 1⟩, []) := by
  decide

/-- Pinned decode: `REX.W+B 90` exchanges r8 with RAX at 64 bits. -/
theorem pin_sxxchg4890r8_dekode :
    decodeSx [natByte 73, natByte 144] =
      some (⟨.xchgRax64 .r8, 2⟩, []) := by
  decide

/-- Pinned decode: redundant-REX `90` is the 32-bit self-exchange
    (the zero-extension surprise, kept distinct from NOP). -/
theorem pin_sx4090_dekode :
    decodeSx [natByte 64, natByte 144] =
      some (⟨.xchgRax32 .rax, 2⟩, []) := by
  decide

/-- Pinned decode: `86 C0` exchanges AL with itself at 8 bits. -/
theorem pin_sx86c0_dekode :
    decodeSx [natByte 134, natByte 192] =
      some (⟨.xchgReg .b8 .rax .rax, 2⟩, []) := by
  decide

/-- Pinned decode: `87 C1` exchanges EAX with ECX at 32 bits. -/
theorem pin_sx87c1_dekode :
    decodeSx [natByte 135, natByte 193] =
      some (⟨.xchgReg .b32 .rax .rcx, 2⟩, []) := by
  decide

/-- Pinned decode: `66 87 C1` is the 16-bit exchange. -/
theorem pin_sx6687c1_dekode :
    decodeSx [natByte 102, natByte 135, natByte 193] =
      some (⟨.xchgReg .b16 .rax .rcx, 3⟩, []) := by
  decide

/-- Pinned decode: `REX.W+R 87 C1` exchanges r8 with ECX. -/
theorem pin_sx4c87c1_dekode :
    decodeSx [natByte 76, natByte 135, natByte 193] =
      some (⟨.xchgReg .b64 .r8 .rcx, 3⟩, []) := by
  decide

/-- Pinned decode: `REX.W 63 C0` moves EAX sign-extended into RAX. -/
theorem pin_sx63c0_dekode :
    decodeSx [natByte 72, natByte 99, natByte 192] =
      some (⟨.movsxd .rax .rax, 3⟩, []) := by
  decide

/-- Pinned decode: `REX.W+R 63 D9` moves ECX into r11 extended. -/
theorem pin_sx4c63d9_dekode :
    decodeSx [natByte 76, natByte 99, natByte 217] =
      some (⟨.movsxd .r11 .rcx, 3⟩, []) := by
  decide

/-- Planted refusal: LOCK on the NOP byte. -/
theorem sxNichts_lock90 :
    decodeSx [natByte 240, natByte 144] = none := by
  decide

/-- Planted refusal: LOCK on the CWDE byte. -/
theorem sxNichts_lock98 :
    decodeSx [natByte 240, natByte 152] = none := by
  decide

/-- Planted refusal: `87` with a memory ModRM (implicitly LOCKed,
    stays with the locked families). -/
theorem sxNichts_xchg87mem :
    decodeSx [natByte 135, natByte 4] = none := by
  decide

/-- Planted refusal: `86` with a memory ModRM. -/
theorem sxNichts_xchg86mem :
    decodeSx [natByte 134, natByte 0] = none := by
  decide

/-- Planted refusal: `63` without REX.W is no MOVSXD here. -/
theorem sxNichts_movsxdOhneRex :
    decodeSx [natByte 99, natByte 192] = none := by
  decide

/-- Planted refusal: `66`+REX.W on `63` (overdetermined). -/
theorem sxNichts_movsxd66rex :
    decodeSx [natByte 102, natByte 72, natByte 99, natByte 192] =
      none := by
  decide

/-- Planted refusal: `66`+REX.W on `87` (overdetermined). -/
theorem sxNichts_xchg87_66rex :
    decodeSx [natByte 102, natByte 72, natByte 135, natByte 192] =
      none := by
  decide

/-- Planted refusal: `66`+REX.W on `98` (overdetermined). -/
theorem sxNichts_cbw66rex :
    decodeSx [natByte 102, natByte 72, natByte 152] = none := by
  decide

/-- Planted refusal: truncated `87` without its ModRM byte. -/
theorem sxNichts_xchg87kurz :
    decodeSx [natByte 135] = none := by
  decide

/-- Pinned bytes: CBW. -/
theorem pin_sxcbw_bytes :
    sxEncode .cbw = [natByte 102, natByte 152] := by
  decide

/-- Pinned bytes: the 32-bit RAX self-exchange needs its REX. -/
theorem pin_sxxchgRax32rax_bytes :
    sxEncode (.xchgRax32 .rax) = [natByte 64, natByte 144] := by
  decide

/-- Pinned bytes: MOVSXD r11, ecx. -/
theorem pin_sxmovsxdR_bytes :
    sxEncode (.movsxd .r11 .rcx) =
      [natByte 76, natByte 99, natByte 217] := by
  decide

/- CUTS:
   Skeleton only: event vocabulary without semantics.
   NOT proved here, and not claimed: everything (see task).
-/

#print axioms SxBefehl
#print axioms SxDecodiert

end Gabbro.Grammatik.X86
