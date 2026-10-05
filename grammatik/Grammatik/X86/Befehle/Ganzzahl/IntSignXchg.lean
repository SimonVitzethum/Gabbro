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
import Grammatik.X86.Kern.Typen
import Grammatik.X86.Kern.Wort
import Grammatik.X86.Speicher.Speicher
import Grammatik.X86.TSO.Kern.TSO
import Grammatik.X86.Kern.Ausfuehrung
import Grammatik.X86.Befehle.Arithmetik.NarrowOps
import Grammatik.X86.Befehle.Arithmetik.MulDiv
import Grammatik.X86.Befehle.Arithmetik.MulDivWidthHardwareForms
import Grammatik.X86.Hw.Grundlage.ExtendedExecution
import Grammatik.X86.Flags.FeatureProfile
import Grammatik.X86.Kern.Gleitprofil
import Grammatik.X86.Befehle.Gleitkomma.ScalarFloat
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Hw.Familien.HwMulDivWidth
import Grammatik.X86.TSO.Verriegelt.XchgOrderNeed
namespace Gabbro.Grammatik.X86

/-- Admitted event forms. `cbw`/`cwd` are the 16-bit preparations
    (opcodes `66 98`/`66 99`); `cwde`/`cdqe`/`cdq`/`cqo` lift the
    accepted width preparations; `nop` is every `90H` encoding
    resolving to the RAX self (bare and prefixed: exactly the
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
    accepted `vor99Schritt` broadcasts at 32/64 bits. `sxXchgSeite`
    states one side of an exchange at an explicit width (8/16-bit
    merge, 32-bit zero-extends, 64-bit whole); both sides read the
    OLD values, so a same-register 87-form exchange keeps the
    32-bit zero-extension while every self-resolving `90H` stays
    `nop` (§3). -/

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
def sxXchgSeite (b : Breite) (old other : Wort) : Wort :=
  match b with
  | .b8 => mergeRegNarrow .b8 old other
  | .b16 => mergeRegNarrow .b16 old other
  | .b32 => trunc .b32 other
  | .b64 => other

/-- Exchange shape: both sides read the OLD values, then RIP
    advances at the caller. -/
def sxXchgSchritt (b : Breite) (a c : Register) (s : Zustand) : Zustand :=
  let va := s.register a
  let vc := s.register c
  let r1 := regSet s.register a (sxXchgSeite b va vc)
  let r2 := regSet r1 c (sxXchgSeite b vc va)
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
    | .xchgReg b a c => .ok { (sxXchgSchritt b a c s) with rip := nach }
    | .xchgRax16 r => .ok { (sxXchgSchritt .b16 Register.rax r s) with rip := nach }
    | .xchgRax32 r => .ok { (sxXchgSchritt .b32 Register.rax r s) with rip := nach }
    | .xchgRax64 r => .ok { (sxXchgSchritt .b64 Register.rax r s) with rip := nach }
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
theorem sxXchgSchritt_eq (b : Breite) (a c : Register) (s : Zustand) :
    (sxXchgSchritt b a c s).register =
      regSet (regSet s.register a (sxXchgSeite b (s.register a) (s.register c))) c
        (sxXchgSeite b (s.register c) (s.register a)) := by
  rfl

/-- Read-back at the first side (distinct registers). -/
theorem sxXchgSchritt_bei_a_neq (b : Breite) (a c : Register) (s : Zustand)
    (hne : a ≠ c) :
    (sxXchgSchritt b a c s).register a =
      sxXchgSeite b (s.register a) (s.register c) := by
  rw [sxXchgSchritt_eq]
  rw [regSet_fremd _ c a _ hne]
  exact regSet_gleich _ _ _

/-- Read-back at the second side (no side condition). -/
theorem sxXchgSchritt_bei_c (b : Breite) (a c : Register) (s : Zustand) :
    (sxXchgSchritt b a c s).register c =
      sxXchgSeite b (s.register c) (s.register a) := by
  rw [sxXchgSchritt_eq]
  exact regSet_gleich _ _ _

/-! ## 3b. The accepted 64-bit register swap is lifted, not redone.

    `XchgOrderNeed` (lane 779) already models the 64-bit register
    exchange (`XchgForm.reg`, pure swap, no barrier) with its byte
    codec over `REX.W + 87 /r`. The 64-bit arm here IS that swap:
    both sides read the old values. The shared bytes below decode
    in both decoders (field naming differs, the swap agrees); the
    memory form, the barrier and the `90`-alias refusal stay solely
    with the accepted file. -/

/-- Shared bytes: the accepted decoder reads the 64-bit exchange
    of the same two registers (field naming differs, the swap is
    the same one). -/
theorem pin_xchgAkzeptiert_dekode :
    decodeXchg [natByte 72, natByte 135, natByte 193] =
      some ((XchgForm.reg .rcx .rax), []) := by
  decide

/-- The 64-bit register exchange IS the accepted register swap. -/
theorem sxXchg64_ist_reg (a c : Register) (s : Zustand)
    (t : TSOZustand) (n : Nat) (q : Register) :
    (sxXchgSchritt .b64 a c s).register q =
      match xchgSchritt (XchgForm.reg a c) n
        ⟨s.register, s.flags, t⟩ with
      | some s' => s'.reg q
      | none => s.register q := by
  rw [sxXchgSchritt_eq]
  unfold xchgSchritt
  simp [sxXchgSeite]

/-- The 16-bit RAX self-exchange event agrees with the `66 87 C0`
    self-exchange event (the canonical bytes of the observable):
    both run the same register update. -/
theorem sxXchgRax16rax_ist (s : Zustand) (l : Nat) :
    sxSchritt ⟨.xchgRax16 .rax, l⟩ s =
      sxSchritt ⟨.xchgReg .b16 .rax .rax, l⟩ s := by
  cases h : laengeOk l <;> simp [sxSchritt, h]

/-- The 32-bit RAX self-exchange event agrees with the `87 C0`
    self-exchange event: both zero-extend EAX. -/
theorem sxXchgRax32rax_ist (s : Zustand) (l : Nat) :
    sxSchritt ⟨.xchgRax32 .rax, l⟩ s =
      sxSchritt ⟨.xchgReg .b32 .rax .rax, l⟩ s := by
  cases h : laengeOk l <;> simp [sxSchritt, h]

/-- The 64-bit RAX self-exchange event agrees with the
    `REX.W 87 C0` self-exchange event. -/
theorem sxXchgRax64rax_ist (s : Zustand) (l : Nat) :
    sxSchritt ⟨.xchgRax64 .rax, l⟩ s =
      sxSchritt ⟨.xchgReg .b64 .rax .rax, l⟩ s := by
  cases h : laengeOk l <;> simp [sxSchritt, h]

/-- CBW keeps the flags. -/
theorem cbwSchritt_flags (s : Zustand) : (cbwSchritt s).flags = s.flags := rfl

/-- CBW keeps the memory. -/
theorem cbwSchritt_memory (s : Zustand) : (cbwSchritt s).speicher = s.speicher := rfl

/-- CWD keeps the flags. -/
theorem cwdSchritt_flags (s : Zustand) : (cwdSchritt s).flags = s.flags := rfl

/-- CWD keeps the memory. -/
theorem cwdSchritt_memory (s : Zustand) : (cwdSchritt s).speicher = s.speicher := rfl

/-- Exchanges keep the flags. -/
theorem sxXchgSchritt_flags (b : Breite) (a c : Register) (s : Zustand) :
    (sxXchgSchritt b a c s).flags = s.flags := rfl

/-- Exchanges keep the memory. -/
theorem sxXchgSchritt_memory (b : Breite) (a c : Register) (s : Zustand) :
    (sxXchgSchritt b a c s).speicher = s.speicher := rfl

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
theorem probe_sxXchgSeite_32 :
    sxXchgSeite .b32 0xFFFFFFFFFFFFFFFF 0x11223344 = 0x11223344 := by
  decide

/-- Pinned 8-bit exchange side: merges the low byte, keeps upper. -/
theorem probe_sxXchgSeite_8 :
    sxXchgSeite .b8 0xABCDEF1234567890 0x11 = 0xABCDEF1234567811 := by
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

theorem ext_weist_sx4090_zurueck :
    decodeExt [natByte 64, natByte 144] = none := by
  decide

theorem ext_weist_sx4c90_zurueck :
    decodeExt [natByte 76, natByte 144] = none := by
  decide

theorem ext_weist_sx66rex90_zurueck :
    decodeExt [natByte 102, natByte 72, natByte 144] = none := by
  decide

/-! ## 6. Decode: the accepted prefix parse, family opcodes after it.

    `decodeSx` reuses `nimmPraefix` (LOCK refusal, `66`/REX parse)
    and `wdBits`/`codeReg` unchanged. REX.X names no SIB anywhere
    in this family (no addressed form lives here: every ModRM use
    is register-direct and every other opcode is ModRM-free), so
    it is ignored; every memory ModRM refuses (an XCHG memory
    operand is implicitly LOCKed and stays with the locked
    families; a MOVSXD memory source needs the TSO read path,
    still open). Every `90H` encoding that resolves to the RAX
    self -- bare `90` and every prefixed form (`66 90`, REX `90`,
    REX.W `90`) -- is the architectural NOP at the consumed
    length, never a zero-extending self-exchange: the observable
    32-bit self-exchange is the `87 C0` form. -/

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

/-- `90+r` dispatch after the prefix: any encoding resolving to
    the RAX self (no B extension, low opcode bits zero) IS the
    architectural NOP at the consumed length, under every prefix;
    otherwise the width follows the prefix (default 32, `66` 16,
    REX.W 64) and REX.B extends the opcode register. REX.R names
    no field here and is ignored. -/
def decodeSx90 (op16 : Bool) (wb _rb bb npfx : Nat) (op : Byte)
    (rest : List Byte) : Option (SxDecodiert × List Byte) :=
  if byteNat op / 8 == 18 then
    let lo := byteNat op % 8
    if bb == 0 && lo == 0 then
      some (⟨.nop, npfx + 1⟩, rest)
    else if !op16 && wb == 0 then
      match codeReg (bb * 8 + lo) with
      | some r => some (⟨.xchgRax32 r, npfx + 1⟩, rest)
      | none => none
    else if op16 && wb == 0 then
      match codeReg (bb * 8 + lo) with
      | some r => some (⟨.xchgRax16 r, npfx + 1⟩, rest)
      | none => none
    else if !op16 && wb == 1 then
      match codeReg (bb * 8 + lo) with
      | some r => some (⟨.xchgRax64 r, npfx + 1⟩, rest)
      | none => none
    else none
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
def decodeSxNachPraefix (op16 : Bool) (wb rb _xb bb npfx : Nat) :
    List Byte → Option (SxDecodiert × List Byte)
  | [] => none
  | op :: rest =>
    if byteNat op == 152 then decodeSx98 op16 wb npfx false rest
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
    else if byteNat op / 8 == 18 then
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
    is needed). No `90H` byte ever encodes a zero-extending event:
    a RAX self-exchange canonicalizes to its `87 C0`-family bytes
    (observably identical steps, see `sxXchgRax16rax_ist` and
    siblings), which decode to the matching `xchgReg` self event. -/

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
    if r == .rax then [natByte 102, natByte 135, natByte 192]
    else
      [natByte 102] ++ wdRex .w32 0 (regHigh r) ++
        [natByte (144 + regLow r)]
  | .xchgRax32 r =>
    if r == .rax then [natByte 135, natByte 192]
    else
      wdRex .w32 0 (regHigh r) ++ [natByte (144 + regLow r)]
  | .xchgRax64 r =>
    if r == .rax then [natByte 72, natByte 135, natByte 192]
    else
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

/-- Pinned decode: redundant-REX `90` resolving to the RAX self
    is NOP (never a zero-extending self-exchange). -/
theorem pin_sx4090_nop_dekode :
    decodeSx [natByte 64, natByte 144] =
      some (⟨.nop, 2⟩, []) := by
  decide

/-- Pinned decode: `66 90` is the 2-byte NOP. -/
theorem pin_sx6690_nop_dekode :
    decodeSx [natByte 102, natByte 144] =
      some (⟨.nop, 2⟩, []) := by
  decide

/-- Pinned decode: `REX.W 90` resolving to the RAX self is NOP. -/
theorem pin_sx4890_nop_dekode :
    decodeSx [natByte 72, natByte 144] =
      some (⟨.nop, 2⟩, []) := by
  decide

/-- Pinned decode: `REX.W+R 90` resolving to the RAX self is NOP
    (the R bit names no field and changes nothing). -/
theorem pin_sx4c90_nop_dekode :
    decodeSx [natByte 76, natByte 144] =
      some (⟨.nop, 2⟩, []) := by
  decide

/-- Pinned decode: `66`+REX.W `90` is NOP at length 3. -/
theorem pin_sx66rex90_nop_dekode :
    decodeSx [natByte 102, natByte 72, natByte 144] =
      some (⟨.nop, 3⟩, []) := by
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

/-- Pinned bytes: the 32-bit RAX self-exchange canonicalizes to
    the `87 C0` form (no `90H` byte encodes a zero-extension). -/
theorem pin_sxxchgRax32rax_bytes :
    sxEncode (.xchgRax32 .rax) = [natByte 135, natByte 192] := by
  decide

/-- Pinned bytes: the 16-bit RAX self-exchange canonicalizes to
    the `66 87 C0` form. -/
theorem pin_sxxchgRax16rax_bytes :
    sxEncode (.xchgRax16 .rax) =
      [natByte 102, natByte 135, natByte 192] := by
  decide

/-- Pinned bytes: the 64-bit RAX self-exchange canonicalizes to
    the `REX.W 87 C0` form. -/
theorem pin_sxxchgRax64rax_bytes :
    sxEncode (.xchgRax64 .rax) =
      [natByte 72, natByte 135, natByte 192] := by
  decide

/-- Pinned bytes: MOVSXD r11, ecx. -/
theorem pin_sxmovsxdR_bytes :
    sxEncode (.movsxd .r11 .rcx) =
      [natByte 76, natByte 99, natByte 217] := by
  decide

/-! ## 9. Round trips: decoding inverts encoding.

    Generic over every event and any suffix, in the accepted
    `cases … <;> rfl` shape: each concrete case reduces by
    evaluation. -/

/-- Round trip for CBW. -/
theorem sxRoundtrip_cbw (suffix : List Byte) :
    decodeSx (sxEncode .cbw ++ suffix) =
      some (⟨.cbw, (sxEncode .cbw).length⟩, suffix) := by
  rfl

/-- Round trip for CWDE. -/
theorem sxRoundtrip_cwde (suffix : List Byte) :
    decodeSx (sxEncode .cwde ++ suffix) =
      some (⟨.cwde, (sxEncode .cwde).length⟩, suffix) := by
  rfl

/-- Round trip for CDQE. -/
theorem sxRoundtrip_cdqe (suffix : List Byte) :
    decodeSx (sxEncode .cdqe ++ suffix) =
      some (⟨.cdqe, (sxEncode .cdqe).length⟩, suffix) := by
  rfl

/-- Round trip for CWD. -/
theorem sxRoundtrip_cwd (suffix : List Byte) :
    decodeSx (sxEncode .cwd ++ suffix) =
      some (⟨.cwd, (sxEncode .cwd).length⟩, suffix) := by
  rfl

/-- Round trip for CDQ. -/
theorem sxRoundtrip_cdq (suffix : List Byte) :
    decodeSx (sxEncode .cdq ++ suffix) =
      some (⟨.cdq, (sxEncode .cdq).length⟩, suffix) := by
  rfl

/-- Round trip for CQO. -/
theorem sxRoundtrip_cqo (suffix : List Byte) :
    decodeSx (sxEncode .cqo ++ suffix) =
      some (⟨.cqo, (sxEncode .cqo).length⟩, suffix) := by
  rfl

/-- Round trip for NOP. -/
theorem sxRoundtrip_nop (suffix : List Byte) :
    decodeSx (sxEncode .nop ++ suffix) =
      some (⟨.nop, (sxEncode .nop).length⟩, suffix) := by
  rfl

/-- Round trip for the 8-bit register exchange. -/
theorem sxRoundtrip_xchgReg8 (a c : Register) (suffix : List Byte) :
    decodeSx (sxEncode (.xchgReg .b8 a c) ++ suffix) =
      some (⟨.xchgReg .b8 a c,
        (sxEncode (.xchgReg .b8 a c)).length⟩, suffix) := by
  cases a <;> cases c <;> rfl

/-- Round trip for the 16-bit register exchange. -/
theorem sxRoundtrip_xchgReg16 (a c : Register) (suffix : List Byte) :
    decodeSx (sxEncode (.xchgReg .b16 a c) ++ suffix) =
      some (⟨.xchgReg .b16 a c,
        (sxEncode (.xchgReg .b16 a c)).length⟩, suffix) := by
  cases a <;> cases c <;> rfl

/-- Round trip for the 32-bit register exchange. -/
theorem sxRoundtrip_xchgReg32 (a c : Register) (suffix : List Byte) :
    decodeSx (sxEncode (.xchgReg .b32 a c) ++ suffix) =
      some (⟨.xchgReg .b32 a c,
        (sxEncode (.xchgReg .b32 a c)).length⟩, suffix) := by
  cases a <;> cases c <;> rfl

/-- Round trip for the 64-bit register exchange. -/
theorem sxRoundtrip_xchgReg64 (a c : Register) (suffix : List Byte) :
    decodeSx (sxEncode (.xchgReg .b64 a c) ++ suffix) =
      some (⟨.xchgReg .b64 a c,
        (sxEncode (.xchgReg .b64 a c)).length⟩, suffix) := by
  cases a <;> cases c <;> rfl

/-- Round trip for the 16-bit RAX exchange off the RAX self
    (the self canonicalizes to the `66 87 C0` form). -/
theorem sxRoundtrip_xchgRax16 (r : Register) (hne : r ≠ .rax)
    (suffix : List Byte) :
    decodeSx (sxEncode (.xchgRax16 r) ++ suffix) =
      some (⟨.xchgRax16 r,
        (sxEncode (.xchgRax16 r)).length⟩, suffix) := by
  cases r with
  | rax => exact absurd rfl hne
  | rcx => rfl
  | rdx => rfl
  | rbx => rfl
  | rsp => rfl
  | rbp => rfl
  | rsi => rfl
  | rdi => rfl
  | r8 => rfl
  | r9 => rfl
  | r10 => rfl
  | r11 => rfl
  | r12 => rfl
  | r13 => rfl
  | r14 => rfl
  | r15 => rfl

/-- Round trip for the 32-bit RAX exchange off the RAX self
    (the self canonicalizes to the `87 C0` form, never bare `90`). -/
theorem sxRoundtrip_xchgRax32 (r : Register) (hne : r ≠ .rax)
    (suffix : List Byte) :
    decodeSx (sxEncode (.xchgRax32 r) ++ suffix) =
      some (⟨.xchgRax32 r,
        (sxEncode (.xchgRax32 r)).length⟩, suffix) := by
  cases r with
  | rax => exact absurd rfl hne
  | rcx => rfl
  | rdx => rfl
  | rbx => rfl
  | rsp => rfl
  | rbp => rfl
  | rsi => rfl
  | rdi => rfl
  | r8 => rfl
  | r9 => rfl
  | r10 => rfl
  | r11 => rfl
  | r12 => rfl
  | r13 => rfl
  | r14 => rfl
  | r15 => rfl

/-- Round trip for the 64-bit RAX exchange off the RAX self
    (the self canonicalizes to the `REX.W 87 C0` form). -/
theorem sxRoundtrip_xchgRax64 (r : Register) (hne : r ≠ .rax)
    (suffix : List Byte) :
    decodeSx (sxEncode (.xchgRax64 r) ++ suffix) =
      some (⟨.xchgRax64 r,
        (sxEncode (.xchgRax64 r)).length⟩, suffix) := by
  cases r with
  | rax => exact absurd rfl hne
  | rcx => rfl
  | rdx => rfl
  | rbx => rfl
  | rsp => rfl
  | rbp => rfl
  | rsi => rfl
  | rdi => rfl
  | r8 => rfl
  | r9 => rfl
  | r10 => rfl
  | r11 => rfl
  | r12 => rfl
  | r13 => rfl
  | r14 => rfl
  | r15 => rfl

/-- Round trip for register MOVSXD. -/
theorem sxRoundtrip_movsxd (dst src : Register) (suffix : List Byte) :
    decodeSx (sxEncode (.movsxd dst src) ++ suffix) =
      some (⟨.movsxd dst src,
        (sxEncode (.movsxd dst src)).length⟩, suffix) := by
  cases dst <;> cases src <;> rfl

/-! ## 10. Dispatcher: the accepted unified chain first.

    `decodeSignXchg` tries `decodeExt` first and the family decoder
    only where the unified chain refuses: no pilot or extension
    form is shadowed, and each new row below is taken exactly once
    (§5 pins supply the refusal evidence). -/

/-- Unified dispatcher instruction: the accepted unified chain
    first, the family only where it refuses. -/
inductive SxHwInstr where
  | ext : ExtInstr → SxHwInstr
  | sx : SxDecodiert → SxHwInstr
  deriving DecidableEq, Repr

/-- Dispatcher: the unified decoder first, the family decoder only
    where the unified chain refuses. No pilot form is shadowed. -/
def decodeSignXchg : List Byte → Option (SxHwInstr × List Byte) :=
  fun bs =>
    match decodeExt bs with
    | some (i, rest) => some (.ext i, rest)
    | none =>
      match decodeSx bs with
      | some (d, rest) => some (.sx d, rest)
      | none => none

/-- Consumed length of one dispatcher instruction (checked data). -/
def sxHwLen : SxHwInstr → Nat
  | .ext i => extLen i
  | .sx d => d.laenge

/-- The dispatcher agrees with the unified chain wherever it
    accepts: no pilot or extension form is shadowed. -/
theorem decodeSignXchg_prefers_ext (bs : List Byte) (i : ExtInstr)
    (rest : List Byte) (h : decodeExt bs = some (i, rest)) :
    decodeSignXchg bs = some (.ext i, rest) := by
  unfold decodeSignXchg
  rw [h]

/-- Where the unified chain refuses, a covered family row is taken. -/
theorem decodeSignXchg_sx (bs : List Byte) (d : SxDecodiert)
    (rest : List Byte) (h1 : decodeExt bs = none)
    (h2 : decodeSx bs = some (d, rest)) :
    decodeSignXchg bs = some (.sx d, rest) := by
  unfold decodeSignXchg
  rw [h1, h2]

/-- Where both chains refuse, the dispatcher refuses. -/
theorem decodeSignXchg_nichts (bs : List Byte)
    (h1 : decodeExt bs = none) (h2 : decodeSx bs = none) :
    decodeSignXchg bs = none := by
  unfold decodeSignXchg
  rw [h1, h2]

/-- Pin: the pilot row goes through unchanged. -/
theorem pin_sxHw_pilot_ret :
    decodeSignXchg (encode .ret) =
      some (.ext (.pilot ⟨.ret, 1⟩), []) :=
  decodeSignXchg_prefers_ext _ _ _ pin_ext_pilot_ret

/-- Pin: CWDE takes the family arm. -/
theorem pin_sxHw_cwde :
    decodeSignXchg [natByte 152] = some (.sx ⟨.cwde, 1⟩, []) :=
  decodeSignXchg_sx _ _ _ ext_weist_wdvor98_zurueck pin_sxcwde_dekode

/-- Pin: CBW takes the family arm. -/
theorem pin_sxHw_cbw :
    decodeSignXchg [natByte 102, natByte 152] =
      some (.sx ⟨.cbw, 2⟩, []) :=
  decodeSignXchg_sx _ _ _ ext_weist_sxcbw_zurueck pin_sxcbw_dekode

/-- Pin: bare `90` takes the family arm as NOP. -/
theorem pin_sxHw_nop :
    decodeSignXchg [natByte 144] = some (.sx ⟨.nop, 1⟩, []) :=
  decodeSignXchg_sx _ _ _ ext_weist_sxnop_zurueck pin_sxnop_dekode

/-- Pin: `66 90` takes the family arm as the 2-byte NOP. -/
theorem pin_sxHw_nop66 :
    decodeSignXchg [natByte 102, natByte 144] =
      some (.sx ⟨.nop, 2⟩, []) :=
  decodeSignXchg_sx _ _ _ ext_weist_sxxchg6690_zurueck
    pin_sx6690_nop_dekode

/-- Pin: redundant-REX `90` takes the family arm as NOP. -/
theorem pin_sxHw_nop40 :
    decodeSignXchg [natByte 64, natByte 144] =
      some (.sx ⟨.nop, 2⟩, []) :=
  decodeSignXchg_sx _ _ _ ext_weist_sx4090_zurueck
    pin_sx4090_nop_dekode

/-- Pin: `91` takes the family arm as the 32-bit RAX exchange. -/
theorem pin_sxHw_xchg91 :
    decodeSignXchg [natByte 145] = some (.sx ⟨.xchgRax32 .rcx, 1⟩, []) :=
  decodeSignXchg_sx _ _ _ ext_weist_sxxchg91_zurueck pin_sxxchg91_dekode

/-- Pin: `REX.W 63 C0` takes the family arm as MOVSXD. -/
theorem pin_sxHw_movsxd :
    decodeSignXchg [natByte 72, natByte 99, natByte 192] =
      some (.sx ⟨.movsxd .rax .rax, 3⟩, []) :=
  decodeSignXchg_sx _ _ _ ext_weist_sxmovsxd_zurueck pin_sx63c0_dekode

/-- Planted refusal: LOCK stays refused through the dispatcher. -/
theorem sxHw_nichts_lock90 :
    decodeSignXchg [natByte 240, natByte 144] = none :=
  decodeSignXchg_nichts _ ext_weist_sxlock90_zurueck sxNichts_lock90

/-! ## 11. One step: exact evaluation selection over the accepted helpers.

    The unified arm IS the accepted unified evaluator; the family
    arm IS the family evaluator on the core half. A divide-style
    trap cannot fire here (proved below: no family step halts),
    and refusal is unified refusal. -/

/-- One unified step: Ext through `stepExt`, the family through
    `sxSchritt` on the core half. -/
def sxHwSchritt (i : SxHwInstr) (t : FpZustand)
    (b : BereitProfil) : ExtAusgang :=
  match i with
  | .ext j => stepExt j t b
  | .sx d =>
    match sxSchritt d t.kern with
    | .ok s' => .weiter { t with kern := s' }
    | .hardwareHalt => .halt
    | .misslungen => .verweigert

/-- Selection: the unified arm IS the accepted unified step. -/
theorem sxHwSchritt_ext (j : ExtInstr) (t : FpZustand)
    (b : BereitProfil) (o : ExtAusgang)
    (h : stepExt j t b = o) :
    sxHwSchritt (.ext j) t b = o := by
  have e : sxHwSchritt (.ext j) t b = stepExt j t b := rfl
  rw [e, h]

/-- Selection: the family arm IS the family evaluator on success. -/
theorem sxHwSchritt_sx_ok (d : SxDecodiert) (t : FpZustand)
    (b : BereitProfil) (s' : Zustand)
    (h : sxSchritt d t.kern = .ok s') :
    sxHwSchritt (.sx d) t b = .weiter { t with kern := s' } := by
  have e : sxHwSchritt (.sx d) t b =
      match sxSchritt d t.kern with
      | .ok s' => ExtAusgang.weiter { t with kern := s' }
      | .hardwareHalt => .halt
      | .misslungen => .verweigert := rfl
  rw [e, h]

/-- Selection: the halt arm fires exactly where the family halts. -/
theorem sxHwSchritt_sx_halt (d : SxDecodiert) (t : FpZustand)
    (b : BereitProfil)
    (h : sxSchritt d t.kern = .hardwareHalt) :
    sxHwSchritt (.sx d) t b = .halt := by
  have e : sxHwSchritt (.sx d) t b =
      match sxSchritt d t.kern with
      | .ok s' => ExtAusgang.weiter { t with kern := s' }
      | .hardwareHalt => .halt
      | .misslungen => .verweigert := rfl
  rw [e, h]

/-- Selection: family refusal is unified refusal. -/
theorem sxHwSchritt_sx_verweigert (d : SxDecodiert) (t : FpZustand)
    (b : BereitProfil)
    (h : sxSchritt d t.kern = .misslungen) :
    sxHwSchritt (.sx d) t b = .verweigert := by
  have e : sxHwSchritt (.sx d) t b =
      match sxSchritt d t.kern with
      | .ok s' => ExtAusgang.weiter { t with kern := s' }
      | .hardwareHalt => .halt
      | .misslungen => .verweigert := rfl
  rw [e, h]

/-- No family step halts: these operations have no fault class
    (no divide, no memory access on the admitted forms). -/
theorem sxSchritt_kein_halt (d : SxDecodiert) (s : Zustand) :
    sxSchritt d s ≠ .hardwareHalt := by
  unfold sxSchritt
  cases hlen : laengeOk d.laenge with
  | false =>
    simp [hlen]
  | true =>
    simp only [hlen]
    cases hbef : d.befehl with
    | cbw => simp [hbef]
    | cwde => simp [hbef, wdSchritt, hlen]
    | cdqe => simp [hbef, wdSchritt, hlen]
    | cwd => simp [hbef]
    | cdq => simp [hbef, wdSchritt, hlen]
    | cqo => simp [hbef, wdSchritt, hlen]
    | nop => simp [hbef]
    | xchgReg b a c => simp [hbef]
    | xchgRax16 r => simp [hbef]
    | xchgRax32 r => simp [hbef]
    | xchgRax64 r => simp [hbef]
    | movsxd dst src => simp [hbef]

/-! ## 12. Named refusals: every refused shape carries its reason.

    `SxGrund` names the refusal classes. LOCK refusal follows
    generically from the accepted prefix parse; memory-ModRM
    refusal is generic over the failing `mod` values; the
    prefix-combination refusals stand in the checked table below
    (each tabled input provably refuses). -/

/-- Named refusal reasons for this family. -/
inductive SxGrund where
  | lockPrefix
  | memoryOperand
  | overdetermined
  | movsxdWithoutRexW
  | truncated
  deriving DecidableEq, Repr

/-- LOCK refusal is generic: where the accepted prefix parse
    refuses, the family decoder refuses. -/
theorem decodeSx_lock (bs : List Byte)
    (h : nimmPraefix bs = none) :
    decodeSx bs = none := by
  cases bs with
  | nil => rfl
  | cons b rest => simp [decodeSx, h]

/-- `87` with a memory ModRM refuses, for every failing `mod`. -/
theorem decodeSx87_mem (op16 : Bool) (wb rb bb npfx : Nat)
    (m : Byte) (rest : List Byte)
    (hmod : byteNat m / 64 = 0 ∨ byteNat m / 64 = 1 ∨
      byteNat m / 64 = 2) :
    decodeSx87 op16 wb rb bb npfx m rest = none := by
  unfold decodeSx87
  rcases hmod with h | h | h <;> simp [h]

/-- `86` with a memory ModRM refuses, for every failing `mod`. -/
theorem decodeSx86_mem (rb bb npfx : Nat)
    (m : Byte) (rest : List Byte)
    (hmod : byteNat m / 64 = 0 ∨ byteNat m / 64 = 1 ∨
      byteNat m / 64 = 2) :
    decodeSx86 rb bb npfx m rest = none := by
  unfold decodeSx86
  rcases hmod with h | h | h <;> simp [h]

/-- `63` with a memory ModRM refuses, for every failing `mod`. -/
theorem decodeSx63_mem (op16 : Bool) (wb rb bb npfx : Nat)
    (m : Byte) (rest : List Byte)
    (hmod : byteNat m / 64 = 0 ∨ byteNat m / 64 = 1 ∨
      byteNat m / 64 = 2) :
    decodeSx63 op16 wb rb bb npfx m rest = none := by
  unfold decodeSx63
  rcases hmod with h | h | h <;> simp [h]

/-- Reason table: every planted refusal input with its name. -/
def sxGrundTabelle : List (List Byte × SxGrund) :=
  [([natByte 240, natByte 144], .lockPrefix),
   ([natByte 240, natByte 152], .lockPrefix),
   ([natByte 135, natByte 4], .memoryOperand),
   ([natByte 134, natByte 0], .memoryOperand),
   ([natByte 99, natByte 192], .movsxdWithoutRexW),
   ([natByte 102, natByte 72, natByte 99, natByte 192], .overdetermined),
   ([natByte 102, natByte 72, natByte 135, natByte 192], .overdetermined),
   ([natByte 102, natByte 72, natByte 152], .overdetermined),
   ([natByte 135], .truncated)]

/-- Every tabled input refuses. -/
theorem sxTabelle_verweigert (p : List Byte × SxGrund)
    (h : p ∈ sxGrundTabelle) : decodeSx p.1 = none := by
  simp [sxGrundTabelle] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

/-! ## 13. Machine adapter: the family on the coherent machine.

    The producer plug instantiates `HwAdapter SxDecodiert`: a
    successful family step re-embeds core data over the shared
    memory; halt and refusal admit no successor state (halt never
    fires here by §11, so every adapter refusal is a decode
    refusal). -/

/-- A bad decode length admits no family step. -/
theorem sx_laenge_misslungen (d : SxDecodiert) (s : Zustand)
    (h : laengeOk d.laenge = false) :
    sxSchritt d s = .misslungen := by
  unfold sxSchritt
  simp [h]

/-- The family plug: one checked family event step on the coherent
    machine. `none` = refusal, never a silent successor. -/
def adapterSignXchg : HwAdapter SxDecodiert :=
  ⟨fun m c d =>
    match sxSchritt d (projZustand m c) with
    | .ok s' =>
      some (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
    | .hardwareHalt => none
    | .misslungen => none⟩

/-- Every adapter step preserves well-formedness: only core data
    moves, profiles are untouched. -/
theorem adapterSignXchg_wf (m : HwMaschine) (c : Nat)
    (d : SxDecodiert) (m' : HwMaschine) (hwf : HwWf m)
    (h : (adapterSignXchg).schritt m c d = some m') :
    HwWf m' := by
  unfold adapterSignXchg at h
  simp only at h
  cases hsch : sxSchritt d (projZustand m c) with
  | ok s' =>
    rw [hsch] at h
    simp only at h
    cases h
    unfold setKernVonFp
    exact setKernDaten_wf _ _ _ hwf
  | hardwareHalt =>
    rw [hsch] at h
    simp only at h
    cases h
  | misslungen =>
    rw [hsch] at h
    simp only at h
    cases h

/-- Agreement: the adapter succeeds exactly where the family step
    succeeds, with the successor core data re-embedded. -/
theorem adapterSignXchg_ok (m : HwMaschine) (c : Nat)
    (d : SxDecodiert) (s' : Zustand)
    (h : sxSchritt d (projZustand m c) = .ok s') :
    (adapterSignXchg).schritt m c d =
      some (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩) := by
  unfold adapterSignXchg
  simp only [h]

/-- The successor core sees the family successor registers over
    the shared memory. -/
theorem adapterSignXchg_proj (m : HwMaschine) (c : Nat)
    (d : SxDecodiert) (s' : Zustand)
    (h : sxSchritt d (projZustand m c) = .ok s') :
    ((setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩).kerne c).register =
      s'.register ∧
    (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩).mem = m.mem ∧
    s'.speicher = m.mem := by
  refine ⟨setKernVonFp_register m c _,
    setKernVonFp_speicher m c _, ?_⟩
  have hmem := sxSchritt_memory d (projZustand m c) s' h
  have hproj : (projZustand m c).speicher = m.mem := rfl
  rw [hproj] at hmem
  exact hmem

/-- A bad decode length admits no adapter step. -/
theorem adapterSignXchg_verweigert_bei_laenge (m : HwMaschine)
    (c : Nat) (d : SxDecodiert)
    (h : laengeOk d.laenge = false) :
    (adapterSignXchg).schritt m c d = none := by
  have hstep := sx_laenge_misslungen d (projZustand m c) h
  unfold adapterSignXchg
  simp only [hstep]

/-! ## 14. Machine outcome: success continues, refusal refuses.

    Reuses the accepted `HwRegAusgang` unchanged (never edited
    here): success re-embeds core data, refusal is `verweigert`.
    The halt arm is selected exactly where the family halts, which
    never happens (§11), so it carries no register claim. -/

/-- One family machine step on core `c`: the family step on the
    core projection, re-embedded on success. -/
def sxHwRegSchritt (m : HwMaschine) (c : Nat)
    (d : SxDecodiert) : HwRegAusgang :=
  match sxSchritt d (projZustand m c) with
  | .ok s' => .weiter (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
  | .hardwareHalt => .halt
  | .misslungen => .verweigert

/-- Selection: a successful family step continues on the machine. -/
theorem sxHwRegSchritt_weiter (m : HwMaschine) (c : Nat)
    (d : SxDecodiert) (s' : Zustand)
    (h : sxSchritt d (projZustand m c) = .ok s') :
    sxHwRegSchritt m c d =
      .weiter (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩) := by
  have e : sxHwRegSchritt m c d =
      match sxSchritt d (projZustand m c) with
      | .ok s' => HwRegAusgang.weiter
        (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
      | .hardwareHalt => .halt
      | .misslungen => .verweigert := rfl
  rw [e, h]

/-- Selection: the halt arm fires exactly where the family halts
    (which never happens, `sxSchritt_kein_halt`). -/
theorem sxHwRegSchritt_halt (m : HwMaschine) (c : Nat)
    (d : SxDecodiert)
    (h : sxSchritt d (projZustand m c) = .hardwareHalt) :
    sxHwRegSchritt m c d = .halt := by
  have e : sxHwRegSchritt m c d =
      match sxSchritt d (projZustand m c) with
      | .ok s' => HwRegAusgang.weiter
        (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
      | .hardwareHalt => .halt
      | .misslungen => .verweigert := rfl
  rw [e, h]

/-- Selection: family refusal is machine refusal. -/
theorem sxHwRegSchritt_verweigert (m : HwMaschine) (c : Nat)
    (d : SxDecodiert)
    (h : sxSchritt d (projZustand m c) = .misslungen) :
    sxHwRegSchritt m c d = .verweigert := by
  have e : sxHwRegSchritt m c d =
      match sxSchritt d (projZustand m c) with
      | .ok s' => HwRegAusgang.weiter
        (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
      | .hardwareHalt => .halt
      | .misslungen => .verweigert := rfl
  rw [e, h]

/-- A machine halt carries no successor. -/
theorem sxHwRegSchritt_halt_ist_kein_weiter (m : HwMaschine)
    (c : Nat) (d : SxDecodiert) (m' : HwMaschine)
    (h : sxHwRegSchritt m c d = .halt) :
    sxHwRegSchritt m c d ≠ .weiter m' := by
  rw [h]
  intro hc
  cases hc

/-- A machine continue preserves well-formedness. -/
theorem sxHwRegSchritt_weiter_wf (m : HwMaschine) (c : Nat)
    (d : SxDecodiert) (m' : HwMaschine) (hwf : HwWf m)
    (h : sxHwRegSchritt m c d = .weiter m') :
    HwWf m' := by
  have e : sxHwRegSchritt m c d =
      match sxSchritt d (projZustand m c) with
      | .ok s' => HwRegAusgang.weiter
        (setKernVonFp m c ⟨s', (m.kerne c).xmm, (m.kerne c).fp⟩)
      | .hardwareHalt => .halt
      | .misslungen => .verweigert := rfl
  rw [e] at h
  cases hsch : sxSchritt d (projZustand m c) with
  | ok s' =>
    rw [hsch] at h
    simp only at h
    cases h
    unfold setKernVonFp
    exact setKernDaten_wf _ _ _ hwf
  | hardwareHalt =>
    rw [hsch] at h
    simp only at h
    cases h
  | misslungen =>
    rw [hsch] at h
    simp only at h
    cases h

/-! ## 15. Joint witness: two cores, family steps, buffered store.

    Core 0 sign-extends `AL = 0xFF` into `AX` (CBW); core 1
    exchanges `EAX` with `ECX` at 32 bits and extends `EAX` into
    `RDX` (MOVSXD); afterwards core 0 issues a buffered byte store
    that only the owner observes by forwarding, and the drain
    changes actual shared memory from 0 to 42. A bad length refuses
    and LOCK stays refused beside the run. Every claim projects to
    plain values before `decide` (machines contain functions). -/

/-- Witness registers core 0: AL holds `0xFF` (-1) for CBW. -/
def sxHwWitReg0 : Register → Wort := fun q =>
  if q = Register.rax then 0xFF
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness registers core 1: full RAX and a doubleword RCX for
    the 32-bit exchange and the MOVSXD source. -/
def sxHwWitReg1 : Register → Wort := fun q =>
  if q = Register.rax then 0x1122334455667788
  else if q = Register.rcx then 0xAABBCCDD
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness cores: core 0 extends, core 1 exchanges. -/
def sxHwWitKern : Nat → HwKern
  | 0 => ⟨sxHwWitReg0, zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨sxHwWitReg1, zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness start machine: shared memory, two cores, empty buffers,
    full silicon. -/
def sxHwWitStart : HwMaschine :=
  ⟨zeugenSpeicher, sxHwWitKern, fun _ => [],
    basisHw, fun _ => basisBereit⟩

/-- The witness machine is well-formed. -/
theorem sxHwWitStart_wf : HwWf sxHwWitStart := by
  intro c f _
  cases f <;> rfl

/-- Core 0 extends `AL = 0xFF` through the machine outcome. -/
def sxHwOutCbw : HwRegAusgang :=
  sxHwRegSchritt sxHwWitStart 0 ⟨.cbw, 2⟩

/-- Core 1 exchanges `EAX` with `ECX` through the machine outcome. -/
def sxHwOutXchg : HwRegAusgang :=
  sxHwRegSchritt sxHwWitStart 1 ⟨.xchgReg .b32 .rax .rcx, 2⟩

/-- Core 1 extends `EAX` into `RDX` through the machine outcome. -/
def sxHwOutMovsxd : HwRegAusgang :=
  sxHwRegSchritt sxHwWitStart 1 ⟨.movsxd .rdx .rax, 3⟩

/-- Read a core register out of a machine outcome. -/
def sxHwRegOut (o : HwRegAusgang) (c : Nat) (q : Register) :
    Option Wort :=
  match o with
  | .weiter m => some ((m.kerne c).register q)
  | _ => none

/-- Core 0 CBW: AX holds `0xFFFF`, RAX upper kept zero. -/
theorem sxHw_cbw_rax :
    sxHwRegOut sxHwOutCbw 0 Register.rax = some 0xFFFF := by
  decide

/-- Core 1 exchange: EAX holds the zero-extended ECX. -/
theorem sxHw_xchg_rax :
    sxHwRegOut sxHwOutXchg 1 Register.rax = some 0xAABBCCDD := by
  decide

/-- Core 1 exchange: ECX holds the zero-extended old EAX. -/
theorem sxHw_xchg_rcx :
    sxHwRegOut sxHwOutXchg 1 Register.rcx = some 0x55667788 := by
  decide

/-- Core 1 MOVSXD: RDX holds the positive doubleword unchanged. -/
theorem sxHw_movsxd_rdx :
    sxHwRegOut sxHwOutMovsxd 1 Register.rdx = some 0x55667788 := by
  decide

/-- Witness data address. -/
def sxHwWitAdr : Adresse := BitVec.ofNat 64 8192

/-- Witness TSO start: canonical memory, empty buffers. -/
def sxHwWitTso0 : TSOZustand := ⟨zeugenSpeicher, fun _ => []⟩

/-- Core 0 issues byte 42 at the data cell. -/
def sxHwWitTso1 : Option TSOZustand :=
  issueByte sxHwWitTso0 0 sxHwWitAdr (BitVec.ofNat 8 42)

/-- Core 0 observes its own byte (forwarding). -/
def sxHwWitEigen : Option (Option Byte) :=
  match sxHwWitTso1 with
  | some s => some (loadByte s 0 sxHwWitAdr)
  | none => none

/-- Core 1 observes the old byte (no foreign forwarding). -/
def sxHwWitFremd : Option (Option Byte) :=
  match sxHwWitTso1 with
  | some s => some (loadByte s 1 sxHwWitAdr)
  | none => none

/-- Core 0 drains its oldest entry. -/
def sxHwWitTso2 : Option TSOZustand :=
  match sxHwWitTso1 with
  | some s => flushKern s 0
  | none => none

/-- The shared byte after the drain. -/
def sxHwWitNachFlush : Option (Option Byte) :=
  match sxHwWitTso2 with
  | some s => some (some (s.mem.bytes sxHwWitAdr))
  | none => none

/-- Core 1 reads the drained byte from shared memory. -/
def sxHwWitFremdNach : Option (Option Byte) :=
  match sxHwWitTso2 with
  | some s => some (loadByte s 1 sxHwWitAdr)
  | none => none

/-- The data cell starts zeroed. -/
theorem sxHw_anfang_null :
    zeugenSpeicher.bytes sxHwWitAdr = BitVec.ofNat 8 0 := by
  rfl

/-- Forwarding: core 0 reads its own unflushed byte. -/
theorem sxHw_weiterleitung :
    sxHwWitEigen = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem sxHw_fremd_alt :
    sxHwWitFremd = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- The drain changes shared memory: the cell reads 42. -/
theorem sxHw_spuelung_aendert_speicher :
    sxHwWitNachFlush = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- After the drain core 1 observes the new byte. -/
theorem sxHw_fremd_neu :
    sxHwWitFremdNach = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- A bad decode length refuses the machine step. -/
theorem sxHw_schlechte_laenge_verweigert :
    sxHwRegSchritt sxHwWitStart 0 ⟨.cbw, 0⟩ = .verweigert := by
  have hstep := sx_laenge_misslungen ⟨.cbw, 0⟩
    (projZustand sxHwWitStart 0) (by decide)
  exact sxHwRegSchritt_verweigert _ _ _ hstep

/-- The joint witness: a reached two-core family run (CBW on core
    0, exchange and MOVSXD on core 1) beside a buffered store that
    only the owner forwards and a drain that changes actual shared
    memory from 0 to 42 -- with the refusal and decode refusals
    beside it. Non-degenerate: the drain changes actual shared
    memory. -/
theorem sxHw_zeuge :
    sxHwRegOut sxHwOutCbw 0 Register.rax = some 0xFFFF ∧
      sxHwRegOut sxHwOutXchg 1 Register.rax = some 0xAABBCCDD ∧
      sxHwRegOut sxHwOutXchg 1 Register.rcx = some 0x55667788 ∧
      sxHwRegOut sxHwOutMovsxd 1 Register.rdx = some 0x55667788 ∧
      sxHwWitEigen = some (some (BitVec.ofNat 8 42)) ∧
      sxHwWitFremd = some (some (BitVec.ofNat 8 0)) ∧
      sxHwWitNachFlush = some (some (BitVec.ofNat 8 42)) ∧
      sxHwWitFremdNach = some (some (BitVec.ofNat 8 42)) ∧
      zeugenSpeicher.bytes sxHwWitAdr = BitVec.ofNat 8 0 ∧
      HwWf sxHwWitStart ∧
      sxHwRegSchritt sxHwWitStart 0 ⟨.cbw, 0⟩ = .verweigert ∧
      decodeSignXchg [natByte 240, natByte 144] = none := by
  refine ⟨sxHw_cbw_rax, sxHw_xchg_rax, sxHw_xchg_rcx,
    sxHw_movsxd_rdx, sxHw_weiterleitung, sxHw_fremd_alt,
    sxHw_spuelung_aendert_speicher, sxHw_fremd_neu, sxHw_anfang_null,
    sxHwWitStart_wf, sxHw_schlechte_laenge_verweigert,
    sxHw_nichts_lock90⟩

/- CUTS:
   Proved here: the sign-extend-accumulator family (CBW/CWDE/CDQE,
   CWD/CDQ/CQO), the register XCHG forms (`86`/`87` ModRM-reg and
   `90+r`, with every `90H` resolving to the RAX self exactly the
   architectural NOP) and the register MOVSXD, connected to the
   coherent machine and the unified byte dispatcher -- the
   dispatcher prefers the accepted unified chain (19 rows proved
   refused, overlapping rows keep their unified arm), one unified
   step selects the evaluators exactly, the 32/64-bit preparations
   ARE the accepted `vor98Schritt`/`vor99Schritt` arms (lifted,
   never redefined), the 64-bit register exchange IS the accepted
   `XchgForm.reg` swap of `XchgOrderNeed` (lifted, never a second
   swap; shared bytes pinned in both decoders), every RAX
   self-exchange event agrees with its `87`-form twin
   (`sxXchgRax16rax_ist` and siblings), every successful step
   keeps flags and memory, no step halts, the `HwAdapter
   SxDecodiert` plug preserves `HwWf` with exact agreement and
   planted refusals, the machine outcome reuses the accepted
   `HwRegAusgang`, and a reached two-core run with owner-only
   forwarding and a memory-changing drain stands beside refusal
   evidence.
   NOT proved here, and not claimed:
   - No hardware correspondence: encodings are self-consistent
     canonical subsets checked against the SDM opcodes cited in
     the accepted `MulDivWidthHardwareForms` file (preparations
     `98`/`99`), the accepted `XchgOrderNeed` header (XCHG/LOCK
     rows, including the `90H`-is-NOP alias NOTE now cited here
     too), and the standard `90+r`/`86`/`87`/`63` rows, not
     x86 truth. Silicon assumptions named: CBW merges into AX
     (upper RAX kept), CWDE zero-extends EAX into RAX, CDQE takes
     the full sign-extension, CWD broadcasts the AX sign into DX
     (upper RDX kept), CDQ/CQO broadcast into the full register,
     32-bit exchanges zero-extend both sides, every `90H`
     resolving to the RAX self (bare and every prefixed form,
     REX.W included) changes nothing but RIP, the RAX
     self-exchange events canonicalize to their `87`-form twins
     (no `90H` byte encodes a zero-extension), XCHG-mem is
     implicitly LOCKed, MOVSXD needs REX.W in 64-bit mode,
     REX.R names no field on `90+r` (it is ignored), REX.X names
     no SIB anywhere in this family (it is ignored; SIB-carrying
     shapes refuse through the `mod` check).
   - Deliberate over-refusals (documented, never silent
     mis-execution): non-`0x48` REX on `98`/`99`, `66`+REX on
     `98`/`99`/`87`, REX without W on `87` outside `66`,
     MOVSXD without REX.W or with `66`.
   - No memory-operand forms: XCHG-mem stays with the locked
     families (the accepted `XchgForm.mem` barrier is neither
     redefined nor rewired here); MOVSXD-mem needs the TSO read
     path (still open).
   - No 8-bit `90+r` form exists (unencodable by construction:
     three RAX-exchange constructors, not one width-indexed).
   - No source/IR/ABI/loader/entry/budget link, no per-access
     target-to-W/GX simulation, no whole-word atomicity beyond
     byte drains, no timing/power behaviour.
-/

#print axioms SxBefehl
#print axioms SxDecodiert
#print axioms decodeSx
#print axioms sxEncode
#print axioms sxSchritt
#print axioms sx_cwde_ist_vor98
#print axioms sxSchritt_flags
#print axioms sxSchritt_memory
#print axioms sxSchritt_kein_halt
#print axioms decodeSignXchg
#print axioms sxHwSchritt
#print axioms adapterSignXchg
#print axioms adapterSignXchg_wf
#print axioms adapterSignXchg_ok
#print axioms sxHwRegSchritt_weiter
#print axioms sxHwWitStart_wf
#print axioms sxTabelle_verweigert
#print axioms sxRoundtrip_movsxd
#print axioms sxHw_zeuge

end Gabbro.Grammatik.X86
