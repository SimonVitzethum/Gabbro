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
    `xchgReg`/`xchgRax` are the register exchanges at an explicit
    width; `movsxd` is the REX.W register move with doubleword
    sign-extension. -/
inductive SxBefehl where
  | cbw | cwde | cdqe | cwd | cdq | cqo | nop
  | xchgReg (b : Breite) (a c : Register)
  | xchgRax (b : Breite) (r : Register)
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
    | .xchgRax b r => .ok { (xchgSchritt b Register.rax r s) with rip := nach }
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
    | xchgRax b r =>
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
    | xchgRax b r =>
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

/- CUTS:
   Skeleton only: event vocabulary without semantics.
   NOT proved here, and not claimed: everything (see task).
-/

#print axioms SxBefehl
#print axioms SxDecodiert

end Gabbro.Grammatik.X86
