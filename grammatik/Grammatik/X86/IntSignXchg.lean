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

/- CUTS:
   Skeleton only: event vocabulary without semantics.
   NOT proved here, and not claimed: everything (see task).
-/

#print axioms SxBefehl
#print axioms SxDecodiert

end Gabbro.Grammatik.X86
