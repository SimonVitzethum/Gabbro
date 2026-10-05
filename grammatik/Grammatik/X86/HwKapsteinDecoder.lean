/-
  File:      Grammatik/X86/HwKapsteinDecoder.lean
  Subject:   Capstone: one byte-decoder priority chain over all families.

  Lane 1291: every byte decoder the capstone union uses
  (`decodeMulDivWidth` over `decodeExt`, `s32Decode`, `mxcsrDecode`,
  `decodeLock`, `decodeLockAdr`, `decodeC`, `decodeCore`,
  `dekodiereAvx2`) in ONE deterministic priority chain `kapDecode`,
  with per-level agreement, a proved lock/lockAdr partition, the
  known width overlap exhibits, and closed witness pins per level.
  Accepted definitions are reused unchanged, never redefined.
-/
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.MulDivWidthHardwareForms
import Grammatik.X86.HwMulDivWidth
import Grammatik.X86.LockedInstructionExecution
import Grammatik.X86.AddressedHardwareExecution
import Grammatik.X86.ScalarFloat32HardwareForms
import Grammatik.X86.FpControlHardwareForms
import Grammatik.X86.HwFpDispatch
import Grammatik.X86.ISA
import Grammatik.X86.CompactForms
import Grammatik.X86.IntegerCore
import Grammatik.X86.Avx2Join

namespace Gabbro.Grammatik.X86

/-- One decoded row of the capstone chain: the width dispatcher arm
    (which already carries the whole unified chain), then each later
    family arm in priority order. -/
inductive KapDekodiert where
  | breit : WdHwInstr → KapDekodiert
  | s32 : S32Decodiert → KapDekodiert
  | mxcsr : MxcsrDec → KapDekodiert
  | lock : LockAnweisung → KapDekodiert
  | lockAdr : Register → AdrForm → KapDekodiert
  | kompakt : CompactDecodiert → KapDekodiert
  | kern : CoreDecodiert → KapDekodiert
  | avx2 : Avx2Join.Avx2Zeile → KapDekodiert
  deriving DecidableEq, Repr

/-- The capstone priority chain over bytes: each decoder runs only
    where every earlier one refuses, so dispatch is disjoint by
    construction and deterministic (it is a function). -/
def kapDecode : List Byte → Option (KapDekodiert × List Byte) :=
  fun bs =>
    match decodeMulDivWidth bs with
    | some (w, rest) => some (KapDekodiert.breit w, rest)
    | none =>
      match s32Decode bs with
      | some (d, rest) => some (KapDekodiert.s32 d, rest)
      | none =>
        match mxcsrDecode bs with
        | some (d, rest) => some (KapDekodiert.mxcsr d, rest)
        | none =>
          match decodeLock bs with
          | some (a, rest) => some (KapDekodiert.lock a, rest)
          | none =>
            match decodeLockAdr bs with
            | some (r, f, rest) => some (KapDekodiert.lockAdr r f, rest)
            | none =>
              match decodeC bs with
              | some (d, rest) => some (KapDekodiert.kompakt d, rest)
              | none =>
                match decodeCore bs with
                | some (d, rest) => some (KapDekodiert.kern d, rest)
                | none =>
                  match Avx2Join.dekodiereAvx2 bs with
                  | some z => some (KapDekodiert.avx2 z, [])
                  | none => none

end Gabbro.Grammatik.X86
