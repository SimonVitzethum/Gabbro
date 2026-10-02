/-
  File:      Grammatik/X86/AddressedHardwareExecution.lean
  Subject:   Full selected SIB/RIP-relative addresses bound to actual effects.

  Lane 730: a generic checked effective-address adapter over the accepted
  `AddressEncoding` selected forms (`AdrForm`, `adrEff`, `parseAdrTail`,
  `kanonisch48`, `fussZugelassen`). It binds the actual instruction
  length/next RIP and the canonical register values to real producer
  access effects (LOCK XADD through `LockedInstructionExecution`, address
  math through `EffectiveAddress`). No new memory micro-interpreter and
  no second decoder for accepted rows: pilot-owned tails stay refused by
  the reused `parseAdrTail`, proved in both directions below.
  Provenance: clone-local Intel SDM 325462-093US Sep 2026, Vol. 1
  Section 3.7.5 (specifying an offset), Section 3.7.5.1 (64-bit mode,
  RIP-relative addressing), LOCK prefix and XADD entries.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.AddressEncoding
import Grammatik.X86.EffectiveAddress
import Grammatik.X86.LockedOps
import Grammatik.X86.LockedInstructionExecution

namespace Gabbro.Grammatik.X86

/-- Ordered admission faults of one addressed access: canonical form
    first, no-wrap second, per-direction permission last. -/
inductive AdrFehler where
  | unkanonisch | umbruch | keinLesen | keinSchreiben
  deriving DecidableEq, Repr

end Gabbro.Grammatik.X86
