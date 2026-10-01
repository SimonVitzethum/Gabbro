/-
  File:      Grammatik/X86/TSO.lean
  Subject:   Executable byte-granularity x86-TSO over the canonical pilot memory.

  Lane 284 (wave A, Lean-first): per-core FIFO store buffers, store issue,
  youngest own-buffer forwarding on loads, globally scheduled oldest-entry
  flush onto the SAME canonical `Speicher` of `Grammatik.X86.Typen`, a local
  fence ready only when the own buffer is empty, and explicit
  permissions/failure. Flushes really write canonical bytes; nothing here is
  a stateless event toy. Aligned multi-byte single-copy atomicity and LOCK
  RMW are NOT claimed (refused/OPEN, see §7). Source W/GX stay the source
  concurrency model; §8 holds one proved target-side link to `Sicht`
  (`Lesbar`/`Frisch` instantiated at bytes) plus the precise OPEN
  cross-granularity obligation. No fairness, no OS, no whole-G-block claim.
-/
import Grammatik.X86.Speicher
import Grammatik.Speichermodell.Sicht

namespace Gabbro.Grammatik.X86

/-- One pending byte store: its address and its byte value. -/
structure TSOEintrag where
  addr : Adresse
  wert : Byte
  deriving DecidableEq, Repr

/-- TSO target state: canonical memory plus one FIFO buffer per core.
    Each core buffer is oldest-first: the head is the next to flush. -/
structure TSOZustand where
  mem : Speicher
  puffer : Nat → List TSOEintrag

end Gabbro.Grammatik.X86
