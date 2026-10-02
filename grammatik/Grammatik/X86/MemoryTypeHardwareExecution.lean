/-
  File:      Grammatik/X86/MemoryTypeHardwareExecution.lean
  Subject:   UC MMIO architectural access and ordering over the canonical
             byte/register/memory state.

  Lane 694 (hardware completion): normal WB RAM follows TSO; selected UC
  device addresses follow exact documented architecture constraints with
  one generic named hardware device-response interface. OS/page-table/
  memory-type configuration is software user logic establishing explicit
  profile facts, never a trusted Bool.

  Provenance (official Intel SDM 325462-093US, September 2026, local
  `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`):
  - Vol.1 Section 20.5 (memory-mapped I/O ordering): UC region reads and
    writes appear in order on the pins; MTRRs make the MMIO space UC;
    chipsets may post UC writes (CPU-retired is not device-completed).
  - Vol.3A Section 14.3 Table 14-2 (Strong Uncacheable UC): reads/writes
    appear on the bus in program order without reordering, no speculative
    access; x87/SIMD UC re-access NOTE (only GP-register forms admitted).
  - Vol.3A Section 14.3.3 (UC code fetch limits; code stays WB here).
  - Vol.3A Sections 11.1.2/11.2.5 (UC lock serialization, I/O and locked
    instruction drain of buffered writes; no universal fence claimed).
  AMD retrieval failed; no AMD provenance or silicon proof is claimed.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Regionen
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Byteschritt
import Grammatik.X86.Codec
import Grammatik.X86.TSO
import Grammatik.X86.FeatureProfile
import Grammatik.X86.NarrowOps
import Grammatik.X86.NarrowCodec
import Grammatik.X86.ScalarFloat
import Grammatik.X86.ExtendedExecution

namespace Gabbro.Grammatik.X86

/-- UC MMIO window profile: the explicit list of UC regions established by
    software (MTRR/PAT/page tables are user logic). An address is UC only
    by membership here; WB is the default elsewhere. -/
abbrev UcProfil := List Region

end Gabbro.Grammatik.X86
