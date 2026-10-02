/-
  File:      Grammatik/X86/HardwareExecution.lean
  Subject:   Coherent multicore architectural execution over the accepted
             byte-facing dispatcher and canonical TSO memory.

  Lane 660: ONE selected composition -- canonical per-core integer/FP
  data, ONE shared canonical memory, per-core TSO buffers and a checked
  core/control profile -- reusing `decodeExt`/`stepExt`/`extByteschritt`
  (ExtendedExecution575) and `issueByte`/`loadByte`/`flushKern`
  (TSO) with the `WortGruppe`/`FremdFrei` guard (WordAccessGrouping).
  No SC word effect is substituted for a buffered access; tearing and
  LOCK cases are explicitly refused (see CUTS).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.TSO
import Grammatik.X86.Gleitprofil
import Grammatik.X86.ScalarFloat
import Grammatik.X86.FeatureProfile
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.WordAccessGrouping
import Grammatik.X86.LockedOps

namespace Gabbro.Grammatik.X86

/-- Per-core data WITHOUT memory: integer file, flags, RIP, XMM file
    and FP context. Memory lives once in the machine below, so all
    core-memory projections agree by construction. -/
structure HwKern where
  register : Register → Wort
  flags : Flags
  rip : Adresse
  xmm : XmmDatei
  fp : FPKontext

/-- The coherent machine: one shared canonical memory, per-core data,
    per-core TSO buffers, one silicon profile and per-core readiness. -/
structure HwMaschine where
  mem : Speicher
  kerne : Nat → HwKern
  puffer : Nat → List TSOEintrag
  hw : HwProfil
  bereit : Nat → BereitProfil

/-! ## 1. Projections: one shared memory seen by every core.

  The TSO view, the canonical core view and the extended FP view all
  read the SAME `mem`. Coherence is therefore proved, never assumed. -/

/-- The shared TSO view: machine memory plus machine buffers. -/
def tsoAnsicht (m : HwMaschine) : TSOZustand :=
  ⟨m.mem, m.puffer⟩

/-- The canonical core view of core `c`: its data over shared memory. -/
def projZustand (m : HwMaschine) (c : Nat) : Zustand :=
  ⟨(m.kerne c).register, (m.kerne c).flags, (m.kerne c).rip, m.mem⟩

/-- The extended FP view of core `c`: canonical core plus XMM/FP data. -/
def projFp (m : HwMaschine) (c : Nat) : FpZustand :=
  ⟨projZustand m c, (m.kerne c).xmm, (m.kerne c).fp⟩

/-- All core-memory projections agree: every core sees `m.mem`. -/
theorem projZustand_speicher (m : HwMaschine) (c : Nat) :
    (projZustand m c).speicher = m.mem := rfl

/-- The extended view agrees on memory as well. -/
theorem projFp_speicher (m : HwMaschine) (c : Nat) :
    (projFp m c).kern.speicher = m.mem := rfl

/-- Two cores project to the same memory. -/
theorem kerne_ein_speicher (m : HwMaschine) (c d : Nat) :
    (projZustand m c).speicher = (projZustand m d).speicher := rfl

/-- The TSO view carries the machine memory. -/
theorem tsoAnsicht_speicher (m : HwMaschine) :
    (tsoAnsicht m).mem = m.mem := rfl

/-- The TSO view carries the machine buffers. -/
theorem tsoAnsicht_puffer (m : HwMaschine) (c : Nat) :
    (tsoAnsicht m).puffer c = m.puffer c := rfl

/- CUTS:
   Skeleton only: data vocabulary and projections so far.
   NOT proved: well-formedness, steps, embeddings, witnesses, adapters.
-/

#print axioms HwMaschine

end Gabbro.Grammatik.X86
