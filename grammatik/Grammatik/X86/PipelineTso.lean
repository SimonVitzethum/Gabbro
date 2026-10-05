/-
  File:      Grammatik/X86/PipelineTso.lean
  Subject:   Pipeline correctness over the multi-core TSO machine (lane 1169).
  Skeleton: single-core embedding of pipeline states into HwMaschine.
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.WordAccessGrouping
import Grammatik.X86.FenceDrain

namespace Gabbro.Grammatik.X86.PipelineTso

open Gabbro.Grammatik.X86

/-- Embed a pipeline state on core `c`: shared memory, core data, empty buffers. -/
def pipeHw (s : Zustand) (c : Nat) (hw : HwProfil) (ber : Nat → BereitProfil) : HwMaschine :=
  ⟨s.speicher, fun d =>
    if d = c then ⟨s.register, s.flags, s.rip, fun _ => BitVec.ofNat 128 0, kontextReset⟩
    else ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags, BitVec.ofNat 64 0,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩,
    fun _ => [], hw, ber⟩

/-- The embedding starts with empty buffers on every core. -/
theorem pipeHw_puffer_leer (s : Zustand) (c : Nat) (hw : HwProfil)
    (ber : Nat → BereitProfil) (d : Nat) :
    (pipeHw s c hw ber).puffer d = [] := rfl

/-- Empty buffers are foreign-free at every footprint. -/
theorem pipeHw_fremdFrei (s : Zustand) (c : Nat) (hw : HwProfil)
    (ber : Nat → BereitProfil) (a : Adresse) :
    FremdFrei (tsoAnsicht (pipeHw s c hw ber)) c a := by
  intro d hne e hmem
  have hbuf : (tsoAnsicht (pipeHw s c hw ber)).puffer d = [] := rfl
  rw [hbuf] at hmem
  cases hmem

/- CUTS:
  Skeleton only: embedding defined, empty-buffer foreign freedom proved.
  NOT proved yet: register-step embedding, forwarding transparency,
  drain-equals-write64, lock/tearing refusals, witness.
-/

#print axioms pipeHw_puffer_leer
#print axioms pipeHw_fremdFrei

end Gabbro.Grammatik.X86.PipelineTso
