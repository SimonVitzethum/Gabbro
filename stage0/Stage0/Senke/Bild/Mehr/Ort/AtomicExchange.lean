module

public import Stage0.Senke.Sperre.Bindung.ImageCAS
public import Stage0.Senke.Welt.WordCell

@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Gabbro.Grammatik Gabbro.Stage0.Senke.Faeden
  Runner Runner.IR Runner.Mem Runner.Mach Runner.Beweis

/-- The linearization point of an emitted atomic exchange is its real
    shared CAS. Failure returns the current word without publication.
    Success stores the typed replacement, even in the presence of
    other threads' pending private stores. -/
theorem image_atomic_word_CAS [Kern] {D : Deklaration} {layout : Senke.Lay D}
    {machine : Cfg imageTSO (Res T)} {memory : imageTSO.St} {reply : Ans} {resume : Ans → Res T}
    {thread : Nat} {global : D.Glob} {world : World D}
    {expected replacement : W} {value : Wert D (D.gtyp global)} {footprint : Nat → W → Prop}
    (single : aggregateFits (D.gtyp global) = true)
    (represented : WeltAt (projectSCState footprint machine.ms).1 layout world)
    (geometry : LayIn layout) (separate : LayDis layout)
    (encoded : Enc layout (D.gtyp global) value replacement)
    (buffers : PrivateBuffers footprint machine.ms.1)
    (outside : ∀ byte, fenster (BitVec.ofNat 64 (layout.ga global)) byte → ∀ owner, ¬ footprint owner byte)
    (writable : Mem.all machine.ms.1.m.wr (BitVec.ofNat 64 (layout.ga global)) 8 = true)
    (waiting : machine.ths[thread]? = some (some (.ask (.cas (BitVec.ofNat 64 (layout.ga global))
      expected replacement) resume)))
    (answered : imageTSO.ans machine.ms thread
      (.cas (BitVec.ofNat 64 (layout.ga global)) expected replacement) reply memory) :
    ProcessStep imageTSO actI machine [] ⟨memory, machine.ths.set thread (some (resume reply))⟩ ∧
    PrivateBuffers footprint memory.1 ∧ machine.ms.1.buf thread = [] ∧
    ∃ observed, reply = some (observed, 0) ∧ Enc layout (D.gtyp global) (world.globs global) observed ∧
      (observed = expected →
        WeltAt (projectSCState footprint memory).1 layout (world.storeGlob global value)) ∧
      (observed ≠ expected → projectSCState footprint memory = projectSCState footprint machine.ms) := by
  let address := BitVec.ofNat 64 (layout.ga global)
  let before := projectSCState footprint machine.ms
  let after := projectSCState footprint memory
  obtain ⟨observed, read, view⟩ := ValueAt.cellWord (aggregateFits_compat single) (represented.2.1 global)
  have agreement : GleichAuf (fenster address) before.1 machine.ms.1.m :=
    fun byte hit => mergedView_committed_at machine.ms.1 footprint byte
      (fun ⟨owner, claimed⟩ => outside byte hit owner claimed)
  have committed : machine.ms.1.m.rd64 address = some observed :=
    (gleich_rd64 agreement).symm.trans read
  obtain ⟨step, returned, written⟩ := image_CAS_reply committed writable waiting answered
  have pending : memory.1.buf = machine.ms.1.buf := congrArg TSt.buf written
  have retained : PrivateBuffers footprint memory.1 := by
    intro owner store member byte hit
    rw [pending] at member
    exact buffers owner store member byte hit
  have projected := projectSCState_cas_shared answered.1 footprint outside
  have permission : Mem.all before.1.wr address 8 = true := (gleich_wr agreement).trans writable
  have actual := sc_memAns_cas projected
  change memAns before.1 (.cas address expected replacement) = some (reply, after.1) at actual
  have spec := cas_spec (e := expected) (n := replacement) read permission
  rw [memAns_cas, spec, returned] at actual
  have changed : after.1 =
      if observed = expected then Mem.write before.1 address 8 replacement.toNat else before.1 :=
    (congrArg Prod.snd (Option.some.inj actual)).symm
  refine ⟨step, retained, answered.1.1, observed, returned, view, ?_, ?_⟩
  · intro equal
    rw [if_pos equal] at changed
    change WeltAt after.1 layout (world.storeGlob global value)
    rw [changed]
    exact weltAt_globWord (aggregateFits_width single) represented geometry separate encoded
  · intro different
    rw [if_neg different] at changed
    exact Subtype.ext changed

end Gabbro.Stage0.Senke.BildMehr
