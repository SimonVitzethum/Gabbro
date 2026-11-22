module

public import Stage0.Senke.Bild.ImageGoal
public import Stage0.Senke.Bild.Mehr.ImageTransition
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz
  Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Stage0.Senke
  Gabbro.Stage0.Senke.BildMehr Runner Runner.IR

variable {src : String} {K : Nat} {options : Profil.Options}

/-- Every actual instruction byte address is below all stack and world
    addresses. In particular its 64-bit address is exact. -/
theorem Emitted.code_byte_before_stacks [Kern] (output : Emitted src K options) {index : Nat}
    (inCode : index < (output.image.code.flatMap encII).length) :
    (BitVec.ofNat 64 (codeBase + index)).toNat < output.image.fp0 := by
  have below : codeBase + index < output.image.fp0 := by
    rw [← output.code_end]
    omega
  obtain ⟨stackBound, limit⟩ := output.stackReservation_bounds
  have frameFits : output.image.fp0 < 2 ^ 64 := by omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (below.trans frameFits)]
  exact below

/-- Writes confined to the emitted stacks and the area following them
    leave every instruction byte and its permissions unchanged. -/
theorem Emitted.code_survives_writes [Kern] (output : Emitted src K options) {saved current : Runner.Mem}
    {footprint : W → Prop} (writes : NurIn footprint saved current)
    (afterCode : ∀ byte, footprint byte → output.image.fp0 ≤ byte.toNat)
    (code : BytesAt saved codeBase (output.image.code.flatMap encII)) :
    BytesAt current codeBase (output.image.code.flatMap encII) := by
  intro index inCode
  have outside : ¬ footprint (BitVec.ofNat 64 (codeBase + index)) :=
    fun written => (Nat.not_le_of_lt (output.code_byte_before_stacks inCode)) (afterCode _ written)
  rw [writes.rd, writes.wr, writes.b _ outside]
  exact code index inCode

/-- All changes within a single emitted stack frame leave the exact
    typed source world and its permissions intact. -/
theorem Emitted.world_survives_stack [Kern] (output : Emitted src K options)
    {saved current : Runner.Mem} {thread : Nat} (declared : thread ≤ output.starts.length)
    {world : World (declOf output.compiled.unit)}
    (stored : WeltAt saved output.image.Y world)
    (writes : Agree (BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * thread)))
      0 output.image.Ks saved current) :
    WeltAt current output.image.Y world := by
  obtain ⟨layoutBound, width⟩ := output.stackReservation_bounds
  have beforeWorld := (Nat.add_le_add_left
    (Nat.mul_le_mul_left 8 (Nat.mul_le_mul_left output.image.Ks (Nat.succ_le_succ declared)))
    output.image.fp0).trans layoutBound
  rw [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one, Nat.mul_add] at beforeWorld
  have tag : output.image.fp0 + 8 * (output.image.Ks * thread) < 2 ^ 64 := by omega
  have frameEnds : (BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * thread))).toNat +
      8 * output.image.Ks ≤ output.image.Y.lo := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt tag]
    omega
  exact weltAt_stab output.layout_checked.1 frameEnds _ _ stored writes

/-- Pending private stores are outside the emitted instruction extent,
    so an issuing thread fetches the same code as shared memory holds. -/
theorem Emitted.code_in_private_view [Kern] (output : Emitted src K options)
    (state : Runner.Beweis.TSt) (stores : PrivateBuffers (imageStackFootprint output) state)
    (thread : Nat) :
    BytesAt (state.view thread) codeBase (output.image.code.flatMap encII) ↔
      BytesAt state.m codeBase (output.image.code.flatMap encII) := by
  have agrees (index : Nat) (inCode : index < (output.image.code.flatMap encII).length) :
      GleichAt (state.view thread) state.m (BitVec.ofNat 64 (codeBase + index)) := by
    let address := BitVec.ofNat 64 (codeBase + index)
    have unchanged := Runner.Beweis.foldl_far (state.buf thread) state.m (y := address) (by
      intro store queued offset inside overlap
      have touched : fenster store.1 address := overlap.symm ▸ fenster_add _ inside
      have privateByte := (stores thread store queued address touched).1
      have above := (Nat.le_add_right _ _).trans privateByte.2.1
      exact (Nat.not_le_of_lt (output.code_byte_before_stacks inCode)) above)
    exact ⟨unchanged.1, unchanged.2, congrFun (Runner.Beweis.foldl_wr _ _) address⟩
  constructor
  · intro code index inCode
    obtain ⟨byte, read, write⟩ := agrees index inCode
    simpa only [byte, read, write] using code index inCode
  · intro code index inCode
    obtain ⟨byte, read, write⟩ := agrees index inCode
    rw [byte, read, write]
    exact code index inCode

/-- A host answer that keeps the emitted code in the issuer's TSO view
    also keeps it in shared memory. The actual syscall keeps the buffers. -/
theorem Emitted.code_after_host_answer [Kern] (output : Emitted src K options)
    {before after : imageTSO.St} {issuer : Nat} {req : Req} {answer : Ans}
    (stores : PrivateBuffers (imageStackFootprint output) before.1)
    (code : BytesAt before.1.m codeBase (output.image.code.flatMap encII))
    (step : imageTSO.ans before issuer (.sys req) answer after)
    (keeps : req ≠ cloneReq → Kern.ans req (before.1.view issuer) answer (after.1.view issuer) →
      BytesAt (before.1.view issuer) codeBase (output.image.code.flatMap encII) →
      BytesAt (after.1.view issuer) codeBase (output.image.code.flatMap encII)) :
    BytesAt after.1.m codeBase (output.image.code.flatMap encII) := by
  have host := step.2
  change (if req = cloneReq then after = before ∧ ∃ id extra, answer = some (id, extra) ∧ id ≠ 0
    else Kern.ans req (before.1.view issuer) answer (after.1.view issuer) ∧
      after.1.buf = before.1.buf) at host
  split at host
  · rw [host.1]
    exact code
  · rename_i ordinary
    have retained : PrivateBuffers (imageStackFootprint output) after.1 := by
      intro i store pending byte touched
      rw [host.2] at pending
      exact stores i store pending byte touched
    exact (output.code_in_private_view _ retained issuer).mp
      (keeps ordinary host.1 ((output.code_in_private_view _ stores issuer).mpr code))

/-- A real asynchronous flush writes only within its own emitted
    stack reservation and preserves the shared instruction bytes. -/
theorem Emitted.code_after_private_flush [Kern] (output : Emitted src K options)
    {state after : imageTSO.St} (stores : PrivateBuffers (imageStackFootprint output) state.1)
    (code : BytesAt state.1.m codeBase (output.image.code.flatMap encII))
    (flushed : imageTSO.tau state after) :
    BytesAt after.1.m codeBase (output.image.code.flatMap encII) := by
  obtain ⟨issuer, address, value, _, pending, updated⟩ := flushed
  have member : (address, value) ∈ state.1.buf issuer := by
    rw [pending]
    exact List.mem_cons_self
  rw [updated]
  apply output.code_survives_writes (write_nurIn state.1.m address value.toNat) _ code
  intro byte hit
  exact (Nat.le_add_right _ _).trans (stores issuer (address, value) member byte hit).1.2.1

/-- A running root stub decodes an actual emitted instruction within
    the startup header. This applies to the entry stub and all clone
    and child stubs at their relocated addresses. -/
theorem Emitted.root_instruction_decodes [Kern] (output : Emitted src K options)
    {memory : Runner.Mem} (loaded : BytesAt memory codeBase (output.image.code.flatMap encII))
    {thread : Nat} (declared : thread ≤ output.starts.length) {pointer : T}
    (instruction : ImageRootInstruction output thread pointer) :
    ∃ index, ∃ inside : index < output.image.code.length,
      pointer.pc = BitVec.ofNat 64 (codeBase + 16 * index) ∧
      InsAt memory pointer.pc output.image.code[index].o
        (II.f output.image.code[index].a) (II.f output.image.code[index].b) (II.f output.image.code[index].c) := by
  obtain ⟨_, index, _, rootBound, address⟩ := instruction
  obtain ⟨_, _, _, layout, serialized, _, _, _⟩ := bild_lage output.emission output.funktionen_voll
    (fun base bound => layU_in output.compiled.unit output.tor base bound)
    (fun base => layU_dis output.compiled.unit output.tor base)
    (fun base => by simp only [layU]; omega)
    (fun base => layU_sync output.compiled.unit output.tor base)
  have header : headLen output.starts.length ≤ output.image.code.length := by
    rw [serialized, List.length_append, layout.head, List.length_map]
    exact Nat.le_add_right _ _
  have inHeader : index < headLen output.starts.length := by
    unfold headLen
    by_cases entry : thread = 0
    · simp only [entry, ite_true, Nat.zero_add, startLen] at rootBound ⊢
      omega
    · simp only [entry, ite_false, startLen] at rootBound ⊢
      omega
  have inside := inHeader.trans_le header
  have decoded := codeAt_bytes _ codeBase loaded
  refine ⟨index, inside, address, ?_⟩
  rw [address, ← ofNat_add64]
  exact decoded index inside

/-- The full start stub for a declared root is at its exact relocated
    address in the production code. The root function is the same one
    whose arguments were selected from the typed start table. -/
theorem Emitted.root_stub_code [Kern] (output : Emitted src K options)
    {memory : Runner.Mem} (loaded : BytesAt memory codeBase (output.image.code.flatMap encII))
    {index : Nat} {root : Σ f : (declOf output.compiled.unit).Fn, Env _ ((declOf output.compiled.unit).params f)}
    (declared : output.starts[index]? = some root) :
    CodeAt memory (BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length + startLen + startLen * index)))
      (startC output.image.A root.1 output.image.depth 60 false) ∧
      2 < output.image.Ks ∧ output.image.depth + 1 < 2 ^ 31 ∧
      startScratch root.1 + 8 ≤ output.image.Ks ∧ output.image.Ks < 2 ^ 31 := by
  obtain ⟨functions, body, sites, layout, serialized, _, _, _⟩ := bild_lage output.emission output.funktionen_voll
    (fun base bound => layU_in output.compiled.unit output.tor base bound)
    (fun base => layU_dis output.compiled.unit output.tor base)
    (fun base => by simp only [layU]; omega)
    (fun base => layU_sync output.compiled.unit output.tor base)
  obtain ⟨inside, exactRoot⟩ := List.getElem?_eq_some_iff.mp declared
  let roots := output.starts.map (·.1)
  have listed : index < roots.length := by simpa only [roots, List.length_map] using inside
  have selected : roots[index] = root.1 := by
    change (output.starts.map (·.1))[index] = root.1
    rw [List.getElem_map, exactRoot]
  have allCode := codeAt_bytes _ codeBase (serialized ▸ loaded)
  have header := codeAt_left (b := body) allCode
  have spawns : (spawnC (startScratch output.compiled.main) sites).length = 10 * output.starts.length := by
    simp only [spawnC_len, layout.hsp, List.length_map, List.length_range, Emitted.starts]
  have rootCode := codeAt_right
    (a := spawnC (startScratch output.compiled.main) sites ++
      startC output.image.A output.compiled.main output.image.depth 231 true) header
  rw [ofNat_add64, List.length_append, spawns, startC_len] at rootCode
  have code := rootsC_at output.image.A output.image.depth roots _ index listed rootCode
  obtain ⟨headerFits, depthFits, slotsFit⟩ := layout.startLimits
  refine ⟨?_, headerFits, depthFits, ?_, slotsFit⟩
  · simpa only [selected, Nat.mul_add, Nat.add_assoc] using code
  · exact layout.hex root.1 (List.mem_cons_of_mem _ (List.mem_map.mpr
      ⟨root, List.mem_of_getElem? declared, rfl⟩))

/-- The first instruction of any emitted start writes its depth word
    to slot 2 in the issuing view and advances its program counter. -/
theorem image_depth_setup [Kern] {D : Deklaration}
    {before : Runner.Mach.Cfg imageTSO (Runner.Res T)} {thread slots depth exit : Nat} {pointer : T}
    {addresses : D.Fn → Nat} {fn : D.Fn} {keep : Bool}
    (stub : CodeAt (before.ms.1.view thread) pointer.pc (startC addresses fn depth exit keep))
    (enough : 2 < slots) (depthFits : depth + 1 < 2 ^ 31)
    (running : before.ths[thread]? = some (some (.next pointer)))
    (frame : FrameOK (before.ms.1.view thread) pointer.fp slots) :
    ∃ after : imageTSO.St,
      Runner.Mach.ProcessPrefix imageTSO Runner.Beweis.actI before [] 5
        ⟨after, before.ths.set thread (some (.next (nxt pointer)))⟩ ∧
      after.1.m = before.ms.1.m ∧
      after.1.view thread = Runner.Mem.write (before.ms.1.view thread)
        (slot pointer.fp (BitVec.ofNat 64 2)) 8 (depth + 1) ∧
      (∀ other, other ≠ thread → after.1.view other = before.ms.1.view other) ∧
      QueuedStores before.ms.1 after.1 thread
        [(slot pointer.fp (BitVec.ofNat 64 2), BitVec.ofNat 64 (depth + 1))] := by
  have first := stub 0 (by rw [startC_len]; decide)
  have instruction : InsAt (before.ms.1.view thread) pointer.pc 1
      (II.f 2) (II.f ((depth + 1 : Nat) : Int)) (II.f 0) := by
    simpa only [startC, List.singleton_append, List.cons_append, List.getElem_cons_zero,
      Nat.mul_zero, BitVec.add_zero, ci] using first
  have slotNumber : sx (II.f 2) = BitVec.ofNat 64 2 := by decide
  have depthWord : sx (II.f ((depth + 1 : Nat) : Int)) =
      BitVec.ofNat 64 (depth + 1) := sx_nat depthFits
  have writable : Runner.Mem.all before.ms.1.m.wr (slot pointer.fp (sx (II.f 2))) 8 = true := by
    rw [slotNumber, ← Runner.Beweis.foldl_wr (before.ms.1.buf thread) before.ms.1.m]
    exact frame.wr 2 enough
  obtain ⟨after, run, memory, view, others, queued⟩ :=
    tso_const_prefix (before := imageToTSO before) running instruction writable
  refine ⟨after, tso_silent_prefix_image run rfl, memory, ?_, others, ?_⟩
  swap
  · rw [slotNumber, depthWord] at queued
    exact queued
  rw [view, slotNumber, depthWord, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (depthFits.trans (by decide : 2 ^ 31 < 2 ^ 64))] <;> rfl

/-- The first instruction of a declared child initializes only that
    child's private depth slot. -/
theorem Emitted.root_depth_start [Kern] (output : Emitted src K options)
    {before : Runner.Mach.Cfg imageTSO (Runner.Res T)} {index : Nat}
    {root : Σ f : (declOf output.compiled.unit).Fn, Env _ ((declOf output.compiled.unit).params f)}
    (declared : output.starts[index]? = some root)
    (loaded : BytesAt (before.ms.1.view (index + 1)) codeBase (output.image.code.flatMap encII)) :
    let pointer : T := ⟨BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length + startLen + startLen * index)),
      BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * (index + 1)))⟩
    before.ths[index + 1]? = some (some (.next pointer)) →
    FrameOK (before.ms.1.view (index + 1)) pointer.fp output.image.Ks →
    ∃ after : imageTSO.St,
      Runner.Mach.ProcessPrefix imageTSO Runner.Beweis.actI before [] 5
        ⟨after, before.ths.set (index + 1) (some (.next (nxt pointer)))⟩ ∧
      after.1.m = before.ms.1.m ∧
      after.1.view (index + 1) = Runner.Mem.write (before.ms.1.view (index + 1))
        (slot pointer.fp (BitVec.ofNat 64 2)) 8 (output.image.depth + 1) ∧
      ∀ other, other ≠ index + 1 → after.1.view other = before.ms.1.view other := by
  intro pointer running frame
  obtain ⟨stub, enough, depthFits, _, _⟩ := output.root_stub_code loaded declared
  obtain ⟨after, run, shared, wrote, others, _⟩ :=
    image_depth_setup (before := before) stub enough depthFits running frame
  exact ⟨after, run, shared, wrote, others⟩

/-- Past the loader, the root phase carries the exact arguments serialized
    for the selected declaration, with its private stack permissions. -/
theorem ImageRootPhase.payload [Kern] {output : Emitted src K options}
    {E : Einheit (declOf output.compiled.unit)} {memory : Mem} {thread : Nat}
    {root : Σ f : (declOf output.compiled.unit).Fn, Env _ ((declOf output.compiled.unit).params f)}
    (declared : E.starts[thread]? = some root)
    {history : List Runner.Mach.Ev} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {control : Res T} (phase : ImageRootPhase output E history memory thread control state)
    (pastLoader : thread ≠ 0 ∨ control ≠ Runner.Beweis.t4) :
    let fp := BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * thread))
    BytesAt memory codeBase (output.image.code.flatMap encII) ∧
      FrameOK memory fp output.image.Ks ∧
      WordsAt memory fp (FB + FB) (encodeEnv output.image.Y root.2) := by
  intro fp
  obtain ⟨firstThread, loader, _⟩ | ⟨start, chosen, _, code, frame, args, _⟩ := phase
  · exact (pastLoader.elim (· firstThread) (· loader)).elim
  have same := Option.some.inj (chosen.symm.trans declared)
  subst start
  refine ⟨code, frame, ?_⟩
  intro i present
  have address : slot fp (BitVec.ofNat 64 (FB + FB + i)) =
      BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * thread) + 8 * (FB + FB + i)) := by
    change BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * thread)) +
      BitVec.ofNat 64 (FB + FB + i) * BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm (FB + FB + i) 8]
  rw [address]
  exact args i present

/-- The root phase exposes a child's arguments in declared start order. -/
theorem Emitted.child_phase_payload [Kern] (output : Emitted src K options)
    {E : Einheit (declOf output.compiled.unit)} (unit : ImageModelUnit output E)
    {memory : Mem} {index : Nat}
    {root : Σ f : (declOf output.compiled.unit).Fn, Env _ ((declOf output.compiled.unit).params f)}
    (declared : output.starts[index]? = some root)
    {history : List Runner.Mach.Ev} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {control : Res T} (phase : ImageRootPhase output E history memory (index + 1) control state) :
    let fp := BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * (index + 1)))
    BytesAt memory codeBase (output.image.code.flatMap encII) ∧
      FrameOK memory fp output.image.Ks ∧
      WordsAt memory fp (FB + FB) (encodeEnv output.image.Y root.2) := by
  have exported : E.starts[index + 1]? = some root := by rw [unit.starts]; exact declared
  exact ImageRootPhase.payload exported phase (.inl (Nat.succ_ne_zero _))

end Gabbro.Stage0
