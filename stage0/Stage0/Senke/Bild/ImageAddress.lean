module

public import Stage0.Senke.Bild.ImageGoal
public import Grammatik.Speichermodell.Adressen.Bereich
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
  have decoded := codeAt_bytes _ codeBase (serialized.symm ▸ layout.hops) loaded
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
      2 < output.image.Ks ∧ output.image.depth + 1 < 2 ^ 31 := by
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
  have allCode := codeAt_bytes _ codeBase layout.hops (serialized ▸ loaded)
  have header := codeAt_left (b := body) allCode
  have spawns : (spawnC (startScratch output.compiled.main) sites).length = 10 * output.starts.length := by
    simp only [spawnC_len, layout.hsp, List.length_map, List.length_range, Emitted.starts]
  have rootCode := codeAt_right
    (a := spawnC (startScratch output.compiled.main) sites ++
      startC output.image.A output.compiled.main output.image.depth 231 true) header
  rw [ofNat_add64, List.length_append, spawns, startC_len] at rootCode
  have code := rootsC_at output.image.A output.image.depth roots _ index listed rootCode
  refine ⟨?_, ?_, ?_⟩
  · simpa only [selected, Nat.mul_add, Nat.add_assoc] using code
  · have room := layout.hroom
    simp only [FB] at room
    omega
  · have depthBound : output.image.depth + 1 ≤ output.image.Ks := by
      rw [layout.hdepth]
      have quotient := Nat.div_le_self (output.image.Ks - FB) (maxTop functions)
      have room := layout.hroom
      simp only [depthOf, FB] at quotient room ⊢
      omega
    have allocation := layout.hylo
    have order := layout.hyord
    have last := layout.hyhi
    have limit := layout.hfit
    have reserved := Nat.le_mul_of_pos_right output.image.Ks
      (Nat.succ_pos ((output.starts.map (·.1)).length))
    simp only [List.length_map, Emitted.starts, Nat.succ_eq_add_one] at allocation reserved
    omega

/-- The first instruction of a declared child actually writes the image's
    depth word to its own slot 2, advances its PC and preserves all other
    thread views. The shared memory has not flushed that store. -/
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
  obtain ⟨stub, enough, depthFits⟩ := output.root_stub_code loaded declared
  have first := stub 0 (by rw [startC_len]; decide)
  have instruction : InsAt (before.ms.1.view (index + 1)) pointer.pc 1
      (II.f 2) (II.f ((output.image.depth + 1 : Nat) : Int)) (II.f 0) := by
    simpa only [startC, List.singleton_append, List.cons_append, List.getElem_cons_zero,
      Nat.mul_zero, BitVec.add_zero, ci, pointer] using first
  have slotNumber : sx (II.f 2) = BitVec.ofNat 64 2 := by decide
  have depthWord : sx (II.f ((output.image.depth + 1 : Nat) : Int)) =
      BitVec.ofNat 64 (output.image.depth + 1) := sx_nat depthFits
  have writable : Runner.Mem.all before.ms.1.m.wr (slot pointer.fp (sx (II.f 2))) 8 = true := by
    rw [slotNumber, ← Runner.Beweis.foldl_wr (before.ms.1.buf (index + 1)) before.ms.1.m]
    exact frame.wr 2 enough
  obtain ⟨after, run, memory, view, others⟩ :=
    tso_const_prefix (before := imageToTSO before) running instruction writable
  refine ⟨after, tso_silent_prefix_image run rfl, memory, ?_, others⟩
  rw [view, slotNumber, depthWord, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (depthFits.trans (by decide : 2 ^ 31 < 2 ^ 64))] <;> rfl

/-- The first child instruction leaves its exact arguments, frame
    permissions and code intact. The issuing view holds the depth word
    before the store is flushed to shared memory. -/
theorem Emitted.root_depth_preserves_frame [Kern] (output : Emitted src K options)
    {before : Runner.Mach.Cfg imageTSO (Runner.Res T)} {index : Nat}
    {root : Σ f : (declOf output.compiled.unit).Fn, Env _ ((declOf output.compiled.unit).params f)}
    (declared : output.starts[index]? = some root)
    (loaded : BytesAt (before.ms.1.view (index + 1)) codeBase (output.image.code.flatMap encII)) :
    let pointer : T := ⟨BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length + startLen + startLen * index)),
      BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * (index + 1)))⟩
    let words := encodeEnv output.image.Y root.2
    before.ths[index + 1]? = some (some (.next pointer)) →
    FrameOK (before.ms.1.view (index + 1)) pointer.fp output.image.Ks →
    FB + FB + words.length ≤ output.image.Ks →
    WordsAt (before.ms.1.view (index + 1)) pointer.fp (FB + FB) words →
    ∃ after : imageTSO.St,
      Runner.Mach.ProcessPrefix imageTSO Runner.Beweis.actI before [] 5
        ⟨after, before.ths.set (index + 1) (some (.next (nxt pointer)))⟩ ∧
      after.1.m = before.ms.1.m ∧
      (∀ other, other ≠ index + 1 → after.1.view other = before.ms.1.view other) ∧
      BytesAt (after.1.view (index + 1)) codeBase (output.image.code.flatMap encII) ∧
      FrameOK (after.1.view (index + 1)) pointer.fp output.image.Ks ∧
      WordsAt (after.1.view (index + 1)) pointer.fp (FB + FB) words ∧
      (after.1.view (index + 1)).rd64 (slot pointer.fp (BitVec.ofNat 64 2)) =
        some (BitVec.ofNat 64 (output.image.depth + 1)) := by
  intro pointer words running frame fits args
  obtain ⟨after, run, memory, wroteDepth, others⟩ := output.root_depth_start declared loaded running frame
  obtain ⟨_, depthSlot, depthFits⟩ := output.root_stub_code loaded declared
  have thread : index + 1 ≤ output.starts.length :=
    Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp declared).1
  refine ⟨after, run, memory, others, ?_, ?_, ?_, ?_⟩ <;> rw [wroteDepth]
  · apply output.code_survives_writes (write_nurIn _ _ _) _ loaded
    intro byte touched
    have own := imageStackFootprint_slot (output := output) (i := index + 1)
      (index := 2) thread depthSlot touched
    exact (Nat.le_add_right _ _).trans own.2.1
  · exact ⟨frame.lt, frame.rd, frame.wr⟩
  · intro i present
    have within : FB + FB + i < output.image.Ks := by omega
    have elsewhere : 2 ≠ FB + FB + i := by simp only [FB]; omega
    rw [Mem.rd64_write_far (slot_far frame.room depthSlot within elsewhere)]
    exact args i present
  · have word := rd64_write_same (w := BitVec.ofNat 64 (output.image.depth + 1)) (frame.rd 2 depthSlot)
    simpa only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (depthFits.trans (by decide : 2 ^ 31 < 2 ^ 64))] using word

/-- The concrete child startup prefix advances the IR counter within
    the child's stub and retains the same dormant GX head. -/
theorem Emitted.root_depth_phase [Kern] (output : Emitted src K options)
    {E : Einheit (declOf output.compiled.unit)} (unit : ImageModelUnit output E)
    {before : Runner.Mach.Cfg imageTSO (Runner.Res T)} {index : Nat}
    {root : Σ f : (declOf output.compiled.unit).Fn, Env _ ((declOf output.compiled.unit).params f)}
    (declared : output.starts[index]? = some root)
    {history : List Runner.Mach.Ev} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (head : state.m.faeden (index + 1) = (imageSourceStart E).m.faeden (index + 1)) :
    let pointer : T := ⟨BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length + startLen + startLen * index)),
      BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * (index + 1)))⟩
    let view := before.ms.1.view (index + 1)
    before.ths[index + 1]? = some (some (.next pointer)) →
    ImageRootPhase output E history view (index + 1) (.next pointer) state →
    FB + FB + (encodeEnv output.image.Y root.2).length ≤ output.image.Ks →
    ∃ after : imageTSO.St,
      Runner.Mach.ProcessPrefix imageTSO Runner.Beweis.actI before [] 5
        ⟨after, before.ths.set (index + 1) (some (.next (nxt pointer)))⟩ ∧
      ImageRootPhase output E history (after.1.view (index + 1)) (index + 1) (.next (nxt pointer)) state ∧
      after.1.m = before.ms.1.m ∧
      (∀ other, other ≠ index + 1 → after.1.view other = before.ms.1.view other) ∧
      (after.1.view (index + 1)).rd64 (slot pointer.fp (BitVec.ofNat 64 2)) =
        some (BitVec.ofNat 64 (output.image.depth + 1)) := by
  intro pointer view running phase fits
  have exported : E.starts[index + 1]? = some root := by rw [unit.starts]; exact declared
  obtain ⟨firstThread, _⟩ | ⟨start, chosen, _, code, frame, args, _⟩ := phase
  · exact (Nat.succ_ne_zero _ firstThread).elim
  have same := Option.some.inj (chosen.symm.trans exported)
  subst start
  have address (i : Nat) : slot pointer.fp (BitVec.ofNat 64 (FB + FB + i)) =
      BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * (index + 1)) + 8 * (FB + FB + i)) := by
    change BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * (index + 1))) +
      BitVec.ofNat 64 (FB + FB + i) * BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm (FB + FB + i) 8]
  have arguments : WordsAt view pointer.fp (FB + FB) (encodeEnv output.image.Y root.2) := by
    intro i present
    rw [address]
    exact args i present
  obtain ⟨after, run, shared, others, loaded, permissions, words, depth⟩ :=
    output.root_depth_preserves_frame declared code running frame fits arguments
  refine ⟨after, run, Or.inr ⟨root, exported, Or.inl head, loaded, permissions, ?_, ?_⟩, shared, others, depth⟩
  · intro i present
    simpa only [address] using words i present
  · refine ⟨nxt pointer, ⟨rfl, 10 * output.starts.length + startLen + startLen * index + 1, ?_, ?_, ?_⟩, Or.inl rfl⟩
    · simp only [Nat.succ_ne_zero, ite_false, startLen]; omega
    · simp only [Nat.succ_ne_zero, ite_false, startLen]; omega
    · change BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length + startLen + startLen * index)) +
          BitVec.ofNat 64 16 = _
      rw [← BitVec.ofNat_add]
      congr 1
      omega

/-- The concrete builder bounds every typed cell and separates its bytes
    from other cells. This is a property of the relocated image's layout. -/
theorem Emitted.layout_checked (output : Emitted src K options) :
    LayIn output.image.Y ∧ LayDis output.image.Y ∧ LaySync output.image.Y := by
  obtain ⟨_, _, _, layout, _⟩ :=
    bild_lage output.emission output.funktionen_voll
      (fun base bound => layU_in output.compiled.unit output.tor base bound)
      (fun base => layU_dis output.compiled.unit output.tor base)
      (fun base => by simp only [layU]; omega)
      (fun base => layU_sync output.compiled.unit output.tor base)
  exact ⟨layout.hlay, layout.hdis, layout.hsync⟩

/-- Physical base of the table's complete, consecutive columns. -/
def InitialLayout.tableBase {u : UProg} (L : Lay (declOf u)) (t : (declOf u).Tab) : Nat :=
  L.lo + globEnd (List.finRange u.globs.length) 0 (globSz u) (fun g => wordAlign (globAlign u g)) +
    (((List.finRange u.tabs.length).map (tabSz u)).take t.val).sum

/-- Every byte of a represented cell is in its actual table, accounting
    for the field's own stride and for all preceding columns. -/
theorem InitialLayout.cell_in_table {u : UProg} {L : Lay (declOf u)} (layout : InitialLayout u L)
    (t : (declOf u).Tab) (f : (declOf u).Feld t) (index : Nat)
    (bounded : (index : Int) < L.count t) :
    InitialLayout.tableBase L t ≤ L.elem t f index ∧
      L.elem t f index + 8 * valueWords ((declOf u).typ t f) ≤ InitialLayout.tableBase L t + tabSz u t := by
  have own := colSz_ge u t f index ((layout.count t) ▸ bounded)
  have column := take_sum_add ((List.finRange (fieldCount u t)).map (colSz u t)) f.val
    (by simpa only [List.length_map, List.length_finRange] using f.isLt)
  simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk] at column
  change (((List.finRange (fieldCount u t)).map (colSz u t)).take f.val).sum +
    colSz u t f ≤ tabSz u t at column
  rw [Lay.elem, layout.columns]
  unfold InitialLayout.tableBase
  omega

/-- The extent leg on the actual column layout. On a closed table,
    reachability supplies the physical index bound on its own. -/
theorem Emitted.changedCell_in_image (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit)) (O : Orakel (declOf output.compiled.unit))
    (foreignConfined : ImBereichO O.mitRuhe)
    {live : Faden → Bool} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (reached : FadenErreichbarX (output.goalUnit Q).P.mitRuhe O.mitRuhe output.image.passes
      (GeteiltV (D := declOf output.compiled.unit) (output.goalUnit Q).P (output.goalUnit Q).ws)
      (output.goalStart Q live) state)
    (t : (declOf output.compiled.unit).Tab) (k : Int) (f : (declOf output.compiled.unit).Feld t)
    (changed : state.m.speicher.slots t k f ≠ (speicherR (output.goalUnit Q).sp0).slots t k f) :
    ImBereich (declOf output.compiled.unit) t k ∧
      (k < (declOf output.compiled.unit).count t →
        ∀ address, output.image.Y.elem t f k.toNat ≤ address →
          address < output.image.Y.elem t f k.toNat + 8 * valueWords ((declOf output.compiled.unit).typ t f) →
          InitialLayout.tableBase output.image.Y t ≤ address ∧
            address < InitialLayout.tableBase output.image.Y t + tabSz output.compiled.unit t) := by
  have outside := rufErreichbarGX_aussen (fun _ shared => by
    obtain ⟨_, impossible, _⟩ := shared.1.1
    cases impossible) foreignConfined (fadenErreichbarX_GX reached)
  have inExtent : ImBereich (declOf output.compiled.unit) t k :=
    Classical.byContradiction fun notIn => changed (outside t k f notIn)
  refine ⟨inExtent, ?_⟩
  intro bounded address lower upper
  have layout := initialLayout_bild output.emission
  have actual : (k.toNat : Int) < output.image.Y.count t := by
    rw [layout.count]
    have nonnegative := inExtent.1
    omega
  obtain ⟨base, last⟩ := InitialLayout.cell_in_table layout t f k.toNat actual
  exact ⟨Nat.le_trans base lower, Nat.lt_of_lt_of_le upper last⟩

/-- The row layout cannot name the exact column addresses and sizes for
    two fields at two indices. The contradiction is in the row stride,
    independently of relocation or of the particular table values. -/
theorem column_addresses_exclude_row_layout {D : Deklaration} (L : Lay D)
    (row : AdressLayout D) (valid : LayoutOk row)
    (t : D.Tab) (f other : D.Feld t) (distinct : f ≠ other)
    (first : row.adresse t 0 f = L.elem t f 0)
    (second : row.adresse t 1 f = L.elem t f 1)
    (size : row.groesse t f = 8 * valueWords (D.typ t f))
    (otherNonempty : 0 < row.groesse t other) : False := by
  have stride : row.breite t = row.groesse t f := by
    simp [AdressLayout.adresse, Lay.elem] at first second
    omega
  have room := valid.feld t f
  have otherRoom := valid.feld t other
  rcases valid.felder t f other distinct with left | right <;> omega

end Gabbro.Stage0
