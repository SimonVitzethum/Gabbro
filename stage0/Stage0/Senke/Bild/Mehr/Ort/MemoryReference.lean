module

public import Stage0.Senke.Bild.Mehr.Ort.SilentControl
import Stage0.Senke.Stopp

@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Runner Runner.IR Runner.Beweis Runner.Mach BildLauf

/-- Normalize the auxiliary response word once for any generated
    read whose requested bytes agree with the proof memory. -/
theorem tso_read_matches {layout : Runner.Beweis.Lay}
    {before after : (TSO layout).St} {thread width : Nat} {address : W}
    {resume : Ans → Res T} {answer : Ans} {localMemory : Mem}
    (tree : Blind (.ask (.rd width address) resume))
    (agrees : GleichAuf (byteWindow (readWidth width) address) (before.1.view thread) localMemory)
    (answered : (TSO layout).ans before thread (.rd width address) answer after) :
    after = before ∧ ∃ normalized,
      memAns localMemory (.rd width address) = some (normalized, localMemory) ∧
      resume answer = resume normalized := by
  obtain ⟨unchanged, extra, response⟩ := answered
  obtain ⟨valid, ignores⟩ := tree.lesen rfl
  refine ⟨unchanged, (rdN localMemory width address).map (·, 0), ?_, ?_⟩
  · rcases valid with rfl | rfl | rfl <;>
      simp only [memAns_rd, rdAntwort, rdN, Option.map_map, Function.comp_def]
  · rw [response, rdN_agrees width agrees]
    cases rdN localMemory width address with
    | none => rfl
    | some word => exact ignores word extra

private theorem memAns_preserves_agreement {region : W → Prop} {before after localMemory : Mem}
    {request : Op} {answer : Ans} (kept : GleichAuf region before localMemory)
    (within : ∀ byte, fussOp request byte → region byte)
    (answered : memAns before request = some (answer, after)) :
    ∃ updated, memAns localMemory request = some (answer, updated) ∧ GleichAuf region after updated := by
  obtain ⟨updated, matched, touched⟩ := memAns_gleich (fun byte hit => kept byte (within byte hit)) answered
  refine ⟨updated, matched, ?_⟩
  intro byte present
  by_cases hit : fussOp request byte
  · exact touched byte hit
  · exact ((memAns_nurIn answered).gleichAt hit).trans
      ((kept byte present).trans ((memAns_nurIn matched).gleichAt hit).symm)

/-- The actual TSO answer advances a solo proof of a scoped IR region.
    The proof memory agrees with exactly the requested byte region,
    even when the issuing view contains unrelated concurrent effects. -/
theorem SoloLauf.answer_tso [Kern] {layout : Runner.Beweis.Lay} {before after : (TSO layout).St}
    {thread : Nat} {region : W → Prop} {start : T} {initial localMemory : Mem}
    {request : Op} {resume : Ans → Res T} {answer : Ans}
    (run : SoloLauf start initial (.ask request resume) localMemory)
    (agrees : GleichAuf region (before.1.view thread) localMemory)
    (within : ∀ byte, fussOp request byte → region byte)
    (memory : istSpeicherOp request = true)
    (answered : (TSO layout).ans before thread request answer after) :
    ∃ updated, SoloLauf start initial (resume answer) updated ∧
      GleichAuf region (after.1.view thread) updated := by
  have finish {actual reply : Ans} {changed : Mem}
      (continued : resume actual = resume reply)
      (answerLocal : memAns localMemory request = some (reply, changed))
      (views : GleichAuf region (after.1.view thread) changed) :
      ∃ updated, SoloLauf start initial (resume actual) updated ∧
        GleichAuf region (after.1.view thread) updated :=
    ⟨changed, continued.symm ▸ run.ask answerLocal, views⟩
  cases request with
  | rd width address =>
    have tree : Blind (.ask (.rd width address) resume) := by
      obtain ⟨_, _, _, _, finished | pending⟩ := run
      · cases finished.1
      · exact pending.blind (blind_step _)
    obtain ⟨rfl, _, read, continued⟩ := tso_read_matches tree (fun byte touched => agrees byte (within byte touched)) answered
    exact finish continued read agrees
  | wr address value =>
    have physical : memAns (before.1.view thread) (.wr address value) = some (answer, after.1.view thread) := by
      have viewPermissions : (before.1.view thread).wr = before.1.m.wr := foldl_wr _ _
      rcases answered with ⟨denied, rfl, rfl⟩ | ⟨allowed, rfl, enqueued⟩
      · rw [memAns_wr, wr64_eq, viewPermissions, ite_eq_right (Bool.eq_false_iff.mp denied)]
      · have update := (tso_store_updates_view (layout := layout) (answer := some (0, 0))
          (.inr ⟨allowed, rfl, enqueued⟩)).resolve_left (fun refused => by cases refused.1)
        rw [memAns_wr, wr64_eq, viewPermissions, ite_eq_left allowed, update.2.1]
    obtain ⟨_, result, retained⟩ := memAns_preserves_agreement agrees within physical
    exact finish rfl result retained
  | cas address expected value =>
    obtain ⟨_, result, retained⟩ :=
      memAns_preserves_agreement agrees within (tso_cas_updates_view answered).2
    exact finish rfl result retained
  | sys | fp => cases memory

theorem frame_slot_byte {memory : Mem} {fp : W} {K index offset : Nat}
    (frame : FrameOK memory fp K) (slotFits : index < K) (inWord : offset < 8) :
    inSlots fp 0 K (slot fp (BitVec.ofNat 64 index) + BitVec.ofNat 64 offset) := by
  have address := slot_toNat frame.room slotFits
  simp only [inSlots, Nat.mul_zero, Nat.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat, address]
  rw [Nat.mod_eq_of_lt (a := offset) (by omega), Nat.mod_eq_of_lt (by have := frame.lt; omega)]
  omega

/-- All solo prefixes of a region are either still inside its request
    scope or pass through its proved instruction boundary. The suffix
    continues from the exact memory delivered by that boundary. -/
theorem SoloLauf.split_after [Kern] {count : Nat} {start finish : T}
    {before current : Mem} {control : Res T} {valid : Mem → Prop} {allowed : Res T → Prop}
    (atPointer : ∀ pointer, allowed (.next pointer))
    (complete : ∀ {pointer memory}, StarM count start before pointer memory →
      pointer = finish ∧ valid memory)
    (partialRun : ∀ {used pointer memory residual after}, StarM used start before pointer memory →
      used < count → RunP (step pointer) memory residual after → allowed residual)
    (path : SoloLauf start before control current) :
    allowed control ∨ ∃ boundary, StarM count start before finish boundary ∧
      SoloLauf finish boundary control current ∧ valid boundary := by
  obtain ⟨used, pointer, memory, advanced, pending⟩ := path
  rcases Nat.lt_or_ge used count with within | completeCount
  · rcases pending with ⟨rfl, _⟩ | tail
    · exact .inl (atPointer _)
    · exact .inl (partialRun advanced within tail)
  · obtain ⟨boundary, atBoundary, first, tail⟩ := StarM.cut advanced count completeCount
    obtain ⟨rfl, validAtBoundary⟩ := complete first
    exact .inr ⟨atBoundary, first, ⟨used - count, pointer, memory, tail, pending⟩, validAtBoundary⟩

/-- A restricted reference yields the same boundary for every actual
    solo execution, irrespective of the values outside its footprint. -/
theorem _root_.Gabbro.Stage0.Senke.BildLauf.IRReference.split_scoped [kernel : Kern]
    {count : Nat} {start finish : T} {reference target before : Mem} {reads writes : W → Prop}
    (code : @IRReference kernel.withoutSyscalls count start reference finish target)
    (agreement : MaskedAgreement reads writes reference before)
    (readable : ∀ byte, reference.rd byte = true → reads byte)
    (writable : ∀ byte, reference.wr byte = true → reads byte ∧ writes byte)
    {control : Res T} {current : Mem} (run : SoloLauf start before control current) :
    HostFreeControl reads writes control ∨
      ∃ boundary, StarM count start before finish boundary ∧ SoloLauf finish boundary control current ∧
        MaskedAgreement reads writes target boundary ∧
        ∀ byte, ¬ writes byte → GleichAt boundary before byte := by
  apply SoloLauf.split_after (fun _ => trivial) _ _ run
  · intro pointer memory complete
    exact (code.scoped_prefix agreement readable writable complete (Nat.le_refl _)).1 rfl
  · intro used pointer memory residual after part within pending
    exact (code.scoped_prefix agreement readable writable part within.le).2 within pending

/-- Restricting the permitted data accesses preserves decoding of an
    installed code region and access to every word of its private frame. -/
theorem maskMemory_code_frame [Kern] {memory : Mem} {pc fp : W} {slots : Nat}
    {code : List II} {reads : W → Prop} (decoded : CodeAt memory pc code)
    (frame : FrameOK memory fp slots) (nowrap : pc.toNat + 16 * code.length < 2 ^ 64)
    (frameReads : ∀ byte, inSlots fp 0 slots byte → reads byte)
    (codeReads : ∀ byte, pc.toNat ≤ byte.toNat → byte.toNat < pc.toNat + 16 * code.length → reads byte) :
    let restricted := maskMemory reads (inSlots fp 0 slots) memory
    FrameOK restricted fp slots ∧ CodeAt restricted pc code := by
  intro restricted
  have agree : MaskedAgreement reads (inSlots fp 0 slots) restricted memory :=
    (maskMemory_agreement reads (inSlots fp 0 slots) memory frameReads).1
  refine ⟨⟨frame.lt, fun index present => ?_, fun index present => ?_⟩, ?_⟩
  · rw [Mem.all_congr (fun offset valid => (agree.1 _ (frameReads _ (frame_slot_byte frame present valid))).2)]
    exact frame.rd index present
  · rw [Mem.all_congr (fun offset valid => agree.2 _ (frame_slot_byte frame present valid))]
    exact frame.wr index present
  · intro index present
    let atInstruction := pc + BitVec.ofNat 64 (16 * index)
    have address (offset : Nat) (inside : offset < 16) :
        reads (atInstruction + BitVec.ofNat 64 offset) := by
      have natural : (atInstruction + BitVec.ofNat 64 offset).toNat = pc.toNat + 16 * index + offset := by
        simp only [atInstruction, BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (a := 16 * index + offset) (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      apply codeReads <;> rw [natural] <;> omega
    have opcode : restricted.rd8 atInstruction = memory.rd8 atInstruction := by
      have pair := agree.1 atInstruction (by simpa using address 0 (by decide))
      simp only [Mem.rd8, pair.1, pair.2]
    have operand (offset : Nat) (fits : offset + 4 ≤ 16) :
        restricted.rd32 (atInstruction + BitVec.ofNat 64 offset) =
          memory.rd32 (atInstruction + BitVec.ofNat 64 offset) := by
      have input (j : Nat) (inside : j < 4) :
          reads (atInstruction + BitVec.ofNat 64 offset + BitVec.ofNat 64 j) := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact address (offset + j) (by omega)
      simp only [Mem.rd32,
        Mem.all_congr (fun j inside => (agree.1 _ (input j inside)).2),
        Mem.le_congr (fun j inside => (agree.1 _ (input j inside)).1)]
    have original := decoded index present
    exact ⟨opcode.trans original.op, (operand 4 (by decide)).trans original.f1,
      (operand 8 (by decide)).trans original.f2, (operand 12 (by decide)).trans original.f3⟩

private theorem StarM.after_reference [Kern] {count used : Nat} {start boundary pointer : T}
    {before atBoundary actual : Mem} (reference : StarM count start before boundary atBoundary)
    (executedPrefix : StarM used start before pointer actual) (reached : count ≤ used) :
    StarM (used - count) boundary atBoundary pointer actual := by
  induction reference generalizing used pointer actual with
  | refl => simpa only [Nat.sub_zero] using executedPrefix
  | next first _ ih =>
    cases executedPrefix with
    | refl => exact (Nat.not_succ_le_zero _ reached).elim
    | next executed tail =>
      obtain ⟨rfl, rfl⟩ := first.det executed.run
      simpa only [Nat.succ_sub_succ_eq_sub] using ih tail (Nat.le_of_succ_le_succ reached)

/-- One confined reference through ordinary memory instructions and
    into a host request determines every partial IR control. This
    allows scheduling at any point in the middle of the reference. -/
theorem StarM.scoped_until_host [Kern] {count : Nat} {start boundary : T}
    {restricted atBoundary final actual : Mem} {reads writes : W → Prop} {call : Req} {resume : Ans → Res T}
    (reference : StarM count start restricted boundary atBoundary)
    (request : RunP (step boundary) atBoundary (.ask (.sys call) resume) final)
    (readable : ∀ byte, restricted.rd byte = true → reads byte)
    (writable : ∀ byte, restricted.wr byte = true → reads byte ∧ writes byte)
    (agreement : MaskedAgreement reads writes restricted actual) :
    ∀ {control memory}, SoloLauf start actual control memory →
      MemoryScopedControl reads writes control ∨ control = .ask (.sys call) resume := by
  obtain ⟨_, replay, atRequest, _, prefixScoped⟩ := StarM.replay_on reference readable writable agreement
  obtain ⟨readMap, writeMap⟩ := StarM.permissions reference
  obtain ⟨_, reached, _, _, requestScoped⟩ := request.replay_on (blind_step _)
    (by intro same; cases same) (by intro op continuation same memory; cases same; rfl)
    (fun byte allowed => readable byte (by simpa only [readMap] using allowed))
    (fun byte allowed => writable byte (by simpa only [writeMap] using allowed)) atRequest
  intro control memory solo
  obtain ⟨used, pointer, atPointer, complete, residual⟩ := solo
  rcases residual with ⟨rfl, _⟩ | residual
  · exact .inl trivial
  rcases Nat.lt_or_ge used count with inside | outside
  · exact .inl (prefixScoped complete inside residual)
  · have remaining := StarM.after_reference replay complete outside
    generalize used - count = remainingCount at remaining
    cases remaining with
    | refl => exact (requestScoped residual).symm
    | next first _ =>
      cases reached.remaining first with
      | ask answer _ => cases answer

private theorem RunP.stop_matches {tree control : Res T} {before after : Mem}
    {observed : Req} {resume : Ans → Res T} (path : RunP tree before control after)
    (atHost : control = .ask (.sys observed) resume) :
    ∀ {expected}, RunTo tree before expected → observed = expected := by
  induction path with
  | refl =>
    cases atHost
    intro expected reference
    cases reference with
    | sys => rfl
    | ask answer _ => cases answer
  | ask answered _ ih =>
    intro expected reference
    cases reference with
    | sys | fp => cases answered
    | ask reply rest =>
      rw [answered] at reply
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj reply)
      exact ih atHost rest

/-- A source-backed reference that stops without an intervening host
    response determines the actual terminal request of a solo IR path. -/
theorem SoloLauf.stop_matches [kernel : Kern] {start : T} {before after : Mem}
    {status : Nat} {request : Req} {resume : Ans → Res T}
    (reference : @Stops kernel.withoutSyscalls start before status)
    (path : SoloLauf start before (.ask (.sys request) resume) after) :
    request.nr = 231 ∧ request.a1 = BitVec.ofNat 64 status := by
  letI : Kern := kernel.withoutSyscalls
  obtain ⟨terminal, atTerminal, expected, completed, stopped, number, result⟩ := reference
  obtain ⟨_, current, currentMemory, actual, pending⟩ := path
  rcases pending with ⟨impossible, _⟩ | pending
  · cases impossible
  have same : request = expected := by
    rcases actual.weiche completed with forward | ⟨_, passed⟩
    · cases forward with
      | refl => exact RunP.stop_matches pending rfl stopped
      | next first _ =>
        cases pending.remaining_run first with
        | ask answered _ => cases answered
        | sys answered _ => exact False.elim answered
    · obtain ⟨rfl, rfl⟩ := passed.halt stopped
      exact RunP.stop_matches pending rfl stopped
  exact ⟨same ▸ number, same ▸ result⟩

/-- A memory-only execution of an instruction tree supplies the SC
    reference up to its residual control, including pending host calls. -/
theorem RunP.sc_reference {layout : Runner.Beweis.Lay}
    {control residual : Res T} {before after : Mem}
    (ran : RunP control before residual after) (table : TabInv layout before)
    (blind : Blind control) :
    ∃ (count : Nat) (final : TabInv layout after),
      SCMemoryPrefix layout ⟨⟨before, table⟩, [some control]⟩ count ⟨⟨after, final⟩, [some residual]⟩ := by
  induction ran with
  | refl => exact ⟨0, table, .nil _⟩
  | @ask request resume before middle after reply residual answered _ ih =>
    have kind : istSpeicherOp request = true := by
      cases request <;> first | rfl | cases answered
    have widths (n : Nat) (address : W) (read : request = .rd n address) :
        n = 1 ∨ n = 4 ∨ n = 8 := (blind.lesen read).1
    obtain ⟨preserved, answer⟩ := memAns_sc (L := layout) (s := ⟨before, table⟩) (i := 0) widths answered
    obtain ⟨count, final, reference⟩ := ih preserved (blind.weiter reply)
    have first : SCSchritt layout 0 ⟨⟨before, table⟩, [some (.ask request resume)]⟩
        ⟨⟨middle, preserved⟩, [some (resume reply)]⟩ := .ask rfl kind answer
    exact ⟨count + 1, final, .cons first reference⟩

private theorem RunM.partial {control : Res T} {before after : Mem} {next : T}
    (ran : RunM control before next after) : RunP control before (.next next) after := by
  induction ran with
  | next => exact .refl _ _
  | ask answered _ ih => exact .ask answered ih

/-- A sequence of whole proved memory instructions gives the counted
    reference used to cover all actual one-thread silent prefixes. -/
theorem StarM.sc_reference {layout : Runner.Beweis.Lay}
    {initial final : T} {before after : Mem} {instructions : Nat}
    (ran : StarM instructions initial before final after) (table : TabInv layout before) :
    ∃ (count : Nat) (preserved : TabInv layout after),
      SCMemoryPrefix layout ⟨⟨before, table⟩, [some (.next initial)]⟩ count
        ⟨⟨after, preserved⟩, [some (.next final)]⟩ := by
  induction ran with
  | refl => exact ⟨0, table, .nil _⟩
  | next instruction _ ih =>
    obtain ⟨first, middleTable, requests⟩ := RunP.sc_reference (RunM.partial instruction) table (blind_step _)
    obtain ⟨rest, finalTable, tail⟩ := ih middleTable
    exact ⟨rest + first + 1, finalTable, .cons (.priv rfl) (requests.trans tail)⟩

/-- A whole generated block and its final partial instruction give one
    memory reference, ending at the control selected by the IR tree. -/
theorem StarM.sc_reference_through {layout : Runner.Beweis.Lay}
    {initial boundary : T} {before middle after : Mem} {instructions : Nat} {residual : Res T}
    (ran : StarM instructions initial before boundary middle)
    (tail : RunP (step boundary) middle residual after) (table : TabInv layout before) :
    ∃ (count : Nat) (preserved : TabInv layout after),
      SCMemoryPrefix layout ⟨⟨before, table⟩, [some (.next initial)]⟩ count
        ⟨⟨after, preserved⟩, [some residual]⟩ := by
  obtain ⟨prefixCount, middleTable, initialRun⟩ := StarM.sc_reference ran table
  obtain ⟨tailCount, finalTable, suffix⟩ := tail.sc_reference middleTable (blind_step _)
  exact ⟨tailCount + 1 + prefixCount, finalTable, initialRun.trans (.cons (.priv rfl) suffix)⟩

private theorem RunP.read8 {before after : Mem} {address : W} {byte : B}
    {resume : W → Res T} {finish : Res T} (read : before.rd8 address = some byte)
    (tail : RunP (resume (byte.setWidth 64)) before finish after) :
    RunP (rd8 address resume) before finish after := by
  refine .ask (a := some (byte.setWidth 64, 0)) (m' := before) (by simp [memAns, read]) ?_
  simpa only [opt_some, BitVec.setWidth_setWidth_of_le byte (k := 8) (l := 64) (by decide),
    BitVec.setWidth_eq] using tail

private theorem RunP.read32 {before after : Mem} {address : W} {word : BitVec 32}
    {resume : BitVec 32 → Res T} {finish : Res T} (read : before.rd32 address = some word)
    (tail : RunP (resume word) before finish after) :
    RunP (rd32 address resume) before finish after := by
  refine .ask (a := some (word.setWidth 64, 0)) (m' := before) (by simp [memAns, read]) ?_
  simpa only [opt_some, BitVec.setWidth_setWidth_of_le word (k := 32) (l := 64) (by decide),
    BitVec.setWidth_eq] using tail

private theorem RunP.read64 {before after : Mem} {address word : W}
    {resume : W → Res T} {finish : Res T} (read : before.rd64 address = some word)
    (tail : RunP (resume word) before finish after) :
    RunP (rd64 address resume) before finish after := by
  exact .ask (a := some (word, 0)) (m' := before) (by simp [memAns, read]) tail

/-- A result continuation decodes its ordinary destination operand and
    writes exactly the received word. This is shared by returning host
    calls, atomic responses, and the instructions using the same tree. -/
theorem resultStore_reference {pointer : T} {memory : Mem} {dest : BitVec 32} {value : W}
    (destination : memory.rd32 (pointer.pc + 4) = some dest)
    (writable : Mem.all memory.wr (slot pointer.fp (sx dest)) 8 = true) :
    RunP (ret1 pointer value) memory (.next (nxt pointer))
      (Mem.write memory (slot pointer.fp (sx dest)) 8 value.toNat) := by
  unfold ret1 f1
  apply RunP.read32 destination
  refine .ask (a := some (0, 0)) (by rw [memAns_wr, Mem.wr64_some writable]) ?_
  exact .refl _ _

/-- The immediate instruction selects its operand and writes one word
    using only the IR memory semantics. -/
theorem constantInstruction_memory [Kern] {pointer : T} {memory : Mem} {dest value pad : BitVec 32}
    (instruction : InsAt memory pointer.pc 1 dest value pad)
    (writable : Mem.all memory.wr (slot pointer.fp (sx dest)) 8 = true) :
    RunM (step pointer) memory (nxt pointer)
      (Mem.write memory (slot pointer.fp (sx dest)) 8 (sx value).toNat) := by
  apply runP_runM (t := nxt pointer) ?_ rfl
  unfold step
  refine RunP.read8 instruction.op ?_
  change RunP (op 1 pointer) _ _ _
  simp only [op]
  apply RunP.read32 instruction.f2
  exact resultStore_reference instruction.f1 writable

/-- The IR instruction tree reaches the host with the continuation
    selected by the operands that it read from the issuing frame. -/
theorem spawnInstruction_reference {parent child : T} {memory : Mem} {dest index pad : BitVec 32}
    (instruction : InsAt memory parent.pc 24 dest index pad)
    (entry : memory.rd64 (slot parent.fp (sx index)) = some child.pc)
    (frame : memory.rd64 (slot parent.fp (sx index) + 8) = some child.fp) :
    RunP (step parent) memory
      (.ask (.sys cloneReq) fun answer =>
        opt answer fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1) memory := by
  unfold step
  refine RunP.read8 instruction.op ?_
  change RunP (op 24 parent) _ _ _
  simp only [op]
  apply RunP.read32 instruction.f2
  simp only [ld]
  exact RunP.read64 entry (RunP.read64 frame (.refl _ _))

end Gabbro.Stage0.Senke.BildMehr
