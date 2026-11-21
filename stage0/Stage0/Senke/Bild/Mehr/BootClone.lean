module

public import Stage0.Senke.Bild.LoaderGoal
public import Stage0.Senke.Images.PrepareSpawn
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Stage0.Senke Runner Runner.IR Runner.Beweis Runner.Mach
  Gabbro.Stage0.Senke.BildMehr

variable {src : String} {K : Nat} {options : Profil.Options}

/-- Only a positive answer to the runner's clone request allocates a
    thread slot. Exited threads keep their old position in the list. -/
def createsThread (event : Ev) : Bool :=
  if event.2.1 = cloneReq then
    match event.2.2 with
    | some (id, _) => decide (0 < id.toInt)
    | none => false
  else false

private theorem processStep_threadSlots {M : MemSys} {act : θ → Res θ}
    {before after : Cfg M θ} {events : List Ev}
    (step : ProcessStep M act before events after) :
    after.ths.length = before.ths.length + events.countP createsThread := by
  cases step with
  | tau _ => simp
  | priv _ _ => simp
  | @ask _ _ _ o _ _ _ _ _ ordinary _ _ =>
    cases o with
    | rd | wr | cas | fp => simp [Mach.lbl]
    | sys q =>
      have distinct : q ≠ cloneReq := by
        intro equal
        subst q
        simp [Op.special] at ordinary
      simp [Mach.lbl, createsThread, distinct]
  | @exit _ _ q _ _ _ number =>
    have distinct : q ≠ cloneReq := by
      intro equal
      subst q
      exact (by decide : cloneReq.nr.toNat ≠ NR_EXIT) number
    simp [createsThread, distinct]
  | @cloneNo _ _ _ _ a _ _ _ _ refused _ =>
    cases a with
    | none => simp [createsThread]
    | some pair =>
      obtain ⟨id, extra⟩ := pair
      simp [createsThread, refused id extra rfl]
  | clone _ _ _ positive _ _ => simp [createsThread, positive]

/-- The actual runner assigns new positions consecutively. The exact
    increase across any continuing prefix is the number of successful
    clone events, even when exits, other system calls and memory steps
    are interleaved. -/
theorem processPrefix_threadSlots {M : MemSys} {act : θ → Res θ}
    {before after : Cfg M θ} {events : List Ev} {steps : Nat}
    (run : ProcessPrefix M act before events steps after) :
    after.ths.length = before.ths.length + events.countP createsThread := by
  induction run with
  | nil => simp
  | cons step _ ih =>
    rw [ih, processStep_threadSlots step, List.countP_append, Nat.add_assoc]

/-- After a spawn instruction has read its entry address and frame, a
    successful clone puts the child at those addresses in the next slot
    and returns the thread ID to the parent's destination operation. -/
theorem bootClone_step {M : MemSys} {before : Cfg M (Res T)} {i : Nat}
    {parent child : T} {id extra : W} {memory : M.St}
    (pending : before.ths[i]? = some (some (.ask (.sys cloneReq) fun answer =>
      opt answer fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1)))
    (answer : M.ans before.ms i (.sys cloneReq) (some (id, extra)) memory)
    (positive : 0 < id.toInt) :
    let threads := before.ths.set i (some (ret1 parent id)) ++ [some (.next child)]
    ProcessStep M actI before [(i, cloneReq, some (id, extra))] ⟨memory, threads⟩ ∧
      threads[before.ths.length]? = some (some (.next child)) := by
  have nonzero : id ≠ 0 := by
    intro equal
    subst id
    exact (by decide : ¬ (0 < (0 : W).toInt)) positive
  constructor
  · exact .clone pending rfl answer positive (by simp only [opt_some, ite_eq_right nonzero]) rfl
  · rw [List.getElem?_append_right (by rw [List.length_set]), List.length_set, Nat.sub_self]
    rfl

/-- The runner fetches a spawn, reads its operand index and both stack
    words, and reaches the pending clone. These five actual TSO steps
    leave memory unchanged and use the parent's view of its own writes. -/
theorem bootClone_read_prefix {layout : Runner.Beweis.Lay}
    {before : Cfg (TSO layout) (Res T)} {i : Nat} {parent child : T}
    {dest index pad : BitVec 32}
    (running : before.ths[i]? = some (some (.next parent)))
    (instruction : InsAt (before.ms.1.view i) parent.pc 24 dest index pad)
    (entry : (before.ms.1.view i).rd64 (slot parent.fp (sx index)) = some child.pc)
    (frame : (before.ms.1.view i).rd64 (slot parent.fp (sx index) + 8) = some child.fp) :
    ProcessPrefix (TSO layout) actI before [] 5
      ⟨before.ms, before.ths.set i (some (.ask (.sys cloneReq) fun answer =>
        opt answer fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1))⟩ := by
  let onThread (r : Res T) : Cfg (TSO layout) (Res T) :=
    ⟨before.ms, before.ths.set i (some r)⟩
  have inside := (List.getElem?_eq_some_iff.mp running).1
  have read (width : Nat) (address value : W) (resume : Ans → Res T)
      (loaded : rdN (before.ms.1.view i) width address = some value) :
      ProcessStep (TSO layout) actI (onThread (.ask (.rd width address) resume)) []
        (onThread (resume (some (value, 0)))) := by
    exact tso_read_step before inside resume loaded
  let clone : Res T := .ask (.sys cloneReq) fun answer =>
    opt answer fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1
  let readFrame (pc : W) : Res T := rd64 (slot parent.fp (sx index) + 8) fun fp =>
    .ask (.sys cloneReq) fun answer =>
      opt answer fun pair => if pair.1 = 0 then .next ⟨pc, fp⟩ else ret1 parent pair.1
  have started : ProcessStep (TSO layout) actI before [] (onThread (IR.step parent)) :=
    .priv running rfl
  have fetched : ProcessStep (TSO layout) actI (onThread (IR.step parent)) [] (onThread (op 24 parent)) := by
    have loaded : rdN (before.ms.1.view i) 1 parent.pc = some ((BitVec.ofNat 8 24).setWidth 64) := by
      simp only [rdN, instruction.op, Option.map_some]
    exact read 1 parent.pc _ (fun answer => opt answer fun pair =>
      op (pair.1.setWidth 8 |>.setWidth 64).toNat parent) loaded
  have indexed : ProcessStep (TSO layout) actI (onThread (op 24 parent)) []
      (onThread (ld parent (sx index) readFrame)) := by
    have loaded : rdN (before.ms.1.view i) 4 (parent.pc + 8) = some (index.setWidth 64) := by
      simp only [rdN, instruction.f2, Option.map_some]
    simpa [op, f2, rd32, ld, readFrame] using
      read 4 (parent.pc + 8) _ (fun answer => opt answer fun pair =>
        ld parent (sx (pair.1.setWidth 32)) fun pc =>
          rd64 (slot parent.fp (sx (pair.1.setWidth 32)) + 8) fun fp =>
            .ask (.sys cloneReq) fun answer =>
              opt answer fun pair => if pair.1 = 0 then .next ⟨pc, fp⟩ else ret1 parent pair.1) loaded
  have entered : ProcessStep (TSO layout) actI (onThread (ld parent (sx index) readFrame)) []
      (onThread (readFrame child.pc)) :=
    read 8 _ _ (fun answer => opt answer fun pair => readFrame pair.1) entry
  have framed : ProcessStep (TSO layout) actI (onThread (readFrame child.pc)) [] (onThread clone) :=
    read 8 _ _ (fun answer => opt answer fun frame =>
      .ask (.sys cloneReq) fun answer =>
        opt answer fun pair => if pair.1 = 0 then .next ⟨child.pc, frame.1⟩ else ret1 parent pair.1) frame
  exact .cons started (.cons fetched (.cons indexed (.cons entered (.cons framed (.nil _)))))

/-- A decoded spawn and its successful host response produce exactly one
    clone event and the child state read from the spawning thread's stack. -/
theorem bootClone_run {layout : Runner.Beweis.Lay}
    {before : Cfg (TSO layout) (Res T)} {i : Nat} {parent child : T}
    {dest index pad : BitVec 32} {id extra : W} {memory : (TSO layout).St}
    (running : before.ths[i]? = some (some (.next parent)))
    (instruction : InsAt (before.ms.1.view i) parent.pc 24 dest index pad)
    (entry : (before.ms.1.view i).rd64 (slot parent.fp (sx index)) = some child.pc)
    (frame : (before.ms.1.view i).rd64 (slot parent.fp (sx index) + 8) = some child.fp)
    (answer : (TSO layout).ans before.ms i (.sys cloneReq) (some (id, extra)) memory)
    (positive : 0 < id.toInt) :
    let threads := before.ths.set i (some (ret1 parent id)) ++ [some (.next child)]
    ProcessPrefix (TSO layout) actI before [(i, cloneReq, some (id, extra))] 6 ⟨memory, threads⟩ ∧
      threads[before.ths.length]? = some (some (.next child)) := by
  have read := bootClone_read_prefix running instruction entry frame
  let pending : Res T := .ask (.sys cloneReq) fun result =>
    opt result fun pair => if pair.1 = 0 then .next child else ret1 parent pair.1
  have indexed : (before.ths.set i (some pending))[i]? = some (some pending) :=
    List.getElem?_set_self (List.getElem?_eq_some_iff.mp running).1
  obtain ⟨created, found⟩ := bootClone_step (before := ⟨before.ms, before.ths.set i (some pending)⟩)
    (parent := parent) (child := child) indexed answer positive
  constructor
  · simpa only [List.nil_append, List.set_set, Nat.reduceAdd] using read.trans (ProcessPrefix.ofStep created)
  · simpa only [List.length_set, List.set_set] using found

/-- Execute the two immediate operands and the full clone instruction
    at any prepared startup site. The host response preserves memory.
    The parent advances by three instructions and the next process slot
    gets the child's relocated addresses. Only parent scratch changes
    in the local memory views. -/
theorem bootSpawn_run [Kern] {layout : Runner.Beweis.Lay}
    {before : Cfg (TSO layout) (Res T)} {i : Nat} {pc fp : W} {K scratch entry stack : Nat}
    (running : before.ths[i]? = some (some (.next ⟨pc, fp⟩)))
    (code : CodeAt (before.ms.1.view i) pc (spawnOne scratch entry stack))
    (frame : FrameOK (before.ms.1.view i) fp K) (far : CodeFar pc 10 fp K)
    (room : scratch + 3 ≤ K) (slots : K < 2 ^ 31) (address : entry < 2 ^ 31) (stackBound : stack < 2 ^ 31)
    {id extra : W} (positive : 0 < id.toInt) :
    let child : T := ⟨BitVec.ofNat 64 entry, BitVec.ofNat 64 stack⟩
    let threads := before.ths.set i (some (.next ⟨pc + BitVec.ofNat 64 (16 * 3), fp⟩)) ++ [some (.next child)]
    ∃ after : (TSO layout).St,
      ProcessPrefix (TSO layout) actI before [(i, cloneReq, some (id, extra))] 18 ⟨after, threads⟩ ∧
      threads[before.ths.length]? = some (some (.next child)) ∧
      after.1.m = before.ms.1.m ∧
      Agree fp scratch K (before.ms.1.view i) (after.1.view i) ∧
      (after.1.view i).rd64 (slot fp (BitVec.ofNat 64 (scratch + 2))) = some id ∧
      ∀ j, j ≠ i → after.1.view j = before.ms.1.view j := by
  intro child threads
  let parent : T := ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩
  have inside := (List.getElem?_eq_some_iff.mp running).1
  obtain ⟨prepared, preparation, committed, preparedViews, beforeResult, instruction, entryRead, stackRead⟩ :=
    spawn_prepare_prefix running code frame far (by omega) slots address stackBound
  have operand : sx (II.f scratch) = BitVec.ofNat 64 scratch := sx_nat (by omega)
  rw [← operand] at entryRead stackRead
  let atClone : Cfg (TSO layout) (Res T) :=
    ⟨prepared, before.ths.set i (some (.next parent))⟩
  have cloneReady : atClone.ths[i]? = some (some (.next parent)) := List.getElem?_set_self inside
  obtain ⟨cloned, _⟩ := bootClone_run (before := atClone) (i := i) (parent := parent) (child := child)
    (extra := extra) cloneReady instruction entryRead stackRead
    (memory := prepared) True.intro positive
  let active : Cfg (TSO layout) (Res T) :=
    ⟨prepared, before.ths.set i (some (ret1 parent id)) ++ [some (.next child)]⟩
  have responseReady : active.ths[i]? = some (some (ret1 parent id)) := by
    have within : i < (before.ths.set i (some (ret1 parent id))).length := by
      simpa only [List.length_set] using inside
    simp only [active, List.getElem?_append_left within, List.getElem?_set_self inside]
  have dest : sx (II.f ((scratch + 2 : Nat) : Int)) = BitVec.ofNat 64 (scratch + 2) :=
    sx_nat (by omega)
  have inFrame : scratch + 2 < K := by omega
  have writable : Mem.all prepared.1.m.wr (slot fp (sx (II.f ((scratch + 2 : Nat) : Int)))) 8 = true := by
    rw [dest, committed, ← foldl_wr (before.ms.1.buf i) before.ms.1.m]
    exact frame.wr _ inFrame
  obtain ⟨finished, resume, memory, wrote, other⟩ :=
    tso_ret1_prefix (before := active) (i := i) (parent := parent) responseReady instruction.f1 writable
  have advance : nxt parent = ⟨pc + BitVec.ofNat 64 (16 * 3), fp⟩ := by
    exact congrArg (fun ip => T.mk ip fp) (pcN pc 2 1 3 rfl)
  have parentUnchanged : Agree fp scratch K (prepared.1.view i) (finished.1.view i) := by
    rw [wrote, dest]
    exact agree_write frame.room (by omega) inFrame _
  have returnWord : (finished.1.view i).rd64 (slot fp (BitVec.ofNat 64 (scratch + 2))) = some id := by
    rw [wrote, dest]
    have preparedFrame := frame.agree beforeResult
    exact Runner.Mem.rd64_wr64 (Runner.Mem.wr64_some (preparedFrame.wr _ inFrame)) (preparedFrame.rd _ inFrame)
  refine ⟨finished, ?_, ?_, memory.trans committed, beforeResult.trans parentUnchanged,
    returnWord, fun j different => (other j different).trans (preparedViews j different)⟩
  · have actual : ProcessPrefix (TSO layout) actI atClone [(i, cloneReq, some (id, extra))] 6 active := by
      simpa only [atClone, active, List.set_set] using cloned
    have parentSlot : i < (before.ths.set i (some (ret1 parent id))).length := by
      simpa only [List.length_set] using inside
    simpa only [List.nil_append, List.append_nil, active, List.set_append_left _ _ parentSlot, List.set_set,
      advance, threads, Nat.reduceAdd] using (preparation.trans actual).trans resume
  · change (before.ths.set i _ ++ [some (.next child)])[before.ths.length]? = _
    rw [List.getElem?_append_right (by rw [List.length_set]), List.length_set, Nat.sub_self]
    rfl

/-- At the relocated clone instruction of a loaded image, once the two
    scratch words have been prepared, a successful response appends the
    declared child's actual entry and stack frame. The postcondition
    identifies its logical boot position and exact start environment. -/
theorem Emitted.loaded_boot_run [Kern] (output : Emitted src K options)
    (Q : AxEns (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf output.compiled.unit))
    {layout : Runner.Beweis.Lay} {before : Cfg (TSO layout) (Res T)}
    {i j : Nat} {id extra : W} {memory : (TSO layout).St}
    {start : Σ f : (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf output.compiled.unit).Fn,
      Env (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf output.compiled.unit)
        ((Gabbro.Grammatik.Parser.UebersetzeAllg.declOf output.compiled.unit).params f)}
    (declared : output.starts[j]? = some start)
    (loaded : BytesAt (before.ms.1.view i) codeBase (output.image.code.flatMap encII))
    (position : before.ths.length = j + 1)
    (answer : (TSO layout).ans before.ms i (.sys cloneReq) (some (id, extra)) memory)
    (positive : 0 < id.toInt) :
    let parent : T := ⟨BitVec.ofNat 64 codeBase + BitVec.ofNat 64 (16 * (10 * j)) +
      BitVec.ofNat 64 (16 * 2), BitVec.ofNat 64 output.image.fp0⟩
    let child : T := ⟨BitVec.ofNat 64
      (codeBase + 16 * (10 * output.starts.length + startLen + startLen * j)),
      BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * (j + 1)))⟩
    let scratch := slot parent.fp (sx (II.f (startScratch output.compiled.main)))
    before.ths[i]? = some (some (.next parent)) →
    (before.ms.1.view i).rd64 scratch = some child.pc →
    (before.ms.1.view i).rd64 (scratch + 8) = some child.fp →
    let threads := before.ths.set i (some (ret1 parent id)) ++ [some (.next child)]
    ProcessPrefix (TSO layout) actI before [(i, cloneReq, some (id, extra))] 6 ⟨memory, threads⟩ ∧
      threads[j + 1]? = some (some (.next child)) ∧
      (output.bootStart Q).lebt (j + 1) = true ∧
      initRuhe (output.goalUnit Q).starts (j + 1) = ⟨some start.1, envR start.2⟩ := by
  intro parent child scratch running entry frame
  obtain ⟨code, live, logical⟩ := output.loaded_boot_site Q loaded declared
  have decoded := code 2 (by rw [spawnOne_len]; decide)
  have actual : InsAt (before.ms.1.view i) parent.pc 24
      (II.f ((startScratch output.compiled.main + 2 : Nat) : Int))
      (II.f (startScratch output.compiled.main)) (II.f 0) := decoded
  obtain ⟨stepped, found⟩ := bootClone_run running actual entry frame answer positive
  exact ⟨stepped, position ▸ found, live, logical⟩

/-- A later startup site uses exactly the same compiler-to-runner argument
    as the first. Once the parent reaches the site with the earlier
    positions allocated, the relocated code supplies the two operands,
    and the clone allocates logical root `j + 1`. The current frame can
    contain writes from earlier sites. -/
theorem Emitted.boot_site_prefix [Kern] (output : Emitted src K options)
    (Q : AxEns (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf output.compiled.unit))
    {layout : Runner.Beweis.Lay} {before : Cfg (TSO layout) (Res T)} {j : Nat} {id extra : W}
    {start : Σ f : (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf output.compiled.unit).Fn,
      Env (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf output.compiled.unit)
        ((Gabbro.Grammatik.Parser.UebersetzeAllg.declOf output.compiled.unit).params f)}
    (declared : output.starts[j]? = some start)
    (loaded : BytesAt (before.ms.1.view 0) codeBase (output.image.code.flatMap encII))
    (position : before.ths.length = j + 1)
    (frame : FrameOK (before.ms.1.view 0) (BitVec.ofNat 64 output.image.fp0) output.image.Ks)
    (positive : 0 < id.toInt) :
    let pc := BitVec.ofNat 64 codeBase + BitVec.ofNat 64 (16 * (10 * j))
    let fp := BitVec.ofNat 64 output.image.fp0
    let child : T := ⟨BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length + startLen + startLen * j)),
      BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * (j + 1)))⟩
    before.ths[0]? = some (some (.next ⟨pc, fp⟩)) →
    let threads := before.ths.set 0 (some (.next ⟨pc + BitVec.ofNat 64 (16 * 3), fp⟩)) ++ [some (.next child)]
    ∃ after : (TSO layout).St,
      ProcessPrefix (TSO layout) actI before [(0, cloneReq, some (id, extra))] 18 ⟨after, threads⟩ ∧
      threads[j + 1]? = some (some (.next child)) ∧
      after.1.m = before.ms.1.m ∧
      Agree fp (startScratch output.compiled.main) output.image.Ks (before.ms.1.view 0) (after.1.view 0) ∧
      (after.1.view 0).rd64 (slot fp (BitVec.ofNat 64 (startScratch output.compiled.main + 2))) = some id ∧
      (∀ k, k ≠ 0 → after.1.view k = before.ms.1.view k) ∧
      BytesAt (after.1.view 0) codeBase (output.image.code.flatMap encII) ∧
      FrameOK (after.1.view 0) fp output.image.Ks ∧
      initRuhe (output.goalUnit Q).starts (j + 1) = ⟨some start.1, envR start.2⟩ ∧
      ∀ O : Orakel (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf output.compiled.unit),
        FadenSchrittX (output.goalUnit Q).P.mitRuhe O.mitRuhe output.image.passes
          (GeteiltV (D := Gabbro.Grammatik.Parser.UebersetzeAllg.declOf output.compiled.unit)
            (output.goalUnit Q).P (output.goalUnit Q).ws)
          (output.bootActivation Q j) (output.bootActivation Q (j + 1)) := by
  intro pc fp child running threads
  have inside := (List.getElem?_eq_some_iff.mp declared).1
  obtain ⟨site, _, logical⟩ := output.loaded_boot_site Q loaded declared
  obtain ⟨_, body, _, placed, serialized, _, _, _⟩ := bild_lage output.emission output.funktionen_voll
    (fun base bound => layU_in output.compiled.unit output.tor base bound)
    (fun base => layU_dis output.compiled.unit output.tor base)
    (fun base => by simp only [layU]; omega)
    (fun base => layU_sync output.compiled.unit output.tor base)
  have frameAddress : output.image.fp0 = codeBase + 16 * (headLen output.starts.length + body.length) := by
    simpa only [Emitted.starts, List.length_map] using placed.hfp
  have enough : startScratch output.compiled.main + 8 ≤ output.image.Ks :=
    placed.hex _ (List.mem_cons_self ..)
  have storage : output.image.fp0 + 8 * (output.image.Ks * (output.starts.length + 1)) ≤ output.image.Y.lo := by
    simpa only [Emitted.starts, List.length_map] using placed.hylo
  have fit := placed.hfit
  have worldOrder := placed.hyord
  have upper := placed.hyhi
  have childIndex : output.image.Ks * (j + 1) ≤ output.image.Ks * (output.starts.length + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have oneFrame : output.image.Ks ≤ output.image.Ks * (output.starts.length + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have frameBound : output.image.fp0 + 8 * output.image.Ks < 2 ^ 31 := by omega
  have childFrame : output.image.fp0 + 8 * (output.image.Ks * (j + 1)) < 2 ^ 31 := by omega
  have childCode : codeBase + 16 * (10 * output.starts.length + startLen + startLen * j) < 2 ^ 31 := by
    simp only [headLen, startLen] at frameAddress ⊢
    omega
  have far : CodeFar pc 10 fp output.image.Ks := by
    change CodeFar (BitVec.ofNat 64 codeBase + BitVec.ofNat 64 (16 * (10 * j))) 10
      (BitVec.ofNat 64 output.image.fp0) output.image.Ks
    rw [ofNat_add64]
    apply codeFar_nat _ (Nat.lt_trans frameBound (by decide))
    simp only [headLen, startLen] at frameAddress
    omega
  obtain ⟨after, run, appended, same, own, response, others⟩ :=
    bootSpawn_run (before := before) (i := 0) (extra := extra) running site frame far (by omega)
      (by omega) childCode childFrame positive
  have codeEnd : codeBase + (output.image.code.flatMap encII).length = output.image.fp0 := by
    rw [flatMap_enc_len, serialized, List.length_append, placed.head, placed.hfp]
  have codeKept : BytesAt (after.1.view 0) codeBase (output.image.code.flatMap encII) := by
    intro byte bound
    have decoded : (BitVec.ofNat 64 (codeBase + byte)).toNat = codeBase + byte := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have stackStart : fp.toNat = output.image.fp0 := by
      change (BitVec.ofNat 64 output.image.fp0).toNat = output.image.fp0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have separate : ¬ inSlots fp (startScratch output.compiled.main) output.image.Ks
        (BitVec.ofNat 64 (codeBase + byte)) := by
      intro overlap
      unfold inSlots at overlap
      rw [decoded, stackStart] at overlap
      omega
    rw [own.rd, own.wr, own.b _ separate]
    exact loaded byte bound
  exact ⟨after, run, position ▸ appended, same, own, response, others, codeKept, frame.agree own, logical,
    fun O => output.bootActivation_step Q O inside⟩

/-- From the actual mapped payload the loader and the first clone site
    reach the first declared child. The compiled immediates supply both
    child addresses and the buffer holds the writes without a flush. -/
theorem Emitted.first_boot_clone [Kern] (output : Emitted src K options)
    (Q : AxEns (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf output.compiled.unit))
    {s : (TSO L0).St} (empty : ∀ i, s.1.buf i = [])
    (loaded : BytesAt s.1.m Runner.Prog.IMG output.bytes)
    {start : Σ f : (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf output.compiled.unit).Fn,
      Env (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf output.compiled.unit)
        ((Gabbro.Grammatik.Parser.UebersetzeAllg.declOf output.compiled.unit).params f)}
    (declared : output.starts[0]? = some start) {id extra : W} (positive : 0 < id.toInt) :
    let parent : T := ⟨BitVec.ofNat 64 codeBase + BitVec.ofNat 64 (16 * 2), BitVec.ofNat 64 output.image.fp0⟩
    let child : T := ⟨BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length + startLen)),
      BitVec.ofNat 64 (output.image.fp0 + 8 * output.image.Ks)⟩
    ∃ after : (TSO L0).St,
      ProcessPrefix (TSO L0) actI ⟨s, [some t4]⟩ [(0, cloneReq, some (id, extra))] 19
        ⟨after, [some (.next (nxt parent)), some (.next child)]⟩ ∧ after.1.m = s.1.m ∧
      (output.bootActivation Q 1).lebt 1 = true ∧
      initRuhe (output.goalUnit Q).starts 1 = ⟨some start.1, envR start.2⟩ ∧
      (∃ frame, startFrameBytes output.image.Ks (FB + FB)
        (encodeEnv output.image.Y.withIdle (envR start.2)) = some frame ∧
        BytesAt (after.1.view 1) (output.image.fp0 + 8 * output.image.Ks) frame) ∧
      ∀ O : Orakel (Gabbro.Grammatik.Parser.UebersetzeAllg.declOf output.compiled.unit),
        FadenSchrittX (output.goalUnit Q).P.mitRuhe O.mitRuhe output.image.passes
          (GeteiltV (D := Gabbro.Grammatik.Parser.UebersetzeAllg.declOf output.compiled.unit)
            (output.goalUnit Q).P (output.goalUnit Q).ws)
          (output.bootActivation Q 0) (output.bootActivation Q 1) := by
  intro parent child
  have present := (List.getElem?_eq_some_iff.mp declared).1
  have beforeView (i : Nat) : s.1.view i = s.1.m := by simp only [TSt.view, empty i, List.foldl_nil]
  let entered : Cfg (TSO L0) (Res T) :=
    ⟨s, [some (.next ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 output.image.fp0⟩)]⟩
  have initialFrame := bild_initialized_frames_u output.initialValid output.emission
    output.funktionen_voll loaded 0 (Nat.zero_le _)
  simp only [Nat.mul_zero, Nat.add_zero] at initialFrame
  have code : BytesAt (s.1.view 0) codeBase (output.image.code.flatMap encII) :=
    (beforeView 0).symm ▸ output.loaded_code loaded
  have atEntry : entered.ths[0]? = some (some (.next
      ⟨BitVec.ofNat 64 codeBase + BitVec.ofNat 64 (16 * (10 * 0)), BitVec.ofNat 64 output.image.fp0⟩)) := by
    simp only [Nat.mul_zero, BitVec.add_zero]
    rfl
  obtain ⟨finished, launched, _, committed, _, _, views, _, _, logical, activated⟩ :=
    output.boot_site_prefix Q (before := entered) (extra := extra) declared code rfl
      ((beforeView 0).symm ▸ initialFrame) positive atEntry
  have readFrame := output.loader_frame loaded
  have loadedEntry : ProcessPrefix (TSO L0) actI ⟨s, [some t4]⟩ [] 1 entered := by
    have step : ProcessStep (TSO L0) actI ⟨s, [some t4]⟩
        (Mach.lbl 0 (.rd 8 (BitVec.ofNat 64 Runner.Prog.IMG))
          (some (BitVec.ofNat 64 output.image.fp0, 0))) entered :=
      .ask (i := 0) rfl rfl rfl
        ⟨rfl, 0, by simp only [beforeView 0, rdN, readFrame, Option.map_some]⟩ rfl
    exact .ofStep step
  have childView : finished.1.view 1 = s.1.m :=
    (views 1 (by decide)).trans (beforeView 1)
  obtain ⟨stackBytes, encoded, stackLoaded⟩ := output.goal_arguments_loaded Q loaded
  have selected : ((output.goalUnit Q).starts.map
      (fun initial => encodeEnv output.image.Y.withIdle (envR initial.2)))[1]? =
      some (encodeEnv output.image.Y.withIdle (envR start.2)) := by
    rw [List.getElem?_map, output.goalUnit_starts]
    change Option.map _ output.starts[0]? = _
    simp only [declared, Option.map_some]
  obtain ⟨fits, exactWords⟩ := List.getElem?_eq_some_iff.mp selected
  obtain ⟨childBytes, childEncoded, childLoaded⟩ :=
    startStackBytes_frame encoded output.image.fp0 stackLoaded 1 fits
  rw [exactWords] at childEncoded
  simp only [Nat.mul_one] at childLoaded
  have childLive : (output.bootActivation Q 1).lebt 1 = true := by
    change decide (1 ≤ min 1 output.starts.length) = true
    simpa only [Nat.min_eq_left (Nat.succ_le_of_lt present)] using decide_eq_true (Nat.le_refl 1)
  refine ⟨finished, ?_, committed, childLive, logical,
    ⟨childBytes, childEncoded, childView.symm ▸ childLoaded⟩, activated⟩
  have advance : nxt parent =
      ⟨BitVec.ofNat 64 codeBase + BitVec.ofNat 64 (16 * 3), BitVec.ofNat 64 output.image.fp0⟩ :=
    congrArg (fun ip => T.mk ip (BitVec.ofNat 64 output.image.fp0)) (pcN (BitVec.ofNat 64 codeBase) 2 1 3 rfl)
  simpa only [entered, advance, List.nil_append, List.set_cons_zero, List.singleton_append, Nat.reduceAdd, Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.mul_one,
    BitVec.add_zero] using loadedEntry.trans launched

end Gabbro.Stage0
