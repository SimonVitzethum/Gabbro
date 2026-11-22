/-
  File:      stage0/Stage0/Senke/Bild/Mehr/Solo.lean
  Subject:   The solo run of one thread (multi-thread image theorem, package MT1). The machine of threads runs an
             instruction request by request (`Runner.Mach.Tr` with `actI`): a thread at `.next t` starts the
             instruction (its state becomes the request tree `step t`), then each request is answered on its own.
             `RunP` is a request tree answered by the memory part of the way; `SoloLauf tb mb r m` says that the
             thread's state `r` with the memory `m` is where its OWN memory-only run from the boundary `(tb, mb)`
             stands: whole instructions (`StarM`, the object of the single-thread chain), then part of the current
             one. The two steps of a thread answered by the memory keep it (`SoloLauf.priv`, `SoloLauf.ask`), and at
             an instruction boundary it is a `StarM` run (`SoloLauf.starM`), so `korrespondenz_lauf` applies.
-/
module
public import Stage0.Senke.Bild.Lauf
public import Stage0.Senke.Bild.Mehr.Lokal
public import Stage0.Senke.Bild.Mehr.BlindOp
public import Runner.Mach.Maschine
@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Runner Runner.IR Gabbro.Stage0.Senke.BildLauf

set_option linter.unusedSectionVars false

variable [Kern]

/-- A request tree answered by the memory alone, part of the way: from `r` at `m` to the rest `r'` at `m'`. -/
inductive RunP : Res T → Mem → Res T → Mem → Prop
  | refl (r : Res T) (m : Mem) : RunP r m r m
  | ask {o : Op} {k : Ans → Res T} {m m' m'' : Mem} {a : Ans} {r : Res T} :
      memAns m o = some (a, m') → RunP (k a) m' r m'' → RunP (.ask o k) m r m''

/-- One more answered request at the end of a partial run. -/
theorem runP_snoc' {r r' : Res T} {m m1 : Mem} (h : RunP r m r' m1) :
    ∀ {o : Op} {k : Ans → Res T}, r' = .ask o k → ∀ {a : Ans} {m2 : Mem}, memAns m1 o = some (a, m2) →
      RunP r m (k a) m2 := by
  induction h with
  | refl r0 m0 =>
    intro o k e a m2 ho
    subst e
    exact .ask ho (.refl _ _)
  | ask hm _ ih =>
    intro o k e a m2 ho
    exact .ask hm (ih e ho)

theorem runP_snoc {r : Res T} {m m1 : Mem} {o : Op} {k : Ans → Res T} (h : RunP r m (.ask o k) m1) {a : Ans}
    {m2 : Mem} (ho : memAns m1 o = some (a, m2)) : RunP r m (k a) m2 :=
  runP_snoc' h rfl ho

/-- Every reachable point within a memory-only instruction can finish
    at the same next pointer and memory as the whole instruction. -/
theorem RunP.remaining {start current : Res T} {before now : Mem}
    (part : RunP start before current now) :
    ∀ {next : T} {after : Mem}, RunM start before next after → RunM current now next after := by
  induction part with
  | refl => exact fun whole => whole
  | ask answered _ ih =>
    intro next after whole
    cases whole with
    | ask same later =>
      rw [answered] at same
      simp only [Option.some.injEq, Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      exact ih later

/-- A memory prefix cannot consume a host or floating operation. It
    preserves the exact remaining reference, even if the next request
    belongs to one of those boundaries. -/
theorem RunP.remaining_run {start current : Res T} {before now : Mem}
    (part : RunP start before current now) :
    ∀ {next : T} {after : Mem}, Run start before next after → Run current now next after := by
  induction part with
  | refl => exact fun whole => whole
  | ask answered _ ih =>
    intro next after whole
    cases whole with
    | ask same later =>
      rw [answered] at same
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      exact ih later
    | sys | fp => cases answered

/-- A partially answered instruction inherits the request behavior of
    the original decoded instruction. -/
theorem RunP.blind {start current : Res T} {before now : Mem}
    (part : RunP start before current now) (original : Blind start) : Blind current := by
  induction part with
  | refl => exact original
  | ask _ _ ih => exact ih (original.weiter _)

/-- A reference can mask writes to shared read-only bytes. It agrees
    with the actual memory on the permissions that can affect it. -/
def MaskedAgreement (reads writes : W → Prop) (reference actual : Mem) : Prop :=
  (∀ byte, reads byte → reference.b byte = actual.b byte ∧ reference.rd byte = actual.rd byte) ∧
  (∀ byte, writes byte → reference.wr byte = actual.wr byte)

/-- Restrict the allowed read and write bytes of a reference memory.
    The actual process and its memory have no such transformation. -/
noncomputable def maskMemory (reads writes : W → Prop) (memory : Mem) : Mem := by
  classical
  exact { memory with
    rd := fun byte => memory.rd byte && decide (reads byte)
    wr := fun byte => memory.wr byte && decide (writes byte) }

/-- The restriction grants access only inside the selected regions and
    agrees with the actual memory wherever that access is permitted. -/
theorem maskMemory_agreement (reads writes : W → Prop) (memory : Mem)
    (within : ∀ byte, writes byte → reads byte) :
    let masked := maskMemory reads writes memory
    MaskedAgreement reads writes masked memory ∧
      (∀ byte, masked.rd byte = true → reads byte) ∧
      (∀ byte, masked.wr byte = true → reads byte ∧ writes byte) := by
  classical
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro byte read
    exact ⟨rfl, by simp only [maskMemory, read, decide_true, Bool.and_true]⟩
  · intro byte write
    simp only [maskMemory, write, decide_true, Bool.and_true]
  · intro byte granted
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp granted).2
  · intro byte granted
    have write : writes byte := of_decide_eq_true (Bool.and_eq_true_iff.mp granted).2
    exact ⟨within byte write, write⟩

private theorem replay_memory_request {reads writes : W → Prop}
    {reference actual finish : Mem} {op : Op} {answer : W × W}
    (readable : ∀ byte, reference.rd byte = true → reads byte)
    (writable : ∀ byte, reference.wr byte = true → reads byte ∧ writes byte)
    (agrees : MaskedAgreement reads writes reference actual)
    (answered : memAns reference op = some (some answer, finish)) :
    ∃ next, memAns actual op = some (some answer, next) ∧
      MaskedAgreement reads writes finish next ∧
      (∀ byte, fussOp op byte → reads byte) ∧
      (schreibtOp op = true → ∀ byte, fussOp op byte → writes byte) := by
  have confined := memAns_confined readable writable answered
  obtain ⟨next, sameAnswer, sameTouched⟩ :=
    memAns_replay (fun byte touched =>
      ⟨(agrees.1 byte (confined.1 byte touched)).1, (agrees.1 byte (confined.1 byte touched)).2,
        fun writesRequest => agrees.2 byte (confined.2 writesRequest byte touched)⟩) answered
  have referenceStable := memAns_nurIn answered
  have actualStable := memAns_nurIn sameAnswer
  refine ⟨next, sameAnswer, ⟨?_, ?_⟩, confined⟩
  · intro byte included
    by_cases touched : fussOp op byte
    · exact sameTouched byte touched
    · have b := (referenceStable.gleichAt touched).1
      exact ⟨b.trans ((agrees.1 byte included).1.trans (actualStable.gleichAt touched).1.symm),
        (congrFun referenceStable.rd byte).trans
          ((agrees.1 byte included).2.trans (congrFun actualStable.rd byte).symm)⟩
  · intro byte included
    exact (congrFun referenceStable.wr byte).trans
      ((agrees.2 byte included).trans (congrFun actualStable.wr byte).symm)

/-- An actual memory prefix sees the same responses as the restricted
    reference until an external effect boundary. The reference can
    contain a floating operation or a host response beyond that prefix. -/
theorem RunP.align_reference {start current : Res T} {actual now : Mem}
    {reads writes : W → Prop} (taken : RunP start actual current now) :
    ∀ {reference finish : Mem} {target : T},
      Run start reference target finish → Blind start →
      (∀ byte, reference.rd byte = true → reads byte) →
      (∀ byte, reference.wr byte = true → reads byte ∧ writes byte) →
      MaskedAgreement reads writes reference actual →
      ∃ cut, RunP start reference current cut ∧ MaskedAgreement reads writes cut now ∧
        ∀ byte, ¬ writes byte → GleichAt now actual byte := by
  induction taken with
  | refl => exact fun _ _ _ _ proof => ⟨_, .refl _ _, proof, fun byte _ => GleichAt.refl _ byte⟩
  | ask actualAnswer _ ih =>
    intro reference finish target success tree readable writable agrees
    cases success with
    | ask answered rest =>
      rename_i referenceAnswer
      cases referenceAnswer with
      | none =>
        rw [tree.missing] at rest
        cases rest
      | some words =>
        obtain ⟨advanced, same, agreement, _, written⟩ :=
          replay_memory_request readable writable agrees answered
        rw [same] at actualAnswer
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj actualAnswer)
        have permissions := memAns_nurIn answered
        obtain ⟨cut, remaining, exactMemory, untouched⟩ := ih rest (tree.weiter _)
          (fun byte permission => readable byte (by simpa only [permissions.rd] using permission))
          (fun byte permission => writable byte (by simpa only [permissions.wr] using permission)) agreement
        exact ⟨cut, .ask answered remaining, exactMemory,
          fun byte outside => (untouched byte outside).trans (memAns_aussen same written byte outside)⟩
    | sys | fp => cases actualAnswer

/-- A restricted reference ending at a memory-independent boundary
    determines every request before that boundary in the actual memory.
    The endpoint can be the next instruction or a pending host answer. -/
theorem RunP.replay_on {r target : Res T} {reference finish : Mem}
    {reads writes : W → Prop}
    (ran : RunP r reference target finish) (tree : Blind r)
    (safe : target ≠ .fault)
    (blocked : ∀ op resume, target = .ask op resume → ∀ memory, memAns memory op = none)
    (readable : ∀ byte, reference.rd byte = true → reads byte)
    (writable : ∀ byte, reference.wr byte = true → reads byte ∧ writes byte)
    {actual : Mem} (agrees : MaskedAgreement reads writes reference actual) :
    ∃ result, RunP r actual target result ∧ MaskedAgreement reads writes finish result ∧
      (∀ byte, ¬ writes byte → GleichAt result actual byte) ∧
      ∀ {current : Mem} {request : Op} {resume : Ans → Res T},
        RunP r actual (.ask request resume) current → (.ask request resume : Res T) ≠ target →
          (∀ byte, fussOp request byte → reads byte) ∧
          (schreibtOp request = true → ∀ byte, fussOp request byte → writes byte) := by
  induction ran generalizing actual with
  | refl =>
    refine ⟨actual, .refl _ _, agrees, fun byte _ => GleichAt.refl _ byte, ?_⟩
    intro current request resume partialRun prior
    cases partialRun with
    | refl => exact (prior rfl).elim
    | ask answered _ =>
      rw [blocked _ _ rfl] at answered
      cases answered
  | @ask op k before middle after answer dest answered rest ih =>
    cases answer with
    | none =>
      rw [tree.missing] at rest
      cases rest with
      | refl => exact (safe rfl).elim
    | some words =>
      obtain ⟨advanced, sameAnswer, sameRegion, included, written⟩ :=
        replay_memory_request readable writable agrees answered
      have referenceStable := memAns_nurIn answered
      obtain ⟨result, replay, sameResult, otherBytes, pending⟩ := ih (tree.weiter _) safe blocked
        (fun byte permission => readable byte (by simpa only [referenceStable.rd] using permission))
        (fun byte permission => writable byte (by simpa only [referenceStable.wr] using permission)) sameRegion
      refine ⟨result, .ask sameAnswer replay, sameResult, ?_, ?_⟩
      · intro byte outside
        exact (otherBytes byte outside).trans (memAns_aussen sameAnswer written byte outside)
      · intro current request resume partialRun prior
        cases partialRun with
        | refl => exact ⟨included, written⟩
        | ask wasAnswered leftover =>
          rw [sameAnswer] at wasAnswered
          simp only [Option.some.injEq, Prod.mk.injEq] at wasAnswered
          obtain ⟨rfl, rfl⟩ := wasAnswered
          exact pending leftover prior

/-- A partial execution of a proved memory-only instruction can wait
    only on a memory request, or be at the exact next instruction. -/
theorem RunP.control_of_runM {start current : Res T} {before now after : Mem} {next : T}
    (part : RunP start before current now) (whole : RunM start before next after) :
    (current = .next next ∧ now = after) ∨
      ∃ request resume, current = .ask request resume ∧ request.special = false := by
  cases part.remaining whole with
  | next => exact Or.inl ⟨rfl, rfl⟩
  | @ask request resume _ _ _ _ _ answered _ =>
    refine Or.inr ⟨request, resume, rfl, ?_⟩
    cases request with
    | rd => rfl
    | wr => rfl
    | cas => rfl
    | sys => cases answered
    | fp => cases answered

/-- A partial run that has reached the end of the tree is a memory-only step. -/
theorem runP_runM {r r' : Res T} {m m1 : Mem} (h : RunP r m r' m1) : ∀ {t : T}, r' = .next t → RunM r m t m1 := by
  induction h with
  | refl r0 m0 =>
    intro t e
    subst e
    exact .next
  | ask hm _ ih =>
    intro t e
    exact .ask hm (ih e)

private theorem RunM.toPrefix {r : Res T} {before after : Mem} {target : T}
    (run : RunM r before target after) : RunP r before (.next target) after := by
  induction run with
  | next => exact .refl _ _
  | ask answer _ ih => exact .ask answer ih

/-- One more instruction at the end of a memory-only run. -/
theorem starM_snoc {n : Nat} {t t1 : T} {m m1 : Mem} (h : StarM n t m t1 m1) :
    ∀ {t2 : T} {m2 : Mem}, RunM (step t1) m1 t2 m2 → StarM (n + 1) t m t2 m2 := by
  induction h with
  | refl t0 m0 =>
    intro t2 m2 hs
    exact .next hs (.refl _ _)
  | next h1 _ ih =>
    intro t2 m2 hs
    exact .next h1 (ih hs)

/-- **The solo run of one thread**: from the boundary `(tb, mb)`, whole instructions answered by the memory alone,
    then the current instruction part of the way; `r` is the thread's state as the machine of threads holds it. -/
def SoloLauf (tb : T) (mb : Mem) (r : Res T) (m : Mem) : Prop :=
  ∃ (n : Nat) (t0 : T) (m0 : Mem), StarM n tb mb t0 m0 ∧ ((r = .next t0 ∧ m = m0) ∨ RunP (step t0) m0 r m)

private theorem RunM.permissions {r : Res T} {before after : Mem} {next : T}
    (run : RunM r before next after) : after.rd = before.rd ∧ after.wr = before.wr := by
  induction run with
  | next => exact ⟨rfl, rfl⟩
  | ask answered _ ih =>
    have stable := memAns_nurIn answered
    exact ⟨ih.1.trans stable.rd, ih.2.trans stable.wr⟩

theorem RunP.permissions {r r' : Res T} {before after : Mem}
    (run : RunP r before r' after) : after.rd = before.rd ∧ after.wr = before.wr := by
  induction run with
  | refl => exact ⟨rfl, rfl⟩
  | ask answered _ ih =>
    have stable := memAns_nurIn answered
    exact ⟨ih.1.trans stable.rd, ih.2.trans stable.wr⟩

/-- Complete memory instructions preserve the memory's permissions. -/
theorem StarM.permissions {n : Nat} {start finish : T} {before after : Mem}
    (path : StarM n start before finish after) : after.rd = before.rd ∧ after.wr = before.wr := by
  induction path with
  | refl => exact ⟨rfl, rfl⟩
  | next ran _ ih =>
    obtain ⟨rd, wr⟩ := RunM.permissions ran
    exact ⟨ih.1.trans rd, ih.2.trans wr⟩

/-- Any number of complete memory instructions in the actual IR
    consumes the corresponding restricted reference interval. Every
    effect still awaiting a response remains in the reference. -/
theorem StarM.align_reference {taken : Nat} {start current : T} {actual now : Mem}
    {reads writes : W → Prop} (part : StarM taken start actual current now) :
    ∀ {count : Nat} {reference finish : Mem} {target : T},
      IRReference count start reference target finish → taken ≤ count →
      (∀ byte, reference.rd byte = true → reads byte) →
      (∀ byte, reference.wr byte = true → reads byte ∧ writes byte) →
      MaskedAgreement reads writes reference actual →
      ∃ cut, IRReference (count - taken) current cut target finish ∧
        MaskedAgreement reads writes cut now ∧ cut.rd = reference.rd ∧ cut.wr = reference.wr ∧
        ∀ byte, ¬ writes byte → GleichAt now actual byte := by
  induction part with
  | refl =>
    intro count reference finish target ran _ _ _ agrees
    exact ⟨reference, by simpa only [Nat.sub_zero] using ran, agrees, rfl, rfl,
      fun byte _ => GleichAt.refl _ byte⟩
  | next executed _ tail =>
    intro count reference finish target ran within readable writable agrees
    cases ran with
    | start => exact (Nat.not_succ_le_zero _ within).elim
    | extend first remaining =>
      obtain ⟨cut, aligned, stable, unaffected⟩ := (RunM.toPrefix executed).align_reference first
        (blind_step _) readable writable agrees
      have finished := aligned.remaining_run first
      cases finished
      obtain ⟨rd, wr⟩ := aligned.permissions
      obtain ⟨endpoint, rest, memory, rd', wr', later⟩ := tail remaining (Nat.le_of_succ_le_succ within)
        (fun byte permission => readable byte (by simpa only [rd] using permission))
        (fun byte permission => writable byte (by simpa only [wr] using permission)) stable
      exact ⟨endpoint, by simpa only [Nat.succ_sub_succ_eq_sub] using rest,
        memory, rd'.trans rd, wr'.trans wr, fun byte outside => (later byte outside).trans (unaffected byte outside)⟩

/-- One successful restricted run characterizes all memory requests of
    the actual IR up to the corresponding instruction boundary. The
    statement quantifies over every partial instruction on that path. -/
theorem StarM.replay_on {count : Nat} {start target : T} {reference finish : Mem}
    {reads writes : W → Prop}
    (ran : StarM count start reference target finish)
    (readable : ∀ byte, reference.rd byte = true → reads byte)
    (writable : ∀ byte, reference.wr byte = true → reads byte ∧ writes byte)
    {actual : Mem} (agrees : MaskedAgreement reads writes reference actual) :
    ∃ result, StarM count start actual target result ∧ MaskedAgreement reads writes finish result ∧
      (∀ byte, ¬ writes byte → GleichAt result actual byte) ∧
      ∀ {taken : Nat} {instruction : T} {atInstruction current : Mem}
        {request : Op} {resume : Ans → Res T},
        StarM taken start actual instruction atInstruction → taken < count →
        RunP (step instruction) atInstruction (.ask request resume) current →
        (∀ byte, fussOp request byte → reads byte) ∧
        (schreibtOp request = true → ∀ byte, fussOp request byte → writes byte) := by
  induction ran generalizing actual with
  | refl =>
    exact ⟨actual, .refl _ _, agrees, fun byte _ => GleichAt.refl _ byte,
      fun _ impossible _ => (Nat.not_lt_zero _ impossible).elim⟩
  | next head _ ih =>
    obtain ⟨middle, executed, reached, otherBytes, requests⟩ :=
      (RunM.toPrefix head).replay_on (blind_step _) (by intro same; cases same)
        (by intro op resume same; cases same) readable writable agrees
    have replayedInstruction := runP_runM executed rfl
    obtain ⟨rd, wr⟩ := RunM.permissions head
    obtain ⟨result, ran, agreement, laterBytes, laterRequests⟩ := ih
      (fun byte granted => readable byte (by simpa only [rd] using granted))
      (fun byte granted => writable byte (by simpa only [wr] using granted)) reached
    refine ⟨result, .next replayedInstruction ran, agreement,
      fun byte outside => (laterBytes byte outside).trans (otherBytes byte outside), ?_⟩
    intro taken instruction atInstruction current request resume complete within pending
    cases complete with
    | refl => exact requests pending (by intro same; cases same)
    | next moved remaining =>
      obtain ⟨rfl, rfl⟩ := replayedInstruction.det moved.run
      exact laterRequests remaining (Nat.lt_of_succ_lt_succ within) pending

/-- The common memory permissions stay fixed through complete and
    partially executed instructions, independently of their number. -/
theorem SoloLauf.permissions {tb : T} {mb m : Mem} {r : Res T}
    (run : SoloLauf tb mb r m) : m.rd = mb.rd ∧ m.wr = mb.wr := by
  obtain ⟨_, _, _, complete, rest⟩ := run
  obtain ⟨rd, wr⟩ := StarM.permissions complete
  rcases rest with ⟨_, rfl⟩ | current
  · exact ⟨rd, wr⟩
  · exact ⟨current.permissions.1.trans rd, current.permissions.2.trans wr⟩

theorem soloLauf_start (tb : T) (mb : Mem) : SoloLauf tb mb (.next tb) mb :=
  ⟨0, tb, mb, .refl _ _, Or.inl ⟨rfl, rfl⟩⟩

/-- **The thread starts an instruction** (`.next t` becomes `step t`, no memory touched). -/
theorem SoloLauf.priv {tb t : T} {mb m : Mem} (h : SoloLauf tb mb (.next t) m) : SoloLauf tb mb (step t) m := by
  obtain ⟨n, t0, m0, hs, h⟩ := h
  rcases h with ⟨e, rfl⟩ | hp
  · cases e
    exact ⟨n, _, _, hs, Or.inr (.refl _ _)⟩
  · exact ⟨n + 1, _, _, starM_snoc hs (runP_runM hp rfl), Or.inr (.refl _ _)⟩

/-- **The memory answers the thread's request.** -/
theorem SoloLauf.ask {tb : T} {mb m m' : Mem} {o : Op} {k : Ans → Res T} {a : Ans}
    (h : SoloLauf tb mb (.ask o k) m) (ho : memAns m o = some (a, m')) : SoloLauf tb mb (k a) m' := by
  obtain ⟨n, t0, m0, hs, h⟩ := h
  rcases h with ⟨e, -⟩ | hp
  · cases e
  · exact ⟨n, t0, m0, hs, Or.inr (runP_snoc hp ho)⟩

/-- **At an instruction boundary the solo run is a memory-only run** of whole instructions. -/
theorem SoloLauf.starM {tb t : T} {mb m : Mem} (h : SoloLauf tb mb (.next t) m) : ∃ n, StarM n tb mb t m := by
  obtain ⟨n, t0, m0, hs, h⟩ := h
  rcases h with ⟨e, rfl⟩ | hp
  · cases e
    exact ⟨n, hs⟩
  · exact ⟨n + 1, starM_snoc hs (runP_runM hp rfl)⟩

/-- Inside a host-free IR region, memory remains in scope. A native
    floating answer uses the CPU relation, and terminal faults are excluded. -/
def HostFreeControl (reads writes : W → Prop) : Res T → Prop
  | .next _ => True
  | .ask request _ =>
    (∀ call, request ≠ .sys call) ∧ (∀ byte, fussOp request byte → reads byte) ∧
      (schreibtOp request = true → ∀ byte, fussOp request byte → writes byte)
  | .fault | .unk => False

/-- A proof over restricted memory determines every actual memory
    prefix before the region ends. A completed prefix agrees with the
    exact reference on all observed bytes, and preserves the rest. -/
theorem _root_.Gabbro.Stage0.Senke.BildLauf.IRReference.scoped_prefix {kernel : Kern} {reads writes : W → Prop}
    {count taken : Nat} {start pointer target : T} {reference finish memory actual : Mem}
    (proof : @IRReference kernel.withoutSyscalls count start reference target finish)
    (agreement : MaskedAgreement reads writes reference memory)
    (readable : ∀ byte, reference.rd byte = true → reads byte)
    (writable : ∀ byte, reference.wr byte = true → reads byte ∧ writes byte)
    (ran : StarM taken start memory pointer actual) (within : taken ≤ count) :
    (taken = count → pointer = target ∧ MaskedAgreement reads writes finish actual ∧
      ∀ byte, ¬ writes byte → GleichAt actual memory byte) ∧
    (taken < count → ∀ {control : Res T} {atControl : Mem},
      RunP (step pointer) actual control atControl → HostFreeControl reads writes control) := by
  letI : Kern := kernel.withoutSyscalls
  obtain ⟨cut, remaining, memoryEq, rd, wr, untouched⟩ :=
    StarM.align_reference ran proof within readable writable agreement
  constructor
  · intro completed
    subst taken
    rw [Nat.sub_self] at remaining
    cases remaining
    exact ⟨rfl, memoryEq, untouched⟩
  · intro inside control atControl waiting
    have left : 0 < count - taken := Nat.sub_pos_of_lt inside
    cases available : count - taken with
    | zero => exact (Nat.not_lt_zero _ (available ▸ left)).elim
    | succ unused =>
      have restOfReference : IRReference (Nat.succ unused) pointer cut target finish := by
        simpa only [available] using remaining
      cases restOfReference with
      | extend first rest =>
        obtain ⟨_, aligned, _, _⟩ := waiting.align_reference first (blind_step _)
          (fun byte granted => readable byte (by simpa only [rd] using granted))
          (fun byte granted => writable byte (by simpa only [wr] using granted)) memoryEq
        have permits := aligned.permissions
        have allowed := aligned.remaining_run first
        cases allowed with
        | next => trivial
        | @ask request resume start middle finish reply next answered continued =>
          cases reply with
          | none =>
            have rejected := (aligned.blind (blind_step _)).missing
            rw [rejected] at continued
            cases continued
          | some words =>
            have nonSyscall (call : Req) : request ≠ .sys call := by
              rintro rfl
              cases answered
            exact ⟨nonSyscall, memAns_confined (reads := reads) (writes := writes)
              (fun byte granted => readable byte (by simpa only [rd, permits.1] using granted))
              (fun byte granted => writable byte (by simpa only [wr, permits.2] using granted))
              answered⟩
        | sys unavailable _ => exact unavailable.elim
        | fp _ _ =>
          exact ⟨(fun _ no => nomatch no), (fun _ absent => False.elim absent), (fun refused => nomatch refused)⟩

end Gabbro.Stage0.Senke.BildMehr
