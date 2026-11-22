module

public import Stage0.Senke.Bild.Mehr.ImageTransition
import Stage0.Senke.Bild.Mehr.StartupOperands

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Stage0.Senke Runner Runner.IR Runner.Beweis Runner.Mach
  Gabbro.Stage0.Senke.BildMehr

/-- The actual thread exit retires one allocated slot. A completed call
    keeps its finished source head, and a declared non-returning call
    keeps the exact issuing head and request. -/
theorem ImageSlotsMatch.retire [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {E : Einheit (declOf output.compiled.unit)}
    {O : Orakel (declOf output.compiled.unit)} {history : List Ev}
    {before : Cfg imageTSO (Res T)} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {i : Nat} {req : Req} {resume : Ans → Res T}
    (slots : ImageSlotsMatch output E O history before state)
    (reached : ImageReach output E O (imageSourceStart E) state)
    (ready : before.ths[i]? = some (some (.ask (.sys req) resume)))
    (number : req.nr.toNat = NR_EXIT)
    (matching : FertigG state.m i ∨ ImageNeverRequest output O state i req) :
    let after : Cfg imageTSO (Res T) := ⟨before.ms, before.ths.set i none⟩
    ProcessStep imageTSO actI before [(i, req, none)] after ∧
      ImageSlotsMatch output E O (history ++ [(i, req, none)]) after state := by
  intro after
  refine ⟨.exit ready rfl number, ?_, ?_⟩
  · intro j
    simpa only [after, List.length_set] using slots.1 j
  · intro j retired
    by_cases same : j = i
    · subst j
      rcases matching with finished | declared
      · exact Or.inl finished
      · refine Or.inr ⟨state, req, history.filter (fun event => event.1 == i),
          reached, .start, rfl, declared, number, ?_⟩
        simp only [List.filter_append, List.filter_cons, beq_self_eq_true, ite_true, List.filter_nil]
    · have unchanged : before.ths[j]? = some none := by
        simpa only [after, List.getElem?_set_ne (Ne.symm same)] using retired
      obtain finished | ⟨atExit, call, earlier, fromStart, since, sameHead, matched, kind, last⟩ :=
        slots.2 j unchanged
      · exact Or.inl finished
      · refine Or.inr ⟨atExit, call, earlier, fromStart, since, sameHead, matched, kind, ?_⟩
        simp only [List.filter_append, List.filter_cons, beq_eq_false_iff_ne.mpr (Ne.symm same),
          Bool.false_eq_true, ite_false, List.filter_nil, List.append_nil, last]

/-- A real thread exit leaves the previously matched external call
    history intact. The exit is already accounted for by the slot proof. -/
theorem ImageForeignTrace.retire {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {history : List Ev}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe} {i : Nat} {req : Req}
    (matched : ImageForeignTrace output history state) (exit : req.nr.toNat = NR_EXIT) :
    ImageForeignTrace output (history ++ [(i, req, none)]) state := by
  have internal : imageExternalEvent (i, req, none) = false := by
    simp only [imageExternalEvent, exit, true_or, or_true, decide_true, Bool.not_true]
  unfold ImageForeignTrace at matched ⊢
  simpa only [List.filter_append, List.filter_cons, internal, Bool.false_eq_true, ite_false,
    List.filter_nil, List.append_nil] using matched

private theorem image_stop_const [Kern] {before : Cfg imageTSO (Res T)} {i : Nat} {pointer : T}
    {slots destination value : Nat}
    (running : before.ths[i]? = some (some (.next pointer)))
    (code : CodeAt (before.ms.1.view i) pointer.pc [ci 1 destination value 0])
    (frame : FrameOK (before.ms.1.view i) pointer.fp slots)
    (inside : destination < slots) (slotFits : slots < 2 ^ 31) (valueFits : value < 2 ^ 31) :
    ∃ after : imageTSO.St,
      ProcessPrefix imageTSO actI before [] 5
        ⟨after, before.ths.set i (some (.next (nxt pointer)))⟩ ∧
      after.1.view i = Mem.write (before.ms.1.view i) (slot pointer.fp (BitVec.ofNat 64 destination)) 8
        (BitVec.ofNat 64 value).toNat := by
  have first := code 0 (by simp)
  have instruction : InsAt (before.ms.1.view i) pointer.pc 1 (II.f destination) (II.f value) (II.f 0) := by
    simpa only [List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero, ci] using first
  have address : sx (II.f destination) = BitVec.ofNat 64 destination := sx_nat (inside.trans slotFits)
  have writable : Mem.all before.ms.1.m.wr (slot pointer.fp (sx (II.f destination))) 8 = true := by
    rw [address, ← foldl_wr (before.ms.1.buf i) before.ms.1.m]
    exact frame.wr destination inside
  obtain ⟨after, steps, _, view, _⟩ := tso_const_prefix (before := imageToTSO before) running instruction writable
  exact ⟨after, tso_silent_prefix_image steps rfl, by rw [view, address, sx_nat valueFits]⟩

/-- The emitted stop sequence stores its request and then issues the exact
    process-wide exit. The actual runner reads the issuing TSO view. -/
theorem image_emitted_stop [Kern] {before : Cfg imageTSO (Res T)} {i : Nat} {pointer : T}
    {slots scratch status : Nat} (running : before.ths[i]? = some (some (.next pointer)))
    (code : CodeAt (before.ms.1.view i) pointer.pc (stopC status scratch))
    (far : CodeFar pointer.pc 3 pointer.fp slots)
    (frame : FrameOK (before.ms.1.view i) pointer.fp slots)
    (room : scratch + 8 ≤ slots) (slotsFit : slots < 2 ^ 31) (statusFit : status < 2 ^ 31) :
    ∃ armed : Cfg imageTSO (Res T), ∃ req resume,
      ProcessPrefix imageTSO actI before [] 21 armed ∧
      armed.ths[i]? = some (some (.ask (.sys req) resume)) ∧
      req.nr.toNat = NR_EXIT_GROUP ∧ req.a1 = BitVec.ofNat 64 status := by
  let m := before.ms.1.view i
  let pc := pointer.pc
  let fp := pointer.fp
  let header : List II := [ci 1 scratch 231 0]
  let statusCode : List II := [ci 1 ((scratch + 1 : Nat) : Int) status 0]
  let call : List II := [ci 23 ((scratch + 7 : Nat) : Int) scratch 0]
  have parts : CodeAt m pc (header ++ (statusCode ++ call)) := code
  have headerCode := codeAt_left parts
  obtain ⟨first, wroteNumber, view1⟩ := image_stop_const running headerCode frame (by omega) slotsFit (by decide)
  let next := nxt pointer
  let middle : Cfg imageTSO (Res T) := ⟨first, before.ths.set i (some (.next next))⟩
  have iWithin := (List.getElem?_eq_some_iff.mp running).1
  have nextReady : middle.ths[i]? = some (some (.next next)) := List.getElem?_set_self iWithin
  have write1 : Agree fp 0 slots m (first.1.view i) := by
    rw [view1]
    exact agree_write frame.room (Nat.zero_le _) (by omega) _
  have frame1 := frame.agree write1
  have remain : CodeAt (first.1.view i) next.pc (statusCode ++ call) :=
    (codeAt_right parts).agree write1 (codeFar_right (n := 1) (k := 2) far)
  obtain ⟨second, wroteStatus, view2⟩ := image_stop_const nextReady (codeAt_left remain) frame1
    (by omega) slotsFit statusFit
  let sys := nxt next
  let decoded : Cfg imageTSO (Res T) := ⟨second, before.ths.set i (some (.next sys))⟩
  have atSys : decoded.ths[i]? = some (some (.next sys)) := List.getElem?_set_self iWithin
  have write2 : Agree fp 0 slots (first.1.view i) (second.1.view i) := by
    rw [view2]
    exact agree_write frame.room (Nat.zero_le _) (by omega) _
  have frame2 := frame1.agree write2
  have farSys : CodeFar sys.pc 1 fp slots := by
    change CodeFar ((pc + 16) + 16) 1 fp slots
    rw [BitVec.add_assoc]
    exact codeFar_right (n := 2) (k := 1) far
  have codeSys : CodeAt (second.1.view i) sys.pc call := (codeAt_right remain).agree write2 farSys
  have instruction : InsAt (second.1.view i) sys.pc 23 (II.f ((scratch + 7 : Nat) : Int)) (II.f scratch) (II.f 0) := by
    have decoded := codeSys 0 (by simp only [call, List.length_singleton]; decide)
    simpa only [call, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero, ci] using decoded
  have address : sx (II.f scratch) = BitVec.ofNat 64 scratch := sx_nat (by omega)
  have numberRead : (second.1.view i).rd64 (slot fp (BitVec.ofNat 64 scratch)) = some (231 : W) := by
    rw [view2, rd64_write_far (slot_far frame.room (by omega) (by omega) (by omega)), view1]
    exact rd64_wr64 (wr64_some (frame.wr scratch (by omega))) (frame.rd scratch (by omega))
  have statusRead : (second.1.view i).rd64 (slot fp (BitVec.ofNat 64 (scratch + 1))) =
      some (BitVec.ofNat 64 status) := by
    rw [view2]
    exact rd64_wr64 (wr64_some (frame1.wr _ (by omega))) (frame1.rd _ (by omega))
  have arg (offset : Nat) (inside : offset < 7) : ∃ word,
      (second.1.view i).rd64 (slot fp (BitVec.ofNat 64 (scratch + offset))) = some word := by
    exact ⟨_, by simp only [Mem.rd64, frame2.rd _ (by omega), ite_true]; rfl⟩
  obtain ⟨a2, read2⟩ := arg 2 (by decide)
  obtain ⟨a3, read3⟩ := arg 3 (by decide)
  obtain ⟨a4, read4⟩ := arg 4 (by decide)
  obtain ⟨a5, read5⟩ := arg 5 (by decide)
  obtain ⟨a6, read6⟩ := arg 6 (by decide)
  have request := tso_sys_prefix (before := imageToTSO decoded) atSys instruction
    (by rw [address]; exact numberRead) (by rw [address, ← show BitVec.ofNat 64 8 = 8 by rfl, slot_plus]; exact statusRead)
    (by rw [address, ← show BitVec.ofNat 64 16 = 16 by rfl, slot_plus]; exact read2)
    (by rw [address, ← show BitVec.ofNat 64 24 = 24 by rfl, slot_plus]; exact read3)
    (by rw [address, ← show BitVec.ofNat 64 32 = 32 by rfl, slot_plus]; exact read4)
    (by rw [address, ← show BitVec.ofNat 64 40 = 40 by rfl, slot_plus]; exact read5)
    (by rw [address, ← show BitVec.ofNat 64 48 = 48 by rfl, slot_plus]; exact read6)
  let req : Req := ⟨231, BitVec.ofNat 64 status, a2, a3, a4, a5, a6⟩
  let resume : Ans → Res T := fun reply => opt reply fun pair => wr64 (slot fp (sx (II.f ((scratch + 7 : Nat) : Int))))
    pair.1 (nxt sys)
  let armed : Cfg imageTSO (Res T) := ⟨second, before.ths.set i (some (.ask (.sys req) resume))⟩
  have ready : armed.ths[i]? = some (some (.ask (.sys req) resume)) := List.getElem?_set_self iWithin
  have numberThenStatus : ProcessPrefix imageTSO actI before [] 10 decoded := by
    simpa only [middle, decoded, List.set_set, List.nil_append] using wroteNumber.trans wroteStatus
  have silent : ProcessPrefix imageTSO actI decoded [] 11 armed := by
    simpa only [decoded, armed, req, resume, List.set_set] using tso_silent_prefix_image request rfl
  exact ⟨armed, req, resume, numberThenStatus.trans silent, ready, rfl, rfl⟩

/-- A reached hardware failure explains the real process exit with its
    exact request and status. All prior microsteps are silent. -/
theorem image_hardware_exit [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {O : Orakel (declOf output.compiled.unit)}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe} {history : List Ev}
    {before armed : Cfg imageTSO (Res T)} {steps i : Nat} {req : Req} {resume : Ans → Res T}
    {cause : Hardware (declOf output.compiled.unit).mitRuhe}
    (silent : ProcessPrefix imageTSO actI before [] steps armed)
    (ready : armed.ths[i]? = some (some (.ask (.sys req) resume)))
    (number : req.nr.toNat = NR_EXIT_GROUP) (status : req.a1 = BitVec.ofNat 64 (hwCode cause))
    (alive : state.lebt i = true) (matched : ImageHardwareCause O.mitRuhe output.image.passes state.m i cause) :
    Tr imageTSO actI before [(i, req, none)] (.exit req.a1) (steps + 1) ∧
      ImageStopMatches output O state history [(i, req, none)] (.exit req.a1) := by
  have stop : Tr imageTSO actI armed [(i, req, none)] (.exit req.a1) 1 := .exitGroup ready rfl number
  exact ⟨by simpa only [List.nil_append, Nat.add_comm] using silent.prepend stop,
    ⟨i, req, rfl, number, rfl, .inr (.inr (.inl ⟨alive, cause, matched, status⟩))⟩⟩

/-- Connect an emitted hardware stop to the exact rendered status of the
    corresponding reached source head. -/
theorem image_emitted_hardware_exit [Kern] {src : String} {reserve : Nat} {options : Profil.Options}
    {output : Emitted src reserve options} {O : Orakel (declOf output.compiled.unit)}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe} {history : List Ev}
    {before : Cfg imageTSO (Res T)} {i slots scratch : Nat} {pointer : T}
    {cause : Hardware (declOf output.compiled.unit).mitRuhe}
    (running : before.ths[i]? = some (some (.next pointer)))
    (code : CodeAt (before.ms.1.view i) pointer.pc (stopC (hwCode cause) scratch))
    (far : CodeFar pointer.pc 3 pointer.fp slots) (frame : FrameOK (before.ms.1.view i) pointer.fp slots)
    (room : scratch + 8 ≤ slots) (slotsFit : slots < 2 ^ 31)
    (alive : state.lebt i = true) (matched : ImageHardwareCause O.mitRuhe output.image.passes state.m i cause) :
    ∃ req, Tr imageTSO actI before [(i, req, none)] (.exit req.a1) 22 ∧
      ImageStopMatches output O state history [(i, req, none)] (.exit req.a1) := by
  have statusFit : hwCode cause < 2 ^ 31 := by cases cause <;> simp only [hwCode] <;> decide
  obtain ⟨_, req, _, silent, ready, number, status⟩ :=
    image_emitted_stop running code far frame room slotsFit statusFit
  exact ⟨req, image_hardware_exit silent ready number status alive matched⟩

end Gabbro.Stage0
