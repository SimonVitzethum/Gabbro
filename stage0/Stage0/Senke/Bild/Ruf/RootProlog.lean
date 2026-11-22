module

public import Stage0.Senke.Bild.Ruf.RootEntry
import Stage0.Senke.Bild.Ruf.RootExit
import Stage0.Senke.Images.CheckSpawn
import Stage0.Senke.Bild.StartG
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Stage0.Senke
  Gabbro.Stage0.Senke.BildMehr Runner Runner.IR Runner.Beweis Runner.Mach

variable {src : String} {reserve : Nat} {options : Profil.Options}

/-- The declared initial memory discharges the entry obligation at the
    exact initial head with its serialized arguments. The theorem is
    fixed to the start machine, so a later call needs its own entry duty. -/
theorem Emitted.initial_root_head (output : Emitted src reserve options)
    {E : Einheit (declOf output.compiled.unit)} (unit : ImageModelUnit output E)
    {thread : Faden} {root : Σ f : (declOf output.compiled.unit).Fn,
      Env (declOf output.compiled.unit) ((declOf output.compiled.unit).params f)}
    (declared : E.starts[thread]? = some root) :
    let entered := ((imageSourceStart E).m.faeden thread).kopf
    entered.f = some root.1 ∧ entered.s0 = worldR (E.sp0.welt []) ∧ HEq entered.rho (envR root.2) ∧
      ReqAmEintritt E.P.mitRuhe entered.f entered.s0 entered.rho := by
  have initial : initRuhe E.starts thread = ⟨some root.1, envR root.2⟩ := by
    unfold initRuhe
    rw [declared]
  have exactHead := BildLauf.rufStartG_faeden_von E.P.mitRuhe (speicherR E.sp0) initial
  dsimp only
  change let entered := ((RufStartG E.P.mitRuhe (speicherR E.sp0) (initRuhe E.starts)).faeden thread).kopf
    entered.f = some root.1 ∧ entered.s0 = worldR (E.sp0.welt []) ∧ HEq entered.rho (envR root.2) ∧
      ReqAmEintritt E.P.mitRuhe entered.f entered.s0 entered.rho
  rw [exactHead]
  refine ⟨rfl, rfl, HEq.rfl, (req_mitRuhe_iff E.P root.1 (E.sp0.welt []) root.2).mpr ?_⟩
  have listed := List.mem_of_getElem? declared
  rw [unit.starts] at listed
  rw [unit.program, unit.memory]
  exact output.startRequires root listed

/-- A startup requirement reads only carriers separated from the other
    declared roots. Its checked initial values remain available when
    the host schedules the root's prologue after another thread runs. -/
theorem Emitted.root_requires_local (output : Emitted src reserve options)
    {E : Einheit (declOf output.compiled.unit)} (hardware : RootNativeFloat.Hardware)
    (accepted : akzeptiertX_pruefer.akzeptiert E output.fsA.1 output.lsA.1 output.csA.1 = true)
    {root : (declOf output.compiled.unit).Fn} (declared : root ∈ E.ws)
    {carrier : (declOf output.compiled.unit).Tab ⊕ (declOf output.compiled.unit).Glob}
    (reads : carrier ∈ (E.P.requires root).orte) : Getrennt E.P output.fsA.1 E.ws carrier := by
  have valid := (akzeptiertX_pruefer.korrekt E output.fsA output.lsA output.csA hardware accepted).1
  have lockless := (valid.wurzeln root declared).1
  have unguarded (lock : (declOf output.compiled.unit).Lock) (guard : Bewacht carrier lock) : False := by
    have allowed := (E.P.requires root).orte_darf carrier reads
    have held : Res.held lock ∈ Signatur.anfang _ ((declOf output.compiled.unit).signatur root) := by
      cases carrier with
      | inl table => exact allowed (.inl lock) guard
      | inr global => exact allowed (.inl lock) guard
    have signed := (held_anfang _ lock).mp held
    rw [show ((declOf output.compiled.unit).signatur root).haelt = [] from lockless] at signed
    exact List.not_mem_nil signed
  rcases (valid.fuss root).1 carrier (fuss_req E.P root reads) with localOrGuard | ⟨lock, guarded, _⟩ | shared
  · rcases Bool.or_eq_true.mp localOrGuard with signature | localRead
    · obtain ⟨lock, guard, _⟩ := sigB_ok signature
      exact (unguarded lock guard).elim
    · exact @of_decide_eq_true _ (Classical.propDecidable _) localRead
  · exact (unguarded lock guarded).elim
  · exact ((shared.2.1 root).1 reads).elim

/-- Main enters the same depth initialization protocol through its
    own boot frame after the emitted clone sites. -/
theorem Emitted.main_depth_start [Kern] (output : Emitted src reserve options)
    {before : Cfg imageTSO (Res T)}
    (loaded : BytesAt (before.ms.1.view 0) codeBase (output.image.code.flatMap encII)) :
    let pointer : T := ⟨BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length)), BitVec.ofNat 64 output.image.fp0⟩
    before.ths[0]? = some (some (.next pointer)) →
    FrameOK (before.ms.1.view 0) pointer.fp output.image.Ks →
    ∃ after : imageTSO.St,
      ProcessPrefix imageTSO actI before [] 5
        ⟨after, before.ths.set 0 (some (.next (nxt pointer)))⟩ ∧
      after.1.m = before.ms.1.m ∧
      after.1.view 0 = Mem.write (before.ms.1.view 0)
        (slot pointer.fp (BitVec.ofNat 64 2)) 8 (output.image.depth + 1) ∧
      ∀ other, other ≠ 0 → after.1.view other = before.ms.1.view other := by
  intro pointer running frame
  obtain ⟨stub, header, depth, _, _⟩ := output.main_stub_code loaded
  obtain ⟨after, run, shared, wrote, others, _⟩ :=
    image_depth_setup (before := before) stub header depth running frame
  exact ⟨after, run, shared, wrote, others⟩

private theorem function_depth_guard [Kern] (output : Emitted src reserve options)
    {memory : Mem} (loaded : BytesAt memory codeBase (output.image.code.flatMap encII))
    (fn : (declOf output.compiled.unit).Fn) :
    let pc := BitVec.ofNat 64 (output.image.A fn)
    let scratch := (functionFrame output.compiled.program fn).canonicalResult
    ∃ rest, CodeAt memory pc (guardC 2 105 scratch ++ rest) := by
  intro pc scratch
  obtain ⟨code, top, lowered, decoded, _, _⟩ := output.relocated_function_code loaded fn
  simp only [lowFun, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at lowered
  obtain ⟨req, _, ensures, _, body, _, snapshot, _, shape, _⟩ := lowered
  rw [← shape] at decoded
  let layout := functionFrame output.compiled.program fn
  refine ⟨req.1 ++ guardC scratch 101 scratch ++
    relocateC FB layout.ensReserved layout.parameterWords ++ snapshot ++
    relocateC layout.ensParams (layout.bodyReserved - layout.ensReserved) layout.parameterWords ++ body.1, ?_⟩
  simpa only [List.append_assoc, scratch, layout] using decoded

/-- A zero depth word at an emitted function entry branches directly
    to the stop for that function's model depth exhaustion. -/
theorem Emitted.depth_guard_zero [Kern] (output : Emitted src reserve options)
    {before : Cfg imageTSO (Res T)} {thread : Nat} {fp : W} (fn : (declOf output.compiled.unit).Fn)
    (loaded : BytesAt (before.ms.1.view thread) codeBase (output.image.code.flatMap encII))
    (oracle : Orakel (declOf output.compiled.unit)) (world : World (declOf output.compiled.unit))
    (arguments : Env (declOf output.compiled.unit) ((declOf output.compiled.unit).params fn)) :
    let pc := BitVec.ofNat 64 (output.image.A fn)
    let scratch := (functionFrame output.compiled.program fn).canonicalResult
    before.ths[thread]? = some (some (.next ⟨pc, fp⟩)) →
    (before.ms.1.view thread).rd64 (slot fp (BitVec.ofNat 64 2)) = some 0 →
    ProcessPrefix imageTSO actI before [] 5
      ⟨before.ms, before.ths.set thread (some (.next ⟨pc + 32, fp⟩))⟩ ∧
    CodeAt (before.ms.1.view thread) (pc + 32) (stopC (logikCode (.abstieg fn)) scratch) ∧
    rufRumpf output.compiled.program oracle output.image.passes 0 fn world arguments = .logik (.abstieg fn) := by
  intro pc scratch running zero
  obtain ⟨_, decoded⟩ := function_depth_guard output loaded fn
  have guard : CodeAt (before.ms.1.view thread) pc (guardC 2 105 scratch) :=
    codeAt_left decoded
  have branch := tso_guard_fail (before := imageToTSO before) running guard
    (by rw [show sx (II.f ((2 : Nat) : Int)) = BitVec.ofNat 64 2 by decide]; exact zero)
  refine ⟨tso_silent_prefix_image branch rfl, ?_, ?_⟩
  · have tail := codeAt_right (a := [ci 19 ((2 : Nat) : Int) 32 0, ci 18 64 0 0]) (by
      simpa only [guardC] using guard : CodeAt (before.ms.1.view thread) pc
        ([ci 19 ((2 : Nat) : Int) 32 0, ci 18 64 0 0] ++ stopC 105 scratch))
    exact tail
  · simp only [rufRumpf]

/-- The emitted guard and its emitted exit sequence report exactly the
    bounded call semantics' depth exhaustion. -/
theorem Emitted.depth_guard_exits [Kern] (output : Emitted src reserve options)
    {before : Cfg imageTSO (Res T)} {thread slots : Nat} {fp : W} (fn : (declOf output.compiled.unit).Fn)
    (loaded : BytesAt (before.ms.1.view thread) codeBase (output.image.code.flatMap encII))
    (oracle : Orakel (declOf output.compiled.unit)) (world : World (declOf output.compiled.unit))
    (arguments : Env (declOf output.compiled.unit) ((declOf output.compiled.unit).params fn)) :
    let pc := BitVec.ofNat 64 (output.image.A fn)
    let scratch := (functionFrame output.compiled.program fn).canonicalResult
    before.ths[thread]? = some (some (.next ⟨pc, fp⟩)) →
    (before.ms.1.view thread).rd64 (slot fp (BitVec.ofNat 64 2)) = some 0 →
    CodeFar (pc + 32) 3 fp slots → FrameOK (before.ms.1.view thread) fp slots →
    scratch + 8 ≤ slots → slots < 2 ^ 31 →
    ∃ req, Tr imageTSO actI before [(thread, req, none)]
        (.exit (BitVec.ofNat 64 (logikCode (.abstieg fn)))) 27 ∧
      req.nr.toNat = NR_EXIT_GROUP ∧ req.a1 = BitVec.ofNat 64 (logikCode (.abstieg fn)) ∧
      rufRumpf output.compiled.program oracle output.image.passes 0 fn world arguments = .logik (.abstieg fn) := by
  intro pc scratch running zero far frame room fit
  obtain ⟨guard, code, semantic⟩ := output.depth_guard_zero fn loaded oracle world arguments running zero
  let failed : Cfg imageTSO (Res T) :=
    ⟨before.ms, before.ths.set thread (some (.next ⟨pc + 32, fp⟩))⟩
  have atStop : failed.ths[thread]? = some (some (.next ⟨pc + 32, fp⟩)) :=
    List.getElem?_set_self (List.getElem?_eq_some_iff.mp running).1
  have statusFit : logikCode (.abstieg fn) < 2 ^ 31 := by simp only [logikCode]; decide
  obtain ⟨armed, req, resume, setup, ready, number, status⟩ :=
    image_emitted_stop (before := failed) atStop code far frame room fit statusFit
  have terminal : Tr imageTSO actI armed [(thread, req, none)] (.exit req.a1) 1 := .exitGroup ready rfl number
  have quiet : ProcessPrefix imageTSO actI before [] 26 armed := guard.trans setup
  refine ⟨req, ?_, number, status, semantic⟩
  simpa only [List.nil_append, status] using quiet.prepend terminal

/-- The emitted depth guard at the matched callee is a named image
    resource stop, justified by the exact number of suspended callers. -/
theorem Emitted.depth_guard_named [Kern] (output : Emitted src reserve options)
    {before : Cfg imageTSO (Res T)} {thread slots : Nat} {fp : W}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe} {history : List Ev}
    (fn : (declOf output.compiled.unit).Fn)
    (exhausted : ImageDepthCause output state thread fn)
    (loaded : BytesAt (before.ms.1.view thread) codeBase (output.image.code.flatMap encII))
    (oracle : Orakel (declOf output.compiled.unit)) (world : World (declOf output.compiled.unit))
    (arguments : Env (declOf output.compiled.unit) ((declOf output.compiled.unit).params fn)) :
    let pc := BitVec.ofNat 64 (output.image.A fn)
    let scratch := (functionFrame output.compiled.program fn).canonicalResult
    before.ths[thread]? = some (some (.next ⟨pc, fp⟩)) →
    (before.ms.1.view thread).rd64 (slot fp (BitVec.ofNat 64 2)) = some 0 →
    CodeFar (pc + 32) 3 fp slots → FrameOK (before.ms.1.view thread) fp slots →
    scratch + 8 ≤ slots → slots < 2 ^ 31 →
    ∃ req, Tr imageTSO actI before [(thread, req, none)] (.exit (BitVec.ofNat 64 105)) 27 ∧
      ImageStopMatches output oracle state history [(thread, req, none)] (.exit (BitVec.ofNat 64 105)) := by
  intro pc scratch running zero far frame room fit
  obtain ⟨req, run, number, status, _⟩ :=
    output.depth_guard_exits fn loaded oracle world arguments running zero far frame room fit
  have code : req.a1 = BitVec.ofNat 64 105 := status
  exact ⟨req, run, thread, req, rfl, number, congrArg Ende.exit code.symm,
    Or.inr (Or.inr (Or.inr (Or.inr ⟨fn, exhausted, code⟩)))⟩

/-- At an original root's depth the actual emitted guard reaches the
    precondition code without going through the depth-exhaustion stop. -/
theorem Emitted.root_depth_guard_pass [Kern] (output : Emitted src reserve options)
    {before : Cfg imageTSO (Res T)} {thread : Nat} {fp : W} (fn : (declOf output.compiled.unit).Fn)
    (loaded : BytesAt (before.ms.1.view thread) codeBase (output.image.code.flatMap encII)) :
    let pc := BitVec.ofNat 64 (output.image.A fn)
    before.ths[thread]? = some (some (.next ⟨pc, fp⟩)) →
    (before.ms.1.view thread).rd64 (slot fp (BitVec.ofNat 64 2)) = some (BitVec.ofNat 64 output.image.depth) →
    ∃ rest,
      ProcessPrefix imageTSO actI before [] 7
        ⟨before.ms, before.ths.set thread (some (.next ⟨pc + BitVec.ofNat 64 (16 * 5), fp⟩))⟩ ∧
      CodeAt (before.ms.1.view thread) (pc + BitVec.ofNat 64 (16 * 5)) rest := by
  intro pc running word
  obtain ⟨rest, decoded⟩ := function_depth_guard output loaded fn
  obtain ⟨_, _, _, layout, _, _, _, _⟩ := bild_lage output.emission output.funktionen_voll
    (fun base bound => layU_in output.compiled.unit output.tor base bound)
    (fun base => layU_dis output.compiled.unit output.tor base)
    (fun base => by simp only [layU]; omega)
    (fun base => layU_sync output.compiled.unit output.tor base)
  have fits : output.image.depth < 2 ^ 64 :=
    (Nat.lt_succ_self _).trans (layout.startLimits.2.1.trans (by decide : 2 ^ 31 < 2 ^ 64))
  have nonzero : BitVec.ofNat 64 output.image.depth ≠ 0 := by
    intro zero
    have equal := congrArg BitVec.toNat zero
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits] at equal
    exact (Nat.ne_of_gt layout.depth_pos) equal
  have guard : CodeAt (before.ms.1.view thread) pc
      (guardC 2 105 (functionFrame output.compiled.program fn).canonicalResult) := codeAt_left decoded
  have slotIndex : sx (II.f ((2 : Nat) : Int)) = BitVec.ofNat 64 2 := by decide
  have operand : (before.ms.1.view thread).rd64 (slot fp (sx (II.f ((2 : Nat) : Int)))) =
      some (BitVec.ofNat 64 output.image.depth) := by rw [slotIndex]; exact word
  have stepped := tso_guard_pass (before := imageToTSO before) running guard
    operand nonzero
  have suffix := codeAt_right decoded
  have size : (guardC 2 105 (functionFrame output.compiled.program fn).canonicalResult).length = 5 := rfl
  rw [size] at suffix
  exact ⟨rest, tso_silent_prefix_image stepped rfl, suffix⟩

/-- A declared child starts with its actual arguments and passes the
    function's depth check in the same silent process prefix. -/
theorem Emitted.child_prologue_prefix [Kern] (output : Emitted src reserve options)
    {E : Einheit (declOf output.compiled.unit)} (unit : ImageModelUnit output E)
    {before : Cfg imageTSO (Res T)} {index : Nat}
    {root : Σ f : (declOf output.compiled.unit).Fn, Env _ ((declOf output.compiled.unit).params f)}
    (declared : output.starts[index]? = some root) {history : List Ev}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe} :
    let entry : T := ⟨BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length + startLen + startLen * index)),
      BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * (index + 1)))⟩
    let target := BitVec.ofNat 64 (output.image.A root.1)
    let frame := slot entry.fp (BitVec.ofNat 64 FB)
    let prologue := target + BitVec.ofNat 64 (16 * 5)
    before.ths[index + 1]? = some (some (.next entry)) →
    ImageRootPhase output E history (before.ms.1.view (index + 1)) (index + 1) (.next entry) state →
    ∃ after : imageTSO.St, ∃ rest,
      ProcessPrefix imageTSO actI before [] 37
        ⟨after, before.ths.set (index + 1) (some (.next ⟨prologue, frame⟩))⟩ ∧
      after.1.m = before.ms.1.m ∧
      (∀ other, other ≠ index + 1 → after.1.view other = before.ms.1.view other) ∧
      GleichAuf (fun byte => ¬ imageStackFootprint output (index + 1) byte)
        (after.1.view (index + 1)) (before.ms.1.view (index + 1)) ∧
      (∀ world, WeltAt (before.ms.1.view (index + 1)) output.image.Y world →
        WeltAt (after.1.view (index + 1)) output.image.Y world) ∧
      FrameOK (after.1.view (index + 1)) frame (output.image.Ks - FB) ∧
      EnvAt output.image.Y (after.1.view (index + 1)) frame root.2 ∧
      (∀ footprint : Nat → W → Prop,
        (∀ byte, imageStackFootprint output (index + 1) byte →
          footprint (index + 1) byte ∧ ∀ other, footprint other byte → other = index + 1) →
        PrivateBuffers footprint before.ms.1 → PrivateBuffers footprint after.1) ∧
      CodeAt (after.1.view (index + 1)) prologue rest := by
  intro entry target frame prologue running phase
  obtain ⟨after, call, shared, otherViews, agreement, world, permissions, environment, _, _, depth, loaded, buffers, _⟩ :=
    output.child_body_from_root_phase unit declared running phase
  have inside := (List.getElem?_eq_some_iff.mp running).1
  let entered : Cfg imageTSO (Res T) :=
    ⟨after, before.ths.set (index + 1) (some (.next ⟨target, frame⟩))⟩
  have ready : entered.ths[index + 1]? = some (some (.next ⟨target, frame⟩)) :=
    List.getElem?_set_self inside
  obtain ⟨rest, passed, code⟩ := output.root_depth_guard_pass (before := entered) root.1 loaded ready depth
  refine ⟨after, rest, ?_, shared, otherViews, agreement, world, permissions, environment, buffers, code⟩
  simpa only [entered, List.set_set, List.nil_append] using call.trans passed

/-- Once startup has reached the emitted main stub, that thread enters
    its actual relocated function with the checked startup arguments.
    The prefix leaves the shared memory and all other views intact. -/
theorem Emitted.main_prologue_prefix [Kern] (output : Emitted src reserve options)
    {E : Einheit (declOf output.compiled.unit)} (unit : ImageModelUnit output E)
    {before : Cfg imageTSO (Res T)} {history : List Ev}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe} :
    let site := output.mainStartSite
    let entry := site.entry
    let target := BitVec.ofNat 64 (output.image.A output.compiled.main)
    let frame := slot entry.fp (BitVec.ofNat 64 FB)
    let prologue := target + BitVec.ofNat 64 (16 * 5)
    before.ths[0]? = some (some (.next entry)) →
    ImageRootPhase output E history (before.ms.1.view 0) 0 (.next entry) state →
    ∃ after : imageTSO.St, ∃ rest,
      ProcessPrefix imageTSO actI before [] 37
        ⟨after, before.ths.set 0 (some (.next ⟨prologue, frame⟩))⟩ ∧
      after.1.m = before.ms.1.m ∧
      (∀ other, other ≠ 0 → after.1.view other = before.ms.1.view other) ∧
      GleichAuf (fun byte => ¬ imageStackFootprint output 0 byte)
        (after.1.view 0) (before.ms.1.view 0) ∧
      (∀ world, WeltAt (before.ms.1.view 0) output.image.Y world → WeltAt (after.1.view 0) output.image.Y world) ∧
      FrameOK (after.1.view 0) frame (output.image.Ks - FB) ∧
      EnvAt output.image.Y (after.1.view 0) frame output.args ∧
      (∀ footprint : Nat → W → Prop,
        (∀ byte, imageStackFootprint output 0 byte →
          footprint 0 byte ∧ ∀ other, footprint other byte → other = 0) →
        PrivateBuffers footprint before.ms.1 → PrivateBuffers footprint after.1) ∧
      CodeAt (after.1.view 0) prologue rest := by
  intro site entry target frame prologue running phase
  have declared : E.starts[0]? = some ⟨output.compiled.main, output.args⟩ := by
    rw [unit.starts]
    rfl
  have pastLoader : (Res.next entry : Res T) ≠ Runner.Beweis.t4 := by
    intro equal
    cases equal
  obtain ⟨bytes, permissions, arguments⟩ := ImageRootPhase.payload declared phase (.inr pastLoader)
  obtain ⟨after, call, shared, views, writes, newFrame, words, _, _, depth, code, buffers, _⟩ :=
    site.body_prefix bytes running permissions arguments
  have valid := fun τ x => mainEnv_valid output.image.Y _ output.args output.pointers τ x
  have environment := (envAt_encoding (reserved := 0) (L := output.image.Y) output.args).mpr ⟨valid, words⟩
  let entered : Cfg imageTSO (Res T) := ⟨after, before.ths.set 0 (some (.next ⟨target, frame⟩))⟩
  have inside := (List.getElem?_eq_some_iff.mp running).1
  have ready : entered.ths[0]? = some (some (.next ⟨target, frame⟩)) := List.getElem?_set_self inside
  obtain ⟨rest, passed, decoded⟩ :=
    output.root_depth_guard_pass (before := entered) (thread := 0) output.compiled.main code ready depth
  refine ⟨after, rest, ?_, shared, views, imageStackFootprint_agree site.bounded writes,
    fun _ stored => output.world_survives_stack site.bounded stored writes,
    newFrame, environment, buffers, decoded⟩
  simpa only [entered, List.set_set, List.nil_append] using call.trans passed

end Gabbro.Stage0
