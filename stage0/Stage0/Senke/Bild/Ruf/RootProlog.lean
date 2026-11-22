module

public import Stage0.Senke.Bild.Ruf.RootEntry
import Stage0.Senke.Images.CheckSpawn
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Stage0.Senke
  Gabbro.Stage0.Senke.BildMehr Runner Runner.IR Runner.Beweis Runner.Mach

variable {src : String} {reserve : Nat} {options : Profil.Options}

/-- The main start stub follows exactly the emitted clone sites. The
    serialized depth and private frame limits are shared with child starts. -/
theorem Emitted.main_stub_code [Kern] (output : Emitted src reserve options) {memory : Mem}
    (loaded : BytesAt memory codeBase (output.image.code.flatMap encII)) :
    let pc := BitVec.ofNat 64 (codeBase + 16 * (10 * output.starts.length))
    CodeAt memory pc (startC output.image.A output.compiled.main output.image.depth 231 true) ∧
      2 < output.image.Ks ∧ output.image.depth + 1 < 2 ^ 31 := by
  intro pc
  obtain ⟨_, lowered, spawnSites, layout, serialized, _, _, _⟩ :=
    bild_lage output.emission output.funktionen_voll
      (fun base bound => layU_in output.compiled.unit output.tor base bound)
      (fun base => layU_dis output.compiled.unit output.tor base)
      (fun base => by simp only [layU]; omega)
      (fun base => layU_sync output.compiled.unit output.tor base)
  have actual := codeAt_bytes _ codeBase layout.hops (serialized ▸ loaded)
  have main := codeAt_right (a := spawnC (startScratch output.compiled.main) spawnSites) (by
    simpa only [Emitted.starts, List.append_assoc] using actual :
      CodeAt memory (BitVec.ofNat 64 codeBase)
        (spawnC (startScratch output.compiled.main) spawnSites ++
          (startC output.image.A output.compiled.main output.image.depth 231 true ++
            (rootsC output.image.A output.image.depth (output.starts.map (·.1)) ++ lowered))))
  have sites : (spawnC (startScratch output.compiled.main) spawnSites).length = 10 * output.starts.length := by
    simp only [spawnC_len, layout.hsp, List.length_map, List.length_range, Emitted.starts]
  rw [sites, ofNat_add64] at main
  exact ⟨codeAt_left main, layout.startLimits.1, layout.startLimits.2.1⟩

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
  obtain ⟨stub, header, depth⟩ := output.main_stub_code loaded
  exact image_depth_setup (before := before) stub header depth running frame

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
      (∀ world, WeltAt (before.ms.1.view (index + 1)) output.image.Y world →
        WeltAt (after.1.view (index + 1)) output.image.Y world) ∧
      FrameOK (after.1.view (index + 1)) frame (output.image.Ks - FB) ∧
      EnvAt output.image.Y (after.1.view (index + 1)) frame root.2 ∧
      CodeAt (after.1.view (index + 1)) prologue rest := by
  intro entry target frame prologue running phase
  obtain ⟨after, call, shared, otherViews, world, permissions, environment, _, _, depth, loaded, _⟩ :=
    output.child_body_from_root_phase unit declared running phase
  have inside := (List.getElem?_eq_some_iff.mp running).1
  let entered : Cfg imageTSO (Res T) :=
    ⟨after, before.ths.set (index + 1) (some (.next ⟨target, frame⟩))⟩
  have ready : entered.ths[index + 1]? = some (some (.next ⟨target, frame⟩)) :=
    List.getElem?_set_self inside
  obtain ⟨rest, passed, code⟩ := output.root_depth_guard_pass (before := entered) root.1 loaded ready depth
  refine ⟨after, rest, ?_, shared, otherViews, world, permissions, environment, code⟩
  simpa only [entered, List.set_set, List.nil_append] using call.trans passed

end Gabbro.Stage0
