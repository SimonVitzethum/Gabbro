module

public import Stage0.Senke.Bild.Ruf.PrologueCode
public import Stage0.Senke.Bild.Prolog
import Stage0.Senke.Bild.Mehr.ImageTransition

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Stage0.Senke Gabbro.Stage0.Senke.BildLauf Gabbro.Stage0.Senke.BildMehr
  Runner Runner.IR

variable {src : String} {reserve : Nat} {options : Profil.Options}

/-- The root enters at the emitted callee frame. Its lowered writes
    fit in that thread's reservation and the world is above every frame. -/
theorem Emitted.prologue_geometry [Kern] (output : Emitted src reserve options) {thread : Nat}
    (declared : thread ≤ output.starts.length) :
    let fp := imagePrologueFrame output thread
    let slots := output.image.Ks - FB
    WIn output.image.Y fp slots slots ∧ slots < 2 ^ 31 ∧
      0 < output.image.depth ∧ output.image.depth + 1 < 2 ^ 31 ∧
      output.image.fp0 ≤ fp.toNat ∧
      ∀ byte, inSlots fp 0 slots byte → imageStackFootprint output thread byte := by
  intro fp slots
  obtain ⟨functions, _, _, layout, _, _, _, _⟩ := bild_lage output.emission output.funktionen_voll
    (fun base bound => layU_in output.compiled.unit output.tor base bound)
    (fun base => layU_dis output.compiled.unit output.tor base)
    (fun base => by simp only [layU]; omega)
    (fun base => layU_sync output.compiled.unit output.tor base)
  let base := output.image.fp0 + 8 * (output.image.Ks * thread)
  let start := BitVec.ofNat 64 base
  have root : WIn output.image.Y start output.image.Ks output.image.Ks :=
    layout.win (by simpa only [Emitted.starts, List.length_map] using declared)
  have reserve := layout.hroom
  have positive := maxTop_pos functions
  have header : FB < output.image.Ks := by omega
  have beforeLimit := output.stackReservation_bounds
  have stackBand := beforeLimit.1
  have limit := beforeLimit.2
  have top : start.toNat + 8 * output.image.Ks < 2 ^ 64 := root.top.trans_lt beforeLimit.2
  have exactBase : start.toNat = base := by
    have inside := Nat.mul_le_mul_left output.image.Ks (declared.trans (Nat.le_succ _))
    have bounded : base ≤ output.image.Y.lo :=
      (Nat.add_le_add_left (Nat.mul_le_mul_left 8 inside) output.image.fp0).trans stackBand
    change (BitVec.ofNat 64 base).toNat = base
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (bounded.trans_lt limit)]
  have frameOffset : fp.toNat = base + 8 * FB := by
    change (slot start (BitVec.ofNat 64 FB)).toNat = _
    rw [slot_toNat top.le header, exactBase]
  refine ⟨root.sub header.le top, by have := layout.startLimits.2.2; dsimp [slots]; omega,
    layout.depth_pos, layout.startLimits.2.1, by rw [frameOffset]; dsimp [base]; omega, ?_⟩
  intro byte inside
  have bounds := inside
  simp only [inSlots, Nat.mul_zero, Nat.add_zero, frameOffset] at bounds
  refine ⟨declared, by dsimp [base] at *; omega, ?_⟩
  rw [Nat.mul_succ]
  dsimp [base, slots] at bounds
  omega

/-- The exact loaded prologue prepares its typed frame at the beginning
    of the installed body. The reference uses only the Lean IR's private
    memory and native operations. -/
theorem FunctionIRPrologue.reference [kernel : Kern]
    {output : Emitted src reserve options}
    {f : (declOf output.compiled.unit).Fn} {memory : Mem}
    (compiled : FunctionIRPrologue output memory f)
    (O : Orakel (declOf output.compiled.unit))
    {table : (declOf output.compiled.unit).Fn → List II} {reserveWords depth : Nat}
    (exactCode : table f = compiled.prefixCode ++ compiled.body.1)
    (lowered : ∃ top, lowFun output.image.passes output.compiled.program output.image.A output.image.Y f =
      some (table f, top) ∧ top ≤ reserveWords)
    (codeSize : 16 * (table f).length < 2 ^ 31) (depthFits : depth + 1 < 2 ^ 64)
    {fp rp caller : W} {K Ks : Nat}
    {world : World (declOf output.compiled.unit)} {args : Env _ ((declOf output.compiled.unit).params f)}
    {held : List (declOf output.compiled.unit).Lock}
    (capacity : (depth + 1 + 1) * reserveWords ≤ Ks)
    (layout : WIn output.image.Y fp Ks K) (small : K < 2 ^ 31)
    (frame : FrameOK memory fp K) (code : PCode memory output.image.A table fp K)
    (returnPC : memory.rd64 (slot fp (BitVec.ofNat 64 0)) = some rp)
    (returnFP : memory.rd64 (slot fp (BitVec.ofNat 64 1)) = some caller)
    (depthWord : memory.rd64 (slot fp (BitVec.ofNat 64 2)) = some (BitVec.ofNat 64 (depth + 1)))
    (environment : EnvAt output.image.Y memory fp args)
    (stored : WeltAt memory output.image.Y world)
    (tickets : TicketSync memory output.image.Y fp Ks held)
    (heldIn : HeldIn held (Signatur.anfang _ ((declOf output.compiled.unit).signatur f))
      ((declOf output.compiled.unit).signatur f).boden)
    (requires : ReqAmEintritt output.compiled.program f world args) :
    ∃ count after,
      @IRReference kernel.withoutSyscalls count (compiled.entry fp) memory (compiled.bodyEntry fp) after ∧
      Agree fp FB K memory after ∧
      (rumpfRahmen output.image.Y O output.image.passes output.compiled.program output.image.A table
        reserveWords depth f fp K Ks rp caller
        (world.lese (Signatur.anfang _ ((declOf output.compiled.unit).signatur f))
          (output.compiled.program.requires f).orte) args held compiled.postcondition).RandIR
          (output.compiled.program.rumpf f) (compiled.bodyEntry fp).pc after world args := by
  letI : Kern := kernel.withoutSyscalls
  obtain ⟨ens, pc, after, run, changed, post, position, body⟩ :=
    prolog_randIR (O := O) lowered codeSize depthFits capacity layout small frame code returnPC returnFP
      depthWord environment stored tickets heldIn requires
  have samePost := compiled.postconditionLowered.symm.trans post
  have ensAt : compiled.postcondition = ens := Option.some.inj samePost
  subst ens
  have bodyAddress := position compiled.body compiled.bodyLowered
  rw [exactCode, List.length_append, Nat.add_sub_cancel] at bodyAddress
  subst pc
  obtain ⟨count, steps⟩ := IRReference.of_star run
  exact ⟨count, after, steps, changed, body⟩

/-- The installed prologue reaches its body in a memory that grants
    access only to the chosen read region and its own frame writes. -/
theorem FunctionIRPrologue.scoped_reference [kernel : Kern]
    {output : Emitted src reserve options}
    {f : (declOf output.compiled.unit).Fn} {memory : Mem}
    (compiled : FunctionIRPrologue output memory f)
    (O : Orakel (declOf output.compiled.unit))
    {table : (declOf output.compiled.unit).Fn → List II} {reserveWords depth : Nat}
    (exactCode : table f = compiled.prefixCode ++ compiled.body.1)
    (lowered : ∃ top, lowFun output.image.passes output.compiled.program output.image.A output.image.Y f =
      some (table f, top) ∧ top ≤ reserveWords)
    (codeSize : 16 * (table f).length < 2 ^ 31) (depthFits : depth + 1 < 2 ^ 64)
    {fp : W} {K Ks : Nat}
    {world : World (declOf output.compiled.unit)} {args : Env _ ((declOf output.compiled.unit).params f)}
    (capacity : (depth + 1 + 1) * reserveWords ≤ Ks)
    (layout : WIn output.image.Y fp Ks K) (small : K < 2 ^ 31)
    (frame : FrameOK memory fp K) (room : frei ((declOf output.compiled.unit).params f) ≤ K)
    (far : CodeFar (compiled.entry fp).pc (table f).length fp K)
    (depthWord : memory.rd64 (slot fp (BitVec.ofNat 64 2)) = some (BitVec.ofNat 64 (depth + 1)))
    (environment : EnvAt output.image.Y memory fp args)
    (stored : WorldOnAt memory output.image.Y world (· ∈ (output.compiled.program.requires f).orte))
    (snapshots : EntrySnapshots.Inputs output.image.Y world memory (oldCells (output.compiled.program.ensures f)))
    (requires : ReqAmEintritt output.compiled.program f world args)
    (reads : W → Prop) (frameReads : ∀ byte, inSlots fp 0 K byte → reads byte)
    (codeReads : ∀ byte, (compiled.entry fp).pc.toNat ≤ byte.toNat →
      byte.toNat < (compiled.entry fp).pc.toNat + 16 * (table f).length → reads byte)
    (requiresReads : ∀ cell : Zelle (declOf output.compiled.unit), cell.da output.image.Y →
      cell.carrier ∈ (output.compiled.program.requires f).orte → ∀ byte : W,
      cell.adr output.image.Y ≤ byte.toNat → byte.toNat < cell.adr output.image.Y + cell.bytes → reads byte)
    (snapshotReads : ∀ cell ∈ oldCells (output.compiled.program.ensures f), ∀ byte : W,
      cell.adr output.image.Y ≤ byte.toNat → byte.toNat < cell.adr output.image.Y + 8 * valueWords cell.ty →
      reads byte) :
    let restricted := maskMemory reads (inSlots fp 0 K) memory
    ∃ count after, @IRReference kernel.withoutSyscalls count
      (compiled.entry fp) restricted (compiled.bodyEntry fp) after ∧ Agree fp FB K restricted after ∧
      CodeAt after (compiled.entry fp).pc (compiled.prefixCode ++ compiled.body.1) ∧
      FrameOK after fp K ∧
      EntryFrameValues output.image.Y output.compiled.program f after fp
        (world.lese (Signatur.anfang _ ((declOf output.compiled.unit).signatur f))
          (output.compiled.program.requires f).orte) args := by
  intro restricted
  letI : Kern := kernel.withoutSyscalls
  have loaded : CodeAt memory (compiled.entry fp).pc (table f) := exactCode.symm ▸ compiled.instructions
  obtain ⟨proofFrame, decoded⟩ := maskMemory_code_frame loaded frame far.1 frameReads codeReads
  have agreement := (maskMemory_agreement reads (inSlots fp 0 K) memory frameReads).1
  have sameFrame (byte : W) (inside : inSlots fp 0 K byte) := agreement.1 byte (frameReads byte inside)
  have maskedArgs : EnvAt output.image.Y restricted fp args := by
    intro ty variableAt
    have fits := variableOffset_bound variableAt
    exact frame_value_agrees frame (by unfold frei vslot at *; omega) sameFrame (environment ty variableAt)
  have maskedDepth : restricted.rd64 (slot fp (BitVec.ofNat 64 2)) = some (BitVec.ofNat 64 (depth + 1)) := by
    have slotFits : 2 < K := by unfold frei FB at room; omega
    have sameWord (offset : Nat) (inside : offset < 8) :=
      sameFrame _ (frame_slot_byte frame slotFits inside)
    have samePermissions : Mem.all restricted.rd (slot fp (BitVec.ofNat 64 2)) 8 =
        Mem.all memory.rd (slot fp (BitVec.ofNat 64 2)) 8 :=
      Mem.all_congr (fun j hj => (sameWord j hj).2)
    have sameValue : restricted.le (slot fp (BitVec.ofNat 64 2)) 8 =
        memory.le (slot fp (BitVec.ofNat 64 2)) 8 :=
      Mem.le_congr (fun j hj => (sameWord j hj).1)
    unfold Mem.rd64 at depthWord ⊢
    rwa [samePermissions, sameValue]
  have observed := expression_world_mask frameReads layout.lay requiresReads stored
  have saved : EntrySnapshots.Inputs output.image.Y world restricted
      (oldCells (output.compiled.program.ensures f)) := by
    intro cell member
    have bounds := EntrySnapshots.capture_bounds _ _ compiled.captureLowered cell member
    exact expression_mask_value frameReads (bounds.2.trans (by decide)) (snapshotReads cell member)
      (snapshots cell member)
  obtain ⟨ens, pc, after, run, changed, post, position, values, _⟩ :=
    prolog_setup (O := O) (rp := 0) (cfp := 0) (H := []) lowered codeSize depthFits capacity
      layout small proofFrame decoded far maskedDepth maskedArgs observed saved requires
  have samePost : compiled.postcondition = ens := Option.some.inj (compiled.postconditionLowered.symm.trans post)
  subst ens
  have address := position compiled.body compiled.bodyLowered
  rw [exactCode, List.length_append, Nat.add_sub_cancel] at address
  subst pc
  obtain ⟨count, steps⟩ := IRReference.of_star run
  exact ⟨count, after, steps, changed, exactCode ▸ decoded.agree changed far, proofFrame.agree changed, values⟩

/-- Retain the production layout when the same instructions are present in another view. -/
def FunctionIRPrologue.withCode [Kern] {output : Emitted src reserve options}
    {f : (declOf output.compiled.unit).Fn} {before after : Mem}
    (compiled : FunctionIRPrologue output before f)
    (installed : CodeAt after (BitVec.ofNat 64 (output.image.A f)) (compiled.prefixCode ++ compiled.body.1)) :
    FunctionIRPrologue output after f :=
  ⟨compiled.requirement, compiled.postcondition, compiled.capture, compiled.body, compiled.prefixCode,
    compiled.requirementLowered, compiled.postconditionLowered, compiled.captureLowered, compiled.bodyLowered,
    compiled.assembled, installed, compiled.beforeStacks⟩

/-- Retain the production code and layout data after private frame setup. -/
def FunctionIRPrologue.agree [Kern] {output : Emitted src reserve options}
    {f : (declOf output.compiled.unit).Fn} {before after : Mem} {fp : W} {lo K : Nat}
    (compiled : FunctionIRPrologue output before f) (written : Agree fp lo K before after)
    (separated : CodeFar (compiled.entry fp).pc (compiled.prefixCode ++ compiled.body.1).length fp K) :
    FunctionIRPrologue output after f :=
  compiled.withCode (compiled.instructions.agree written separated)

/-- Start tracking a prologue at the actual function entry, using its
    verified continuation to the already installed body boundary. -/
noncomputable def ImageProloguePhase.enter [kernel : Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {thread count : Nat} {memory after : Mem}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (root : Σ f : (declOf output.compiled.unit).Fn, Env _ ((declOf output.compiled.unit).params f))
    (declared : E.starts[thread]? = some root) (alive : state.lebt thread = true)
    (unentered : state.m.faeden thread = (imageSourceStart E).m.faeden thread)
    (compiled : FunctionIRPrologue output after root.1)
    (entryWorld : World (declOf output.compiled.unit))
    (values : EntryFrameValues output.image.Y output.compiled.program root.1 after
      (imagePrologueFrame output thread) entryWorld root.2)
    (entryFrame : FrameOK after (imagePrologueFrame output thread) (output.image.Ks - FB))
    (entryFits : frei ((declOf output.compiled.unit).params root.1)
      (functionFrame output.compiled.program root.1).bodyReserved ≤ output.image.Ks - FB)
    (ownsWrites : ∀ byte, inSlots (imagePrologueFrame output thread) 0 (output.image.Ks - FB) byte →
      imageStackFootprint output thread byte)
    (continuation : @IRReference kernel.withoutSyscalls count
      (compiled.entry (imagePrologueFrame output thread))
      (maskMemory (imagePrologueReads output thread root.1)
        (inSlots (imagePrologueFrame output thread) 0 (output.image.Ks - FB)) memory)
      (compiled.bodyEntry (imagePrologueFrame output thread)) after) :
    ImageProloguePhase output E thread (.next (compiled.entry (imagePrologueFrame output thread))) memory state :=
  let writes := inSlots (imagePrologueFrame output thread) 0 (output.image.Ks - FB)
  let reads := imagePrologueReads output thread root.1
  let scope := maskMemory_agreement reads writes memory (fun byte hit => Or.inl (ownsWrites byte hit))
  ⟨root, declared, alive, unentered, writes, fun _ inside => inside, ownsWrites, maskMemory reads writes memory,
    after, compiled, entryWorld, values, entryFrame, entryFits,
    ⟨count, continuation⟩, .next _, scope.2.1, scope.2.2, scope.1⟩

/-- At the exact relocated entry, the serialized root arguments and
    the checked precondition establish the scheduled prologue phase. -/
theorem Emitted.enter_prologue [Kern] (output : Emitted src reserve options)
    {E : Einheit (declOf output.compiled.unit)} (unit : ImageModelUnit output E)
    (O : Orakel (declOf output.compiled.unit)) {thread : Nat} {memory : Mem}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (root : Σ f : (declOf output.compiled.unit).Fn, Env _ ((declOf output.compiled.unit).params f))
    (declared : E.starts[thread]? = some root) (alive : state.lebt thread = true)
    (unentered : state.m.faeden thread = (imageSourceStart E).m.faeden thread)
    (loaded : output.IRFunctionSemantics memory)
    {world : World (declOf output.compiled.unit)}
    (stored : WorldOnAt memory output.image.Y world (· ∈ (output.compiled.program.requires root.1).orte))
    (snapshots : ∀ cell ∈ oldCells (output.compiled.program.ensures root.1), cell.da output.image.Y →
      ValueAt output.image.Y memory (BitVec.ofNat 64 (cell.adr output.image.Y)) 0 cell.ty (cell.val world))
    (requires : ReqAmEintritt output.compiled.program root.1 world root.2)
    (frame : FrameOK memory (imagePrologueFrame output thread) (output.image.Ks - FB))
    (environment : EnvAt output.image.Y memory (imagePrologueFrame output thread) root.2)
    (depthWord : memory.rd64 (slot (imagePrologueFrame output thread) (BitVec.ofNat 64 2)) =
      some (BitVec.ofNat 64 output.image.depth)) :
    ∃ phase : ImageProloguePhase output E thread
        (.next ⟨BitVec.ofNat 64 (output.image.A root.1), imagePrologueFrame output thread⟩) memory state,
      phase.root = root ∧ phase.reads = imagePrologueReads output thread root.1 := by
  have declaredStack : thread ≤ output.starts.length := by
    have present := (List.getElem?_eq_some_iff.mp declared).1
    rw [unit.starts, List.length_cons] at present
    omega
  obtain ⟨layout, small, positive, depthBound, aboveCode, ownsWrites⟩ := output.prologue_geometry declaredStack
  obtain ⟨table, words, space, functions, _⟩ := loaded
  obtain ⟨top, lowered, topFits, decoded, extent⟩ := functions root.1
  obtain ⟨compiled, exactCode, parameters⟩ := FunctionIRPrologue.of_lowered lowered decoded extent
  let slots := output.image.Ks - FB
  let depth := output.image.depth - 1
  let fp := imagePrologueFrame output thread
  let reads := imagePrologueReads output thread root.1
  have depthEq : depth + 1 = output.image.depth := by dsimp [depth]; omega
  have capacity : (depth + 1 + 1) * words ≤ slots := by rw [depthEq]; dsimp [slots]; omega
  have bodyFits : frei ((declOf output.compiled.unit).params root.1)
      (functionFrame output.compiled.program root.1).bodyReserved ≤ slots :=
    parameters.trans (topFits.trans ((Nat.le_mul_of_pos_left _ (by omega : 0 < depth + 1 + 1)).trans capacity))
  have room : frei ((declOf output.compiled.unit).params root.1) ≤ slots := by
    unfold frei at bodyFits ⊢
    omega
  have codeBound : output.image.fp0 < 2 ^ 31 :=
    aboveCode.trans_lt ((Nat.le_add_right _ _).trans_lt
      (layout.top.trans_lt (layout.ord.trans_lt layout.lay.2.2)))
  have pc : (compiled.entry fp).pc.toNat = output.image.A root.1 := by
    change (BitVec.ofNat 64 (output.image.A root.1)).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have far : CodeFar (compiled.entry fp).pc (table root.1).length fp slots :=
    ⟨by rw [pc]; omega, (layout.top.trans_lt (layout.ord.trans_lt layout.lay.2.2)).le.trans (by decide),
      by rw [pc]; exact extent.trans aboveCode⟩
  have frameReads : ∀ byte, inSlots fp 0 slots byte → reads byte :=
    fun byte inside => .inl (ownsWrites byte inside)
  have codeReads : ∀ byte, (compiled.entry fp).pc.toNat ≤ byte.toNat →
      byte.toNat < (compiled.entry fp).pc.toNat + 16 * (table root.1).length → reads byte := by
    intro byte _ inside
    rw [pc] at inside
    exact .inr (.inl (inside.trans_le extent))
  have requiresReads (cell : Zelle (declOf output.compiled.unit)) (valid : cell.da output.image.Y)
      (member : cell.carrier ∈ (output.compiled.program.requires root.1).orte) (byte : W)
      (first : cell.adr output.image.Y ≤ byte.toNat)
      (last : byte.toNat < cell.adr output.image.Y + cell.bytes) : reads byte :=
    .inr (.inr ⟨cell, valid, .inl member, first, last⟩)
  have snapshotReads (cell : Zelle (declOf output.compiled.unit))
      (member : cell ∈ oldCells (output.compiled.program.ensures root.1)) (byte : W)
      (first : cell.adr output.image.Y ≤ byte.toNat)
      (last : byte.toNat < cell.adr output.image.Y + 8 * valueWords cell.ty) : reads byte := by
    have valid := (EntrySnapshots.capture_bounds _ _ compiled.captureLowered cell member).1
    exact .inr (.inr ⟨cell, valid, .inr member, first, by cases cell <;> exact last⟩)
  obtain ⟨count, finished, reference, _, installed, bodyFrame, values⟩ :=
    compiled.scoped_reference O exactCode ⟨top, lowered, topFits⟩ (by omega)
      (by rw [depthEq]; omega) capacity layout small frame room far (depthEq.symm ▸ depthWord)
      environment stored
      (fun cell member => snapshots cell member (EntrySnapshots.capture_bounds _ _ compiled.captureLowered cell member).1)
      requires reads frameReads codeReads requiresReads snapshotReads
  let finishedCode := compiled.withCode installed
  exact ⟨ImageProloguePhase.enter root declared alive unentered finishedCode _ values
    bodyFrame bodyFits ownsWrites reference,
    rfl, rfl⟩

/-- The scheduled runtime partition supplies the prologue's exact world
    inputs at the issuing thread's actual memory view. -/
theorem ImageRuntimePartition.at_prologue_entry [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} (unit : ImageModelUnit output E)
    {O : Orakel (declOf output.compiled.unit)} (hardware : RootNativeFloat.Hardware)
    (accepted : akzeptiertX_pruefer.akzeptiert E output.fsA.1 output.lsA.1 output.csA.1 = true)
    (duties : StartPflicht E) {thread : Nat} {history : List Runner.Mach.Ev}
    {machine : Runner.Mach.Cfg imageTSO (Res T)}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {body : List (Option (Res T))} {pendingPhase : Mem → Nat → Res T → Prop}
    (partition : ImageRuntimePartition (Senke.Faeden.imageRuntimeFootprint output E state.m)
      output E O history machine state body pendingPhase)
    (pending : body[thread]? = some none)
    (root : Σ f : (declOf output.compiled.unit).Fn, Env _ ((declOf output.compiled.unit).params f))
    (declared : E.starts[thread]? = some root) (alive : state.lebt thread = true)
    (unentered : state.m.faeden thread = (imageSourceStart E).m.faeden thread) :
    let memory := machine.ms.1.view thread
    let frame := imagePrologueFrame output thread
    BytesAt memory codeBase (output.image.code.flatMap encII) →
    ReqAmEintritt output.compiled.program root.1 (worldZ (state.m.speicher.welt [])) root.2 →
    FrameOK memory frame (output.image.Ks - FB) →
    EnvAt output.image.Y memory frame root.2 →
    memory.rd64 (slot frame (BitVec.ofNat 64 2)) = some (BitVec.ofNat 64 output.image.depth) →
    Nonempty (ImageProloguePhase output E thread
      (.next ⟨BitVec.ofNat 64 (output.image.A root.1), frame⟩) memory state) := by
  intro memory frame loaded requires frameOK environment depthWord
  obtain ⟨committed, world, agrees⟩ := partition.prologue_world unit hardware accepted duties pending declared
  obtain ⟨inputs, snapshots⟩ := output.prologue_sources world agrees
  obtain ⟨phase, _, _⟩ := output.enter_prologue unit O root declared alive unentered
    (Emitted.function_semantics_at loaded) inputs snapshots requires frameOK environment depthWord
  exact ⟨phase⟩

end Gabbro.Stage0
