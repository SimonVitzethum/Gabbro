module

public import Stage0.Senke.Bild.Ruf.PrologueCode
public import Stage0.Senke.Bild.Prolog

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Stage0.Senke Gabbro.Stage0.Senke.BildLauf Gabbro.Stage0.Senke.BildMehr
  Runner Runner.IR

variable {src : String} {reserve : Nat} {options : Profil.Options}

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
    (stored : WeltAt memory output.image.Y world)
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
      CodeAt after (compiled.entry fp).pc (compiled.prefixCode ++ compiled.body.1) := by
  intro restricted
  letI : Kern := kernel.withoutSyscalls
  have loaded : CodeAt memory (compiled.entry fp).pc (table f) := exactCode.symm ▸ compiled.instructions
  obtain ⟨protected, decoded⟩ := maskMemory_code_frame loaded frame far.1 frameReads codeReads
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
    simp only [Mem.rd64, Mem.all_congr (fun j hj => (sameWord j hj).2),
      Mem.le_congr (fun j hj => (sameWord j hj).1)]
    exact depthWord
  have observed := expression_world_mask frameReads layout.lay requiresReads
    (⟨fun t _ field index valid => stored.1 t field index valid, fun g _ => stored.2.1 g⟩ :
      WorldOnAt memory output.image.Y world (· ∈ (output.compiled.program.requires f).orte))
  have saved : EntrySnapshots.Inputs output.image.Y world restricted
      (oldCells (output.compiled.program.ensures f)) := by
    intro cell member
    have bounds := EntrySnapshots.capture_bounds _ _ compiled.captureLowered cell member
    have original := EntrySnapshots.Inputs.of_world stored
      (fun cell member => (EntrySnapshots.capture_bounds _ _ compiled.captureLowered cell member).1) cell member
    exact expression_mask_value frameReads (bounds.2.trans (by decide)) (snapshotReads cell member) original
  obtain ⟨ens, pc, after, run, changed, post, position, _⟩ :=
    prolog_setup (O := O) (rp := 0) (cfp := 0) (H := []) lowered codeSize depthFits capacity
      layout small protected decoded far maskedDepth maskedArgs observed saved requires
  have samePost : compiled.postcondition = ens := Option.some.inj (compiled.postconditionLowered.symm.trans post)
  subst ens
  have address := position compiled.body compiled.bodyLowered
  rw [exactCode, List.length_append, Nat.add_sub_cancel] at address
  subst pc
  obtain ⟨count, steps⟩ := IRReference.of_star run
  exact ⟨count, after, steps, changed, exactCode ▸ decoded.agree changed far⟩

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
    (compiled : FunctionIRPrologue output after root.1) (reads : W → Prop) (K : Nat)
    (frameReads : ∀ byte, inSlots (imagePrologueFrame output thread) 0 K byte → reads byte)
    (ownsWrites : ∀ byte, inSlots (imagePrologueFrame output thread) 0 K byte →
      imageStackFootprint output thread byte)
    (continuation : @IRReference kernel.withoutSyscalls count
      (compiled.entry (imagePrologueFrame output thread))
      (maskMemory reads (inSlots (imagePrologueFrame output thread) 0 K) memory)
      (compiled.bodyEntry (imagePrologueFrame output thread)) after) :
    ImageProloguePhase output E thread (.next (compiled.entry (imagePrologueFrame output thread))) memory state :=
  let writes := inSlots (imagePrologueFrame output thread) 0 K
  let scope := maskMemory_agreement reads writes memory frameReads
  ⟨root, declared, alive, unentered, reads, writes, ownsWrites, maskMemory reads writes memory,
    after, compiled, ⟨count, continuation⟩, .next _, scope.2.1, scope.2.2, scope.1⟩

end Gabbro.Stage0
