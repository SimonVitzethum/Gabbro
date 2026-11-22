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

/-- Retain the production code and layout data after private frame
    setup has written only above the installed instruction region. -/
def FunctionIRPrologue.agree [Kern] {output : Emitted src reserve options}
    {f : (declOf output.compiled.unit).Fn} {before after : Mem} {fp : W} {lo K : Nat}
    (compiled : FunctionIRPrologue output before f) (written : Agree fp lo K before after)
    (separated : CodeFar (compiled.entry fp).pc (compiled.prefixCode ++ compiled.body.1).length fp K) :
    FunctionIRPrologue output after f :=
  ⟨compiled.requirement, compiled.postcondition, compiled.capture, compiled.body, compiled.prefixCode,
    compiled.requirementLowered, compiled.postconditionLowered, compiled.captureLowered, compiled.bodyLowered,
    compiled.assembled, compiled.instructions.agree written separated, compiled.beforeStacks⟩

/-- Start tracking a prologue at the actual function entry, using its
    verified continuation to the already installed body boundary. -/
def ImageProloguePhase.enter [kernel : Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {thread count : Nat} {memory after : Mem}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (root : Σ f : (declOf output.compiled.unit).Fn, Env _ ((declOf output.compiled.unit).params f))
    (declared : E.starts[thread]? = some root) (alive : state.lebt thread = true)
    (unentered : state.m.faeden thread = (imageSourceStart E).m.faeden thread)
    (compiled : FunctionIRPrologue output after root.1) (reads : W → Prop)
    (continuation : @IRReference kernel.withoutSyscalls count
      (compiled.entry (imagePrologueFrame output thread)) memory
      (compiled.bodyEntry (imagePrologueFrame output thread)) after) :
    ImageProloguePhase output E thread (.next (compiled.entry (imagePrologueFrame output thread))) memory state :=
  ⟨root, declared, alive, unentered, reads, memory, after, compiled, ⟨count, continuation⟩,
    .next _, fun byte _ => GleichAt.refl _ byte⟩

end Gabbro.Stage0
