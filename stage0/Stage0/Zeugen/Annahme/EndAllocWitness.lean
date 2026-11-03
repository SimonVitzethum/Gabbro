module
public import Stage0.SourceWitness
public import Grammatik.Bausteine.Arena.ArenaZucker
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section

namespace Gabbro.Stage0.EndAllocWitness

set_option maxRecDepth 2000
set_option maxHeartbeats 400000

/-- End-block allocation with `else`: the first two allocations take the success
    path (indices 0 and 1 in the two-slot arena), the third finds the declared
    ceiling and takes the `else` path. Both branches of the end-block form are
    exercised by the one image; the ceiling refuses the store only through the
    `else` continuation, never by wrapping or fabricating a value. -/
def text : String :=
  "module end_alloc_probe { arena A capacity 1 .. 2 of u32; impl fn main() -> u64 in 0 .. 100 effects { writes A } { let i = alloc A (10) else { return 7; }; let j = alloc A (20) else { return 8; }; let k = alloc A (30) else { return 9; }; return 23; } }"

def candidate : Except String (Emitted text 64) := emit text 64

theorem candidate_present : candidate.toOption.isSome = true := by decide +kernel

def output : Emitted text 64 := candidate.toOption.get candidate_present

theorem accepted_image : emit text 64 = .ok output :=
  Gabbro.Grammatik.except_ok_get candidate_present

/-- The image passes the original-source gate, rather than only the canonical
    G allocation emitter. This was the gate that rejected explicit else arms. -/
theorem original_metadata_zeuge : output.compiled.unit.exportGate = .ok () := by
  decide +kernel

theorem canonical_source_zeuge : CanonicalSourceProgram output.compiled :=
  compile_source_program text output.compiled

/-- The same source path with room left: success binds the original counter. -/
def fitsText : String :=
  "module end_alloc_fits { arena A capacity 1 .. 2 of u32; impl fn main() -> u64 in 0 .. 100 effects { writes A } { let i = alloc A (10) else { return 7; }; return i; } }"

/-- Allocation inside an ordinary block, including two stores and the ceiling arm.
    The distinct trailing return detects an incorrect fallthrough from `else`. -/
def blockText : String :=
  "module block_alloc_probe { arena A capacity 1 .. 2 of u32; impl fn main() -> u64 in 0 .. 100 effects { writes A } { if true { let i = alloc A (10) else { return 7; }; let j = alloc A (20) else { return 8; }; let k = alloc A (30) else { return 9; }; } return 23; } }"

/-- Ordinary-block success uses the bound index before returning to the outer body. -/
def blockFitsText : String :=
  "module block_alloc_fits { arena A capacity 1 .. 2 of u32; impl fn main() -> u64 in 0 .. 100 effects { writes A } { if true { let i = alloc A (10) else { return 7; }; return i; } return 23; } }"

theorem fits_image_zeuge : (emit fitsText 64).isOk = true := by decide +kernel

theorem block_image_zeuge : (emit blockText 64).isOk = true := by decide +kernel

theorem block_fits_image_zeuge : (emit blockFitsText 64).isOk = true := by decide +kernel

/-- The accepted source image inherits the connected generic lowering theorem,
    including both allocation branches and the store-and-bump continuation. -/
theorem image_correct_zeuge [Runner.IR.Kern] [Senke.CloneOK] : output.Correct :=
  output.correct

namespace Branches

open Gabbro.Grammatik Gabbro.Grammatik.ArenaZeuge

/-- A nonzero payload makes skipped stores and preservation at the ceiling visible. -/
def world (used : Int) (nonneg : 0 ≤ used) (bound : used ≤ 4) : World ZD :=
  { welt used nonneg bound with
    slots := fun _ _ _ => ⟨9, by decide, by decide⟩ }

def emptyWorld : World ZD := world 0 (by decide) (by decide)
def lastWorld : World ZD := world 3 (by decide) (by decide)
def fullWorld : World ZD := world 4 (by decide) (by decide)

def done {Γ : Ctx} : Endblock ZD ZV false Γ [] := .ret .empty (.refl [])

def block : Block ZD ZV false [] [] [] :=
  Block.arenaAlloc Log sieben rfl zeuge_darf rfl zeuge_gdarf done .nil

def ending : Endblock ZD ZV false [] [] :=
  Endblock.arenaAlloc Log sieben rfl zeuge_darf rfl zeuge_gdarf done done

def requiredBlock : Block ZD ZV false [] [] [] :=
  Block.arenaAllocRequired Log sieben rfl zeuge_darf rfl zeuge_gdarf .nil

def requiredEnd : Endblock ZD ZV false [] [] :=
  Endblock.arenaAllocRequired Log sieben rfl zeuge_darf rfl zeuge_gdarf done

/-- Observe the counter and both boundary slots, without discarding the other
    world fields from the semantic outcome or from the generic simulation. -/
def snapshot (σ : World ZD) : Int × Int × Int :=
  (Log.stand σ, (σ.slots () 0 ()).n, (σ.slots () 3 ()).n)

def blockResult : Ausgang ZV false [] → Option (Bool × (Int × Int × Int))
  | .ok σ _ => some (true, snapshot σ)
  | .zurueck σ _ => some (false, snapshot σ)
  | _ => none

def endResult : EndAusgang ZV false [] → Option (Int × Int × Int)
  | .zurueck σ _ => some (snapshot σ)
  | _ => none

variable (O : Orakel ZD) (passes : Nat)
  (R : (f : ZD.Fn) → World ZD → Env ZD (ZD.params f) → RufAusgang f)

/-- Ordinary-block success stores at the bound index, bumps once, and falls through. -/
theorem block_fits_zeuge :
    blockResult (execBlock O passes R block emptyWorld .nil) = some (true, 1, 7, 9) := by
  decide +kernel

/-- The last available index still fits; the next counter is the exact ceiling. -/
theorem block_last_fits_zeuge :
    blockResult (execBlock O passes R block lastWorld .nil) = some (true, 4, 9, 7) := by
  decide +kernel

/-- At the ceiling `else` returns, preserving both payload and counter. -/
theorem block_ceiling_zeuge :
    blockResult (execBlock O passes R block fullWorld .nil) = some (false, 4, 9, 9) := by
  decide +kernel

theorem end_fits_zeuge :
    endResult (execEnd O passes R ending emptyWorld .nil) = some (1, 7, 9) := by
  decide +kernel

theorem end_last_fits_zeuge :
    endResult (execEnd O passes R ending lastWorld .nil) = some (4, 9, 7) := by
  decide +kernel

theorem end_ceiling_zeuge :
    endResult (execEnd O passes R ending fullWorld .nil) = some (4, 9, 9) := by
  decide +kernel

/-- Required allocation shares the same successful store and counter update. -/
theorem required_fits_zeuge :
    blockResult (execBlock O passes R requiredBlock emptyWorld .nil) = some (true, 1, 7, 9) ∧
    endResult (execEnd O passes R requiredEnd emptyWorld .nil) = some (1, 7, 9) := by
  decide +kernel

/-- Required allocation has the same logical stop at both nesting levels.
    The caller's existing capacity duty excludes this outcome; it is not OOM. -/
theorem required_ceiling_zeuge :
    execBlock O passes R requiredBlock fullWorld .nil = .logik .kapazitaet ∧
    execEnd O passes R requiredEnd fullWorld .nil = .logik .kapazitaet := by
  constructor
  · exact arenaAllocRequired_an_schranke O passes R Log sieben rfl zeuge_darf
      rfl zeuge_gdarf .nil fullWorld .nil rfl
  · exact arenaAllocRequiredEnd_an_schranke O passes R Log sieben rfl zeuge_darf
      rfl zeuge_gdarf done fullWorld .nil rfl

end Branches

end Gabbro.Stage0.EndAllocWitness
