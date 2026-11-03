module
public import Stage0.IRBild
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

namespace Gabbro.Stage0.Pipeline.RetireWitness

open Gabbro.Grammatik Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2 Runner.IR Senke

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The source supplies an initial linear owner, transfers it terminally to
    finish, and finish explicitly retires it before returning. No mint, foreign
    provider or runtime token value is hidden in this witness. -/
def text : String :=
  "module retire_probe { linear type Mark; table T count 1 owner Mark { slot { b : bool, } } impl fn finish() effects { consumes Mark } { retires Mark; } impl fn main() -> u8 effects { consumes Mark } { finish(); return 23; } }"

def candidate : Except String (Emitted text 256) := emit text 256

theorem candidate_present : candidate.toOption.isSome = true := by
  decide +kernel

def output : Emitted text 256 := candidate.toOption.get candidate_present

theorem accepted_image : emit text 256 = .ok output :=
  Gabbro.Grammatik.except_ok_get candidate_present

/-- Both signatures are terminal transfers, with no ordinary owner consumption;
    the callee's explicit retire is retained in the actual compiler's U tree. -/
theorem image_shape :
    output.compiled.unit.fns.map (·.name) = ["finish", "main"] ∧
    (output.compiled.unit.fns.map fun f => (mkSig output.compiled.unit f).owner.moves.map (·.after)) =
      [[none], [none]] ∧
    (output.compiled.unit.fns.map fun f => (mkSig output.compiled.unit f).konsumiert) = [[], []] ∧
    (output.compiled.unit.fns.flatMap (·.body)).countP
      (fun | .retires _ => true | _ => false) = 1 ∧
    0 < output.image.code.length ∧ 16 < output.bytes.length := by
  decide +kernel

/-- Every function must return the exact empty residual inventory. -/
theorem return_inventory :
    ∀ f : (declOf output.compiled.unit).Fn, (verOf output.compiled.unit f).ende = [] := by
  decide +kernel

/-- The existing generic statement lowering erases retire for every mark, stage,
    inventory, frame and reservation. The generic `lowS_ok` retire case supplies
    the simulation used by `irBild_correct`; no separate execution path is added. -/
theorem retires_ghost {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (mark : D.Marke) (stage : Nat) (held : Res.marke mark stage ∈ Λ)
    (origin : D.Annahme) (passes : Nat) (address : D.Fn → Nat) (layout : Lay D)
    (frame : FrameLayout) (post : List II × Nat) (pinned : List Nat) (exits : Int × Int)
    (reserved : Nat) :
    lowS (V := V) passes address layout frame post pinned exits
      (l := l) (Γ := Γ) (.retires mark stage held origin) reserved =
        some ([], frei Γ reserved) := by rfl

theorem canonical_source : CanonicalSourceProgram output.compiled :=
  compile_source_program text output.compiled

theorem image_correct [Runner.IR.Kern] [Senke.CloneOK] : output.Correct := output.correct

/-- A signature alone cannot discharge the callee's terminal input. -/
def droppedText : String :=
  "module retire_probe { linear type Mark; table T count 1 owner Mark { slot { b : bool, } } impl fn finish() effects { consumes Mark } { } impl fn main() -> u8 effects { consumes Mark } { finish(); return 23; } }"

theorem dropped_image_refused :
    emit droppedText 256 = .error "lower: return without produced marks" := by
  decide +kernel

/-- The actual compiler refuses retirement of a held but borrowed owner. -/
def borrowedText : String :=
  "module retire_probe { linear type Mark; table T count 1 owner Mark { slot { b : bool, } } impl fn main() -> u8 effects { borrows Mark } { retires Mark; return 23; } }"

theorem borrowed_image_refused :
    emit borrowedText 256 = .error "retire of borrowed mark: Mark" := by
  decide +kernel

end Gabbro.Stage0.Pipeline.RetireWitness
