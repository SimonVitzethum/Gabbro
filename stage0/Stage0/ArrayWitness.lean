module
public import Stage0.SourceWitness
public import Stage0.Frontend.ExportCorrectness
import Grammatik.Kern.Taktik.KernelRfl
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


namespace Gabbro.Stage0.ArrayWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
set_option maxRecDepth 2000
set_option maxHeartbeats 100000

def characters : List Char := ['c', 'o', 'n', 's', 't', ' ', 'V', 'A', 'L', 'U', 'E', 'S', ' ', ':', ' ', '[', '[', 'u', '8', ';', ' ', '1', ']', ';', ' ', '1', ']', ' ', '=', ' ', '[', '[', '4', '2', ']', ']', ';', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '8', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', '4', '2', ';', ' ', '}']
def text : String := String.ofList characters

def candidate : Except String (Emitted text 64) := emit text 64

theorem candidate_present : candidate.toOption.isSome = true := by kernel_rfl

def output : Emitted text 64 := candidate.toOption.get candidate_present

theorem accepted_image : emit text 64 = .ok output := Gabbro.Grammatik.except_ok_get candidate_present

theorem fieldless : ∀ t : Fin output.compiled.unit.tabs.length, fieldCount output.compiled.unit t = 0 := by
  have each : (List.finRange _).all (fun t => fieldCount output.compiled.unit t == 0) = true := by
    kernel_rfl
  intro t
  exact beq_iff_eq.mp (List.all_eq_true.mp each t (List.mem_finRange t))

theorem carriers : output.compiled.unit.globs.length = 0 ∧ output.compiled.unit.axs.length = 0 ∧
    output.compiled.unit.regs.length = 0 := ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl⟩

theorem params_empty : (declOf output.compiled.unit).params output.compiled.main = [] := by kernel_rfl

theorem image_bound : Runner.Prog.IMG + output.bytes.length < 2 ^ 64 :=
  (ImagePhases.geometry output).2

attribute [irreducible] output

def members := uMembers (pre108 output.compiled.source.prepared.elaborierbar)

theorem first_present : (members[0]?).isSome = true := by kernel_rfl

def item : SItemTief := (members[0]?).get first_present

theorem array_member : item ∈ members := List.mem_of_getElem? (i := 0) (Option.some_get first_present).symm

attribute [irreducible] item

def exactShape : Bool := match item with
  | .constT "VALUES" (.array (.array (.atom "u8") (.lit 1)) (.lit 1))
      (.rows [.rows [.one (.lit 42)]]) => true
  | _ => false

theorem array_shape : exactShape = true := by kernel_rfl

theorem array_case : ∃ name element count payload, item = .constT name (.array element count) payload := by
  have h : (match item with | .constT _ (.array _ _) _ => true | _ => false) = true := by kernel_rfl
  split at h
  · rename_i name element count payload he
    exact ⟨name, element, count, payload, he⟩
  · contradiction

theorem array_constant_typed_zeuge : Frontend.ArrayMeaning output.compiled.unit output.compiled.source.scopes item :=
  output.compiled.arrayConstants _ array_member

theorem arrayMeaning_collected_zeuge :
    ∃ name, Frontend.ArrayCollected output.compiled.unit output.compiled.source.scopes name := by
  obtain ⟨name, element, count, payload, he⟩ := array_case
  have hm := array_member
  have ht := array_constant_typed_zeuge
  rw [he] at hm ht
  exact ⟨name, Frontend.arrayMeaning_collected _ _ name element count payload hm ht⟩

variable [RootNativeFloat.Hardware]

local instance kernel : Runner.IR.Kern := { toHardware := inferInstance, ans := fun _ _ _ _ => True }
local instance clone : Senke.CloneOK where
  ans _ := ⟨1, 0, by decide, trivial⟩

def initial : SourceWitness.InitialState output :=
  SourceWitness.InitialState.ofFieldless output fieldless carriers.1 carriers.2.1 carriers.2.2 image_bound

attribute [irreducible] initial

/-- The actual accepted array source/image has jointly inhabited initial contracts. -/
theorem source_image_joint_zeuge : emit text 64 = .ok output ∧ exactShape = true ∧
    Frontend.ArrayMeaning output.compiled.unit output.compiled.source.scopes item ∧
    Nonempty (SourceWitness.InitialState output) ∧
    initial.world = Senke.initialWorld output.compiled.unit output.initialValid ∧
    output.image.args = Senke.encodeEnv output.image.Y output.args ∧
    output.image.roots = output.starts.map (·.1) ∧
    output.image.rootArgs = output.starts.map (fun start => Senke.encodeEnv output.image.Y start.2) ∧
    output.startPlan.concurrent.map (fun start => (start.path, start.sourceArgs)) =
      StartArgument.sourceIdentities (uMembers (pre108 output.compiled.source.prepared.elaborierbar)) ∧
    irBild text 64 = .ok output.bytes ∧ CanonicalSourceProgram output.compiled ∧
    (∃ name, Frontend.ArrayCollected output.compiled.unit output.compiled.source.scopes name) :=
  ⟨accepted_image, array_shape, array_constant_typed_zeuge, ⟨initial⟩, rfl,
    initial.start_environments.1, initial.start_environments.2.1,
    initial.start_environments.2.2, output.starts_source,
    (by unfold irBild; rw [accepted_image]; rfl), compile_source_program text output.compiled,
    arrayMeaning_collected_zeuge⟩

theorem entry_ir_simulation_zeuge :
    output.Simulates initial.oracle initial.memory initial.world := initial.simulates

theorem roots_ir_simulation_zeuge :
    ∀ j (hj : j < output.starts.length), output.RootSimulates initial.oracle initial.memory initial.world j hj :=
  initial.roots_simulate

theorem initialized_start_environments_zeuge :
    output.image.args = Senke.encodeEnv output.image.Y output.args ∧
    output.image.roots = output.starts.map (·.1) ∧
    output.image.rootArgs = output.starts.map (fun start => Senke.encodeEnv output.image.Y start.2) :=
  initial.start_environments

end Gabbro.Stage0.ArrayWitness

namespace Gabbro.Stage0
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- An actual accepted nonempty nested-array source/image instantiates the generic
    certificate with the original initializer duty and canonical program jointly satisfied. -/
theorem exported_batch2_ir_correct_zeuge [Runner.IR.Kern] [Senke.CloneOK] :
    ∃ output : Emitted ArrayWitness.text 64,
      emit ArrayWitness.text 64 = .ok output ∧ output.Correct ∧
      CanonicalSourceProgram output.compiled ∧
      Frontend.uninitializedExport (uMembers (pre108 output.compiled.source.prepared.elaborierbar)) output.compiled.unit = false := by
  have image : irBild ArrayWitness.text 64 = .ok ArrayWitness.output.bytes := by
    change (emit ArrayWitness.text 64).map (fun output => output.bytes) = _
    rw [ArrayWitness.accepted_image]
    rfl
  obtain ⟨output, emitted, _, canonical, correct, _⟩ :=
    exported_batch2_ir_correct ArrayWitness.text 64 ArrayWitness.output.bytes image
  exact ⟨output, emitted, correct, canonical, output.compiled.initializer_exports⟩

end Gabbro.Stage0
