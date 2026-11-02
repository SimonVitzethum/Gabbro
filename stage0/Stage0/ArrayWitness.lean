module
public import Stage0.SourceWitness
@[expose] public section


namespace Gabbro.Stage0.ArrayWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
set_option maxRecDepth 2000
set_option maxHeartbeats 100000

def characters : List Char := ['c', 'o', 'n', 's', 't', ' ', 'V', 'A', 'L', 'U', 'E', 'S', ' ', ':', ' ', '[', '[', 'u', '8', ';', ' ', '1', ']', ';', ' ', '1', ']', ' ', '=', ' ', '[', '[', '4', '2', ']', ']', ';', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'u', '8', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', '4', '2', ';', ' ', '}']
def text : String := String.ofList characters

def candidate : Except String (Emitted text 64) := emit text 64

theorem candidate_present : candidate.toOption.isSome = true := by decide +kernel

def output : Emitted text 64 := candidate.toOption.get candidate_present

theorem accepted_image : emit text 64 = .ok output := Gabbro.Grammatik.except_ok_get candidate_present

theorem fieldless : ∀ t : Fin output.compiled.unit.tabs.length, fieldCount output.compiled.unit t = 0 := by
  decide +kernel

theorem carriers : output.compiled.unit.globs.length = 0 ∧ output.compiled.unit.axs.length = 0 ∧
    output.compiled.unit.regs.length = 0 := by decide +kernel

theorem params_empty : (declOf output.compiled.unit).params output.compiled.main = [] := by decide +kernel

theorem image_bound : Runner.Prog.IMG + output.image.bytes.length < 2 ^ 64 := by decide +kernel

attribute [irreducible] output

def members := uMembers (pre108 output.compiled.source.prepared.selected)

theorem first_present : (members[0]?).isSome = true := by decide +kernel

def item : SItemTief := (members[0]?).get first_present

theorem array_member : item ∈ members := List.mem_of_getElem? (i := 0) (Option.some_get first_present).symm

attribute [irreducible] item

def exactShape : Bool := match item with
  | .constT "VALUES" (.array (.array (.atom "u8") (.lit 1)) (.lit 1))
      (.rows [.rows [.one (.lit 42)]]) => true
  | _ => false

theorem array_shape : exactShape = true := by decide +kernel

theorem array_case : ∃ name element count payload, item = .constT name (.array element count) payload := by
  have h : (match item with | .constT _ (.array _ _) _ => true | _ => false) = true := by decide +kernel
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

local instance kernel : Runner.IR.Kern := ⟨fun _ _ _ _ => True⟩
local instance clone : Senke.CloneOK where
  ans _ := ⟨1, 0, by decide, trivial⟩

def initial : SourceWitness.InitialState output :=
  SourceWitness.InitialState.ofFieldless output fieldless carriers.1 carriers.2.1 carriers.2.2 image_bound

attribute [irreducible] initial

/-- The actual accepted array source/image has jointly inhabited initial contracts. -/
theorem source_image_joint_zeuge : emit text 64 = .ok output ∧ exactShape = true ∧
    Frontend.ArrayMeaning output.compiled.unit output.compiled.source.scopes item ∧
    Nonempty (SourceWitness.InitialState output) :=
  ⟨accepted_image, array_shape, array_constant_typed_zeuge, ⟨initial⟩⟩

theorem entry_ir_simulation_zeuge :
    output.Simulates initial.oracle initial.memory initial.world := initial.simulates

end Gabbro.Stage0.ArrayWitness
