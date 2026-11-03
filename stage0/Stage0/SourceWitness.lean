module
public import Stage0.IRBild
public import Stage0.Senke.Images.InitialRead
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


namespace Gabbro.Stage0.SourceWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
  Runner.IR
set_option maxRecDepth 2000
set_option maxHeartbeats 100000

/-- The same actual initialized payload supplies the canonical source world. All
    storage/stack bounds below come from the accepted image constructor. -/
theorem loaded_initial_world [Runner.IR.Kern]
    {src : String} {K : Nat} {options : Profil.Options} {image : Emitted src K options}
    {memory : Runner.Mem} (loaded : Senke.BytesAt memory Runner.Prog.IMG image.bytes) :
    Senke.WeltAt memory image.image.Y (Senke.initialWorld image.compiled.unit image.initialValid) :=
  image.loaded_initial_world loaded

/-- All initial contracts of the existing image theorem, attached to one emitted image. -/
structure InitialState [Runner.IR.Kern] {src : String} {K : Nat} {options : Profil.Options}
    (image : Emitted src K options) where
  oracle : Orakel (declOf image.compiled.unit)
  memory : Runner.Mem
  bytes : Senke.BytesAt memory Runner.Prog.IMG image.bytes
  gates : Senke.TorOK image.image.Y oracle
  view : Senke.SichtOK oracle

/-- The world belongs to the accepted image's canonical initializer; a witness cannot
    substitute an independently chosen initial environment or source memory. -/
def InitialState.world [Runner.IR.Kern] {src : String} {K : Nat} {options : Profil.Options}
    {image : Emitted src K options} (_state : InitialState image) : World (declOf image.compiled.unit) :=
  Senke.initialWorld image.compiled.unit image.initialValid

theorem InitialState.loaded [Runner.IR.Kern]
    {src : String} {K : Nat} {options : Profil.Options} {image : Emitted src K options}
    (state : InitialState image) : Senke.WeltAt state.memory image.image.Y state.world :=
  loaded_initial_world state.bytes

theorem InitialState.simulates [Runner.IR.Kern] [Senke.CloneOK]
    {src : String} {K : Nat} {options : Profil.Options} {image : Emitted src K options}
    (state : InitialState image) : image.Simulates state.oracle state.memory state.world :=
  (image.source_correct.2 state.oracle state.memory state.bytes state.gates state.view).1

/-- The same loaded image and canonical world realize every ordered root occurrence,
    with the exact typed environment selected by its source start plan. -/
theorem InitialState.roots_simulate [Runner.IR.Kern] [Senke.CloneOK]
    {src : String} {K : Nat} {options : Profil.Options} {image : Emitted src K options}
    (state : InitialState image) :
    ∀ j (hj : j < image.starts.length), image.RootSimulates state.oracle state.memory state.world j hj :=
  (image.source_correct.2 state.oracle state.memory state.bytes state.gates state.view).2

/-- The loaded witness retains the constructor's complete main environment and one
    encoded environment per source-derived root occurrence, with the same list order. -/
theorem InitialState.start_environments [Runner.IR.Kern]
    {src : String} {K : Nat} {options : Profil.Options} {image : Emitted src K options}
    (_state : InitialState image) :
    image.image.args = Senke.encodeEnv image.image.Y image.args ∧
    image.image.roots = image.starts.map (·.1) ∧
    image.image.rootArgs = image.starts.map (fun start => Senke.encodeEnv image.image.Y start.2) := by
  have hfs : ∀ g : (declOf image.compiled.unit).Fn,
      (List.finRange image.compiled.unit.fns.length)[g.val]? = some g := by
    intro g
    simp only [List.finRange, List.getElem?_ofFn, g.isLt, ↓reduceDIte]
    congr 1
  obtain ⟨_, _, _, _, _, roots, mainArgs, rootArgs⟩ :=
    Senke.bild_lage image.emission hfs
      (fun x bound => Senke.layU_in image.compiled.unit image.tor x bound)
      (fun x => Senke.layU_dis image.compiled.unit image.tor x)
      (fun x => by simp only [Senke.layU]; omega)
      (fun x => Senke.layU_sync image.compiled.unit image.tor x)
  exact ⟨mainArgs, roots, rootArgs⟩

/-- Character-pinned source avoids reducing the UTF decoder through a whole compiler witness. -/
def characters : List Char := ['t', 'y', 'p', 'e', ' ', 'A', ' ', '=', ' ', 'i', '8', ';', ' ', 't', 'y', 'p', 'e', ' ', 'B', ' ', '=', ' ', 'A', ';', ' ', 'c', 'o', 'n', 's', 't', ' ', 'f', 'n', ' ', 'n', 'e', 'g', 'a', 't', 'i', 'v', 'e', '(', ')', ' ', '-', '>', ' ', 'B', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', '0', ' ', '-', ' ', '1', ';', ' ', '}', ' ', 'c', 'o', 'n', 's', 't', ' ', 'N', 'E', 'G', 'A', 'T', 'I', 'V', 'E', ' ', ':', ' ', 'B', ' ', '=', ' ', 'n', 'e', 'g', 'a', 't', 'i', 'v', 'e', '(', ')', ';', ' ', 'c', 'o', 'n', 's', 't', ' ', 'C', ' ', ':', ' ', 'B', ' ', '=', ' ', 'N', 'E', 'G', 'A', 'T', 'I', 'V', 'E', ' ', '+', ' ', '4', '3', ';', ' ', 't', 'y', 'p', 'e', ' ', 'B', 'o', 'u', 'n', 'd', ' ', '=', ' ', 'u', '8', ' ', 'i', 'n', ' ', '0', ' ', '.', '.', ' ', 'C', ';', ' ', 't', 'y', 'p', 'e', ' ', 'F', 'i', 'n', 'a', 'l', ' ', '=', ' ', 'B', 'o', 'u', 'n', 'd', ';', ' ', 'c', 'o', 'n', 's', 't', ' ', 'A', 'N', 'S', 'W', 'E', 'R', ' ', ':', ' ', 'F', 'i', 'n', 'a', 'l', ' ', '=', ' ', 'C', ';', ' ', 't', 'a', 'b', 'l', 'e', ' ', 'E', 'm', 'p', 't', 'y', ' ', 'c', 'o', 'u', 'n', 't', ' ', '4', '2', '9', '4', '9', '6', '7', '2', '9', '6', ' ', '{', ' ', 's', 'l', 'o', 't', ' ', '{', '}', ' ', '}', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'F', 'i', 'n', 'a', 'l', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'A', 'N', 'S', 'W', 'E', 'R', ';', ' ', '}']
def text : String := String.ofList characters

def candidate : Except String (Emitted text 64) := emit text 64

theorem candidate_present : candidate.toOption.isSome = true := by decide +kernel

def output : Emitted text 64 := candidate.toOption.get candidate_present


theorem carrier_shape :
    output.compiled.unit.tabs.length = 1 ∧ output.compiled.unit.globs.length = 0 ∧
    output.compiled.unit.axs.length = 0 ∧ output.compiled.unit.regs.length = 0 := by
  decide +kernel

theorem params_empty : (declOf output.compiled.unit).params output.compiled.main = [] := by
  decide +kernel

theorem result_type : (declOf output.compiled.unit).erg output.compiled.main = some (.int 0 42) := by
  decide +kernel

abbrev D := declOf output.compiled.unit

theorem noIndex {n : Nat} (h : n = 0) (i : Fin n) : False := by
  have := i.isLt
  omega

def emptyOracle (u : UProg) (ha : u.axs.length = 0) (hr : u.regs.length = 0) :
    Orakel (declOf u) where
  wirkt a := (noIndex ha a).elim
  regLies r := (noIndex hr r).elim
  regSchreib r := (noIndex hr r).elim
  sichtbar _ _ := true

def oracle : Orakel D := emptyOracle output.compiled.unit carrier_shape.2.2.1 carrier_shape.2.2.2

theorem fieldless : ∀ t : Fin output.compiled.unit.tabs.length,
    fieldCount output.compiled.unit t = 0 := by decide +kernel

theorem table_count : output.compiled.unit.tabs.map (·.count) = [2 ^ 32] := by decide +kernel

def world : World D := Senke.initialWorld output.compiled.unit output.initialValid

local instance kernel : Runner.IR.Kern := ⟨fun _ _ _ _ => True⟩
local instance clone : Senke.CloneOK where
  ans _ := ⟨1, 0, by decide, trivial⟩

theorem emptyGates [Runner.IR.Kern] (u : UProg) (ha : u.axs.length = 0)
    (hr : u.regs.length = 0) (L : Senke.Lay (declOf u)) : Senke.TorOK L (emptyOracle u ha hr) :=
  ⟨(fun a => (noIndex ha a).elim), (fun a => (noIndex ha a).elim),
    (fun a => (noIndex ha a).elim), (fun a => (noIndex ha a).elim)⟩

local instance gates : Senke.TorOK output.image.Y oracle :=
  emptyGates output.compiled.unit carrier_shape.2.2.1 carrier_shape.2.2.2 output.image.Y
theorem emptyView (u : UProg) (ha : u.axs.length = 0) (hr : u.regs.length = 0) :
    Senke.SichtOK (emptyOracle u ha hr) := ⟨fun _ _ => rfl⟩

local instance view : Senke.SichtOK oracle := emptyView _ carrier_shape.2.2.1 carrier_shape.2.2.2

def loadedMemory (bytes : List Runner.B) : Runner.Mem where
  b a := (bytes[a.toNat - Runner.Prog.IMG]?).getD 0
  rd _ := true
  wr _ := true

def memory : Runner.Mem := loadedMemory output.bytes

theorem accepted_image : emit text 64 = .ok output :=
  Gabbro.Grammatik.except_ok_get candidate_present


theorem source_scopes :
    output.compiled.source.scopes.values = [("NEGATIVE", -1), ("C", 42), ("ANSWER", 42)] ∧
    output.compiled.source.scopes.declared = [("A", (-128, 127)), ("B", (-128, 127)), ("Bound", (0, 42)), ("Final", (0, 42))] ∧
    output.compiled.unit.fns.length = 1 ∧ 0 < output.image.code.length := by
  decide +kernel

/-- This accepted image actually uses the new final-original-values alias path. -/
theorem aliases_final :
    output.compiled.source.scopes.aliasConstants = output.compiled.source.scopes.values := by
  decide +kernel

theorem image_bound : Runner.Prog.IMG + output.bytes.length < 2 ^ 64 := by decide +kernel

theorem loadedBytes (bytes : List Runner.B) (bound : Runner.Prog.IMG + bytes.length < 2 ^ 64) :
    Senke.BytesAt (loadedMemory bytes) Runner.Prog.IMG bytes := by
  intro i hi
  refine ⟨rfl, rfl, ?_⟩
  change (bytes[(BitVec.ofNat 64 (Runner.Prog.IMG + i)).toNat - Runner.Prog.IMG]?).getD 0 = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [Nat.add_sub_cancel_left, List.getElem?_eq_getElem hi, Option.getD_some]

theorem bytes_loaded : Senke.BytesAt memory Runner.Prog.IMG output.bytes :=
  loadedBytes _ image_bound

theorem world_loaded : Senke.WeltAt memory output.image.Y world :=
  loaded_initial_world bytes_loaded


/-- Reuse the same concrete initial-state construction for another actual emitted pure image. -/
def InitialState.ofFieldless [Runner.IR.Kern] {src : String} {K : Nat} {options : Profil.Options}
    (image : Emitted src K options)
    (_fields : ∀ t : Fin image.compiled.unit.tabs.length, fieldCount image.compiled.unit t = 0)
    (_globals : image.compiled.unit.globs.length = 0) (foreign : image.compiled.unit.axs.length = 0)
    (registers : image.compiled.unit.regs.length = 0)
    (bound : Runner.Prog.IMG + image.bytes.length < 2 ^ 64) : InitialState image where
  oracle := emptyOracle image.compiled.unit foreign registers
  memory := loadedMemory image.bytes
  bytes := loadedBytes _ bound
  gates := emptyGates _ foreign registers _
  view := emptyView _ foreign registers

attribute [irreducible] output

/-- A concrete accepted source/image with jointly inhabited initial contracts; its image carries the entry arguments. -/
def initial : InitialState output where
  oracle := oracle
  memory := memory
  bytes := bytes_loaded
  gates := gates
  view := view

attribute [irreducible] initial

theorem source_image_joint_zeuge :
    emit text 64 = .ok output ∧
    output.compiled.source.scopes.values = [("NEGATIVE", -1), ("C", 42), ("ANSWER", 42)] ∧
    output.compiled.source.scopes.declared = [("A", (-128, 127)), ("B", (-128, 127)), ("Bound", (0, 42)), ("Final", (0, 42))] ∧
    output.compiled.unit.fns.length = 1 ∧ 0 < output.image.code.length ∧
    output.compiled.unit.tabs.map (·.count) = [2 ^ 32] ∧
    output.compiled.source.scopes.aliasConstants = output.compiled.source.scopes.values ∧
    Nonempty (InitialState output) ∧
    initial.world = Senke.initialWorld output.compiled.unit output.initialValid ∧
    output.image.args = Senke.encodeEnv output.image.Y output.args ∧
    output.image.roots = output.starts.map (·.1) ∧
    output.image.rootArgs = output.starts.map (fun start => Senke.encodeEnv output.image.Y start.2) ∧
    output.startPlan.concurrent.map (fun start => (start.path, start.sourceArgs)) =
      StartArgument.sourceIdentities (uMembers (pre108 output.compiled.source.prepared.elaborierbar)) ∧
    irBild text 64 = .ok output.bytes ∧ CanonicalSourceProgram output.compiled :=
  ⟨accepted_image, source_scopes.1, source_scopes.2.1, source_scopes.2.2.1,
    source_scopes.2.2.2, table_count, aliases_final, ⟨initial⟩, rfl,
    initial.start_environments.1, initial.start_environments.2.1,
    initial.start_environments.2.2, output.starts_source,
    (by unfold irBild; rw [accepted_image]; rfl), compile_source_program text output.compiled⟩

/-- Instantiation of the generic execution theorem at this concrete, inhabited entry state. -/
theorem entry_ir_simulation_zeuge :
    output.Simulates initial.oracle initial.memory initial.world :=
  initial.simulates

theorem roots_ir_simulation_zeuge :
    ∀ j (hj : j < output.starts.length), output.RootSimulates initial.oracle initial.memory initial.world j hj :=
  initial.roots_simulate

theorem initialized_start_environments_zeuge :
    output.image.args = Senke.encodeEnv output.image.Y output.args ∧
    output.image.roots = output.starts.map (·.1) ∧
    output.image.rootArgs = output.starts.map (fun start => Senke.encodeEnv output.image.Y start.2) :=
  initial.start_environments

end Gabbro.Stage0.SourceWitness
