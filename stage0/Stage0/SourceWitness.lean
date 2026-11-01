module
public import Stage0.IRBild
@[expose] public section


namespace Gabbro.Stage0.SourceWitness
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
  Runner.IR
set_option maxRecDepth 2000
set_option maxHeartbeats 100000

/-- All initial contracts of the existing image theorem, attached to one emitted image. -/
structure InitialState [Runner.IR.Kern] {src : String} {K : Nat} {options : Profil.Options}
    (image : Emitted src K options) where
  oracle : Orakel (declOf image.compiled.unit)
  memory : Runner.Mem
  world : World (declOf image.compiled.unit)
  bytes : Senke.BytesAt memory Runner.Prog.IMG image.image.bytes
  loaded : Senke.WeltAt memory image.image.Y world
  gates : Senke.TorOK image.image.Y oracle
  view : Senke.SichtOK oracle

theorem InitialState.simulates [Runner.IR.Kern] [Senke.CloneOK]
    {src : String} {K : Nat} {options : Profil.Options} {image : Emitted src K options}
    (state : InitialState image) : image.Simulates state.oracle state.memory state.world :=
  image.correct.2 state.oracle state.memory state.world
    state.bytes state.loaded state.gates state.view

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

private theorem noIndex {n : Nat} (h : n = 0) (i : Fin n) : False := by
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

def fieldlessWorld (u : UProg) (ht : ∀ t : Fin u.tabs.length, fieldCount u t = 0)
    (hg : u.globs.length = 0) : World (declOf u) where
  slots t _ f := (noIndex (ht t) f).elim
  globs g := (noIndex hg g).elim
  spur := []

def world : World D := fieldlessWorld output.compiled.unit fieldless carrier_shape.2.1

local instance kernel : Runner.IR.Kern := ⟨fun _ _ _ _ => True⟩
local instance clone : Senke.CloneOK where
  ans _ := ⟨1, 0, by decide, trivial⟩

private theorem emptyGates [Runner.IR.Kern] (u : UProg) (ha : u.axs.length = 0)
    (hr : u.regs.length = 0) (L : Senke.Lay (declOf u)) : Senke.TorOK L (emptyOracle u ha hr) :=
  ⟨(fun a => (noIndex ha a).elim), (fun a => (noIndex ha a).elim)⟩

local instance gates : Senke.TorOK output.image.Y oracle :=
  emptyGates output.compiled.unit carrier_shape.2.2.1 carrier_shape.2.2.2 output.image.Y
private theorem emptyView (u : UProg) (ha : u.axs.length = 0) (hr : u.regs.length = 0) :
    Senke.SichtOK (emptyOracle u ha hr) := ⟨fun _ _ => rfl⟩

local instance view : Senke.SichtOK oracle := emptyView _ carrier_shape.2.2.1 carrier_shape.2.2.2

def loadedMemory (bytes : List Runner.B) : Runner.Mem where
  b a := (bytes[a.toNat - Runner.Prog.IMG]?).getD 0
  rd _ := true
  wr _ := true

def memory : Runner.Mem := loadedMemory output.image.bytes

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

theorem image_bound : Runner.Prog.IMG + output.image.bytes.length < 2 ^ 64 := by decide +kernel

private theorem loadedBytes (bytes : List Runner.B) (bound : Runner.Prog.IMG + bytes.length < 2 ^ 64) :
    Senke.BytesAt (loadedMemory bytes) Runner.Prog.IMG bytes := by
  intro i hi
  refine ⟨rfl, rfl, ?_⟩
  change (bytes[(BitVec.ofNat 64 (Runner.Prog.IMG + i)).toNat - Runner.Prog.IMG]?).getD 0 = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [Nat.add_sub_cancel_left, List.getElem?_eq_getElem hi, Option.getD_some]

theorem bytes_loaded : Senke.BytesAt memory Runner.Prog.IMG output.image.bytes :=
  loadedBytes _ image_bound

private theorem fieldlessWorldLoaded (u : UProg)
    (ht : ∀ t : Fin u.tabs.length, fieldCount u t = 0) (hg : u.globs.length = 0)
    (L : Senke.Lay (declOf u)) (bytes : List Runner.B) :
    Senke.WeltAt (loadedMemory bytes) L (fieldlessWorld u ht hg) :=
  ⟨(fun t f _ => (noIndex (ht t) f).elim), (fun g => (noIndex hg g).elim), fun _ _ _ => rfl⟩

theorem world_loaded : Senke.WeltAt memory output.image.Y world :=
  fieldlessWorldLoaded output.compiled.unit fieldless carrier_shape.2.1 output.image.Y _


/-- Reuse the same concrete initial-state construction for another actual emitted pure image. -/
def InitialState.ofFieldless [Runner.IR.Kern] {src : String} {K : Nat} {options : Profil.Options}
    (image : Emitted src K options)
    (fields : ∀ t : Fin image.compiled.unit.tabs.length, fieldCount image.compiled.unit t = 0)
    (globals : image.compiled.unit.globs.length = 0) (foreign : image.compiled.unit.axs.length = 0)
    (registers : image.compiled.unit.regs.length = 0)
    (bound : Runner.Prog.IMG + image.image.bytes.length < 2 ^ 64) : InitialState image :=
  ⟨emptyOracle image.compiled.unit foreign registers, loadedMemory image.image.bytes,
    fieldlessWorld image.compiled.unit fields globals,
    loadedBytes _ bound, fieldlessWorldLoaded _ fields globals _ _,
    emptyGates _ foreign registers _, emptyView _ foreign registers⟩

attribute [irreducible] output

/-- A concrete accepted source/image with jointly inhabited initial contracts; its image carries the entry arguments. -/
def initial : InitialState output :=
  ⟨oracle, memory, world, bytes_loaded, world_loaded, gates, view⟩

attribute [irreducible] initial

theorem source_image_joint_zeuge :
    emit text 64 = .ok output ∧
    output.compiled.source.scopes.values = [("NEGATIVE", -1), ("C", 42), ("ANSWER", 42)] ∧
    output.compiled.source.scopes.declared = [("A", (-128, 127)), ("B", (-128, 127)), ("Bound", (0, 42)), ("Final", (0, 42))] ∧
    output.compiled.unit.fns.length = 1 ∧ 0 < output.image.code.length ∧
    output.compiled.unit.tabs.map (·.count) = [2 ^ 32] ∧
    output.compiled.source.scopes.aliasConstants = output.compiled.source.scopes.values ∧
    Nonempty (InitialState output) :=
  ⟨accepted_image, source_scopes.1, source_scopes.2.1, source_scopes.2.2.1,
    source_scopes.2.2.2, table_count, aliases_final, ⟨initial⟩⟩

/-- Instantiation of the generic execution theorem at this concrete, inhabited entry state. -/
theorem entry_ir_simulation_zeuge :
    output.Simulates initial.oracle initial.memory initial.world :=
  initial.simulates

end Gabbro.Stage0.SourceWitness
