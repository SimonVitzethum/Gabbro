import Stage0.IRBild

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
  arguments : Env (declOf image.compiled.unit) ((declOf image.compiled.unit).params image.compiled.main)
  bytes : Senke.BytesAt memory Runner.Prog.IMG image.image.bytes
  loaded : Senke.WeltAt memory image.image.Y world
  gates : Senke.TorOK image.image.Y oracle
  view : Senke.SichtOK oracle

theorem InitialState.simulates [Runner.IR.Kern] [Senke.CloneOK]
    {src : String} {K : Nat} {options : Profil.Options} {image : Emitted src K options}
    (state : InitialState image) : image.Simulates state.oracle state.memory state.world state.arguments :=
  image.correct.2 state.oracle state.memory state.world state.arguments
    state.bytes state.loaded state.gates state.view

/-- Character-pinned source avoids reducing the UTF decoder through a whole compiler witness. -/
def characters : List Char := ['t', 'y', 'p', 'e', ' ', 'A', ' ', '=', ' ', 'u', '8', ';', ' ', 't', 'y', 'p', 'e', ' ', 'B', ' ', '=', ' ', 'A', ';', ' ', 'c', 'o', 'n', 's', 't', ' ', 'C', ' ', ':', ' ', 'B', ' ', '=', ' ', '4', '0', ' ', '+', ' ', '2', ';', ' ', 'i', 'm', 'p', 'l', ' ', 'f', 'n', ' ', 'm', 'a', 'i', 'n', '(', ')', ' ', '-', '>', ' ', 'B', ' ', '{', ' ', 'r', 'e', 't', 'u', 'r', 'n', ' ', 'C', ';', ' ', '}']
def text : String := String.ofList characters

def candidate : Except String (Emitted text 64) := emit text 64

theorem candidate_present : candidate.toOption.isSome = true := by decide +kernel

def output : Emitted text 64 := candidate.toOption.get candidate_present


theorem empty_carriers :
    output.compiled.unit.tabs.length = 0 ∧ output.compiled.unit.globs.length = 0 ∧
    output.compiled.unit.axs.length = 0 ∧ output.compiled.unit.regs.length = 0 := by
  decide +kernel

theorem params_empty : (declOf output.compiled.unit).params output.compiled.main = [] := by
  decide +kernel

theorem result_type : (declOf output.compiled.unit).erg output.compiled.main = some (.int 0 255) := by
  decide +kernel

abbrev D := declOf output.compiled.unit

private theorem noIndex {n : Nat} (h : n = 0) (i : Fin n) : False := by
  have := i.isLt
  omega

private def emptyOracle (u : UProg) (ha : u.axs.length = 0) (hr : u.regs.length = 0) :
    Orakel (declOf u) where
  wirkt a := (noIndex ha a).elim
  regLies r := (noIndex hr r).elim
  regSchreib r := (noIndex hr r).elim
  sichtbar _ _ := true

def oracle : Orakel D := emptyOracle output.compiled.unit empty_carriers.2.2.1 empty_carriers.2.2.2

private def emptyWorld (u : UProg) (ht : u.tabs.length = 0) (hg : u.globs.length = 0) :
    World (declOf u) where
  slots t := (noIndex ht t).elim
  globs g := (noIndex hg g).elim
  spur := []

def world : World D := emptyWorld output.compiled.unit empty_carriers.1 empty_carriers.2.1

private def emptyArguments (D : Deklaration) (ctx : Ctx) (h : ctx = []) : Env D ctx :=
  Eq.mpr (congrArg (fun ctx => Env D ctx) h) (Env.nil : Env D [])

def arguments : Env D (D.params output.compiled.main) := emptyArguments D _ params_empty



local instance kernel : Runner.IR.Kern := ⟨fun _ _ _ _ => True⟩
local instance clone : Senke.CloneOK where
  ans _ := ⟨1, 0, by decide, trivial⟩

private theorem emptyGates [Runner.IR.Kern] (u : UProg) (ha : u.axs.length = 0)
    (hr : u.regs.length = 0) (L : Senke.Lay (declOf u)) : Senke.TorOK L (emptyOracle u ha hr) :=
  ⟨(fun a => (noIndex ha a).elim), (fun a => (noIndex ha a).elim)⟩

local instance gates : Senke.TorOK output.image.Y oracle :=
  emptyGates output.compiled.unit empty_carriers.2.2.1 empty_carriers.2.2.2 output.image.Y
private theorem emptyView (u : UProg) (ha : u.axs.length = 0) (hr : u.regs.length = 0) :
    Senke.SichtOK (emptyOracle u ha hr) := ⟨fun _ _ => rfl⟩

local instance view : Senke.SichtOK oracle := emptyView _ empty_carriers.2.2.1 empty_carriers.2.2.2

private def loadedMemory (bytes : List Runner.B) : Runner.Mem where
  b a := (bytes[a.toNat - Runner.Prog.IMG]?).getD 0
  rd _ := true
  wr _ := true

def memory : Runner.Mem := loadedMemory output.image.bytes

theorem accepted_image : emit text 64 = .ok output :=
  Gabbro.Grammatik.except_ok_get candidate_present


theorem source_scopes :
    output.compiled.source.scopes.values = [("C", 42)] ∧
    output.compiled.source.scopes.declared = [("A", (0, 255)), ("B", (0, 255))] ∧
    output.compiled.unit.fns.length = 1 ∧ 0 < output.image.code.length := by
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

private theorem emptyWorldLoaded (u : UProg) (ht : u.tabs.length = 0) (hg : u.globs.length = 0)
    (L : Senke.Lay (declOf u)) (bytes : List Runner.B) :
    Senke.WeltAt (loadedMemory bytes) L (emptyWorld u ht hg) :=
  ⟨(fun t => (noIndex ht t).elim), (fun g => (noIndex hg g).elim), fun _ _ _ => rfl⟩

theorem world_loaded : Senke.WeltAt memory output.image.Y world :=
  emptyWorldLoaded output.compiled.unit empty_carriers.1 empty_carriers.2.1 output.image.Y _



attribute [irreducible] output

/-- A concrete accepted source/image with jointly inhabited initial contracts and entry arguments. -/
def initial : InitialState output :=
  ⟨oracle, memory, world, arguments, bytes_loaded, world_loaded, gates, view⟩

attribute [irreducible] initial

theorem source_image_joint_zeuge :
    emit text 64 = .ok output ∧
    output.compiled.source.scopes.values = [("C", 42)] ∧
    output.compiled.source.scopes.declared = [("A", (0, 255)), ("B", (0, 255))] ∧
    output.compiled.unit.fns.length = 1 ∧ 0 < output.image.code.length ∧
    Nonempty (InitialState output) :=
  ⟨accepted_image, source_scopes.1, source_scopes.2.1, source_scopes.2.2.1,
    source_scopes.2.2.2, ⟨initial⟩⟩

/-- Instantiation of the generic execution theorem at this concrete, inhabited entry state. -/
theorem entry_ir_simulation_zeuge :
    output.Simulates initial.oracle initial.memory initial.world initial.arguments :=
  initial.simulates

end Gabbro.Stage0.SourceWitness
