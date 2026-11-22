module

public import Stage0.Senke.Bild.Ruf.RootProlog
import Stage0.Senke.Bild.Mehr.Ort.LockFootprint
import Stage0.Senke.Bild.Ruf.Idle.Lowering

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Stage0.Senke Gabbro.Stage0.Senke.BildMehr Gabbro.Stage0.Senke.Faeden Runner Runner.IR

variable {src : String} {reserve : Nat} {options : Profil.Options}

/-- The private root stack, installed code, required carriers and entry snapshots
    supply the read bytes of the root prologue. -/
def imagePrologueReads (output : Emitted src reserve options) (thread : Nat)
    (f : (declOf output.compiled.unit).Fn) (byte : W) : Prop :=
  imageStackFootprint output thread byte ∨ byte.toNat < output.image.fp0 ∨
    ∃ cell : Zelle (declOf output.compiled.unit), cell.da output.image.Y ∧
      (cell.carrier ∈ (output.compiled.program.requires f).orte ∨
        cell ∈ oldCells (output.compiled.program.ensures f)) ∧
      cell.adr output.image.Y ≤ byte.toNat ∧ byte.toNat < cell.adr output.image.Y + cell.bytes

/-- Every buffered-byte owner allowed by the checked image footprint is
    the reader itself whenever the prologue can read that byte. -/
theorem Emitted.prologue_read_owner [Kern] (output : Emitted src reserve options)
    {E : Einheit (declOf output.compiled.unit)} (unit : ImageModelUnit output E)
    (hardware : RootNativeFloat.Hardware)
    (accepted : akzeptiertX_pruefer.akzeptiert E output.fsA.1 output.lsA.1 output.csA.1 = true)
    (duties : StartPflicht E) {thread writer : Nat}
    {root : Σ f : (declOf output.compiled.unit).Fn, Env _ ((declOf output.compiled.unit).params f)}
    (declared : E.starts[thread]? = some root)
    {source : RufMaschineG (declOf output.compiled.unit).mitRuhe} {byte : W}
    (readable : imagePrologueReads output thread root.1 byte)
    (owned : imageRuntimeFootprint output E source writer byte) : writer = thread := by
  have placed (owner : Nat) (x : W) (owns : imageRuntimeFootprint output E source owner x) :=
    imageRuntimeFootprint_placed output.layout_checked.1.withIdle owns
  rcases readable with stack | code | ⟨cell, valid, reads, first, last⟩
  · exact imageStackFootprint_owner placed stack owned
  · exact ((Nat.not_le_of_lt code) (imageFootprint_after_code placed owned)).elim
  have readsContract : cell.carrier ∈ (E.P.requires root.1).orte ∨ cell.carrier ∈ (E.P.ensures root.1).orte := by
    rw [unit.program]
    exact reads.elim Or.inl (fun captured => .inr (oldCells_carrier _ cell captured))
  have listed : root.1 ∈ E.ws := by
    unfold Einheit.ws
    exact List.mem_map_of_mem (List.mem_append_left _ (List.mem_append_left _ (List.mem_of_getElem? declared)))
  let physical := cell.withIdle
  have allocated := (cell.withIdle_da output.image.Y).mpr valid
  have begins : physical.adr output.image.Y.withIdle ≤ byte.toNat := by
    simpa only [physical, Zelle.withIdle_adr] using first
  have ends : byte.toNat < physical.adr output.image.Y.withIdle + physical.bytes := by
    simpa only [physical, Zelle.withIdle_adr, Zelle.withIdle_bytes] using last
  have separated := output.layout_checked.2.1.withIdle
  have unguarded : ∀ lock, ¬ Bewacht physical.carrier lock := by
    have noGuard := output.root_contract_unguarded hardware accepted listed readsContract
    cases cell <;> exact noGuard
  rcases owned with (stack | guarded) | plain
  · have world := carrierFootprint_bounds output.layout_checked.1.withIdle
      (carriers := fun _ => True) ⟨physical, allocated, trivial, begins, ends⟩
    exact ((Nat.not_le_of_lt (imageStackFootprint_before_world stack)) world.1).elim
  · obtain ⟨other, present, lower, higher, lock, _⟩ := guarded
    have equal : physical = other := by
      by_contra different
      rcases separated.spans physical other allocated present different with left | right <;> omega
    obtain ⟨guard, guards⟩ := lock
    exact (unguarded guard (equal.symm ▸ guards)).elim
  · have entry : (initRuhe E.starts thread).1 = some root.1 := by
      change (initRuhe E.starts thread).1 = _
      rw [initRuhe, declared]
    have reached : kVon E.P.mitRuhe (fsRuhe output.fsA.1) (initRuhe E.starts) thread (some root.1) = true := by
      rw [← entry]
      exact reachB_wurzel E.P.mitRuhe (fsRuhe output.fsA.1) (initRuhe E.starts thread).1
    have known : physical.carrier ∈ (E.P.mitRuhe.requires (some root.1)).orte ∨
        physical.carrier ∈ (E.P.mitRuhe.ensures (some root.1)).orte := by
      cases cell <;> simpa only [physical, Zelle.withIdle, Zelle.carrier,
        requires_mitRuhe_orte, ensures_mitRuhe_orte] using readsContract
    have inFootprint : physical.carrier ∈ fussOrteG E.P.mitRuhe (some root.1) :=
      fuss_teilG _ _ (known.elim (fuss_req _ _) (fuss_ens _ _))
    exact plainWriterFootprint_access hardware accepted duties separated allocated begins ends plain reached
      (.inl inFootprint)

end Gabbro.Stage0
