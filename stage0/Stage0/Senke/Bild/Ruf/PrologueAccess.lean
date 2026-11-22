module

public import Stage0.Senke.Bild.Ruf.RootProlog
public import Stage0.Senke.Bild.Mehr.Ort.LockFootprint
import Stage0.Senke.Bild.Ruf.Idle.Lowering

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Parser.UebersetzeAllg
  Gabbro.Stage0.Senke Gabbro.Stage0.Senke.BildMehr Gabbro.Stage0.Senke.Faeden
  Runner Runner.IR Runner.Beweis Runner.Mach

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
      fuss_teilG _ _ (known.elim (fun read => fuss_req _ _ read) (fun read => fuss_ens _ _ read))
    exact plainWriterFootprint_access hardware accepted duties separated allocated begins ends plain reached
      (.inl inFootprint)

/-- A pending root reads the exact committed model values. Other bodies
    can have tentative writes, but none of their write footprints can
    overlap the checked prologue reads. -/
theorem ImageRuntimePartition.prologue_world [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} (unit : ImageModelUnit output E)
    (hardware : RootNativeFloat.Hardware)
    (accepted : akzeptiertX_pruefer.akzeptiert E output.fsA.1 output.lsA.1 output.csA.1 = true)
    (duties : StartPflicht E) {O : Orakel (declOf output.compiled.unit)}
    {history : List Ev} {machine : Cfg imageTSO (Res T)}
    {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    {body : List (Option (Res T))} {pendingPhase : Mem → Nat → Res T → Prop}
    (partition : ImageRuntimePartition (imageRuntimeFootprint output E state.m)
      output E O history machine state body pendingPhase)
    {thread : Nat} (pending : body[thread]? = some none)
    {root : Σ f : (declOf output.compiled.unit).Fn, Env _ ((declOf output.compiled.unit).params f)}
    (declared : E.starts[thread]? = some root) :
    ∃ committed, WeltAt committed output.image.Y (worldZ (state.m.speicher.welt [])) ∧
      GleichAuf (imagePrologueReads output thread root.1) (machine.ms.1.view thread) committed := by
  let footprint := imageRuntimeFootprint output E state.m
  have accessible (byte : W) (read : imagePrologueReads output thread root.1 byte)
      (owner : Nat) (owned : footprint owner byte) : owner = thread :=
    output.prologue_read_owner unit hardware accepted duties declared read owned
  have projected (byte : W) (read : imagePrologueReads output thread root.1 byte) :
      GleichAt (projectSCState footprint machine.ms).1 (machine.ms.1.view thread) byte :=
    mergedView_accessible_at machine.ms.1 footprint thread byte
      (fun i store queued address touched => (partition.1 i store queued address touched).1)
      (accessible byte read)
  have main {m : Mem} (stored : WeltAt m output.image.Y.withIdle (state.m.speicher.welt [])) :
      WeltAt m output.image.Y (worldZ (state.m.speicher.welt [])) := by
    apply WeltAt.withIdle_iff.mp
    rwa [worldR_worldZ]
  rcases partition.2.2.1 with ⟨_, world⟩ | ⟨snapshots, positions, committed, related, indices⟩
  · exact ⟨_, main world, fun byte read => (projected byte read).symm⟩
  · refine ⟨committed, main related.welt, fun byte read => (projected byte read).symm.trans (related.aussen byte ?_)⟩
    intro issuer snapshot known written
    have actual : issuer = thread := accessible byte read issuer ((indices issuer snapshot known).2.write byte written)
    subst issuer
    have live := related.zustand thread snapshot known
    change body[thread]? = some (some snapshot.r) at live
    rw [pending] at live
    cases live

/-- The reading thread receives the complete canonical words for its
    precondition and snapshots from the committed world at this boundary. -/
theorem Emitted.prologue_sources [Kern] (output : Emitted src reserve options)
    {thread : Nat} {f : (declOf output.compiled.unit).Fn} {committed view : Mem}
    {world : World (declOf output.compiled.unit)}
    (stored : WeltAt committed output.image.Y world)
    (agrees : GleichAuf (imagePrologueReads output thread f) view committed) :
    WorldOnAt view output.image.Y world (· ∈ (output.compiled.program.requires f).orte) ∧
      ∀ cell ∈ oldCells (output.compiled.program.ensures f), cell.da output.image.Y →
        ValueAt output.image.Y view (BitVec.ofNat 64 (cell.adr output.image.Y)) 0 cell.ty (cell.val world) := by
  let L := output.image.Y
  have layout := output.layout_checked.1
  have value (cell : Zelle (declOf output.compiled.unit)) (valid : cell.da L)
      (reads : cell.carrier ∈ (output.compiled.program.requires f).orte ∨
        cell ∈ oldCells (output.compiled.program.ensures f)) :
      ValueAt L view (BitVec.ofNat 64 (cell.adr L)) 0 cell.ty (cell.val world) := by
    have written : ValueAt L committed (BitVec.ofNat 64 (cell.adr L)) 0 cell.ty (cell.val world) := by
      cases cell with
      | glob g => exact stored.2.1 g
      | elem t field index => exact stored.1 t field index valid
    have bound : cell.adr L + 8 * valueWords cell.ty < 2 ^ 64 := by
      have within : cell.adr L + 8 * valueWords cell.ty ≤ L.hi := by
        cases cell with
        | glob g => exact (layout.2.1 g).2
        | elem t field index => exact (layout.1 t field index valid).2
      exact within.trans_lt (layout.2.2.trans (by decide))
    refine ValueAt.congr_read_bytes bound (fun byte first last => ?_) written
    have exactBytes := agrees byte (.inr (.inr ⟨cell, valid, reads, first, by cases cell <;> exact last⟩))
    exact ⟨exactBytes.1, exactBytes.2.1⟩
  exact ⟨⟨fun t read field index valid => value (.elem t field index) valid (.inl read),
    fun g read => value (.glob g) trivial (.inl read)⟩,
    fun cell read valid => value cell valid (.inr read)⟩

end Gabbro.Stage0
