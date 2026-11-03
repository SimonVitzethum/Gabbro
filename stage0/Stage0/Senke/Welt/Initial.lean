/- Serialize the canonical declared initial memory with the shared value encoding.
   This is compile-time image data, not a source execution interpreter. -/
module
public import Grammatik.GabbroV.Start.GvStartPflicht
public import Stage0.Senke.Welt.AnordnungLayout
public import Stage0.Senke.Welt.StartLayout
public import Stage0.Senke.Welt.InitialBytes
public import Stage0.Senke.Welt.Initial.Constants
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

/-- The initial source world uses exactly the existing canonical memory constructor. -/
def initialWorld (u : UProg) (valid : GabbroV.sp0OkB u = true) : World (declOf u) where
  slots := (GabbroV.sp0Of u valid).slots
  globs := (GabbroV.sp0Of u valid).globs
  spur := []

theorem initialWorld_memory (u : UProg) (valid : GabbroV.sp0OkB u = true) :
    (initialWorld u valid).speicher = GabbroV.sp0Of u valid ∧ (initialWorld u valid).spur = [] :=
  ⟨rfl, rfl⟩

theorem initialWorld_column (u : UProg) (valid : GabbroV.sp0OkB u = true)
    (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) (k : Int) :
    (initialWorld u valid).slots t k f = (initialWorld u valid).slots t 0 f := by rfl

/-- Bytes of a value use the existing runner word serializer and unique encoder. -/
def initialValueBytes {D : Deklaration} (L : Lay D) (τ : Ty) (v : Wert D τ) : List Runner.B :=
  startWordBytes (encodeWords L τ v)

@[simp] theorem initialValueBytes_length {D : Deklaration} (L : Lay D) (τ : Ty) (v : Wert D τ) :
    (initialValueBytes L τ v).length = 8 * valueWords τ := by
  simp [initialValueBytes, encodeWords_length]

/-- Thread exactly the canonical global-layout cursor. Padding is image data,
    never a replacement for a declared field or a discarded high limb. -/
def initialGlobalBlocks (u : UProg) (valid : GabbroV.sp0OkB u = true)
    (L : Lay (declOf u)) : List (Fin u.globs.length) → Nat → List Runner.B
  | [], _ => []
  | g :: gs, cursor =>
    let start := alignUp cursor (wordAlign (globAlign u g))
    List.replicate (start - cursor) 0 ++
      (initialValueBytes L ((declOf u).gtyp g) ((initialWorld u valid).globs g) ++
        initialGlobalBlocks u valid L gs (start + globSz u g))

def initialGlobals (u : UProg) (valid : GabbroV.sp0OkB u = true) (L : Lay (declOf u)) : List Runner.B :=
  initialGlobalBlocks u valid L (List.finRange u.globs.length) 0

def initialColumn (u : UProg) (valid : GabbroV.sp0OkB u = true) (L : Lay (declOf u))
    (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) : List Runner.B :=
  (List.replicate ((declOf u).count t).toNat
    (initialValueBytes L ((declOf u).typ t f) ((initialWorld u valid).slots t 0 f))).flatten

def initialTable (u : UProg) (valid : GabbroV.sp0OkB u = true) (L : Lay (declOf u))
    (t : Fin u.tabs.length) : List Runner.B :=
  (List.finRange (fieldCount u t)).flatMap (initialColumn u valid L t)

/-- Same global/table/column order as layU, with complete values in every cell. -/
def initialWorldBytes (u : UProg) (valid : GabbroV.sp0OkB u = true) (L : Lay (declOf u)) : List Runner.B :=
  initialGlobals u valid L ++ (List.finRange u.tabs.length).flatMap (initialTable u valid L)

theorem initialGlobalBlocks_length (u : UProg) (valid : GabbroV.sp0OkB u = true)
    (L : Lay (declOf u)) (gs : List (Fin u.globs.length)) (cursor : Nat) :
    (initialGlobalBlocks u valid L gs cursor).length =
      globEnd gs cursor (globSz u) (fun g => wordAlign (globAlign u g)) - cursor := by
  induction gs generalizing cursor with
  | nil => simp [initialGlobalBlocks, globEnd]
  | cons g gs ih =>
    have aligned := le_alignUp cursor (wordAlign (globAlign u g))
    have tail := globEnd_ge gs (alignUp cursor (wordAlign (globAlign u g)) + globSz u g)
      (globSz u) (fun g => wordAlign (globAlign u g))
    simp only [initialGlobalBlocks, List.length_append, List.length_replicate,
      initialValueBytes_length, ih, globEnd]
    simp only [globSz] at tail ⊢
    omega

@[simp] theorem initialGlobals_length (u : UProg) (valid : GabbroV.sp0OkB u = true) (L : Lay (declOf u)) :
    (initialGlobals u valid L).length =
      globEnd (List.finRange u.globs.length) 0 (globSz u) (fun g => wordAlign (globAlign u g)) := by
  simp only [initialGlobals, initialGlobalBlocks_length, Nat.sub_zero]

@[simp] theorem initialColumn_length (u : UProg) (valid : GabbroV.sp0OkB u = true) (L : Lay (declOf u))
    (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) :
    (initialColumn u valid L t f).length = colSz u t f := by
  simp [initialColumn, colSz, Nat.mul_comm, Nat.mul_left_comm]

@[simp] theorem initialTable_length (u : UProg) (valid : GabbroV.sp0OkB u = true) (L : Lay (declOf u))
    (t : Fin u.tabs.length) : (initialTable u valid L t).length = tabSz u t := by
  simp [initialTable, List.length_flatMap, tabSz]

/-- Initialization reserves exactly the byte extent of the actual typed layout. -/
theorem initialWorldBytes_length (u : UProg) (valid : GabbroV.sp0OkB u = true) (L : Lay (declOf u)) :
    (initialWorldBytes u valid L).length =
      globEnd (List.finRange u.globs.length) 0 (globSz u) (fun g => wordAlign (globAlign u g)) + tabsSz u := by
  simp [initialWorldBytes, List.length_flatMap, tabsSz]

/-- Initialization carries the same complete ValueAt contract as loads and returns. -/
theorem initialValueBytes_at {D : Deklaration} {L : Lay D} {m : Runner.Mem} {address : Nat}
    {τ : Ty} {v : Wert D τ} (loaded : BytesAt m address (initialValueBytes L τ v))
    (valid : ValueValid L τ v) : ValueAt L m (BitVec.ofNat 64 address) 0 τ v := by
  refine ⟨valid, fun i hi => ?_⟩
  have read := startWordBytes_read (encodeWords L τ v) address loaded i hi
  have addr : Runner.IR.slot (BitVec.ofNat 64 address) (BitVec.ofNat 64 (0 + i)) =
      BitVec.ofNat 64 (address + 8 * i) := by
    simp only [Nat.zero_add, Runner.IR.slot]
    change BitVec.ofNat 64 address + BitVec.ofNat 64 i * BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    congr 1; omega
  rwa [addr]

end Gabbro.Stage0.Senke
