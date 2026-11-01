/- Serialize the canonical declared initial memory with the shared value encoding.
   This is compile-time image data, not a source execution interpreter. -/
module
public import Grammatik.GabbroV.GvStartPflicht
public import Stage0.Senke.Welt.AnordnungLayout
public import Stage0.Senke.Welt.StartLayout
public import Stage0.Senke.Welt.InitialBytes
public import Stage0.Senke.Ausdruck.Aggregat.Encoding
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

private theorem mapM_valid {α β : Type} (f : α → Option β) (valid : β → Prop)
    (step : ∀ x y, f x = some y → valid y) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → ∀ y ∈ ys, valid y := by
  intro xs
  induction xs with
  | nil => intro ys made; simp at made; subst ys; simp
  | cons x xs ih =>
    intro ys made
    rw [List.mapM_cons] at made
    cases first : f x with
    | none => simp [first] at made
    | some value =>
      cases rest : xs.mapM f with
      | none => simp [first, rest] at made
      | some values =>
        simp [first, rest] at made
        subst ys
        intro y hy
        rcases List.mem_cons.mp hy with same | tail
        · subst y; exact step x value first
        · exact ih values rest y tail

/-- Every existing canonical constant initializer retains recursive representation validity. -/
theorem initialConstant_valid {D : Deklaration} (L : Lay D) (τ : Ty) :
    ∀ (k : UKonst) (v : Wert D τ), GabbroV.konstWert τ k = some v → ValueValid L τ v := by
  induction τ with
  | ref n => intro k v made; cases k <;> simp [GabbroV.konstWert] at made
  | fl a b => intro k v made; cases k <;> simp [GabbroV.konstWert] at made
  | arr τ n ih =>
    intro k v made
    by_cases zero : k = .null
    · subst k
      rw [GabbroV.konstWert.eq_10] at made
      obtain ⟨z, hz, eq⟩ := Option.map_eq_some_iff.mp made
      rw [← eq]
      intro i; exact ih _ _ hz
    · rw [GabbroV.konstWert.eq_11 k τ n zero] at made
      cases items : GabbroV.konstListe k with
      | none => simp [items] at made
      | some ks =>
        cases values : ks.mapM (GabbroV.konstWert (F := D.Fn) (P := D.passt) τ) with
        | none => simp [items, values] at made
        | some vs =>
          by_cases length : vs.length = n
          · simp only [items, values, length, dite_true] at made
            cases made
            intro i
            exact mapM_valid (GabbroV.konstWert τ) (ValueValid L τ) (fun x y h => ih x y h)
              ks vs values _ (List.get_mem _ _)
          · simp [items, values, length] at made
  | _ => intro _ _ _; trivial

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
    (initialWorld u valid).slots t k f = (initialWorld u valid).slots t 0 f := rfl

/-- Bytes of a value use the existing runner word serializer and unique encoder. -/
def initialValueBytes {D : Deklaration} (L : Lay D) (τ : Ty) (v : Wert D τ) : List Runner.B :=
  startWordBytes (encodeWords L τ v)

@[simp] theorem initialValueBytes_length {D : Deklaration} (L : Lay D) (τ : Ty) (v : Wert D τ) :
    (initialValueBytes L τ v).length = 8 * valueWords τ := by
  simp [initialValueBytes, encodeWords_length]

def initialGlobals (u : UProg) (valid : GabbroV.sp0OkB u = true) (L : Lay (declOf u)) : List Runner.B :=
  (List.finRange u.globs.length).flatMap fun (g : Fin u.globs.length) =>
    initialValueBytes L ((declOf u).gtyp g) ((initialWorld u valid).globs g)

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

@[simp] theorem initialGlobals_length (u : UProg) (valid : GabbroV.sp0OkB u = true) (L : Lay (declOf u)) :
    (initialGlobals u valid L).length = globsSz u := by
  unfold initialGlobals
  rw [List.length_flatMap]
  simp only [initialValueBytes_length]
  rfl

@[simp] theorem initialColumn_length (u : UProg) (valid : GabbroV.sp0OkB u = true) (L : Lay (declOf u))
    (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) :
    (initialColumn u valid L t f).length = colSz u t f := by
  simp [initialColumn, colSz, Nat.mul_comm, Nat.mul_left_comm]

@[simp] theorem initialTable_length (u : UProg) (valid : GabbroV.sp0OkB u = true) (L : Lay (declOf u))
    (t : Fin u.tabs.length) : (initialTable u valid L t).length = tabSz u t := by
  simp [initialTable, List.length_flatMap, tabSz]

/-- Initialization reserves exactly the byte extent of the actual typed layout. -/
theorem initialWorldBytes_length (u : UProg) (valid : GabbroV.sp0OkB u = true) (L : Lay (declOf u)) :
    (initialWorldBytes u valid L).length = globsSz u + tabsSz u := by
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
