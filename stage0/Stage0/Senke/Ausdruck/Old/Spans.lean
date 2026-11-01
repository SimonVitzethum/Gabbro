/- Entry snapshots reuse the common complete value spans and checked storage transport. -/
module
public import Stage0.Senke.Welt.Spans.Span
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable {D : Deklaration}

/-- Entry cells retain their canonical declared type and world value. -/
def Zelle.ty : Zelle D → Ty
  | .glob g => D.gtyp g
  | .elem t f _ => D.typ t f

def Zelle.val (world : World D) : (cell : Zelle D) → Wert D cell.ty
  | .glob g => world.globs g
  | .elem t f k => world.slots t k f

namespace EntrySnapshots

local instance (L : Lay D) (cell : Zelle D) : Decidable (cell.da L) := by
  cases cell <;> unfold Zelle.da <;> infer_instance

/-- The one shared encoding determines every captured span's width. -/
def words : List (Zelle D) → Nat
  | [] => 0
  | cell :: rest => valueWords (cell.ty) + words rest

/-- Captures occupy adjacent complete spans in the function-local reserved prefix. -/
def At (L : Lay D) (world : World D) (m : Runner.Mem) (fp : Runner.W) :
    List (Zelle D) → Nat → Prop
  | [], _ => True
  | cell :: rest, base =>
      ValueAt L m fp base (cell.ty) (cell.val world) ∧
      At L world m fp rest (base + valueWords (cell.ty))

/-- Actual checked source storage, retaining full values and recursive validity. -/
def Inputs (L : Lay D) (world : World D) (m : Runner.Mem) (cells : List (Zelle D)) : Prop :=
  ∀ cell ∈ cells, StorageAt L m (cell.adr L) (cell.ty) (cell.val world)

/-- Each absolute storage read uses the existing complete-span load emitter. -/
def capture (L : Lay D) : List (Zelle D) → Nat → Option (List II)
  | [], _ => some []
  | cell :: rest, base =>
      if decide (cell.da L) && decide (cell.adr L + 8 * valueWords (cell.ty) < 2 ^ 31) then do
        let tail ← capture L rest (base + valueWords (cell.ty))
        pure (loadSpan (valueWords (cell.ty)) base (cell.adr L) ++ tail)
      else none

@[simp] theorem words_append (left right : List (Zelle D)) :
    words (left ++ right) = words left + words right := by
  induction left with
  | nil => simp [words]
  | cons cell rest ih => simp only [List.cons_append, words, ih]; omega

theorem At.append (L : Lay D) (world : World D) (m : Runner.Mem) (fp : Runner.W)
    (left right : List (Zelle D)) (base : Nat) :
    At L world m fp (left ++ right) base ↔
      At L world m fp left base ∧ At L world m fp right (base + words left) := by
  induction left generalizing base with
  | nil => simp [At, words]
  | cons cell rest ih =>
    simp only [List.cons_append, At, ih, words]
    rw [show base + (valueWords (cell.ty) + words rest) =
      base + valueWords (cell.ty) + words rest by omega]
    exact and_assoc.symm

theorem At.left {L : Lay D} {world : World D} {m : Runner.Mem} {fp : Runner.W}
    {left right : List (Zelle D)} {base : Nat}
    (saved : At L world m fp (left ++ right) base) : At L world m fp left base :=
  (At.append L world m fp left right base).mp saved |>.1

theorem At.right {L : Lay D} {world : World D} {m : Runner.Mem} {fp : Runner.W}
    {left right : List (Zelle D)} {base : Nat}
    (saved : At L world m fp (left ++ right) base) :
    At L world m fp right (base + words left) :=
  (At.append L world m fp left right base).mp saved |>.2

/-- Frame writes beginning after a complete snapshot prefix preserve all its limbs. -/
theorem At.agree {L : Lay D} {world : World D} {m m' : Runner.Mem} {fp : Runner.W}
    {cells : List (Zelle D)} {base lo K : Nat}
    (captured : At L world m fp cells base) (frame : FrameOK m fp K)
    (changed : Agree fp lo K m m') (beforeWrite : base + words cells ≤ lo) (top : lo ≤ K) :
    At L world m' fp cells base := by
  induction cells generalizing base with
  | nil => trivial
  | cons cell rest ih =>
    obtain ⟨value, tail⟩ := captured
    simp only [words] at beforeWrite
    refine ⟨⟨value.1, ?_⟩, ih tail (by omega)⟩
    intro i hi
    have bound : i < valueWords (cell.ty) := by simpa only [encodeWords_length] using hi
    rw [agree_rd_low changed frame.room (by omega) top]
    exact value.2 i hi

/-- Userspace writes preserve every captured limb below their frame frontier. -/
theorem At.agreeW {L : Lay D} {world : World D} {m m' : Runner.Mem} {fp : Runner.W}
    {cells : List (Zelle D)} {base lo K : Nat}
    (captured : At L world m fp cells base) (room : fp.toNat + 8 * K ≤ 2 ^ 64)
    (changed : AgreeW L fp lo K m m') (separated : fp.toNat + 8 * K ≤ L.lo)
    (beforeWrite : base + words cells ≤ lo) (top : lo ≤ K) :
    At L world m' fp cells base := by
  induction cells generalizing base with
  | nil => trivial
  | cons cell rest ih =>
    obtain ⟨value, tail⟩ := captured
    simp only [words] at beforeWrite
    refine ⟨⟨value.1, ?_⟩, ih tail (by omega)⟩
    intro i hi
    have bound : i < valueWords cell.ty := by simpa only [encodeWords_length] using hi
    rw [agreeW_rd_low changed separated room (by omega) top]
    exact value.2 i hi

/-- Successful capture checks validity and the complete absolute source span. -/
theorem capture_bounds {L : Lay D} : (cells : List (Zelle D)) → (base : Nat) →
    {code : List II} → capture L cells base = some code →
    ∀ cell ∈ cells, cell.da L ∧ cell.adr L + 8 * valueWords (cell.ty) < 2 ^ 31
  | [], _, _, _, _, hc => nomatch hc
  | head :: rest, base, _, emitted, cell, hc => by
    simp only [capture] at emitted
    split at emitted
    · next guard =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at emitted
      obtain ⟨tail, tailCode, _⟩ := emitted
      rcases List.mem_cons.mp hc with rfl | hc
      · exact guard
      · exact capture_bounds rest _ tailCode cell hc
    · cases emitted

/-- Capture length is exactly the common complete word count, not a scalar occurrence count. -/
theorem capture_length {L : Lay D} : (cells : List (Zelle D)) → (base : Nat) →
    {code : List II} → capture L cells base = some code → code.length = 2 * words cells
  | [], _, _, emitted => by simp only [capture, Option.some.injEq] at emitted; subst emitted; rfl
  | head :: rest, base, _, emitted => by
    simp only [capture] at emitted
    split at emitted
    · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at emitted
      obtain ⟨tail, tailCode, rfl⟩ := emitted
      have := capture_length rest _ tailCode
      simp only [List.length_append, loadSpan_length, words]
      omega
    · cases emitted

/-- Writes confined to the frame preserve every complete absolute source span. -/
theorem Inputs.agree {L : Lay D} {world : World D} {m m' : Runner.Mem} {fp : Runner.W}
    {cells : List (Zelle D)} {lo K : Nat} (inputs : Inputs L world m cells)
    (changed : Agree fp lo K m m')
    (separated : ∀ cell ∈ cells, fp.toNat + 8 * K ≤ cell.adr L)
    (bounded : ∀ cell ∈ cells, cell.adr L + 8 * valueWords (cell.ty) < 2 ^ 31) :
    Inputs L world m' cells := by
  intro cell hc
  obtain ⟨valid, source⟩ := inputs cell hc
  refine ⟨valid, ?_⟩
  intro i hi
  have width : i < valueWords (cell.ty) := by simpa only [encodeWords_length] using hi
  have bound := bounded cell hc
  have sep := separated cell hc
  have read := source i hi
  simp only [Nat.zero_add, absolute_slot] at read ⊢
  rw [rd64_agree_out changed (by omega) (Or.inr (by omega))]
  exact read

/-- Capture all distinct entry cells in sequence on the actual IR machine. The
    exact footprint excludes original parameters, headers and earlier snapshots. -/
theorem capture_ok [Kern] {L : Lay D} {world : World D} {fp : Runner.W} {K : Nat} :
    (cells : List (Zelle D)) → (base : Nat) → {code : List II} →
    capture L cells base = some code →
    ∀ (m : Runner.Mem) (pc : Runner.W), FrameOK m fp K → K < 2 ^ 31 →
    base + words cells ≤ K →
    (∀ cell ∈ cells, fp.toNat + 8 * K ≤ cell.adr L) →
    CodeAt m pc code → CodeFar pc code.length fp K → Inputs L world m cells →
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * code.length), fp⟩ m' ∧
      Agree fp base (base + words cells) m m' ∧ At L world m' fp cells base
  | [], base, _, emitted, m, pc, _, _, _, _, _, _, _ => by
    simp only [capture, Option.some.injEq] at emitted
    subst emitted
    exact ⟨m, by simpa using Star.refl _ m, Agree.refl _ _ _ _, trivial⟩
  | head :: rest, base, _, emitted, m, pc, frame, small, capacity, sep, code, far, inputs => by
    have bounds := capture_bounds (L := L) (head :: rest) base emitted
    simp only [capture] at emitted
    split at emitted
    · next guard =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at emitted
      obtain ⟨tail, tailCode, rfl⟩ := emitted
      have capacity' : base + valueWords (head.ty) + words rest ≤ K := by
        simpa only [words, Nat.add_assoc] using capacity
      have headFar : CodeFar pc (2 * valueWords (head.ty)) fp K := by
        simpa only [loadSpan_length] using
          (codeFar_left (n := (loadSpan (valueWords (head.ty)) base (head.adr L)).length)
            (k := tail.length) (by simpa only [List.length_append] using far))
      obtain ⟨m1, headRun, headChanged, headValue⟩ := loadValue_run frame small (by omega)
        (sep head (by simp)) guard.2 (codeAt_left code) headFar (inputs head (by simp))
      have changed : Agree fp base K m m1 := Agree.widen headChanged (by omega)
      have tailInputs : Inputs L world m1 rest :=
        fun cell hc => (Inputs.agree inputs changed sep (fun cell hc => (bounds cell hc).2)) cell
          (List.mem_cons_of_mem _ hc)
      have advance : 16 * (loadSpan (valueWords (head.ty)) base (head.adr L)).length =
          32 * valueWords (head.ty) := by rw [loadSpan_length]; omega
      have tailFar := codeFar_right
        (n := (loadSpan (valueWords (head.ty)) base (head.adr L)).length)
        (k := tail.length) (by simpa only [List.length_append] using far)
      rw [advance] at tailFar
      have tailAt := (codeAt_right code).agree changed (by simpa only [advance] using tailFar)
      rw [advance] at tailAt
      obtain ⟨m2, tailRun, tailChanged, tailValue⟩ := capture_ok rest _ tailCode m1 _
        (frame.agree changed) small capacity' (fun cell hc => sep cell (List.mem_cons_of_mem _ hc))
        tailAt tailFar tailInputs
      have firstTotal : Agree fp base (base + words (head :: rest)) m m1 :=
        Agree.widen headChanged (by simp only [words]; omega)
      have tailTotal : Agree fp base (base + words (head :: rest)) m1 m2 := by
        simpa only [words, Nat.add_assoc] using tailChanged.mono (show base ≤ base + valueWords (head.ty) by omega)
      have tailBroad : Agree fp (base + valueWords (head.ty)) K m1 m2 :=
        Agree.widen tailChanged capacity'
      have headSaved : ValueAt L m2 fp base (head.ty) (head.val world) :=
        (At.agree (cells := [head]) (base := base) (captured := ⟨headValue, trivial⟩)
          (frame.agree changed) tailBroad (by simp only [words]; omega) (by omega)).1
      refine ⟨m2, ?_, firstTotal.trans tailTotal, headSaved, tailValue⟩
      simpa only [List.length_append, Nat.mul_add, advance, BitVec.ofNat_add, BitVec.add_assoc]
        using headRun.trans tailRun
    · cases emitted

/-- The shared world relation already carries the whole canonical storage value. -/
theorem Inputs.of_world {world : World D} {m : Runner.Mem} {cells : List (Zelle D)}
    (stored : WeltAt m L world) (valid : ∀ cell ∈ cells, cell.da L) : Inputs L world m cells := by
  intro cell hc
  cases cell with
  | glob g => exact stored.2.1 g
  | elem t f k => exact stored.1 t f k (valid _ hc)

/-- The source's read bookkeeping changes no captured cell value. -/
theorem At.lese {world : World D} {m : Runner.Mem} {fp : Runner.W}
    {cells : List (Zelle D)} {base : Nat} (saved : At L world m fp cells base)
    (locks : List (Res D)) (places : List (D.Tab ⊕ D.Glob)) :
    At L (world.lese locks places) m fp cells base := by
  induction cells generalizing base with
  | nil => trivial
  | cons cell rest ih =>
    refine ⟨?_, ih saved.2⟩
    cases cell <;> exact saved.1

/-- Capture connected to the current function entry's world and checked layout.
    This is a real execution, with the full exact destination footprint. -/
theorem capture_world_ok [Kern] {world : World D} {m : Runner.Mem} {fp pc : Runner.W}
    {cells : List (Zelle D)} {base K : Nat} {code : List II}
    (emitted : capture L cells base = some code)
    (frame : FrameOK m fp K) (small : K < 2 ^ 31) (capacity : base + words cells ≤ K)
    (atCode : CodeAt m pc code) (far : CodeFar pc code.length fp K)
    (stored : WeltAt m L world) (layout : LayIn L) (separated : fp.toNat + 8 * K ≤ L.lo) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * code.length), fp⟩ m' ∧
      Agree fp base (base + words cells) m m' ∧ At L world m' fp cells base := by
  have bounds := capture_bounds cells base emitted
  apply capture_ok cells base emitted m pc frame small capacity ?_ atCode far
    (Inputs.of_world stored (fun cell hc => (bounds cell hc).1))
  intro cell hc
  apply Nat.le_trans separated
  have valid := (bounds cell hc).1
  cases cell with
  | glob g => exact (layout.2.1 g).1
  | elem t f k => exact (layout.1 t f k valid).1

end EntrySnapshots
end Gabbro.Stage0.Senke
