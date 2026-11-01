/-
  File:      stage0/Stage0/Senke/Hilfe.lean
  Subject:   Tools for `ir_sim`: code split in parts, field values, writing a frame slot, one instruction as a step.
-/
import Stage0.Senke.Ausdruck

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

/-- Slot `i` of the frame at slot `F` is slot `F + i`. -/
theorem slot_slot (fp : Runner.W) (F i : Nat) :
    slot (slot fp (BitVec.ofNat 64 F)) (BitVec.ofNat 64 i) = slot fp (BitVec.ofNat 64 (F + i)) := by
  simp only [slot]
  apply BitVec.eq_of_toNat_eq
  have h8 : (8 : Runner.W).toNat = 8 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h8]
  omega

/-- Caller and callee views name the same complete value span. -/
theorem ValueAt.frame_shift {D : Deklaration} {L : Lay D} {m : Runner.Mem} {fp : Runner.W}
    {F base : Nat} {τ : Ty} {v : Wert D τ} :
    ValueAt L m (slot fp (BitVec.ofNat 64 F)) base τ v ↔ ValueAt L m fp (F + base) τ v := by
  constructor
  · intro value
    refine ⟨value.1, ?_⟩
    intro i hi
    have read := value.2 i hi
    rw [slot_slot] at read
    simpa only [Nat.add_assoc] using read
  · intro value
    refine ⟨value.1, ?_⟩
    intro i hi
    rw [slot_slot]
    simpa only [Nat.add_assoc] using value.2 i hi

theorem star_cast {t t' u u' : T} {m m' : Runner.Mem} (h : Star t m t' m') (h1 : t = u) (h2 : t' = u') :
    Star u m u' m' := by subst h1; subst h2; exact h

theorem pc_add (pc : Runner.W) (a b : Nat) :
    pc + BitVec.ofNat 64 (16 * a) + BitVec.ofNat 64 (16 * b) = pc + BitVec.ofNat 64 (16 * (a + b)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]

theorem codeAt_left {m : Runner.Mem} {pc : Runner.W} {a b : List II} (h : CodeAt m pc (a ++ b)) : CodeAt m pc a :=
  fun k hk => by
    have := h k (by simp; omega)
    simpa [List.getElem_append_left hk] using this

theorem codeAt_right {m : Runner.Mem} {pc : Runner.W} {a b : List II} (h : CodeAt m pc (a ++ b)) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * a.length)) b := fun k hk => by
  have := h (a.length + k) (by simp; omega)
  rw [← pc_add] at this
  simpa [List.getElem_append_right (Nat.le_add_right _ _)] using this

theorem codeFar_left {pc fp : Runner.W} {n k K : Nat} (h : CodeFar pc (n + k) fp K) : CodeFar pc n fp K := by
  obtain ⟨h1, h2, h3⟩ := h; exact ⟨by omega, h2, by omega⟩

theorem codeFar_right {pc fp : Runner.W} {n k K : Nat} (h : CodeFar pc (n + k) fp K) :
    CodeFar (pc + BitVec.ofNat 64 (16 * n)) k fp K := by
  obtain ⟨h1, h2, h3⟩ := h
  have := pc.isLt
  have hx : (pc + BitVec.ofNat 64 (16 * n)).toNat = pc.toNat + 16 * n := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨by rw [hx]; omega, h2, by rw [hx]; omega⟩

/-- A field holding a small natural number. -/
theorem sx_nat {d : Nat} (h : d < 2 ^ 31) : sx (II.f (d : Int)) = BitVec.ofNat 64 d := by
  apply BitVec.eq_of_toNat_eq
  have hm : (BitVec.ofInt 32 (d : Int)).msb = false := by
    simp only [BitVec.msb_eq_decide, BitVec.toNat_ofInt, decide_eq_false_iff_not]; omega
  simp only [sx, II.f, BitVec.signExtend_eq_setWidth_of_msb_false hm, BitVec.toNat_setWidth,
    BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

/-- A field holding a literal of 32 bits. -/
theorem sx_lit {n : Int} (h : lit32 n = true) : sx (II.f n) = BitVec.ofInt 64 n := by
  simp only [lit32, Bool.and_eq_true, decide_eq_true_eq] at h
  apply BitVec.eq_of_toInt_eq
  simp only [sx, II.f, BitVec.toInt_signExtend_of_le (by decide : 32 ≤ 64), BitVec.toInt_ofInt]
  rw [Int.bmod_eq_of_le (by omega) (by omega), Int.bmod_eq_of_le (by omega) (by omega)]

/-- Writing slot `d` of a frame. -/
theorem wr_slot {m : Runner.Mem} {fp : Runner.W} {K d : Nat} (hF : FrameOK m fp K) (hd : d < K) (v : Runner.W) :
    m.wr64 (slot fp (BitVec.ofNat 64 d)) v = some (write m (slot fp (BitVec.ofNat 64 d)) 8 v.toNat) ∧
    (write m (slot fp (BitVec.ofNat 64 d)) 8 v.toNat).rd64 (slot fp (BitVec.ofNat 64 d)) = some v ∧
    Agree fp d K m (write m (slot fp (BitVec.ofNat 64 d)) 8 v.toNat) :=
  ⟨wr64_some (hF.wr d hd), rd64_wr64 (wr64_some (hF.wr d hd)) (hF.rd d hd),
   agree_write hF.room (Nat.le_refl d) hd _⟩

/-- One instruction as a step of the machine. -/
theorem star_ins {m m' : Runner.Mem} {pc fp : Runner.W} {i : II} (hc : CodeAt m pc [i]) (ho : i.o < 256)
    (hr : Run (op i.o ⟨pc, fp⟩) m ⟨pc + 16, fp⟩ m') :
    Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * [i].length), fp⟩ m' :=
  Star.one (run_step (t := ⟨pc, fp⟩) (by simpa using hc 0 (by simp)) ho hr)

theorem vslot_lt {reserved : Nat} {Γ : Ctx} {τ : Ty} (x : Var Γ τ) : vslot x reserved < frei Γ reserved := by
  have := variableOffset_bound x
  have := valueWords_pos τ
  unfold vslot frei; omega

/-- The complete value survives writes above its end, including all nested data. -/
theorem ValueAt.agree {m m' : Runner.Mem} {fp : Runner.W} {base lo K : Nat} {τ : Ty}
    {v : Wert D τ} (value : ValueAt L m fp base τ v) (changed : Agree fp lo K m m')
    (frame : FrameOK m fp K) (below : base + valueWords τ ≤ lo) (fits : lo ≤ K) :
    ValueAt L m' fp base τ v := by
  refine ⟨value.1, ?_⟩
  intro i hi
  have width := encodeWords_length L τ v
  rw [agree_rd_low changed frame.room (by omega) fits]
  exact value.2 i hi

theorem ResultAt.agree {m m' : Runner.Mem} {fp : Runner.W} {base lo K : Nat}
    {e : Option Ty} {v : ErgVal D e} (value : ResultAt L m fp base e v)
    (changed : Agree fp lo K m m') (frame : FrameOK m fp K)
    (below : base + resultWords e ≤ lo) (fits : lo ≤ K) : ResultAt L m' fp base e v := by
  cases e with
  | some τ => exact ValueAt.agree value changed frame below fits
  | none =>
    intro i hi
    have zero : i = 0 := by simpa using hi
    subst i
    rw [agree_rd_low changed frame.room (by change base + 1 ≤ lo at below; omega) fits]
    exact value 0 (by simp)

theorem ResultAt.first {m : Runner.Mem} {fp : Runner.W} {base : Nat}
    {e : Option Ty} {v : ErgVal D e} (value : ResultAt L m fp base e v) :
    ∃ w, m.rd64 (slot fp (BitVec.ofNat 64 base)) = some w := by
  cases e with
  | none => exact ⟨0, value 0 (by simp)⟩
  | some τ =>
    have width := encodeWords_length L τ v
    have positive := valueWords_pos τ
    exact ⟨(encodeWords L τ v)[0]'(by omega), value.2 0 (by omega)⟩

/-- A slot following an exact copy footprint retains its whole word. This is
    the shared status/header separation fact for received return areas. -/
theorem agree_rd_above {m m' : Runner.Mem} {fp : Runner.W} {lo last K i : Nat}
    (changed : Agree fp lo last m m') (room : fp.toNat + 8 * K ≤ 2 ^ 64)
    (above : last ≤ i) (fits : i < K) :
    m'.rd64 (slot fp (BitVec.ofNat 64 i)) = m.rd64 (slot fp (BitVec.ofNat 64 i)) := by
  have address := slot_toNat (i := i) room fits
  simp only [Runner.Mem.rd64, changed.rd]
  rw [le_congr (fun j hj => changed.b _ fun ⟨low, high⟩ => by
    have := fp.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, address] at low high
    omega)]


theorem envAt_agree {D : Deklaration} {L : Lay D} {m m' : Runner.Mem} {fp : Runner.W} {Γ : Ctx} {ρ : Env D Γ} {d K : Nat} {reserved : Nat}
    (h : EnvAt L m fp ρ reserved) (ha : Agree fp d K m m') (hF : FrameOK m fp K) (hd : frei Γ reserved ≤ d) (hK : d ≤ K) :
    EnvAt L m' fp ρ reserved := by
  intro τ x
  have bound := variableOffset_bound x
  exact (h τ x).agree ha hF (by unfold vslot frei at *; omega) hK

end Gabbro.Stage0.Senke
