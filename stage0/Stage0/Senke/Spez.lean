/-
  File:      stage0/Stage0/Senke/Spez.lean
  Subject:   What a lowered function owes its caller (`FunSpec`), and frames inside frames.

  `PCode m A C fp K`: every function's code `C g` lies at its address `A g`, apart from the stack (the slots
  `0 .. K-1` of the frame at `fp`, which hold every frame called from there). `FunSpec A C S dv c`: for every
  function `f`, entered with a frame whose header the `call` wrote, depth `dv` in slot 2 and the arguments in the
  parameter slots, and a stack of at least `c` slots: where `S f` (the call semantics) answers `ok v`, the IR
  returns to the caller with the word of `v` in slot 2, having changed nothing but its own frame from slot 2 on;
  where it answers `logik e`, the IR stops with `exit_group (logikCode e)`; no other answer.
-/
import Stage0.Senke.Funktion

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

variable {D : Deklaration}

def PCode (m : Runner.Mem) (A : D.Fn → Nat) (C : D.Fn → List II) (fp : Runner.W) (K : Nat) : Prop :=
  ∀ g, CodeAt m (BitVec.ofNat 64 (A g)) (C g) ∧ CodeFar (BitVec.ofNat 64 (A g)) (C g).length fp K

/-- The word of a result. -/
def EncErg : (e : Option Ty) → ErgVal D e → Runner.W → Prop
  | some τ, v, w => Enc τ v w
  | none, _, _ => True

def FunSpec (A : D.Fn → Nat) (C : D.Fn → List II) (S : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (dv : Runner.W) (c : Nat) : Prop :=
  ∀ (f : D.Fn) (m : Runner.Mem) (fp : Runner.W) (K : Nat) (rp cfp : Runner.W) (σ : World D)
    (ρ : Env D (D.params f)),
    c ≤ K → K < 2 ^ 31 → FrameOK m fp K → PCode m A C fp K →
    m.rd64 (slot fp (BitVec.ofNat 64 0)) = some rp → m.rd64 (slot fp (BitVec.ofNat 64 1)) = some cfp →
    m.rd64 (slot fp (BitVec.ofNat 64 2)) = some dv → EnvAt m fp ρ →
    match S f σ ρ with
    | .ok _ v => ∃ m', Star ⟨BitVec.ofNat 64 (A f), fp⟩ m ⟨rp, cfp⟩ m' ∧ Agree fp 2 K m m' ∧
        ∃ w, m'.rd64 (slot fp (BitVec.ofNat 64 2)) = some w ∧ EncErg (D.erg f) v w
    | .logik e => Stops ⟨BitVec.ofNat 64 (A f), fp⟩ m (logikCode e)
    | _ => False

/-! ## Frames inside frames -/

/-- Slot `i` of the frame at slot `F` is slot `F + i`. -/
theorem slot_slot (fp : Runner.W) (F i : Nat) :
    slot (slot fp (BitVec.ofNat 64 F)) (BitVec.ofNat 64 i) = slot fp (BitVec.ofNat 64 (F + i)) := by
  simp only [slot]
  apply BitVec.eq_of_toNat_eq
  have h8 : (8 : Runner.W).toNat = 8 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h8]
  omega

theorem frame_sub {m : Runner.Mem} {fp : Runner.W} {K F : Nat} (h : FrameOK m fp K) (hF : F ≤ K) :
    FrameOK m (slot fp (BitVec.ofNat 64 F)) (K - F) := by
  have hr := h.lt
  have hs : (slot fp (BitVec.ofNat 64 F)).toNat = fp.toNat + 8 * F := by
    have := fp.isLt
    have h8 : (8 : Runner.W).toNat = 8 := rfl
    simp only [slot, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h8]
    rw [Nat.mod_eq_of_lt (a := F) (by omega)]; omega
  refine ⟨by rw [hs]; omega, fun i hi => ?_, fun i hi => ?_⟩
  · rw [slot_slot]; exact h.rd _ (by omega)
  · rw [slot_slot]; exact h.wr _ (by omega)

/-- What the callee's frame changes is, in the caller's frame, the slots from `F` on. -/
theorem agree_sub {m m' : Runner.Mem} {fp : Runner.W} {K F lo : Nat} (hr : fp.toNat + 8 * K < 2 ^ 64) (hF : F ≤ K)
    (h : Agree (slot fp (BitVec.ofNat 64 F)) lo (K - F) m m') : Agree fp (F + lo) K m m' := by
  have hs : (slot fp (BitVec.ofNat 64 F)).toNat = fp.toNat + 8 * F := by
    have := fp.isLt
    have h8 : (8 : Runner.W).toNat = 8 := rfl
    simp only [slot, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h8]
    rw [Nat.mod_eq_of_lt (a := F) (by omega)]; omega
  refine ⟨h.rd, h.wr, fun x hx => h.b x fun ⟨h1, h2⟩ => hx ⟨?_, ?_⟩⟩
  · rw [hs] at h1; omega
  · rw [hs] at h2; omega

theorem codeFar_sub {pc fp : Runner.W} {n K F : Nat} (h : CodeFar pc n fp K) (hlt : fp.toNat + 8 * K < 2 ^ 64)
    (hF : F ≤ K) : CodeFar pc n (slot fp (BitVec.ofNat 64 F)) (K - F) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hs : (slot fp (BitVec.ofNat 64 F)).toNat = fp.toNat + 8 * F := by
    have := fp.isLt
    have h8 : (8 : Runner.W).toNat = 8 := rfl
    simp only [slot, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h8]
    rw [Nat.mod_eq_of_lt (a := F) (by omega)]; omega
  refine ⟨h1, by rw [hs]; omega, by rw [hs]; omega⟩

theorem pcode_sub {m : Runner.Mem} {A : D.Fn → Nat} {C : D.Fn → List II} {fp : Runner.W} {K F : Nat}
    (h : PCode m A C fp K) (hlt : fp.toNat + 8 * K < 2 ^ 64) (hF : F ≤ K) :
    PCode m A C (slot fp (BitVec.ofNat 64 F)) (K - F) :=
  fun g => ⟨(h g).1, codeFar_sub (h g).2 hlt hF⟩

theorem pcode_agree {m m' : Runner.Mem} {A : D.Fn → Nat} {C : D.Fn → List II} {fp : Runner.W} {K lo : Nat}
    (h : PCode m A C fp K) (ha : Agree fp lo K m m') : PCode m' A C fp K :=
  fun g => ⟨(h g).1.agree ha (h g).2, (h g).2⟩

end Gabbro.Stage0.Senke
