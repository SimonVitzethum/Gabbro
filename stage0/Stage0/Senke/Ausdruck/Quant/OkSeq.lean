/-
  File:      stage0/Stage0/Senke/Ausdruck/Quant/OkSeq.lean
  Subject:   Sequencing and constant-operand lemmas for `Ok`, independent of the world: the two halves of a code
             run one after the other, and a binary instruction against a literal.
-/
import Stage0.Senke.Ausdruck.Top

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- Code in two parts: what the first leaves in slot `d` is what the second starts from. -/
theorem ok_seq {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {a b : List II} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {Pa Pb : Runner.W → Prop} (h : Pre L m pc fp K d (a ++ b) ρ W reserved)
    (ha : Ok m pc fp K d a Pa)
    (hb : ∀ m' w, Pre L m' (pc + BitVec.ofNat 64 (16 * a.length)) fp K d b ρ W reserved →
      m'.rd64 (slot fp (BitVec.ofNat 64 d)) = some w → Pa w →
      Ok m' (pc + BitVec.ofNat 64 (16 * a.length)) fp K d b Pb)
    (hK : d ≤ K) : Ok m pc fp K d (a ++ b) Pb := by
  obtain ⟨m1, s1, a1, w, r, p⟩ := ha
  have hp1 := h.next a1 (Nat.le_refl _) hK
  obtain ⟨m2, s2, a2, w2, r2, p2⟩ := hb m1 w hp1 r p
  refine ⟨m2, s1.trans ?_, a1.trans a2, w2, r2, p2⟩
  have e : pc + BitVec.ofNat 64 (16 * (a ++ b).length) =
      pc + BitVec.ofNat 64 (16 * a.length) + BitVec.ofNat 64 (16 * b.length) := by
    rw [List.length_append, pc_add]
  rw [e]; exact s2

/-- Nothing to run: slot `d` keeps its word. -/
theorem ok_nil {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {w : Runner.W}
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 d)) = some w) : Ok m pc fp K d [] (· = w) :=
  ⟨m, by simpa using Star.refl _ m, Agree.refl _ _ _ _, w, hr, rfl⟩

/-- `d := g (slot d) k`: the constant into `d+1`, then the instruction `o`. -/
theorem binK_ok {m : Runner.Mem} {pc fp : Runner.W} {K d o : Nat} {k : Int} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {w r : Runner.W} {g : Runner.W → Runner.W → Option Runner.W}
    (h : Pre L m pc fp K d [ci 1 (d + 1) k 0, ci o d d (d + 1)] ρ W reserved)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 d)) = some w) (hk : lit32 k = true) (hop : op o = bin g) (ho : o < 256)
    (hg : g w (BitVec.ofInt 64 k) = some r) (hK : d + 1 < K) :
    Ok m pc fp K d [ci 1 (d + 1) k 0, ci o d d (d + 1)] (· = r) := by
  have h' : Pre L m pc fp K d ([] ++ [ci 1 (d + 1) k 0] ++ [ci o d d (d + 1)]) ρ W reserved := by simpa using h
  have := bin_ok2 (ca := []) (cb := [ci 1 (d + 1) k 0]) (Pa := (· = w)) (P := (· = r)) (ok_nil hr)
    (Pb := (· = BitVec.ofInt 64 k))
    (fun m' pc' hp' => const_ok (k := k) (d := d + 1) (by rw [show ((d + 1 : Nat) : Int) = (d : Int) + 1 by omega]; exact hp') hk hK) (fun wa wb pa pb => ⟨r, by rw [pa, pb]; exact hg, rfl⟩) hop ho hK h'
  simpa using this

/-- The address of element `k`: the index word times the stride plus the column. -/
theorem addr_w {n : Int} {s c : Nat} (hn : 0 ≤ n) :
    BitVec.ofInt 64 n * BitVec.ofInt 64 (s : Int) + BitVec.ofInt 64 (c : Int) = BitVec.ofNat 64 (c + s * n.toNat) := by
  rw [← BitVec.ofInt_natCast, ← BitVec.ofInt_mul, ← BitVec.ofInt_add]
  congr 1
  rw [Int.natCast_add, Int.natCast_mul, Int.toNat_of_nonneg hn]
  rw [Int.mul_comm, Int.add_comm]

end Gabbro.Stage0.Senke
