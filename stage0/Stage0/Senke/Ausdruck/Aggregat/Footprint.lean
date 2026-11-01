/- Exact union of the explicit store temporary and the typed world span. -/
import Runner.IR.Rahmen
namespace Gabbro.Stage0.Senke
open Runner.IR Runner.Mem

structure SpanEffect (fp : Runner.W) (tmp address count : Nat) (m m' : Runner.Mem) : Prop where
  rd : m'.rd = m.rd
  wr : m'.wr = m.wr
  b : ∀ x, ¬ inSlots fp tmp (tmp + 1) x →
    ¬ (address ≤ x.toNat ∧ x.toNat < address + 8 * count) → m'.b x = m.b x

theorem SpanEffect.refl (fp : Runner.W) (tmp address count : Nat) (m : Runner.Mem) :
    SpanEffect fp tmp address count m m := ⟨rfl, rfl, fun _ _ _ => rfl⟩

theorem SpanEffect.frame {fp : Runner.W} {tmp address count K : Nat} {m m' : Runner.Mem}
    (h : SpanEffect fp tmp address count m m') (frame : FrameOK m fp K) : FrameOK m' fp K :=
  ⟨frame.lt, by intro i hi; rw [h.rd]; exact frame.rd i hi,
    by intro i hi; rw [h.wr]; exact frame.wr i hi⟩

/-- Reads disjoint from both explicit destinations are unchanged. -/
theorem SpanEffect.read {fp : Runner.W} {tmp address count a : Nat} {m m' : Runner.Mem}
    (h : SpanEffect fp tmp address count m m') (bound : a + 8 ≤ 2 ^ 64)
    (scratch : a + 8 ≤ fp.toNat + 8 * tmp ∨ fp.toNat + 8 * (tmp + 1) ≤ a)
    (world : a + 8 ≤ address ∨ address + 8 * count ≤ a) :
    m'.rd64 (BitVec.ofNat 64 a) = m.rd64 (BitVec.ofNat 64 a) := by
  simp only [rd64, h.rd]
  rw [le_congr (m := m') (m' := m) (fun j hj => ?_)]
  have e : BitVec.ofNat 64 a + BitVec.ofNat 64 j = BitVec.ofNat 64 (a + j) := by rw [BitVec.ofNat_add]
  rw [e]
  have hn : (BitVec.ofNat 64 (a + j)).toNat = a + j := by simp only [BitVec.toNat_ofNat]; omega
  apply h.b
  · simp only [inSlots, hn]; omega
  · rw [hn]; omega

theorem SpanEffect.scratch {fp : Runner.W} {tmp address count K : Nat} {m : Runner.Mem}
    (frame : FrameOK m fp K) (ht : tmp < K) (w : Runner.W) :
    SpanEffect fp tmp address count m (write m (slot fp (BitVec.ofNat 64 tmp)) 8 w.toNat) := by
  have h : Agree fp tmp (tmp + 1) m (write m (slot fp (BitVec.ofNat 64 tmp)) 8 w.toNat) :=
    agree_write (by have := frame.room; omega) (Nat.le_refl _) (Nat.lt_succ_self _) _
  exact ⟨h.rd, h.wr, fun x hx _ => h.b x hx⟩

theorem SpanEffect.store {fp : Runner.W} {tmp address count : Nat} {m : Runner.Mem}
    (pos : 0 < count) (bound : address + 8 * count ≤ 2 ^ 64) (w : Runner.W) :
    SpanEffect fp tmp address count m (write m (BitVec.ofNat 64 address) 8 w.toNat) := by
  refine ⟨rfl, rfl, fun x _ hx => ?_⟩
  change (if _ then _ else _) = _
  split
  · next hit =>
    have := x.isLt
    have ha : (BitVec.ofNat 64 address).toNat = address := by simp only [BitVec.toNat_ofNat]; omega
    simp only [BitVec.toNat_sub, ha] at hit
    apply False.elim; apply hx; constructor <;> omega
  · rfl

theorem SpanEffect.trans {fp : Runner.W} {tmp address count : Nat} {m m' m'' : Runner.Mem}
    (h : SpanEffect fp tmp address count m m') (h' : SpanEffect fp tmp address count m' m'') :
    SpanEffect fp tmp address count m m'' :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, fun x hx hw => (h'.b x hx hw).trans (h.b x hx hw)⟩

theorem SpanEffect.tail {fp : Runner.W} {tmp address count : Nat} {m m' : Runner.Mem}
    (h : SpanEffect fp tmp (address + 8) count m m') :
    SpanEffect fp tmp address (count + 1) m m' := by
  refine ⟨h.rd, h.wr, fun x hx hw => h.b x hx ?_⟩
  intro ⟨a, b⟩; apply hw; constructor <;> omega

/-- If both permitted spans lie in the frame, the same exact footprint is a frame agreement. -/
theorem SpanEffect.agreeFrame {fp : Runner.W} {tmp address count dst K : Nat} {m m' : Runner.Mem}
    (h : SpanEffect fp tmp address count m m') (low : dst ≤ tmp) (high : tmp < K)
    (start : fp.toNat + 8 * dst ≤ address) (stop : address + 8 * count ≤ fp.toNat + 8 * K) :
    Agree fp dst K m m' := by
  refine ⟨h.rd, h.wr, fun x hx => h.b x ?_ ?_⟩
  · intro ⟨a, b⟩; apply hx; constructor <;> omega
  · intro ⟨a, b⟩; apply hx; constructor <;> omega

theorem SpanEffect.widenCount {fp : Runner.W} {tmp address count larger : Nat} {m m' : Runner.Mem}
    (h : SpanEffect fp tmp address count m m') (le : count ≤ larger) :
    SpanEffect fp tmp address larger m m' := by
  refine ⟨h.rd, h.wr, fun x hx hw => h.b x hx ?_⟩
  intro ⟨a, b⟩; apply hw; constructor <;> omega

end Gabbro.Stage0.Senke
