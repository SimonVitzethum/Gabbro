/- Instruction-level operations shared by both consuming selector loops. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Scan
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Blocks
public import Stage0.Senke.Ausdruck.Quant.Bind
public import Stage0.Senke.Ausdruck.Arithmetik.Interval
public section

namespace Gabbro.Stage0.Senke.Consuming
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- The exact bound test emitted in both scans. The index is read directly
    from its binder; materializing the bound preserves every selector word. -/
theorem scan_bound_ok {Γ : Ctx} {ρ : Env D Γ} {m : Mem} {pc fp : W}
    {K d index j : Nat} {count : Int} {W : Mem → Prop}
    (hp : Pre L m pc fp K d
      (travCountC (d + 1) count ++ [ci 13 d index (d + 1)]) ρ W reserved)
    (room : d + 3 ≤ K) (below : index < d) (smallIndex : j < 2 ^ 63)
    (countBound : inW count count = true)
    (read : m.rd64 (slot fp (BitVec.ofNat 64 index)) = some (BitVec.ofNat 64 j)) :
    Ok m pc fp K d
      (travCountC (d + 1) count ++ [ci 13 d index (d + 1)])
      (· = Runner.IR.bool (decide ((j : Int) < count))) := by
  obtain ⟨m1, constant, a1, w1, read1, rfl⟩ := travCountC_ok count (by omega)
    { hp.left with ctx := by have := hp.ctx; omega }
  have tail := hp.next (a1.mono (Nat.le_succ _)) (Nat.le_refl _) (by omega)
  have indexRead : m1.rd64 (slot fp (BitVec.ofNat 64 index)) = some (BitVec.ofNat 64 j) := by
    rw [agree_rd_low a1 hp.frame.room (by omega) (by omega)]
    exact read
  obtain ⟨m2, comparison, a2, w2, read2, rfl⟩ := eng_bin_ok tail
    (by omega) (by omega) (by omega) indexRead read1
    (g := fun a b => some (Runner.IR.bool (a.slt b))) rfl (by decide) rfl
  refine ⟨m2, ?_, (a1.mono (Nat.le_succ _)).trans a2, _, read2, ?_⟩
  · simpa only [List.length_append, List.length_singleton, pc_add] using constant.trans comparison
  · rw [slt_k smallIndex countBound]

/-- Reuse the actual lowered membership operand for the predecessor. The
    candidate word is backed up below expression scratch, the predecessor is
    installed in membership's canonical binder, and the candidate is restored
    before the edge operand runs. The live flag and predecessor word survive.
    Nested quantifiers/counts inside membership may borrow their own binder
    slots, because the child proof restores them before returning. -/
theorem member_borrow_ok {Γ : Ctx} {ρ : Env D Γ} {m : Mem} {pc fp : W}
    {K : Nat} {count : Int} {predecessor : Zahl 0 (count - 1)} {candidate : W}
    {cb : List II} {P : W → Prop} {W : Mem → Prop}
    (widthOne : valueWords (.index count) = 1)
    (room : frei Γ reserved + 5 ≤ K)
    (hp : Pre L m pc fp K (frei Γ reserved + 4)
      ([ci 2 (frei Γ reserved + 3) (frei Γ reserved) 0,
        ci 2 (frei Γ reserved) (frei Γ reserved + 1) 0] ++ cb ++
        [ci 2 (frei Γ reserved) (frei Γ reserved + 3) 0]) ρ W reserved)
    (candidateRead : m.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved))) = some candidate)
    (predecessorRead : m.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved + 1))) =
      some (BitVec.ofInt 64 predecessor.n))
    (operand : ∀ m pc, Pre L m pc fp K (frei Γ reserved + 4) cb
      (Env.cons (show Wert D (.index count) from predecessor) ρ) W reserved →
      Ok m pc fp K (frei Γ reserved + 4) cb P) :
    ∃ m', Star ⟨pc, fp⟩ m
      ⟨pc + BitVec.ofNat 64 (16 * (cb.length + 3)), fp⟩ m' ∧
      Agree fp (frei Γ reserved + 3) K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved))) = some candidate ∧
      ∃ result, m'.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved + 4))) = some result ∧ P result := by
  let s := frei Γ reserved
  have pre : Pre L m pc fp K (s + 3)
      ([ci 2 (s + 3) s 0] ++ ([ci 2 s (s + 1) 0] ++ (cb ++ [ci 2 s (s + 3) 0]))) ρ W reserved :=
    { hp with ctx := by dsimp [s]; omega }
  let m1 := write m (slot fp (BitVec.ofNat 64 (s + 3))) 8 candidate.toNat
  have a1 : Agree fp (s + 3) K m m1 := agree_write hp.frame.room (by omega) (by omega) _
  have backup : m1.rd64 (slot fp (BitVec.ofNat 64 (s + 3))) = some candidate :=
    rd_same hp.frame (by omega) candidate
  have save := quant_mov hp.frame hp.small (by omega) (by omega) pre.left.code candidateRead
  have h1 := pre.next a1 (Nat.le_refl _) (by omega)
  have predecessorRead1 : m1.rd64 (slot fp (BitVec.ofNat 64 (s + 1))) =
      some (BitVec.ofInt 64 predecessor.n) := by
    rw [agree_rd_low a1 hp.frame.room (by omega) (by omega)]
    exact predecessorRead
  let m2 := write m1 (slot fp (BitVec.ofNat 64 s)) 8 (BitVec.ofInt 64 predecessor.n).toNat
  have a2 : Agree fp s K m1 m2 := agree_write h1.frame.room (by omega) (by omega) _
  have install := quant_mov h1.frame hp.small (by omega) (by omega) h1.left.code predecessorRead1
  have h1s : Pre L m1 _ fp K s
      ([ci 2 s (s + 1) 0] ++ (cb ++ [ci 2 s (s + 3) 0])) ρ W reserved :=
    { h1 with ctx := Nat.le_refl _ }
  have h2 := h1s.next a2 (show s ≤ s + 4 by omega) (by omega)
  have newBinder : m2.rd64 (slot fp (BitVec.ofNat 64 s)) = some (BitVec.ofInt 64 predecessor.n) :=
    rd_same h1.frame (by omega) _
  have memberPre : Pre L m2 _ fp K (s + 4) cb
      (Env.cons (show Wert D (.index count) from predecessor) ρ) W reserved :=
    { h2.left with
      ctx := by simp only [frei, contextWords_cons, widthOne]; dsimp [s]; omega
      env := envAt_cons h2.env (ValueAt.of_enc widthOne newBinder rfl) }
  obtain ⟨m3, memberRun, a3, result, resultRead, resultProperty⟩ := operand m2 _ memberPre
  have h3 := h2.next a3 (Nat.le_refl _) (by omega)
  have backup3 : m3.rd64 (slot fp (BitVec.ofNat 64 (s + 3))) = some candidate := by
    rw [agree_rd_low a3 h2.frame.room (by omega) (by omega)]
    rw [rd_other h1.frame.room (by omega) (by omega) (by omega)]
    exact backup
  let m4 := write m3 (slot fp (BitVec.ofNat 64 s)) 8 candidate.toNat
  have restore := quant_mov h3.frame hp.small (by omega) (by omega) h3.code backup3
  have restored : Agree fp (s + 3) K m m4 := quant_restore hp.frame
    (by omega) (by omega) candidateRead (by
      intro x outsideScratch outsideBinder
      rw [a3.b x (by unfold inSlots at *; omega)]
      have localRoom : fp.toNat + 8 * (s + 1) ≤ 2 ^ 64 := by have := hp.frame.room; omega
      rw [(agree_write (K := s + 1) localRoom (lo := s) (by omega) (by omega)
        (BitVec.ofInt 64 predecessor.n).toNat).b x outsideBinder]
      exact a1.b x outsideScratch)
    (a3.rd.trans (a2.rd.trans a1.rd)) (a3.wr.trans (a2.wr.trans a1.wr))
  refine ⟨m4, ?_, restored, rd_same h3.frame (by omega) candidate,
    result, ?_, resultProperty⟩
  · have run := save.trans (install.trans (memberRun.trans restore))
    simpa only [List.length_singleton, pc_add, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using run
  · rw [rd_other h3.frame.room (by omega) (by omega) (by omega)]
    exact resultRead

end Gabbro.Stage0.Senke.Consuming
