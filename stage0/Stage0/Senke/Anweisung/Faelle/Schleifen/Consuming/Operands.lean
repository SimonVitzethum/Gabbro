/- Selector initializers and reuse of the canonical membership binder. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Edges
@[expose] public section

namespace Gabbro.Stage0.Senke.Consuming
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {P : Programm D} {f : D.Fn}

/-- Concatenate adjacent instruction slices; addresses remain byte addresses. -/
theorem codeAt_join {m : Mem} {pc : W} {a b : List II}
    (left : CodeAt m pc a)
    (right : CodeAt m (pc + BitVec.ofNat 64 (16 * a.length)) b) : CodeAt m pc (a ++ b) := by
  intro k hk
  by_cases before : k < a.length
  · simpa only [List.getElem_append_left before] using left k before
  · have inside : k - a.length < b.length := by simp only [List.length_append] at hk; omega
    have h := right (k - a.length) inside
    have index : a.length + (k - a.length) = k := by omega
    simpa only [List.getElem_append_right (by omega), addr_norm, ← Nat.mul_add, index] using h

namespace Image
variable {reserved : Nat} {x : Image L P f reserved}
variable {Γ : Ctx} {m : Mem} {σ : World D} {ρ : Env D Γ}

/-- The two literal writes that initialize a scan use disjoint words. -/
theorem Ready.literals (h : x.Ready m σ ρ) {i a b : Nat} {va vb : Int}
    (found : x.fragment[i]? = some (.code [ci 1 a va 0, ci 1 b vb 0]))
    (ctx : frei Γ reserved ≤ min a b) (low : x.s ≤ min a b)
    (insideA : a < x.K) (insideB : b < x.K) (distinct : a ≠ b)
    (literalA : lit32 va = true) (literalB : lit32 vb = true)
    (endAt : x.at i + 32 = x.at (i + 1)) :
    ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.at i) (x.at (i + 1)) m
      (fun m' => x.Ready m' σ ρ ∧ Agree x.fp (min a b) x.K m m' ∧
        x.read m' a (BitVec.ofInt 64 va) ∧ x.read m' b (BitVec.ofInt 64 vb)) := by
  have slice := (h.slice i (.code [ci 1 a va 0, ci 1 b vb 0]) _ found rfl).1
  obtain ⟨run1, a1, ready1, ra⟩ := h.literal (codeAt_left (a := [ci 1 a va 0]) slice)
    (by omega) (by omega) insideA literalA
  have tail := (codeAt_right (a := [ci 1 a va 0]) slice).agree a1
    (codeFar_at x.far (by
      have len := assemble_length x.assembled
      simp only [fragment, pieces, width, Piece.width] at len
      omega))
  obtain ⟨run2, a2, ready2, rb⟩ := ready1.literal tail
    (by omega) (by omega) insideB literalB
  have aa := (a1.mono (Nat.min_le_left a b)).trans (a2.mono (Nat.min_le_right a b))
  have result : Ok m (x.at i) x.fp x.K (min a b) [ci 1 a va 0, ci 1 b vb 0]
      (fun _ => True) := by
    refine ⟨_, ?_, aa, ?_, ?_, trivial⟩
    · simpa only [List.length_cons, List.length_nil, addr_norm, endAt] using run1.trans run2
    · exact BitVec.ofNat 64 ((write (write m (slot x.fp (BitVec.ofNat 64 a)) 8
        (BitVec.ofInt 64 va).toNat) (slot x.fp (BitVec.ofNat 64 b)) 8
        (BitVec.ofInt 64 vb).toNat).le (slot x.fp (BitVec.ofNat 64 (min a b))) 8)
    · simp only [Runner.Mem.rd64, ready2.frame.rd (min a b) (by omega), ↓reduceIte]
  obtain ⟨m', path, frame, kept, ready, localFrame, value, read, trivial⟩ := h.ok result
    (by simpa using endAt) ctx low (by omega)
  refine ⟨m', path, frame, kept, ready, localFrame, ?_, ?_⟩
  · rw [Image.read, rd_other ready1.frame.room insideB insideA (Ne.symm distinct)]
    exact ra
  · exact rb

/-- Run the existing membership borrowing proof on slices 20,21,22. -/
theorem Ready.borrow (h : x.Ready m σ ρ) {Λ : List (Res D)}
    {member : Expr D (.index (D.count x.table) :: Γ) Λ .bool} {top : Nat}
    {candidate predecessor : Wert D (.index (D.count x.table))}
    (origin : x.s = frei Γ reserved)
    (indexWidth : valueWords (.index (D.count x.table)) = 1)
    (lowered : lowE (reserved := reserved) L member (x.s + 4) = some (x.member, top))
    (topBound : top ≤ x.Ks)
    (rc : x.read m x.s (BitVec.ofInt 64 candidate.n))
    (rp : x.read m (x.s + 1) (BitVec.ofInt 64 predecessor.n)) :
    ScanRun L x.fp x.lo x.K (x.counter :: x.saved :: x.pr) (x.at 20) (x.at 23) m
      (fun m' => x.Ready m' σ ρ ∧ Agree x.fp (x.s + 3) x.K m m' ∧
        x.read m' (x.s + 4)
          (Runner.IR.bool (wahr? (eval σ member σ (.cons predecessor ρ))))) := by
  have save := (h.slice 20 (.code [ci 2 (x.s + 3) x.s 0, ci 2 x.s (x.s + 1) 0]) _ rfl rfl).1
  have memberCode := (h.slice 21 (.code x.member) _ rfl rfl).1
  have restore := (h.slice 22 (.code [ci 2 x.s (x.s + 3) 0]) _ rfl rfl).1
  have code : CodeAt m (x.at 20)
      ([ci 2 (x.s + 3) x.s 0, ci 2 x.s (x.s + 1) 0] ++ x.member ++
        [ci 2 x.s (x.s + 3) 0]) := by
    apply codeAt_join
    · apply codeAt_join save
      simpa only [show x.at 20 + BitVec.ofNat 64 (16 *
        [ci 2 (x.s + 3) x.s 0, ci 2 x.s (x.s + 1) 0].length) = x.at 21 by consume_arith x]
        using memberCode
    · simpa only [show x.at 20 + BitVec.ofNat 64 (16 *
        ([ci 2 (x.s + 3) x.s 0, ci 2 x.s (x.s + 1) 0] ++ x.member).length) =
          x.at 22 by consume_arith x] using restore
  have far : CodeFar (x.at 20) (x.member.length + 3) x.fp x.K := by
    have := codeFar_at (i := x.offset 20) (k := x.member.length + 3) x.far (by consume_arith x)
    exact this
  have pre := mkPreS (L := L) (ρ := ρ) (d := x.s + 4) (by omega)
    x.small h.frame code (by simpa using far) h.env
  obtain ⟨m', path, frame, candidateRead, value, read, encoding⟩ := member_borrow_ok
    indexWidth (by have := x.scratch; have := x.layout.ks; omega)
    (by simpa only [← origin] using pre) rc rp (by
      intro mem pc hp
      have pw := PreS.welt hp x.layout.ks h.world x.layout.lay x.layout.top
      exact lowE_ok (same := by intro _; rfl) σ σ (fun _ h => h) x.layout.lay
        member (x.s + 4) x.member top lowered topBound mem pc (.cons predecessor ρ) pw |>.word trivial)
  have scratchRoom : x.s + 3 ≤ x.K := by have := x.scratch; have := x.layout.ks; omega
  refine ⟨m', ?_, agreeW_of (frame.mono (by have := x.controls; have := x.scratch; omega)),
    keeps_of_agree frame h.frame.room (by
      intro j hj
      have := x.controls; have := x.scratch
      simp only [List.mem_cons] at hj
      rcases hj with rfl | rfl | hj <;> try omega
      have := x.protected j hj; omega) scratchRoom,
    h.agree frame (by omega) (by rw [← x.abi]; have := x.controls; have := x.scratch; omega)
      scratchRoom, frame, ?_⟩
  · simpa only [← origin, show x.at 20 + BitVec.ofNat 64 (16 * (x.member.length + 3)) =
      x.at 23 by consume_arith x] using path
  · simpa only [Enc, bool_word] using encoding ▸ read

end Image
end Gabbro.Stage0.Senke.Consuming
