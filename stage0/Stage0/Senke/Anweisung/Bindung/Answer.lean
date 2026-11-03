/- A common checked scalar answer contract for foreign bindings. -/
module
public import Stage0.Senke.Anweisung.Bindung.TorLauf
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- The result check implements canonical decoding, including Boolean
    normalization. Its output may differ from the raw answer word. -/
theorem chkAnswer_ok {τ : Ty} {s reserved : Nat} {c : List II}
    {z : Int → Option D.Fn} (h : chkC (some τ) s = some c)
    {m : Runner.Mem} {pc fp : Runner.W} {K : Nat} {Γ : Ctx}
    {ρ : Env D Γ} {w : Runner.W}
    (hp : PreS L m pc fp K s c ρ reserved) (room : s + 10 ≤ K)
    (input : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some w) :
    match einpassenErg z (some τ) w.toInt with
    | some v => ∃ m' w',
        Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * c.length), fp⟩ m' ∧
        Agree fp s K m m' ∧
        m'.rd64 (slot fp (BitVec.ofNat 64 s)) = some w' ∧ Enc L τ v w'
    | none => Stops ⟨pc, fp⟩ m 110 := by
  cases τ with
  | int lo hi =>
    have test := chkC_ok h (hp.up (by omega)) room input
    have decode := einpassen_int (L := L) (z := z) (e := some (.int lo hi)) rfl rfl w
    by_cases inside : lo ≤ w.toInt ∧ w.toInt ≤ hi
    · obtain ⟨v, decoded, encoded⟩ := decode.1 inside
      rw [decoded]
      obtain ⟨m', run, changed⟩ := test.1 inside
      exact ⟨m', w, run, changed.mono (Nat.le_succ _),
        by rw [agree_rd_low changed hp.frame.room (by omega) (by omega)]; exact input,
        encoded⟩
    · rw [decode.2 inside]
      exact test.2 inside
  | bool =>
    simp only [chkC, Option.some.injEq] at h
    subst c
    exact boolC_ok hp (by omega) input
  | never =>
    simp only [chkC, Option.some.injEq] at h
    subst c
    exact stop_ok hp.code hp.far hp.frame (by omega) hp.small (by decide)
  | _ => simp [chkC] at h

/-- Under an errno profile, an unlisted error word and its canonical sentinel
    have the same Boolean payload. This does not turn a listed error into a value. -/
theorem bool_errno_decode {z : Int → Option D.Fn} {n : Nat} (positive : 0 < n)
    {b : TorB} (w : Runner.W)
    (miss : b.fehler.find? (fun x => x.1 == w.toInt) = none) :
    sonstPasst z (some .bool) n (rohW b n w) =
      (einpassenErg z (some .bool) w.toInt).map Sum.inl := by
  have nz : n ≠ 0 := by omega
  have divisor : ((n : Int) + 1) ≠ 0 := by omega
  by_cases negative : -4095 ≤ w.toInt ∧ w.toInt ≤ -1
  · have raw : rohW b n w = (-1) * ((n : Int) + 1) := by
      simp only [rohW, nz, ↓reduceIte]
      rw [if_pos negative, miss]
      simp only
      omega
    rw [raw]
    simp only [sonstPasst, Int.mul_emod_left, ↓reduceIte,
      Int.mul_ediv_cancel _ divisor, einpassenErg, einpassen, Option.map_some]
    have nonzero : w.toInt ≠ 0 := by omega
    simp [nonzero]
  · have raw : rohW b n w = w.toInt * ((n : Int) + 1) := by
      simp only [rohW, nz, ↓reduceIte]
      rw [if_neg negative]
    rw [raw]
    simp only [sonstPasst, Int.mul_emod_left, ↓reduceIte,
      Int.mul_ediv_cancel _ divisor]

/-- All admitted scalar success types share the same canonical decoder after
    an errno miss. The integer rule retains its nonnegative lower bound. -/
theorem fallible_decode {z : Int → Option D.Fn} {τ : Ty} {n : Nat}
    (accepted : fallibleTy τ = true) (positive : 0 < n)
    {b : TorB} (valid : fehlGut n b.fehler = true) (w : Runner.W)
    (miss : b.fehler.find? (fun x => x.1 == w.toInt) = none) :
    sonstPasst z (some τ) n (rohW b n w) =
      (einpassenErg z (some τ) w.toInt).map Sum.inl := by
  cases τ with
  | int lo hi =>
    have lower : 0 ≤ lo := of_decide_eq_true accepted
    have nz : n ≠ 0 := by omega
    have divisor : ((n : Int) + 1) ≠ 0 := by omega
    by_cases negative : -4095 ≤ w.toInt ∧ w.toInt ≤ -1
    · have raw : rohW b n w = (-1) * ((n : Int) + 1) := by
        simp only [rohW, nz, ↓reduceIte]
        rw [if_pos negative, miss]
        simp only
        omega
      rw [raw]
      simp only [sonstPasst, Int.mul_emod_left, ↓reduceIte,
        Int.mul_ediv_cancel _ divisor, einpassenErg, einpassen]
      rw [dif_neg (by omega), dif_neg (by omega)]
      rfl
    · have raw : rohW b n w = w.toInt * ((n : Int) + 1) := by
        simp only [rohW, nz, ↓reduceIte]
        rw [if_neg negative]
      rw [raw]
      simp only [sonstPasst, Int.mul_emod_left, ↓reduceIte,
        Int.mul_ediv_cancel _ divisor]
  | bool => exact bool_errno_decode positive w miss
  | _ => simp [fallibleTy] at accepted

end Gabbro.Stage0.Senke
