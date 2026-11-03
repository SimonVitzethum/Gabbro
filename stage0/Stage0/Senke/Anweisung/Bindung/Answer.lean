/- A common checked scalar answer contract for foreign bindings. -/
module
public import Stage0.Senke.Anweisung.Bindung.TorLauf
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- The result check implements canonical decoding, including Boolean
    normalization. Its output may differ from the raw answer word. -/
theorem chkAnswer_ok {e : Option Ty} {τ : Ty} (he : e = some τ) {s reserved : Nat} {c : List II}
    {z : Int → Option D.Fn} (h : chkC (some τ) s = some c)
    {m : Runner.Mem} {pc fp : Runner.W} {K : Nat} {Γ : Ctx}
    {ρ : Env D Γ} {w : Runner.W}
    (hp : PreS L m pc fp K s c ρ reserved) (room : s + 10 ≤ K)
    (input : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some w)
    (valid : ∀ n, τ = .ref n → 0 ≤ w.toInt →
      ValueValid L (.ref n) (Val.vonZelle w.toInt.toNat)) :
    match einpassenErg z e w.toInt with
    | some v => ∃ m' w',
        Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * c.length), fp⟩ m' ∧
        Agree fp s K m m' ∧
        m'.rd64 (slot fp (BitVec.ofNat 64 s)) = some w' ∧ Enc L τ (ergWert he v) w'
    | none => Stops ⟨pc, fp⟩ m 110 := by
  subst e
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
    obtain ⟨m', run, changed, w', output, encoded⟩ := boolC_ok hp (by omega) input
    exact ⟨m', w', run, changed, output, encoded⟩
  | ref n =>
    simp only [chkC, Option.some.injEq] at h
    subst c
    have test := loC_ok (hp.up (by omega)) (by decide) room input
    by_cases nonnegative : 0 ≤ w.toInt
    · simp only [einpassenErg, einpassen, if_pos nonnegative]
      obtain ⟨m', run, changed⟩ := test.1 nonnegative
      refine ⟨m', w, run, changed.mono (Nat.le_succ _), ?_, ?_⟩
      · rw [agree_rd_low changed hp.frame.room (by omega) (by omega)]
        exact input
      · refine ⟨?_, valid n rfl nonnegative⟩
        rw [← BitVec.ofInt_natCast, Int.toNat_of_nonneg nonnegative]
        exact BitVec.ofInt_toInt.symm
    · simp only [einpassenErg, einpassen, if_neg nonnegative]
      exact test.2 nonnegative
  | ptr cap =>
    simp only [chkC, Option.some.injEq] at h
    subst c
    obtain ⟨m', run, changed, w', output, encoded⟩ := const_ok hp (by decide) (by omega)
    exact ⟨m', w', run, changed, output, encoded⟩
  | never =>
    simp only [chkC, Option.some.injEq] at h
    subst c
    exact stop_ok hp.code hp.far hp.frame (by omega) hp.small (by decide)
  | _ => simp [chkC] at h

/-- Listed errnos select the same nominal reason for every answer type. -/
theorem fallible_hit {z : Int → Option D.Fn} {e : Option Ty} {n : Nat}
    {b : TorB} (valid : fehlGut n b.fehler = true) (w : Runner.W)
    {x : Int × Nat} (hit : b.fehler.find? (fun x => x.1 == w.toInt) = some x) :
    ∃ hx : x.2 < n, sonstPasst z e n (rohW b n w) = some (.inr ⟨x.2, hx⟩) := by
  have member := List.mem_of_find?_eq_some hit
  have equal := List.find?_some hit
  simp only [fehlGut, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at valid
  obtain ⟨⟨⟨lower, upper⟩, bound⟩, _⟩ := valid x member
  simp only [beq_iff_eq] at equal
  have nz : n ≠ 0 := by omega
  have raw : rohW b n w = (x.2 : Int) + 1 := by
    simp only [rohW, nz, ↓reduceIte]
    rw [if_pos ⟨by omega, by omega⟩, hit]
  have tag : ((x.2 : Int) + 1) % ((n : Int) + 1) = (x.2 : Int) + 1 :=
    Int.emod_eq_of_lt (by omega) (by omega)
  refine ⟨bound, ?_⟩
  simp only [sonstPasst, raw, tag]
  rw [if_neg (by omega), dif_pos ⟨by omega, by omega⟩]
  simp

/-- All admitted scalar success types share the same canonical decoder after
    an errno miss. The integer rule retains its nonnegative lower bound. -/
theorem fallible_decode {z : Int → Option D.Fn} {e : Option Ty} {τ : Ty} {n : Nat}
    (he : e = some τ)
    (accepted : fallibleTy τ = true) (positive : 0 < n)
    {b : TorB} (valid : fehlGut n b.fehler = true) (w : Runner.W)
    (miss : b.fehler.find? (fun x => x.1 == w.toInt) = none) :
    sonstPasst z e n (rohW b n w) =
      (einpassenErg z e w.toInt).map Sum.inl := by
  subst e
  have nz : n ≠ 0 := by omega
  have divisor : ((n : Int) + 1) ≠ 0 := by omega
  let negative := -4095 ≤ w.toInt ∧ w.toInt ≤ -1
  have raw : rohW b n w = (if negative then -1 else w.toInt) * ((n : Int) + 1) := by
    simp only [rohW, nz, ↓reduceIte]
    by_cases error : negative
    · rw [if_pos error, miss, if_pos error]
      simp only
      omega
    · rw [if_neg error, if_neg error]
  rw [raw]
  simp only [sonstPasst, Int.mul_emod_left, ↓reduceIte, Int.mul_ediv_cancel _ divisor]
  by_cases error : negative
  · rw [if_pos error]
    cases τ with
    | int lo hi =>
      have lower : 0 ≤ lo := of_decide_eq_true accepted
      simp only [einpassenErg, einpassen]
      rw [dif_neg (by omega), dif_neg (by dsimp only [negative] at error; omega)]
      rfl
    | ref n =>
      simp only [einpassenErg, einpassen]
      rw [if_neg (by omega), if_neg (by dsimp only [negative] at error; omega)]
      rfl
    | ptr cap => rfl
    | bool =>
      have nonzero : w.toInt ≠ 0 := by dsimp only [negative] at error; omega
      simp [einpassenErg, einpassen, nonzero]
    | _ => simp [fallibleTy] at accepted
  · rw [if_neg error]

end Gabbro.Stage0.Senke
