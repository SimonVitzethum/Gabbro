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
    · simp only [if_pos error, miss]
      omega
    · simp only [if_neg error]
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

/-- **A gate bound in a block** (`bindAxiom`): the call, then the test of its answer. Inside the range the value is in
    slot `frei Γ` and the oracle's world in memory; outside it, G has no answer and the code stops with 110. -/
theorem torBind_ok {reserved : Nat} {L : Lay D} {O : Orakel D} [TorOK L O] {Λ : List (Res D)} {Γ : Ctx} {a : D.Ax}
    {args : Args D Γ Λ (D.aparams a)} {τ : Ty} (he : D.aerg a = some τ) {ct ck cr : List II} {tt : Nat}
    {fp pc : Runner.W} {K Ks : Nat} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (ht : torC0 L a args (frei Γ reserved) reserved = some (ct, tt)) (hck : chkC (D.aerg a) (frei Γ reserved) = some ck)
    (htt : tt ≤ Ks) (htk : frei Γ reserved + 10 ≤ Ks) (hW : WIn L fp Ks K) (hp : PreS L m pc fp K (frei Γ reserved) (ct ++ ck ++ cr) ρ reserved)
    (hWa : WeltAt m L σ) :
    (∃ v m2, axiomAntwort O a σ (evalArgs σ args σ ρ) =
        ((O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1, some v) ∧
      Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (ct ++ ck).length), fp⟩ m2 ∧ AgreeW L fp (frei Γ reserved) K m m2 ∧
      ValueAt L m2 fp (frei Γ reserved) τ (ergWert he v) ∧
      WeltAt m2 L (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1) ∨
    (axiomAntwort O a σ (evalArgs σ args σ ρ) = ((O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1, none) ∧
      Stops ⟨pc, fp⟩ m 110) := by
  have hks := hW.ks
  have hck' : chkC (some τ) (frei Γ reserved) = some ck := by simpa only [he] using hck
  have width := chkC_width hck'
  have hp' : PreS L m pc fp K (frei Γ reserved) (ct ++ (ck ++ cr)) ρ reserved :=
    (List.append_assoc ct ck cr) ▸ hp
  obtain ⟨m1, w, run, changed, input, world, raw⟩ := torC0_ok (O := O) ht htt hW hp'.left hWa
  have next := hp'.nextW hW changed (by have := hp.ctx; omega) (Nat.le_refl _) (by omega)
  have pre : PreS L m1 _ fp Ks (frei Γ reserved) ck ρ reserved :=
    ⟨hp.ctx, by have := hp.small; omega, frameOK_sub next.frame hks, next.left.code,
      codeFar_sub2 next.left.far hks, next.env, trivial, wstab_true _ _⟩
  have bound : L.tor a ≠ none := by
    simp only [torC0] at ht
    split at ht
    · exact torC_bound ht
    · cases ht
  have noReasons : D.agruende a = 0 := by
    simp only [torC0] at ht
    split at ht
    · assumption
    · cases ht
  have valid : ∀ n, τ = .ref n → 0 ≤ w.toInt →
      ValueValid L (.ref n) (Val.vonZelle w.toInt.toNat) := by
    intro n type nonnegative
    exact TorOK.ref_answer a n (he.trans (congrArg some type)) bound
      (σ.fragt (.inl a)) (evalArgs σ args σ ρ) w.toInt (.inl ⟨noReasons, raw.symm⟩) nonnegative
  have checked := chkAnswer_ok (z := O.zeiger) he hck' pre htk input valid
  rw [axiomAntwort_eq, raw]
  cases result : einpassenErg O.zeiger (D.aerg a) w.toInt with
  | some v =>
    rw [result] at checked
    obtain ⟨m2, w2, run2, changed2, output, encoded⟩ := checked
    refine .inl ⟨v, m2, rfl, ?_, changed.trans (agreeW_of (Agree.widen changed2 hks)),
      ValueAt.of_enc width output encoded, ?_⟩
    · exact run.trans (by rw [List.length_append, ← pc_add]; exact run2)
    · exact weltAt_stab hW.lay (by have := hW.lo; omega) m1 m2 world
        (changed2.mono (Nat.zero_le _))
  | none =>
    rw [result] at checked
    exact .inr ⟨rfl, Stops.prefix run checked⟩

end Gabbro.Stage0.Senke
