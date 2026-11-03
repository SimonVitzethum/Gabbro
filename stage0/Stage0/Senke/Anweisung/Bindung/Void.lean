/- The VOID gate decoder and its execution correspondence. -/
module
public import Stage0.Senke.Anweisung.FehlerLauf
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration}

/-- **G's decoding of a fallible VOID answer**: a listed errno is its reason; anything
    else runs on, since every raw word is the void value (`einpassenErg` on `none`). -/
theorem sonst_none_hit {z : Int → Option D.Fn} {e : Option Ty} {n : Nat} {b : TorB}
    (he : e = none) (hf : fehlGut n b.fehler = true) (w : Runner.W)
    {x : Int × Nat} (hfind : b.fehler.find? (fun x => x.1 == w.toInt) = some x) :
    ∃ hx : x.2 < n, sonstPasst z e n (rohW b n w) = some (.inr ⟨x.2, hx⟩) := by
  subst he
  have hmem := List.mem_of_find?_eq_some hfind
  have hx := List.find?_some hfind
  simp only [fehlGut, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hf
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, _⟩ := hf x hmem
  simp only [beq_iff_eq] at hx
  have hn0 : n ≠ 0 := by omega
  have hr : rohW b n w = (x.2 : Int) + 1 := by
    simp only [rohW, hn0, ↓reduceIte]
    rw [if_pos ⟨by omega, by omega⟩, hfind]
  have ht : ((x.2 : Int) + 1) % ((n : Int) + 1) = (x.2 : Int) + 1 := Int.emod_eq_of_lt (by omega) (by omega)
  refine ⟨h3, ?_⟩
  simp only [sonstPasst, hr, ht]
  rw [if_neg (by omega), dif_pos ⟨by omega, by omega⟩]
  simp

/-- **G's decoding of an unlisted answer to a fallible VOID gate**: the raw word is
    always the void value, so the machine runs on. -/
theorem sonst_none_miss {z : Int → Option D.Fn} {e : Option Ty} {n : Nat} (he : e = none) (hn : 0 < n) {b : TorB}
    (w : Runner.W)
    (hfind : b.fehler.find? (fun x => x.1 == w.toInt) = none) :
    sonstPasst z e n (rohW b n w) = some (.inl (he.symm ▸ ())) := by
  subst he
  have hn0 : n ≠ 0 := by omega
  have hk : ((n : Int) + 1) ≠ 0 := by omega
  by_cases hneg : -4095 ≤ w.toInt ∧ w.toInt ≤ -1
  · have hr : rohW b n w = -((n : Int) + 1) := by
      simp only [rohW, hn0, ↓reduceIte]
      rw [if_pos hneg, hfind]
    have htag : rohW b n w % ((n : Int) + 1) = 0 := by
      rw [hr]
      have h1 : (-((n : Int) + 1)) = (-1) * ((n : Int) + 1) := by omega
      rw [h1]; exact Int.mul_emod_left _ _
    have hdiv : rohW b n w / ((n : Int) + 1) = -1 := by
      rw [hr]
      have h1 : (-((n : Int) + 1)) = (-1) * ((n : Int) + 1) := by omega
      rw [h1]; exact Int.mul_ediv_cancel _ hk
    simp only [sonstPasst, htag, ↓reduceIte, hdiv, einpassenErg]
  · have hr : rohW b n w = w.toInt * ((n : Int) + 1) := by
      simp only [rohW, hn0, ↓reduceIte]
      rw [if_neg hneg]
    have htag : rohW b n w % ((n : Int) + 1) = 0 := by
      rw [hr]; exact Int.mul_emod_left _ _
    have hdiv : rohW b n w / ((n : Int) + 1) = w.toInt := by
      rw [hr]; exact Int.mul_ediv_cancel _ hk
    simp only [sonstPasst, htag, ↓reduceIte, hdiv, einpassenErg]

/-- **G's decoding of a fallible VOID answer**, both cases together. -/
theorem sonst_none_dec {z : Int → Option D.Fn} {e : Option Ty} {n : Nat} (he : e = none) (hn : 0 < n) {b : TorB}
    (hf : fehlGut n b.fehler = true) (w : Runner.W) :
    match b.fehler.find? (fun x => x.1 == w.toInt) with
    | some x => ∃ hx : x.2 < n, sonstPasst z e n (rohW b n w) = some (.inr ⟨x.2, hx⟩)
    | none => sonstPasst z e n (rohW b n w) = some (.inl (he.symm ▸ ())) := by
  cases hfind : b.fehler.find? (fun x => x.1 == w.toInt) with
  | some x => exact sonst_none_hit he hf w hfind
  | none => exact sonst_none_miss he hn w hfind

/-- **A fallible VOID gate** (`bindAxiomOptElse` with `e := none`): the call, the errno
    tests, and G's two answers -- a value runs on to the rest in the same context, a reason
    jumps to the `else` block. No range test: every raw word is the void value, so there is
    no hardware stop. -/
theorem torElseNone_ok {L : Lay D} {O : Orakel D} [TorOK L O] {Λ : List (Res D)} {Γ : Ctx} {a : D.Ax}
    {args : Args D Γ Λ (D.aparams a)}
    (he : D.aerg a = none) {b : TorB} (hb : L.tor a = some b)
    (hf : fehlGut (D.agruende a) b.fehler = true) (hn : 0 < D.agruende a)
    {reserved : Nat} {ct cr ce : List II} {tt : Nat} (ht : torC L a args (frei Γ reserved) reserved = some (ct, tt))
    (hJ : 16 + 16 * (6 * b.fehler.length) + 16 * (cr.length) < 2 ^ 31)
    {fp pc : Runner.W} {K Ks : Nat} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (htt : tt ≤ Ks) (htk : frei Γ reserved + 10 ≤ Ks) (hW : WIn L fp Ks K)
    (hp : PreS L m pc fp K (frei Γ reserved)
      (ct ++ fehlC (frei Γ reserved) b.fehler ((16 * (cr.length) : Nat) : Int) ++ cr ++ ce) ρ reserved)
    (hWa : WeltAt m L σ) :
    (∃ v m2, axiomAntwortSonst O a σ (evalArgs σ args σ ρ) =
        ((O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1, some (.inl v)) ∧
      Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (ct.length + 6 * b.fehler.length)), fp⟩ m2 ∧
      AgreeW L fp (frei Γ reserved) K m m2 ∧
      WeltAt m2 L (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1) ∨
    (∃ r m2, axiomAntwortSonst O a σ (evalArgs σ args σ ρ) =
        ((O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1, some (.inr r)) ∧
      Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (ct.length + 6 * b.fehler.length + cr.length)), fp⟩
        m2 ∧
      AgreeW L fp (frei Γ reserved) K m m2 ∧ m2.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved))) = some (BitVec.ofNat 64 r.val) ∧
      WeltAt m2 L (O.wirkt a (σ.fragt (.inl a)) (evalArgs σ args σ ρ)).1) := by
  have hks := hW.ks
  have hlo2 := hW.lo
  have hn0 : D.agruende a ≠ 0 := by omega
  have e : ct ++ fehlC (frei Γ reserved) b.fehler ((16 * (cr.length) : Nat) : Int) ++ cr ++ ce =
      ct ++ (fehlC (frei Γ reserved) b.fehler ((16 * (cr.length) : Nat) : Int) ++ (cr ++ ce)) := by
    simp only [List.append_assoc]
  have hp' := e ▸ hp
  obtain ⟨b', hb', m1, w, s1, a1, hw1, hW1, hroh⟩ := torC_ok (O := O) ht htt hW hp'.left hWa
  rw [hb] at hb'
  cases hb'
  have hsmall := hp.small
  have hFs := frameOK_sub hp.frame hks
  have hroom := hFs.room
  have hn1 := hp'.nextW hW a1 (by have := hp.ctx; omega) (Nat.le_refl _) (by omega)
  have hpF : PreS L m1 (pc + BitVec.ofNat 64 (16 * ct.length)) fp Ks (frei Γ reserved + 1)
      (fehlC (frei Γ reserved) b.fehler ((16 * (cr.length) : Nat) : Int)) ρ reserved :=
    mkPreS (by omega) (by omega) (frameOK_sub hn1.frame hks) hn1.left.code
      (codeFar_sub2 hn1.left.far hks) hn1.env
  have hfc := fehlC_ok b.fehler ((16 * (cr.length) : Nat) : Int) m1 _ hpF hf (by omega) (by simp only [Int.natCast_add, Int.natCast_mul]; omega)
    (by omega) hw1
  have hdec := sonst_none_dec (z := O.zeiger) he hn hf w
  rw [axiomAntwortSonst_eq, hroh]
  revert hfc hdec
  cases b.fehler.find? (fun x => x.1 == w.toInt) with
  | some x =>
    intro ⟨m2, s2, a2, hw2⟩ ⟨hx, hs⟩
    refine .inr ⟨⟨x.2, hx⟩, m2, by rw [hs], s1.trans (star_cast s2 rfl ?_),
      a1.trans (agreeW_of (Agree.widen a2 hks)), hw2, weltAt_stab hW.lay hlo2 m1 m2 hW1 (a2.mono (Nat.zero_le _))⟩
    rw [adr_int, show ((16 * ct.length : Nat) : Int) + (16 * (6 * (b.fehler.length : Int)) +
      ((16 * cr.length : Nat) : Int)) =
      ((16 * (ct.length + 6 * b.fehler.length + cr.length) : Nat) : Int) by simp only [Int.natCast_add, Int.natCast_mul]; omega,
      BitVec.ofInt_natCast]
  | none =>
    intro ⟨m2, s2, a2⟩ hs
    exact .inl ⟨_, m2, by rw [hs], s1.trans (by rw [pc_add] at s2; exact s2),
      a1.trans (agreeW_of ((Agree.widen a2 hks).mono (Nat.le_succ _))),
      weltAt_stab hW.lay hlo2 m1 m2 hW1 (a2.mono (Nat.zero_le _))⟩

end Gabbro.Stage0.Senke
