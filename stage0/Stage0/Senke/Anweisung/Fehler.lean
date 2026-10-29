/-
  File:      stage0/Stage0/Senke/Anweisung/Fehler.lean
  Subject:   A fallible gate's answer (`bindAxiomElse`): the kernel's word against the binding's listed errnos
             (`fehlC_ok`: a hit puts its reason case into slot `s` and jumps to the `else` block), and G's decoding of
             the raw answer (`sonst_dec`): a listed errno is its reason, a word in the value's range the value, anything
             else no answer.
-/
import Stage0.Senke.Anweisung.TorLauf

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

theorem adr_int (pc : Runner.W) (a : Nat) (b : Int) :
    pc + BitVec.ofNat 64 a + BitVec.ofInt 64 b = pc + BitVec.ofInt 64 ((a : Int) + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofInt_natCast, ← BitVec.ofInt_add]

theorem fehlC_len (s : Nat) : (l : List (Int × Nat)) → (J : Int) → (fehlC s l J).length = 6 * l.length
  | [], _ => rfl
  | (e, i) :: r, J => by
    simp only [fehlC, fehlC1, List.length_append, List.length_cons, List.length_nil, fehlC_len s r J]; omega

theorem eq_lit {w : Runner.W} {e : Int} (he : lit32 e = true) : (w == BitVec.ofInt 64 e) = decide (w.toInt = e) := by
  simp only [lit32, Bool.and_eq_true, decide_eq_true_eq] at he
  by_cases h : w.toInt = e
  · subst h; simp [BitVec.ofInt_toInt]
  · have : w ≠ BitVec.ofInt 64 e := fun hw => h (by rw [hw, toInt_ofInt_in (by omega) (by omega)])
    simp [this, h]

/-- One errno test. -/
theorem fehlC1_ok {m : Runner.Mem} {pc fp : Runner.W} {K s : Nat} {e : Int} {i : Nat} {J : Int} {Γ : Ctx}
    {ρ : Env D Γ} {w : Runner.W} (hp : PreS m pc fp K (s + 1) (fehlC1 s e i J) ρ) (he : lit32 e = true)
    (hi : i < 2 ^ 31) (hJ : lit32 (16 + J) = true) (hs : s + 3 ≤ K)
    (hw : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some w) :
    (w.toInt = e → ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofInt 64 (96 + J), fp⟩ m' ∧ Agree fp s K m m' ∧
        m'.rd64 (slot fp (BitVec.ofNat 64 s)) = some (BitVec.ofNat 64 i)) ∧
    (w.toInt ≠ e → ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 96, fp⟩ m' ∧ Agree fp (s + 1) K m m') := by
  have hsmall := hp.small
  have hp' : PreS m pc fp K (s + 1) (([ci 2 ((s + 1 : Nat) : Int) s 0] ++ [ci 1 (((s + 1 : Nat) : Int) + 1) e 0,
      ci 14 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) (((s + 1 : Nat) : Int) + 1)]) ++
      ([ci 19 ((s + 1 : Nat) : Int) 48 0] ++ ([ci 1 s i 0] ++ [ci 18 (16 + J) 0 0]))) ρ := hp
  obtain ⟨m1, s1, a1, v, hv, rfl⟩ := ok_seq hp'.left (mov_ok hp'.left.left (by omega) (by omega) hw)
    (Pb := (· = Runner.IR.bool (w == BitVec.ofInt 64 e)))
    (fun m' w' hp'' hr he' => (binK_ok (r := Runner.IR.bool (w' == BitVec.ofInt 64 e)) hp'' hr he rfl (by decide)
      rfl (by omega)).mono fun x hx => by rw [hx, he']) (by omega)
  have hn := hp'.next a1 (Nat.le_refl _) (by omega)
  simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil] at s1 hn
  have hroom := hp.frame.room
  rw [eq_lit he] at hv
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [h, decide_true] at hv
    have sb := brz_stay hn.left.code (j := s + 1) (by omega) hsmall hv (by decide)
    have hn2 := hn.next (Agree.refl _ _ _ _) (a := [ci 19 ((s + 1 : Nat) : Int) 48 0]) (Nat.le_refl _) (by omega)
    have sc := const_step (k := (i : Int)) hn2.left.code hn2.frame (by omega) hsmall
      (lit_ok (by omega) (by omega))
    let m2 := write m1 (slot fp (BitVec.ofNat 64 s)) 8 (BitVec.ofInt 64 (i : Int)).toNat
    have a2 : Agree fp s K m1 m2 := agree_write hroom (Nat.le_refl _) (by omega) _
    have hcj : CodeAt m2 (pc + BitVec.ofNat 64 (16 * 3) + BitVec.ofNat 64 (16 * 1) + 16) [ci 18 (16 + J) 0 0] :=
      (codeAt_right hn2.code).agree a2 (by simpa using codeFar_right (n := 1) (k := 1) hn2.far)
    have sj := jmp_go (fp := fp) hcj hJ
    refine ⟨m2, s1.trans (sb.trans (sc.trans (star_cast sj rfl ?_))), (a1.mono (Nat.le_succ s)).trans a2, ?_⟩
    · rw [show (16 : Runner.W) = BitVec.ofNat 64 16 from rfl, addr_norm, addr_norm, adr_int,
        show ((16 * 3 + (16 * 1 + 16) : Nat) : Int) + (16 + J) = 96 + J by omega]
    · rw [← BitVec.ofInt_natCast]; exact rd64_write_same (hn2.frame.rd s (by omega))
  · simp only [h, decide_false] at hv
    have sb := brz_go hn.left.code (j := s + 1) (by omega) hsmall (by decide) hv
    exact ⟨m1, s1.trans (star_cast sb rfl (by rw [adr_int]; rfl)), a1⟩

/-- **The errno tests**: the first listed errno equal to the word puts its case into slot `s` and jumps to `J` bytes
    past the tests; none equal, on after them with slot `s` kept. -/
theorem fehlC_ok {fp : Runner.W} {K s n : Nat} {Γ : Ctx} {ρ : Env D Γ} {w : Runner.W} :
    (l : List (Int × Nat)) → (J : Int) → (m : Runner.Mem) → (pc : Runner.W) →
    PreS m pc fp K (s + 1) (fehlC s l J) ρ → fehlGut n l = true → 0 ≤ J → 16 + 16 * (6 * l.length) + J < 2 ^ 31 →
    s + 3 ≤ K → m.rd64 (slot fp (BitVec.ofNat 64 s)) = some w →
    match l.find? (fun x => x.1 == w.toInt) with
    | some x => ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofInt 64 (16 * (6 * l.length) + J), fp⟩ m' ∧ Agree fp s K m m' ∧
        m'.rd64 (slot fp (BitVec.ofNat 64 s)) = some (BitVec.ofNat 64 x.2)
    | none => ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (6 * l.length)), fp⟩ m' ∧ Agree fp (s + 1) K m m'
  | [], _, m, pc, _, _, _, _, _, _ => ⟨m, by simpa using Star.refl _ m, Agree.refl _ _ _ _⟩
  | (e, i) :: r, J, m, pc, hp, hl, hJ0, hJ, hs, hw => by
    simp only [fehlGut, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
    obtain ⟨⟨⟨⟨he1, he2⟩, _⟩, hi⟩, hr⟩ := hl
    simp only [List.length_cons] at hJ
    have hp' : PreS m pc fp K (s + 1) (fehlC1 s e i (16 * (6 * r.length) + J) ++ fehlC s r J) ρ := hp
    obtain ⟨hhit, hmiss⟩ := fehlC1_ok hp'.left (lit_ok (by omega) (by omega)) hi (lit_ok (by omega) (by omega)) hs hw
    simp only [List.find?_cons]
    by_cases h : w.toInt = e
    · have hb : (e == w.toInt) = true := by simp [h]
      simp only [hb]
      obtain ⟨m', s1, a1, hw'⟩ := hhit h
      refine ⟨m', star_cast s1 rfl ?_, a1, hw'⟩
      have e1 : (96 : Int) + (16 * (6 * (r.length : Int)) + J) = 16 * (6 * ((r.length + 1 : Nat) : Int)) + J := by
        push_cast; omega
      simp only [List.length_cons, e1]
    · have hb : (e == w.toInt) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h' => h h'.symm
      simp only [hb]
      obtain ⟨m1, s1, a1⟩ := hmiss h
      have hn := hp'.next a1 (Nat.le_refl _) (by omega)
      have e96 : (fehlC1 s e i (16 * (6 * r.length) + J)).length = 6 := rfl
      rw [e96] at hn
      have ih := fehlC_ok r J m1 _ hn hr hJ0 (by omega) hs
        (by rw [agree_rd_low a1 hp.frame.room (by omega) (by omega)]; exact hw)
      revert ih
      cases r.find? (fun x => x.1 == w.toInt) with
      | some x =>
        intro ⟨m', s2, a2, hw'⟩
        refine ⟨m', s1.trans (star_cast s2 (by simp) ?_), (a1.mono (Nat.le_succ s)).trans a2, hw'⟩
        have e1 : (((16 * 6 : Nat) : Int) + (16 * (6 * (r.length : Int)) + J)) =
            16 * (6 * ((r.length + 1 : Nat) : Int)) + J := by push_cast; omega
        simp only [List.length_cons]
        rw [show (BitVec.ofNat 64 96 : Runner.W) = BitVec.ofNat 64 (16 * 6) from rfl, adr_int, e1]
      | none =>
        intro ⟨m', s2, a2⟩
        refine ⟨m', s1.trans (star_cast s2 (by simp) ?_), a1.trans a2⟩
        simp only [List.length_cons]
        rw [show (BitVec.ofNat 64 96 : Runner.W) = BitVec.ofNat 64 (16 * 6) from rfl, addr_norm,
          show 16 * 6 + 16 * (6 * r.length) = 16 * (6 * (r.length + 1)) by omega]

/-! ## G's decoding of a fallible answer -/

theorem sonst_val {z : Int → Option D.Fn} {lo hi : Int} {n : Nat} (v : Int) :
    sonstPasst (D := D) z (some (.int lo hi)) n (v * ((n : Int) + 1)) =
      (einpassenErg z (some (.int lo hi)) v).map Sum.inl := by
  have hk : ((n : Int) + 1) ≠ 0 := by omega
  simp only [sonstPasst, Int.mul_emod_left, ↓reduceIte, Int.mul_ediv_cancel _ hk]

/-- **G's decoding**: a listed errno is its reason; else a word in the value's range is the value, and anything else
    no answer (an unlisted errno decodes to `-1`, outside a range from `0`). -/
theorem sonst_dec {z : Int → Option D.Fn} {e : Option Ty} {τ : Ty} (he : e = some τ) {lo hi : Int}
    (hτ : τ = .int lo hi) (hlo : 0 ≤ lo) {n : Nat} (hn : 0 < n) {b : TorB} (hf : fehlGut n b.fehler = true)
    (w : Runner.W) :
    match b.fehler.find? (fun x => x.1 == w.toInt) with
    | some x => ∃ hx : x.2 < n, sonstPasst z e n (rohW b n w) = some (.inr ⟨x.2, hx⟩)
    | none => (lo ≤ w.toInt ∧ w.toInt ≤ hi → ∃ v, sonstPasst z e n (rohW b n w) = some (.inl v) ∧
          Enc τ (ergWert he v) w) ∧ (¬ (lo ≤ w.toInt ∧ w.toInt ≤ hi) → sonstPasst z e n (rohW b n w) = none) := by
  subst he hτ
  have hn0 : n ≠ 0 := by omega
  have hk : ((n : Int) + 1) ≠ 0 := by omega
  cases hfind : b.fehler.find? (fun x => x.1 == w.toInt) with
  | some x =>
    have hmem := List.mem_of_find?_eq_some hfind
    have hx := List.find?_some hfind
    simp only [fehlGut, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hf
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, _⟩ := hf x hmem
    simp only [beq_iff_eq] at hx
    refine ⟨h3, ?_⟩
    have hr : rohW b n w = (x.2 : Int) + 1 := by
      simp only [rohW, hn0, ↓reduceIte]
      rw [if_pos ⟨by omega, by omega⟩, hfind]
    have ht : ((x.2 : Int) + 1) % ((n : Int) + 1) = (x.2 : Int) + 1 := Int.emod_eq_of_lt (by omega) (by omega)
    simp only [sonstPasst, hr, ht]
    rw [if_neg (by omega), dif_pos ⟨by omega, by omega⟩]
    simp
  | none =>
    by_cases hneg : -4095 ≤ w.toInt ∧ w.toInt ≤ -1
    · have hr : rohW b n w = (-1) * ((n : Int) + 1) := by
        simp only [rohW, hn0, ↓reduceIte]
        rw [if_pos hneg, hfind]; simp only; omega
      refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
      rw [hr, sonst_val]
      simp only [einpassenErg, einpassen]
      rw [dif_neg (by omega)]
      rfl
    · have hr : rohW b n w = w.toInt * ((n : Int) + 1) := by
        simp only [rohW, hn0, ↓reduceIte]
        rw [if_neg hneg]
      rw [hr, sonst_val]
      obtain ⟨g1, g2⟩ := einpassen_int (D := D) (z := z) (e := some (.int lo hi)) rfl rfl w
      refine ⟨fun h => ?_, fun h => by rw [g2 h]; rfl⟩
      obtain ⟨v, hv, hen⟩ := g1 h
      exact ⟨v, by rw [hv]; rfl, hen⟩

end Gabbro.Stage0.Senke
