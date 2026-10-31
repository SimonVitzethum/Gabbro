/-
  File:      stage0/Stage0/Senke/Anweisung/SchleifeTeile.lean
  Subject:   The pieces of `traverse`'s proof: the indices from `k` on (`idxAb`), single jumps (`brz_go`, `brz_stay`,
             `jmp_go`), where each part of `travCode` lies (`trav_*`), and the loop's head (`trav_head`, `trav_cmp_ok`).
-/
import Stage0.Senke.Anweisung.Simulation
import Stage0.Senke.Ausdruck.Quant.Indices
import Stage0.Senke.Ausdruck.Gleit.Wort

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D} {reserved : Nat}

@[simp] theorem travCountC_length (d : Nat) (n : Int) :
    (travCountC d n).length = travCountSize n := by
  unfold travCountC travCountSize
  split <;> simp [konstWL, bin2]

attribute [local irreducible] konstWL travCountC travCountSize

/-- A count constant preserves every lower frame word. -/
theorem travCountC_ok {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} (n : Int)
    (room : d + 2 ≤ K) (hp : Pre L m pc fp K d (travCountC d n) ρ W reserved) :
    Ok m pc fp K d (travCountC d n) (· = BitVec.ofInt 64 n) := by
  unfold travCountC at hp ⊢
  split at hp
  · rename_i h
    rw [ite_eq_left h]
    exact const_ok hp h (by omega)
  · rename_i h
    rw [ite_eq_right h]
    exact (konstWL_ok 4 _ (BitVec.isLt _) room hp).mono
      (fun _ h => by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h)

/-- Materialize the count above the saved index, then compare signed words. -/
theorem trav_compare_ok {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} {v : Runner.W} (n : Int)
    (hp : Pre L m pc fp K d
      (travCountC (d + 1) n ++ [ci 13 d d (d + 1)]) ρ W reserved)
    (room : d + 3 ≤ K) (rv : m.rd64 (slot fp (BitVec.ofNat 64 d)) = some v) :
    Ok m pc fp K d (travCountC (d + 1) n ++ [ci 13 d d (d + 1)])
      (· = Runner.IR.bool (v.slt (BitVec.ofInt 64 n))) := by
  obtain ⟨m1, s1, a1, w1, r1, rfl⟩ := travCountC_ok n (by omega)
    { hp.left with ctx := by have := hp.ctx; omega }
  have h1 := hp.next (a1.mono (Nat.le_succ _)) (Nat.le_refl _) (by omega)
  have rv1 : m1.rd64 (slot fp (BitVec.ofNat 64 d)) = some v := by
    rw [agree_rd_low a1 hp.frame.room (by omega) (by omega)]; exact rv
  obtain ⟨m2, s2, a2, w2, r2, rfl⟩ := eng_bin_ok (d := d) (a := d) (b := d + 1) h1 (by omega) (by omega) (by omega)
    rv1 r1 (g := fun x y => some (Runner.IR.bool (x.slt y))) rfl (by decide) rfl
  refine ⟨m2, ?_, (a1.mono (Nat.le_succ _)).trans a2, _, r2, rfl⟩
  simpa only [List.length_append, List.length_singleton, pc_add] using s1.trans s2

/-! ## The indices -/

/-! ## Jumps -/

theorem step_eq (pc : Runner.W) {x y z : Nat} (h : x + y = z) :
    pc + BitVec.ofNat 64 (16 * x) + BitVec.ofNat 64 (16 * y) = pc + BitVec.ofNat 64 (16 * z) := by
  rw [addr_norm]; congr 2; omega

theorem lit_ok {x : Int} (h1 : -2 ^ 31 ≤ x) (h2 : x < 2 ^ 31) : lit32 x = true := by
  simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega

theorem adr_eq (pc : Runner.W) {x y : Nat} {J : Int} (h : (16 * x : Int) + J = 16 * y) :
    pc + BitVec.ofNat 64 (16 * x) + BitVec.ofInt 64 J = pc + BitVec.ofNat 64 (16 * y) := by
  rw [BitVec.add_assoc, ← BitVec.ofInt_natCast, ← BitVec.ofInt_add, ← BitVec.ofInt_natCast]
  congr 2

/-- `brz j J` with slot `j` zero: on at `pc + J`. -/
theorem brz_go {m : Runner.Mem} {pc fp : Runner.W} {K j : Nat} {J : Int}
    (hc : CodeAt m pc [ci 19 j J 0]) (hj : j < K) (hK : K < 2 ^ 31) (hJ : lit32 J = true)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 j)) = some 0) : Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofInt 64 J, fp⟩ m := by
  have hi := hc 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  have r := run_step (t := ⟨pc, fp⟩) hi (by decide)
    (run_brz_zero (t := ⟨pc, fp⟩) hi (by rw [sx_nat (by omega)]; exact hr))
  rw [sx_lit hJ] at r
  exact Star.one r

/-- `brz j J` with slot `j` not zero: on at the next instruction. -/
theorem brz_stay {m : Runner.Mem} {pc fp : Runner.W} {K j : Nat} {J : Int} {w : Runner.W}
    (hc : CodeAt m pc [ci 19 j J 0]) (hj : j < K) (hK : K < 2 ^ 31)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 j)) = some w) (hw : w ≠ 0) :
    Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 1), fp⟩ m := by
  have hi := hc 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  exact star_ins (m' := m) hc (by simp [ci])
    (by simp only [ci]; exact run_brz_ne (t := ⟨pc, fp⟩) hi (by rw [sx_nat (by omega)]; exact hr) hw)

/-- `jmp J`: on at `pc + J`. -/
theorem jmp_go {m : Runner.Mem} {pc fp : Runner.W} {J : Int} (hc : CodeAt m pc [ci 18 J 0 0]) (hJ : lit32 J = true) :
    Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofInt 64 J, fp⟩ m := by
  have hi := hc 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  have r := run_step (t := ⟨pc, fp⟩) hi (by decide) (run_jmp (t := ⟨pc, fp⟩) hi)
  rw [sx_lit hJ] at r
  exact Star.one r

/-! ## The pieces of the code -/

theorem codeAt_at {m : Runner.Mem} {pc p : Runner.W} {xs ys zs : List II} (hc : CodeAt m pc (xs ++ (ys ++ zs)))
    (hp : p = pc + BitVec.ofNat 64 (16 * xs.length)) : CodeAt m p ys := by
  subst hp; exact codeAt_left (codeAt_right hc)

theorem codeFar_at {pc fp : Runner.W} {n K i k : Nat} (h : CodeFar pc n fp K) (hik : i + k ≤ n) :
    CodeFar (pc + BitVec.ofNat 64 (16 * i)) k fp K :=
  codeFar_left (k := n - i - k) (by have := codeFar_right (n := i) (k := n - i) (by rwa [Nat.add_sub_cancel' (by omega)]); rwa [show k + (n - i - k) = n - i by omega])

section
variable {m : Runner.Mem} {pc : Runner.W} {s : Nat} {n : Int} {ci' cb : List II}

theorem travCode_len : (travCode s n ci' cb).length = 13 + travCountSize n + 2 * ci'.length + cb.length := by
  simp only [travCode, travCountC_length, stopC, sysC, List.length_append, List.length_cons, List.length_nil]; omega

theorem trav_inv (hc : CodeAt m pc (travCode s n ci' cb)) : CodeAt m (pc + BitVec.ofNat 64 (16 * 1)) ci' :=
  codeAt_at (xs := [ci 1 s 0 0]) (by simpa [travCode] using hc) (by simp)

theorem trav_brz1 (hc : CodeAt m pc (travCode s n ci' cb)) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * (1 + ci'.length)))
      [ci 19 ((s + 1 : Nat) : Int) (16 * (9 + travCountSize n + ci'.length + cb.length)) 0] :=
  codeAt_at (xs := [ci 1 s 0 0] ++ ci') (by simpa [travCode, List.append_assoc] using hc)
    (by simp only [List.length_append, List.length_singleton])

theorem trav_cmp (hc : CodeAt m pc (travCode s n ci' cb)) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * (2 + ci'.length)))
      ([ci 2 ((s + 1 : Nat) : Int) s 0] ++ (travCountC (s + 2) n ++ [ci 13 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) ((s + 2 : Nat) : Int)])) :=
  codeAt_at (xs := [ci 1 s 0 0] ++ ci' ++ [ci 19 ((s + 1 : Nat) : Int) (16 * (9 + travCountSize n + ci'.length + cb.length)) 0])
    (by simpa [travCode, List.append_assoc] using hc)
    (by simp only [List.length_append, List.length_singleton]; congr 2; omega)

theorem trav_brz2 (hc : CodeAt m pc (travCode s n ci' cb)) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * (4 + travCountSize n + ci'.length)))
      [ci 19 ((s + 1 : Nat) : Int) (16 * (9 + ci'.length + cb.length)) 0] :=
  codeAt_at (xs := [ci 1 s 0 0] ++ ci' ++ [ci 19 ((s + 1 : Nat) : Int) (16 * (9 + travCountSize n + ci'.length + cb.length)) 0,
      ci 2 ((s + 1 : Nat) : Int) s 0] ++ travCountC (s + 2) n ++ [ci 13 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) ((s + 2 : Nat) : Int)])
    (by simpa [travCode, List.append_assoc] using hc)
    (by simp only [travCountC_length, List.length_append, List.length_cons, List.length_nil]; congr 2; omega)

theorem trav_body (hc : CodeAt m pc (travCode s n ci' cb)) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * (5 + travCountSize n + ci'.length))) cb :=
  codeAt_at (xs := [ci 1 s 0 0] ++ ci' ++ [ci 19 ((s + 1 : Nat) : Int) (16 * (9 + travCountSize n + ci'.length + cb.length)) 0,
      ci 2 ((s + 1 : Nat) : Int) s 0] ++ travCountC (s + 2) n ++ [ci 13 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) ((s + 2 : Nat) : Int),
      ci 19 ((s + 1 : Nat) : Int) (16 * (9 + ci'.length + cb.length)) 0])
    (by simpa [travCode, List.append_assoc] using hc)
    (by simp only [travCountC_length, List.length_append, List.length_cons, List.length_nil]; congr 2; omega)

theorem trav_next (hc : CodeAt m pc (travCode s n ci' cb)) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * (5 + travCountSize n + ci'.length + cb.length))) [ci 1 (s + 1) 1 0, ci 3 s s (s + 1)] :=
  codeAt_at (xs := [ci 1 s 0 0] ++ ci' ++ [ci 19 ((s + 1 : Nat) : Int) (16 * (9 + travCountSize n + ci'.length + cb.length)) 0,
      ci 2 ((s + 1 : Nat) : Int) s 0] ++ travCountC (s + 2) n ++ [ci 13 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) ((s + 2 : Nat) : Int),
      ci 19 ((s + 1 : Nat) : Int) (16 * (9 + ci'.length + cb.length)) 0] ++ cb)
    (by simpa [travCode, List.append_assoc] using hc)
    (by simp only [travCountC_length, List.length_append, List.length_cons, List.length_nil]; congr 2; omega)

theorem trav_back (hc : CodeAt m pc (travCode s n ci' cb)) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * (7 + travCountSize n + ci'.length + cb.length))) [ci 18 (-(16 * (6 + travCountSize n + ci'.length + cb.length))) 0 0] :=
  codeAt_at (xs := [ci 1 s 0 0] ++ ci' ++ [ci 19 ((s + 1 : Nat) : Int) (16 * (9 + travCountSize n + ci'.length + cb.length)) 0,
      ci 2 ((s + 1 : Nat) : Int) s 0] ++ travCountC (s + 2) n ++ [ci 13 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) ((s + 2 : Nat) : Int),
      ci 19 ((s + 1 : Nat) : Int) (16 * (9 + ci'.length + cb.length)) 0] ++ cb ++ [ci 1 (s + 1) 1 0, ci 3 s s (s + 1)])
    (by simpa [travCode, List.append_assoc] using hc)
    (by simp only [travCountC_length, List.length_append, List.length_cons, List.length_nil]; congr 2; omega)

theorem trav_inv2 (hc : CodeAt m pc (travCode s n ci' cb)) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * (8 + travCountSize n + ci'.length + cb.length))) ci' :=
  codeAt_at (xs := [ci 1 s 0 0] ++ ci' ++ [ci 19 ((s + 1 : Nat) : Int) (16 * (9 + travCountSize n + ci'.length + cb.length)) 0,
      ci 2 ((s + 1 : Nat) : Int) s 0] ++ travCountC (s + 2) n ++ [ci 13 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) ((s + 2 : Nat) : Int),
      ci 19 ((s + 1 : Nat) : Int) (16 * (9 + ci'.length + cb.length)) 0] ++ cb ++ [ci 1 (s + 1) 1 0, ci 3 s s (s + 1)] ++ [ci 18 (-(16 * (6 + travCountSize n + ci'.length + cb.length))) 0 0])
    (by simpa [travCode, List.append_assoc] using hc)
    (by simp only [travCountC_length, List.length_append, List.length_cons, List.length_nil]; congr 2; omega)

theorem trav_brz3 (hc : CodeAt m pc (travCode s n ci' cb)) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * (8 + travCountSize n + 2 * ci'.length + cb.length))) [ci 19 ((s + 1 : Nat) : Int) 32 0] :=
  codeAt_at (xs := [ci 1 s 0 0] ++ ci' ++ [ci 19 ((s + 1 : Nat) : Int) (16 * (9 + travCountSize n + ci'.length + cb.length)) 0,
      ci 2 ((s + 1 : Nat) : Int) s 0] ++ travCountC (s + 2) n ++ [ci 13 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) ((s + 2 : Nat) : Int),
      ci 19 ((s + 1 : Nat) : Int) (16 * (9 + ci'.length + cb.length)) 0] ++ cb ++ [ci 1 (s + 1) 1 0, ci 3 s s (s + 1)] ++ [ci 18 (-(16 * (6 + travCountSize n + ci'.length + cb.length))) 0 0] ++ ci')
    (by simpa [travCode, List.append_assoc] using hc)
    (by simp only [travCountC_length, List.length_append, List.length_cons, List.length_nil]; congr 2; omega)

theorem trav_jmp2 (hc : CodeAt m pc (travCode s n ci' cb)) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * (9 + travCountSize n + 2 * ci'.length + cb.length))) [ci 18 64 0 0] :=
  codeAt_at (xs := [ci 1 s 0 0] ++ ci' ++ [ci 19 ((s + 1 : Nat) : Int) (16 * (9 + travCountSize n + ci'.length + cb.length)) 0,
      ci 2 ((s + 1 : Nat) : Int) s 0] ++ travCountC (s + 2) n ++ [ci 13 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) ((s + 2 : Nat) : Int),
      ci 19 ((s + 1 : Nat) : Int) (16 * (9 + ci'.length + cb.length)) 0] ++ cb ++ [ci 1 (s + 1) 1 0, ci 3 s s (s + 1)] ++ [ci 18 (-(16 * (6 + travCountSize n + ci'.length + cb.length))) 0 0] ++ ci' ++ [ci 19 ((s + 1 : Nat) : Int) 32 0])
    (by simpa [travCode, List.append_assoc] using hc)
    (by simp only [travCountC_length, List.length_append, List.length_cons, List.length_nil]; congr 2; omega)

theorem trav_stop (hc : CodeAt m pc (travCode s n ci' cb)) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * (10 + travCountSize n + 2 * ci'.length + cb.length))) (stopC 104 (s + 1)) := by
  have := codeAt_right (a := [ci 1 s 0 0] ++ ci' ++ [ci 19 ((s + 1 : Nat) : Int) (16 * (9 + travCountSize n + ci'.length + cb.length)) 0,
      ci 2 ((s + 1 : Nat) : Int) s 0] ++ travCountC (s + 2) n ++ [ci 13 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) ((s + 2 : Nat) : Int),
      ci 19 ((s + 1 : Nat) : Int) (16 * (9 + ci'.length + cb.length)) 0] ++ cb ++ [ci 1 (s + 1) 1 0, ci 3 s s (s + 1)] ++ [ci 18 (-(16 * (6 + travCountSize n + ci'.length + cb.length))) 0 0] ++ ci' ++
    [ci 19 ((s + 1 : Nat) : Int) 32 0, ci 18 64 0 0]) (b := stopC 104 (s + 1)) (by simpa [travCode, List.append_assoc] using hc)
  have e : ∀ p q : Runner.W, p = q → CodeAt m p (stopC 104 (s + 1)) → CodeAt m q (stopC 104 (s + 1)) := by
    intro p q h hc; subst h; exact hc
  refine e _ _ ?_ this
  simp only [travCountC_length, List.length_append, List.length_cons, List.length_nil]; congr 2; omega

end

/-! ## The head of the loop -/

/-- A statement's precondition from its parts. -/
theorem mkPreS {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {c : List II} {Γ : Ctx} {ρ : Env D Γ} {reserved : Nat}
    (hctx : frei Γ reserved ≤ d) (hK : K < 2 ^ 31) (hF : FrameOK m fp K) (hc : CodeAt m pc c) (hf : CodeFar pc c.length fp K)
    (he : EnvAt L m fp ρ reserved) : PreS L m pc fp K d c ρ reserved :=
  ⟨hctx, hK, hF, hc, hf, he, trivial, wstab_true _ _⟩

theorem slt_k {k : Nat} {n : Int} (hk : k < 2 ^ 63) (hn : inW n n = true) :
    (BitVec.ofNat 64 k).slt (BitVec.ofInt 64 n) = decide ((k : Int) < n) := by
  simp only [inW, Bool.and_eq_true, decide_eq_true_eq] at hn
  rw [← BitVec.ofInt_natCast]
  exact slt_in (by omega) (by omega)

/-- The head: the invariant into slot `s + 1` (G's `inv` of the loop), and the memory keeps the world, the frame
    below `s + 1` and the code. -/
theorem trav_head {L : Lay D} {fp pc : Runner.W} {K Ks : Nat} {Γ : Ctx} {Λ : List (Res D)} {inv : Expr D Γ Λ .bool}
    {ci' : List II × Nat} {cb : List II} {n : Int} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (hci : lowE (reserved := reserved) L inv (frei Γ reserved + 1) = some ci') (htop : ci'.2 ≤ Ks) (hW : WIn L fp Ks K)
    (hp : PreS L m pc fp K (frei Γ reserved) (travCode (frei Γ reserved) n ci'.1 cb) ρ reserved) (hWa : WeltAt m L σ) :
    ∃ m1 w, Star ⟨pc + BitVec.ofNat 64 (16 * 1), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (1 + ci'.1.length)), fp⟩ m1 ∧
      Agree fp (frei Γ reserved + 1) Ks m m1 ∧ m1.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved + 1))) = some w ∧
      w = (if wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true then 1 else 0) ∧ WeltAt m1 L σ := by
  have hks := hW.ks
  have hlen := travCode_len (s := frei Γ reserved) (n := n) (ci' := ci'.1) (cb := cb)
  have hq : PreS L m (pc + BitVec.ofNat 64 (16 * 1)) fp K (frei Γ reserved + 1) ci'.1 ρ reserved :=
    mkPreS (by omega) hp.small hp.frame (trav_inv hp.code) (codeFar_at hp.far (by omega)) hp.env
  have hpw := PreS.welt hq hks hWa hW.lay (by have := hW.lo; omega)
  obtain ⟨m1, s1, a1s, w, hw, hen⟩ := lowE_ok (σ.lese Λ inv.orte) (σ.lese Λ inv.orte) (fun _ h => h) inv _ ci'.1
    ci'.2 hci htop m _ ρ hpw
  refine ⟨m1, w, ?_, a1s, hw, hen, hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _))⟩
  rw [addr_norm] at s1
  simpa [Nat.mul_add] using s1

/-- `k < count` into slot `s + 1`. -/
theorem trav_cmp_ok {L : Lay D} {fp pc : Runner.W} {K Ks k : Nat} {Γ : Ctx} {ci' cb : List II} {n : Int}
    {m : Runner.Mem} {σ : World D} {ρ : Env D Γ} (hn : inW n n = true)
    (hp : PreS L m pc fp K (frei Γ reserved) (travCode (frei Γ reserved) n ci' cb) ρ reserved) (hW : WIn L fp Ks K) (hWa : WeltAt m L σ)
    (hks : frei Γ reserved + 9 ≤ Ks) (hk0 : m.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved))) = some (BitVec.ofNat 64 k))
    (hk : k < 2 ^ 63) :
    ∃ m2, Star ⟨pc + BitVec.ofNat 64 (16 * (2 + ci'.length)), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (4 + travCountSize n + ci'.length)), fp⟩ m2 ∧
      Agree fp (frei Γ reserved + 1) Ks m m2 ∧
      m2.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved + 1))) = some (Runner.IR.bool (decide ((k : Int) < n))) ∧
      WeltAt m2 L σ := by
  have hlen := travCode_len (s := frei Γ reserved) (n := n) (ci' := ci') (cb := cb)
  have hksK := hW.ks
  have hq : PreS L m (pc + BitVec.ofNat 64 (16 * (2 + ci'.length))) fp K (frei Γ reserved + 1)
      ([ci 2 ((frei Γ reserved + 1 : Nat) : Int) (frei Γ reserved) 0] ++ (travCountC (frei Γ reserved + 2) n ++ [ci 13 ((frei Γ reserved + 1 : Nat) : Int) ((frei Γ reserved + 1 : Nat) : Int) ((frei Γ reserved + 2 : Nat) : Int)])) ρ reserved :=
    mkPreS (by omega) hp.small hp.frame (trav_cmp hp.code) (codeFar_at hp.far (by simp; omega)) hp.env
  have hpw := PreS.welt hq hksK hWa hW.lay (by have := hW.lo; omega)
  have := hpw.small
  obtain ⟨m2, s2, a2, w, hw, hwe⟩ := ok_seq hpw (mov_ok hpw.left (by omega) (by omega) hk0)
    (Pb := (· = Runner.IR.bool ((BitVec.ofNat 64 k).slt (BitVec.ofInt 64 n))))
    (fun m' w' hp' hr he => (trav_compare_ok n hp' (by omega) hr).mono
      fun x hx => by rw [hx, he]) (by omega)
  refine ⟨m2, ?_, a2, by rw [hw, hwe, slt_k hk hn], hpw.wstab m m2 hWa (a2.mono (Nat.zero_le _))⟩
  have e : pc + BitVec.ofNat 64 (16 * (2 + ci'.length)) + BitVec.ofNat 64 (16 * ([ci 2 ((frei Γ reserved + 1 : Nat) : Int) (frei Γ reserved) 0] ++ (travCountC (frei Γ reserved + 2) n ++ [ci 13 ((frei Γ reserved + 1 : Nat) : Int) ((frei Γ reserved + 1 : Nat) : Int) ((frei Γ reserved + 2 : Nat) : Int)])).length) =
      pc + BitVec.ofNat 64 (16 * (4 + travCountSize n + ci'.length)) := by
    rw [addr_norm]; simp only [travCountC_length, List.length_append, List.length_cons, List.length_nil]
    congr 2; omega
  rw [← e]; exact s2

end Gabbro.Stage0.Senke
