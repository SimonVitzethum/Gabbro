/-
  File:      stage0/Stage0/Senke/Anweisung/SchleifeTeile.lean
  Subject:   The pieces of `traverse`'s proof: the indices from `k` on (`idxAb`), single jumps (`brz_go`, `brz_stay`,
             `jmp_go`), where each part of `travCode` lies (`trav_*`), and the loop's head (`trav_head`, `trav_cmp_ok`).
-/
import Stage0.Senke.Anweisung.Simulation
import Stage0.Senke.Ausdruck.Quant.Indices

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

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

theorem travCode_len : (travCode s n ci' cb).length = 14 + 2 * ci'.length + cb.length := by
  simp only [travCode, stopC, sysC, List.length_append, List.length_cons, List.length_nil]; omega

theorem trav_inv (hc : CodeAt m pc (travCode s n ci' cb)) : CodeAt m (pc + BitVec.ofNat 64 (16 * 1)) ci' :=
  codeAt_at (xs := [ci 1 s 0 0]) (by simpa [travCode] using hc) (by simp)

theorem trav_brz1 (hc : CodeAt m pc (travCode s n ci' cb)) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * (1 + ci'.length)))
      [ci 19 ((s + 1 : Nat) : Int) (16 * (10 + ci'.length + cb.length)) 0] :=
  codeAt_at (xs := [ci 1 s 0 0] ++ ci') (by simpa [travCode, List.append_assoc] using hc)
    (by simp only [List.length_append, List.length_singleton])

theorem trav_cmp (hc : CodeAt m pc (travCode s n ci' cb)) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * (2 + ci'.length)))
      [ci 2 ((s + 1 : Nat) : Int) s 0, ci 1 (((s + 1 : Nat) : Int) + 1) n 0,
       ci 13 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) (((s + 1 : Nat) : Int) + 1)] :=
  codeAt_at (xs := [ci 1 s 0 0] ++ ci' ++ [ci 19 ((s + 1 : Nat) : Int) (16 * (10 + ci'.length + cb.length)) 0])
    (by simpa [travCode, List.append_assoc] using hc)
    (by simp only [List.length_append, List.length_singleton]; congr 2; omega)

theorem trav_brz2 (hc : CodeAt m pc (travCode s n ci' cb)) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * (5 + ci'.length)))
      [ci 19 ((s + 1 : Nat) : Int) (16 * (9 + ci'.length + cb.length)) 0] :=
  codeAt_at (xs := [ci 1 s 0 0] ++ ci' ++ [ci 19 ((s + 1 : Nat) : Int) (16 * (10 + ci'.length + cb.length)) 0,
      ci 2 ((s + 1 : Nat) : Int) s 0, ci 1 (((s + 1 : Nat) : Int) + 1) n 0,
      ci 13 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) (((s + 1 : Nat) : Int) + 1)])
    (by simpa [travCode, List.append_assoc] using hc)
    (by simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil]; congr 2; omega)

theorem trav_body (hc : CodeAt m pc (travCode s n ci' cb)) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * (6 + ci'.length))) cb :=
  codeAt_at (xs := [ci 1 s 0 0] ++ ci' ++ [ci 19 ((s + 1 : Nat) : Int) (16 * (10 + ci'.length + cb.length)) 0,
      ci 2 ((s + 1 : Nat) : Int) s 0, ci 1 (((s + 1 : Nat) : Int) + 1) n 0,
      ci 13 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) (((s + 1 : Nat) : Int) + 1),
      ci 19 ((s + 1 : Nat) : Int) (16 * (9 + ci'.length + cb.length)) 0])
    (by simpa [travCode, List.append_assoc] using hc)
    (by simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil]; congr 2; omega)

theorem trav_next (hc : CodeAt m pc (travCode s n ci' cb)) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * (6 + ci'.length + cb.length))) [ci 1 (s + 1) 1 0, ci 3 s s (s + 1)] :=
  codeAt_at (xs := [ci 1 s 0 0] ++ ci' ++ [ci 19 ((s + 1 : Nat) : Int) (16 * (10 + ci'.length + cb.length)) 0,
      ci 2 ((s + 1 : Nat) : Int) s 0, ci 1 (((s + 1 : Nat) : Int) + 1) n 0,
      ci 13 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) (((s + 1 : Nat) : Int) + 1),
      ci 19 ((s + 1 : Nat) : Int) (16 * (9 + ci'.length + cb.length)) 0] ++ cb)
    (by simpa [travCode, List.append_assoc] using hc)
    (by simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil]; congr 2; omega)

theorem trav_back (hc : CodeAt m pc (travCode s n ci' cb)) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * (8 + ci'.length + cb.length))) [ci 18 (-(16 * (7 + ci'.length + cb.length))) 0 0] :=
  codeAt_at (xs := [ci 1 s 0 0] ++ ci' ++ [ci 19 ((s + 1 : Nat) : Int) (16 * (10 + ci'.length + cb.length)) 0,
      ci 2 ((s + 1 : Nat) : Int) s 0, ci 1 (((s + 1 : Nat) : Int) + 1) n 0,
      ci 13 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) (((s + 1 : Nat) : Int) + 1),
      ci 19 ((s + 1 : Nat) : Int) (16 * (9 + ci'.length + cb.length)) 0] ++ cb ++ [ci 1 (s + 1) 1 0, ci 3 s s (s + 1)])
    (by simpa [travCode, List.append_assoc] using hc)
    (by simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil]; congr 2; omega)

theorem trav_inv2 (hc : CodeAt m pc (travCode s n ci' cb)) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * (9 + ci'.length + cb.length))) ci' :=
  codeAt_at (xs := [ci 1 s 0 0] ++ ci' ++ [ci 19 ((s + 1 : Nat) : Int) (16 * (10 + ci'.length + cb.length)) 0,
      ci 2 ((s + 1 : Nat) : Int) s 0, ci 1 (((s + 1 : Nat) : Int) + 1) n 0,
      ci 13 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) (((s + 1 : Nat) : Int) + 1),
      ci 19 ((s + 1 : Nat) : Int) (16 * (9 + ci'.length + cb.length)) 0] ++ cb ++ [ci 1 (s + 1) 1 0, ci 3 s s (s + 1)] ++ [ci 18 (-(16 * (7 + ci'.length + cb.length))) 0 0])
    (by simpa [travCode, List.append_assoc] using hc)
    (by simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil]; congr 2; omega)

theorem trav_brz3 (hc : CodeAt m pc (travCode s n ci' cb)) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * (9 + 2 * ci'.length + cb.length))) [ci 19 ((s + 1 : Nat) : Int) 32 0] :=
  codeAt_at (xs := [ci 1 s 0 0] ++ ci' ++ [ci 19 ((s + 1 : Nat) : Int) (16 * (10 + ci'.length + cb.length)) 0,
      ci 2 ((s + 1 : Nat) : Int) s 0, ci 1 (((s + 1 : Nat) : Int) + 1) n 0,
      ci 13 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) (((s + 1 : Nat) : Int) + 1),
      ci 19 ((s + 1 : Nat) : Int) (16 * (9 + ci'.length + cb.length)) 0] ++ cb ++ [ci 1 (s + 1) 1 0, ci 3 s s (s + 1)] ++ [ci 18 (-(16 * (7 + ci'.length + cb.length))) 0 0] ++ ci')
    (by simpa [travCode, List.append_assoc] using hc)
    (by simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil]; congr 2; omega)

theorem trav_jmp2 (hc : CodeAt m pc (travCode s n ci' cb)) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * (10 + 2 * ci'.length + cb.length))) [ci 18 64 0 0] :=
  codeAt_at (xs := [ci 1 s 0 0] ++ ci' ++ [ci 19 ((s + 1 : Nat) : Int) (16 * (10 + ci'.length + cb.length)) 0,
      ci 2 ((s + 1 : Nat) : Int) s 0, ci 1 (((s + 1 : Nat) : Int) + 1) n 0,
      ci 13 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) (((s + 1 : Nat) : Int) + 1),
      ci 19 ((s + 1 : Nat) : Int) (16 * (9 + ci'.length + cb.length)) 0] ++ cb ++ [ci 1 (s + 1) 1 0, ci 3 s s (s + 1)] ++ [ci 18 (-(16 * (7 + ci'.length + cb.length))) 0 0] ++ ci' ++ [ci 19 ((s + 1 : Nat) : Int) 32 0])
    (by simpa [travCode, List.append_assoc] using hc)
    (by simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil]; congr 2; omega)

theorem trav_stop (hc : CodeAt m pc (travCode s n ci' cb)) :
    CodeAt m (pc + BitVec.ofNat 64 (16 * (11 + 2 * ci'.length + cb.length))) (stopC 104 (s + 1)) := by
  have := codeAt_right (a := [ci 1 s 0 0] ++ ci' ++ [ci 19 ((s + 1 : Nat) : Int) (16 * (10 + ci'.length + cb.length)) 0,
      ci 2 ((s + 1 : Nat) : Int) s 0, ci 1 (((s + 1 : Nat) : Int) + 1) n 0,
      ci 13 ((s + 1 : Nat) : Int) ((s + 1 : Nat) : Int) (((s + 1 : Nat) : Int) + 1),
      ci 19 ((s + 1 : Nat) : Int) (16 * (9 + ci'.length + cb.length)) 0] ++ cb ++ [ci 1 (s + 1) 1 0, ci 3 s s (s + 1)] ++ [ci 18 (-(16 * (7 + ci'.length + cb.length))) 0 0] ++ ci' ++
    [ci 19 ((s + 1 : Nat) : Int) 32 0, ci 18 64 0 0]) (b := stopC 104 (s + 1)) (by simpa [travCode, List.append_assoc] using hc)
  have e : ∀ p q : Runner.W, p = q → CodeAt m p (stopC 104 (s + 1)) → CodeAt m q (stopC 104 (s + 1)) := by
    intro p q h hc; subst h; exact hc
  refine e _ _ ?_ this
  simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil]; congr 2; omega

end

/-! ## The head of the loop -/

/-- A statement's precondition from its parts. -/
theorem mkPreS {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {c : List II} {Γ : Ctx} {ρ : Env D Γ}
    (hctx : frei Γ ≤ d) (hK : K < 2 ^ 31) (hF : FrameOK m fp K) (hc : CodeAt m pc c) (hf : CodeFar pc c.length fp K)
    (he : EnvAt L m fp ρ) : PreS L m pc fp K d c ρ :=
  ⟨hctx, hK, hF, hc, hf, he, trivial, wstab_true _ _⟩

theorem slt_k {k : Nat} {n : Int} (hk : k < 2 ^ 31) (hn : lit32 n = true) :
    (BitVec.ofNat 64 k).slt (BitVec.ofInt 64 n) = decide ((k : Int) < n) := by
  simp only [lit32, Bool.and_eq_true, decide_eq_true_eq] at hn
  rw [← BitVec.ofInt_natCast]
  exact slt_in (by omega) (by omega)

/-- The head: the invariant into slot `s + 1` (G's `inv` of the loop), and the memory keeps the world, the frame
    below `s + 1` and the code. -/
theorem trav_head {L : Lay D} {fp pc : Runner.W} {K Ks : Nat} {Γ : Ctx} {Λ : List (Res D)} {inv : Expr D Γ Λ .bool}
    {ci' : List II × Nat} {cb : List II} {n : Int} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (hci : lowE L inv (frei Γ + 1) = some ci') (htop : ci'.2 ≤ Ks) (hW : WIn L fp Ks K)
    (hp : PreS L m pc fp K (frei Γ) (travCode (frei Γ) n ci'.1 cb) ρ) (hWa : WeltAt m L σ) :
    ∃ m1 w, Star ⟨pc + BitVec.ofNat 64 (16 * 1), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (1 + ci'.1.length)), fp⟩ m1 ∧
      Agree fp (frei Γ + 1) Ks m m1 ∧ m1.rd64 (slot fp (BitVec.ofNat 64 (frei Γ + 1))) = some w ∧
      w = (if wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true then 1 else 0) ∧ WeltAt m1 L σ := by
  have hks := hW.ks
  have hlen := travCode_len (s := frei Γ) (n := n) (ci' := ci'.1) (cb := cb)
  have hq : PreS L m (pc + BitVec.ofNat 64 (16 * 1)) fp K (frei Γ + 1) ci'.1 ρ :=
    mkPreS (by omega) hp.small hp.frame (trav_inv hp.code) (codeFar_at hp.far (by omega)) hp.env
  have hpw := PreS.welt hq hks hWa hW.lay (by have := hW.lo; omega)
  obtain ⟨m1, s1, a1s, w, hw, hen⟩ := lowE_ok (σ.lese Λ inv.orte) (σ.lese Λ inv.orte) (fun _ h => h) inv _ ci'.1
    ci'.2 hci htop m _ ρ hpw
  refine ⟨m1, w, ?_, a1s, hw, hen, hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _))⟩
  rw [addr_norm] at s1
  simpa [Nat.mul_add] using s1

/-- `k < count` into slot `s + 1`. -/
theorem trav_cmp_ok {L : Lay D} {fp pc : Runner.W} {K Ks k : Nat} {Γ : Ctx} {ci' cb : List II} {n : Int}
    {m : Runner.Mem} {σ : World D} {ρ : Env D Γ} (hn : lit32 n = true)
    (hp : PreS L m pc fp K (frei Γ) (travCode (frei Γ) n ci' cb) ρ) (hW : WIn L fp Ks K) (hWa : WeltAt m L σ)
    (hks : frei Γ + 9 ≤ Ks) (hk0 : m.rd64 (slot fp (BitVec.ofNat 64 (frei Γ))) = some (BitVec.ofNat 64 k))
    (hk : k < 2 ^ 31) :
    ∃ m2, Star ⟨pc + BitVec.ofNat 64 (16 * (2 + ci'.length)), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (5 + ci'.length)), fp⟩ m2 ∧
      Agree fp (frei Γ + 1) Ks m m2 ∧
      m2.rd64 (slot fp (BitVec.ofNat 64 (frei Γ + 1))) = some (Runner.IR.bool (decide ((k : Int) < n))) ∧
      WeltAt m2 L σ := by
  have hlen := travCode_len (s := frei Γ) (n := n) (ci' := ci') (cb := cb)
  have hksK := hW.ks
  have hq : PreS L m (pc + BitVec.ofNat 64 (16 * (2 + ci'.length))) fp K (frei Γ + 1)
      ([ci 2 ((frei Γ + 1 : Nat) : Int) (frei Γ) 0] ++ [ci 1 (((frei Γ + 1 : Nat) : Int) + 1) n 0,
        ci 13 ((frei Γ + 1 : Nat) : Int) ((frei Γ + 1 : Nat) : Int) (((frei Γ + 1 : Nat) : Int) + 1)]) ρ :=
    mkPreS (by omega) hp.small hp.frame (trav_cmp hp.code) (codeFar_at hp.far (by simp; omega)) hp.env
  have hpw := PreS.welt hq hksK hWa hW.lay (by have := hW.lo; omega)
  have := hpw.small
  obtain ⟨m2, s2, a2, w, hw, hwe⟩ := ok_seq hpw (mov_ok hpw.left (by omega) (by omega) hk0)
    (Pb := (· = Runner.IR.bool ((BitVec.ofNat 64 k).slt (BitVec.ofInt 64 n))))
    (fun m' w' hp' hr he => (binK_ok (r := Runner.IR.bool (w'.slt (BitVec.ofInt 64 n))) hp' hr hn rfl (by decide)
      rfl (by omega)).mono fun x hx => by rw [hx, he]) (by omega)
  refine ⟨m2, ?_, a2, by rw [hw, hwe, slt_k hk hn], hpw.wstab m m2 hWa (a2.mono (Nat.zero_le _))⟩
  have e : pc + BitVec.ofNat 64 (16 * (2 + ci'.length)) + BitVec.ofNat 64 (16 * ([ci 2 ((frei Γ + 1 : Nat) : Int) (frei Γ) 0] ++ [ci 1 (((frei Γ + 1 : Nat) : Int) + 1) n 0,
        ci 13 ((frei Γ + 1 : Nat) : Int) ((frei Γ + 1 : Nat) : Int) (((frei Γ + 1 : Nat) : Int) + 1)]).length) =
      pc + BitVec.ofNat 64 (16 * (5 + ci'.length)) := by
    rw [addr_norm]; simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil]
    congr 2; omega
  rw [← e]; exact s2

end Gabbro.Stage0.Senke
