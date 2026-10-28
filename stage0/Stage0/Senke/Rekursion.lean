/-
  File:      stage0/Stage0/Senke/Rekursion.lean
  Subject:   Every lowered function keeps its `FunSpec` against G's call semantics `rufAt n`, by induction over
             the depth `n`.

  The code of `f` (`lowFun`): the depth guard (slot 2 zero: `exit_group(105)`, G's `abstieg`), `requires` with
  its guard (`exit_group(101)`), the body (`lowEnd_ok`, whose calls go to depth `n - 1`). The stack each call
  needs is at most `L` slots (the largest `top` of all functions), so a call at depth `n` needs `(n + 1) * L`.
-/
import Stage0.Senke.FunktionSatz

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

variable {D : Deklaration}

theorem guard_brz {m : Runner.Mem} {pc : Runner.W} {a c s : Nat} (hc : CodeAt m pc (guardC a c s)) :
    InsAt m pc 19 (II.f (a : Int)) (II.f 32) (II.f 0) := by
  have h := hc 0 (by simp [guardC])
  simpa [guardC, ci] using h

/-- The guard over slot `a`, which holds zero: `exit_group(c)`. -/
theorem guard_stop {m : Runner.Mem} {pc fp : Runner.W} {K a c s : Nat} (hc : CodeAt m pc (guardC a c s))
    (hf : CodeFar pc 5 fp K) (hF : FrameOK m fp K) (ha : a < K) (hs : s + 8 ≤ K) (hK : K < 2 ^ 31)
    (hcode : c < 2 ^ 31) (h0 : m.rd64 (slot fp (BitVec.ofNat 64 a)) = some 0) : Stops ⟨pc, fp⟩ m c := by
  have hbrz := guard_brz hc
  have hd : sx (II.f (a : Int)) = BitVec.ofNat 64 a := sx_nat (by omega)
  have hl : sx (II.f 32) = BitVec.ofNat 64 32 := sx_nat (d := 32) (by omega)
  have sb := Star.one (run_step (t := ⟨pc, fp⟩) hbrz (by decide)
    (run_brz_zero (t := ⟨pc, fp⟩) hbrz (by rw [hd]; exact h0)))
  rw [hl] at sb
  exact Stops.prefix sb (stop_ok (codeAt_right (a := [ci 19 a 32 0, ci 18 64 0 0]) hc)
    (codeFar_right (n := 2) (k := 3) hf) hF hs hK hcode)

/-- The guard over slot `a`, which holds a nonzero word: on after the guard, nothing written. -/
theorem guard_pass {m : Runner.Mem} {pc fp : Runner.W} {a c s : Nat} {v : Runner.W}
    (hc : CodeAt m pc (guardC a c s)) (ha : a < 2 ^ 31) (hv : m.rd64 (slot fp (BitVec.ofNat 64 a)) = some v)
    (hne : v ≠ 0) : Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (guardC a c s).length), fp⟩ m := by
  have hbrz := guard_brz hc
  have hd : sx (II.f (a : Int)) = BitVec.ofNat 64 a := sx_nat (by omega)
  have rb := run_brz_ne (t := ⟨pc, fp⟩) hbrz (by rw [hd]; exact hv) hne
  have sb := star_ins (fp := fp) (m' := m) (codeAt_left (a := [ci 19 a 32 0]) hc) (by simp [ci])
    (by simp only [ci]; exact rb)
  have hj := codeAt_right (a := [ci 19 a 32 0]) hc
  have hjmp := hj 0 (by simp [guardC])
  simp only [guardC, ci, List.cons_append, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hjmp
  have sj := Star.one (run_step (t := ⟨_, fp⟩) hjmp (by decide) (run_jmp (t := ⟨_, fp⟩) hjmp))
  have hl : sx (II.f 64) = BitVec.ofNat 64 64 := sx_nat (d := 64) (by omega)
  rw [hl] at sj
  refine star_cast (sb.trans sj) rfl ?_
  simp only [T.mk.injEq, and_true, List.length_singleton, addr_norm]
  rfl

theorem ofNat_succ (k : Nat) : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + 1 := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h1]
  omega

theorem lowFun_spec {P : Programm D} {O : Orakel D} {passes : Nat} {A : D.Fn → Nat} {C : D.Fn → List II} {L : Nat}
    (hC : ∀ g, ∃ top, lowFun P A g = some (C g, top) ∧ top ≤ L) (hA : ∀ g, A g < 2 ^ 31)
    (hlen : ∀ g, 16 * (C g).length < 2 ^ 31) :
    ∀ n, n < 2 ^ 64 → FunSpec A C (rufAt P O passes n) (BitVec.ofNat 64 n) ((n + 1) * L) := by
  intro n
  induction n with
  | zero =>
    intro _ f m fp K rp cfp σ ρ hc hK hF hP h0 h1 h2 hE
    obtain ⟨top, hlf, htop⟩ := hC f
    simp only [lowFun] at hlf
    split at hlf
    · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at hlf
      obtain ⟨⟨cq, tq⟩, hq, ⟨cens, tens⟩, hens, ⟨cb, tb⟩, hb, hCf, htf⟩ := hlf
      have hFB3 : FB = 3 := rfl
      have hcode := (hP f).1
      have hfar := (hP f).2
      rw [← hCf] at hcode hfar
      simp only [rufAt]
      refine guard_stop (codeAt_left (codeAt_left (codeAt_left hcode))) ?_ hF (by omega) (by omega) hK
        (by simp [logikCode]) h2
      have := codeFar_left (n := (guardC 2 105 (FB + (D.params f).length)).length)
        (k := cq.length + (guardC (FB + (D.params f).length) 101 (FB + (D.params f).length)).length + cb.length)
        (by simpa [Nat.add_assoc] using hfar)
      simpa [guardC, stopC] using this
    · simp at hlf
  | succ k ih =>
    intro hn f m fp K rp cfp σ ρ hc hK hF hP h0 h1 h2 hE
    have ih := ih (by omega)
    obtain ⟨top, hlf, htop⟩ := hC f
    simp only [lowFun] at hlf
    split at hlf
    · next hcond =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at hlf
      obtain ⟨⟨cq, tq⟩, hq, ⟨cens, tens⟩, hens, ⟨cb, tb⟩, hb, hCf, htf⟩ := hlf
      have hFB3 : FB = 3 := rfl
      have hmul : (k + 1 + 1) * L = (k + 1) * L + L := Nat.succ_mul _ _
      have hroom := hF.room
      let s := FB + (D.params f).length
      have hcode0 := (hP f).1
      have hfar0 := (hP f).2
      rw [← hCf] at hcode0 hfar0
      have hlenf := hlen f
      rw [← hCf] at hlenf
      simp only [List.length_append] at hlenf
      have hcode : CodeAt m (BitVec.ofNat 64 (A f))
          (guardC 2 105 s ++ (cq ++ (guardC s 101 s ++ cb))) := by simpa [List.append_assoc] using hcode0
      have hfar : CodeFar (BitVec.ofNat 64 (A f)) (guardC 2 105 s ++ (cq ++ (guardC s 101 s ++ cb))).length fp K := by
        simpa [List.append_assoc, Nat.add_assoc] using hfar0
      have hgl : ∀ a c, (guardC a c s).length = 5 := fun _ _ => rfl
      -- the depth guard passes
      have hne : BitVec.ofNat 64 (k + 1) ≠ 0 := by
        intro h
        have := congrArg BitVec.toNat h
        have h0' : (0 : BitVec 64).toNat = 0 := rfl
        simp only [BitVec.toNat_ofNat, h0'] at this
        omega
      have sg := guard_pass (codeAt_left hcode) (by omega) h2 hne
      -- `requires` into slot `s`
      have hf1 := codeFar_tail hfar
      have hc1 := codeAt_right hcode
      simp only [rufAt]
      generalize σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte = σR
      have hpq : Pre m _ fp K s cq ρ :=
        ⟨Nat.le_refl _, hK, hF, codeAt_left hc1, codeFar_left (by rw [← List.length_append]; exact hf1), hE⟩
      obtain ⟨m1, s1, a1, b, hb1, hbe⟩ := lowE_ok (fp := fp) (K := K) σR σR (P.requires f) s cq tq hq (by omega) m _
        ρ hpq
      have hF1 := hF.agree a1
      have hf2 := codeFar_tail hf1
      have hc2 := (codeAt_right hc1).agree a1 hf2
      simp only [Enc] at hbe
      by_cases hreq : wahr? (eval σR (P.requires f) σR ρ) = false
      · rw [if_pos hreq]
        -- `requires` fails
        have hb0 : b = 0 := by
          split at hbe
          · next ht => exact (Bool.false_ne_true (hreq.symm.trans ht)).elim
          · exact hbe
        rw [hb0] at hb1
        exact Stops.prefix (sg.trans s1) (guard_stop (codeAt_left hc2)
          (by have := codeFar_left (n := 5) (k := cb.length) (by rw [← hgl s 101, ← List.length_append]; exact hf2)
              simpa [hgl] using this) hF1 (by omega) (by omega) hK (by simp [logikCode]) hb1)
      · rw [if_neg hreq]
        have hbt : b = 1 := by
          split at hbe
          · exact hbe
          · next hn => simp only [Bool.not_eq_true] at hn; exact absurd hn hreq
        have sg2 := guard_pass (codeAt_left hc2) (by omega) hb1 (by rw [hbt]; decide)
        have hf3 := codeFar_tail hf2
        have hc3 := codeAt_right hc2
        -- the body, its calls at depth `k`
        have hu : Umf A C (BitVec.ofNat 64 k) m1 fp K :=
          ⟨pcode_agree hP a1, by
            rw [agree_rd_low a1 hroom (by omega) (by omega), h2, ofNat_succ], by omega⟩
        have hk : Kopf f m1 fp K rp cfp ρ := Kopf.agree ⟨h0, h1, hE, by omega⟩ a1 hF (Nat.le_refl _)
        have hpb : Pre m1 _ fp K (frei (D.params f)) cb ρ :=
          ⟨Nat.le_refl _, hK, hF1, hc3, hf3, envAt_agree hE a1 hF (Nat.le_refl _) (by omega)⟩
        have hret := lowEnd_ok (O := O) (passes := passes) (σ0 := σR) ih hA (lo := s) rfl hens (P.rumpf f) cb tb hb
          (by omega) (by omega) m1 _ σR ρ hpb (Nat.le_refl _) hu hk
        have spre := sg.trans (s1.trans sg2)
        have apre : Agree fp 2 K m m1 := a1.mono (by omega)
        generalize execEnd O passes (rufAt P O passes k) (P.rumpf f) σR ρ = o at hret ⊢
        cases o with
        | zurueck σ' v =>
          simp only [Ret, RetZ] at hret
          split at hret
          · next hens' =>
            simp only [hens', if_true]
            exact Stops.prefix spre hret
          · next hens' =>
            simp only [hens', if_false]
            have hfil : D.invs.filter (schuldet f) = [] := by
              simp only [List.isEmpty_iff] at hcond; exact hcond
            have hsch : ∀ i ∈ D.invs, schuldet f i = false := by
              intro i hi
              have := List.filter_eq_nil_iff.mp hfil i hi
              simpa using this
            have hno : ∀ q : D.Inv → Bool, D.invs.find? (fun i => schuldet f i && q i) = none := fun q =>
              List.find?_eq_none.mpr fun i hi => by simp [hsch i hi]
            simp only [hfil, List.foldl_nil, hno]
            obtain ⟨m', s', a', w, hw, he⟩ := hret
            exact ⟨m', spre.trans s', apre.trans a', w, hw, he⟩
        | logik e => exact Stops.prefix spre hret
        | why _ _ => exact hret.elim
        | leave _ _ _ => exact hret.elim
        | next _ _ _ => exact hret.elim
        | hardware _ => exact hret.elim
    · simp at hlf

end Gabbro.Stage0.Senke
