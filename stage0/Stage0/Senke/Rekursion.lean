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

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

theorem ofNat_succ (k : Nat) : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + 1 := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h1]
  omega

theorem lowFun_spec {P : Programm D} {O : Orakel D} [TorOK Y O] {passes : Nat} {A : D.Fn → Nat} {C : D.Fn → List II} {L : Nat}
    (hC : ∀ g, ∃ top, lowFun P A Y g = some (C g, top) ∧ top ≤ L) (hA : ∀ g, A g < 2 ^ 31)
    (hlen : ∀ g, 16 * (C g).length < 2 ^ 31) :
    ∀ n, n < 2 ^ 64 → FunSpec Y A C (rufAt P O passes n) (BitVec.ofNat 64 n) ((n + 1) * L) := by
  intro n
  induction n with
  | zero =>
    intro _ f m fp K Ks rp cfp σ ρ hc hW hK hF hP h0 h1 h2 hE hWa
    have hks := hW.ks
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
    intro hn f m fp K Ks rp cfp σ ρ hc hW hK hF hP h0 h1 h2 hE hWa
    have hks := hW.ks
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
      have hWaR : WeltAt m Y (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) := hWa
      generalize σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte = σR at hWaR ⊢
      have hpq : PreS m _ fp K s cq ρ :=
        ⟨Nat.le_refl _, hK, hF, codeAt_left hc1, codeFar_left (by rw [← List.length_append]; exact hf1), hE, trivial, wstab_true _ _⟩
      have hpw := PreS.welt hpq hks hWaR hW.lay (by have := hW.lo; omega)
      obtain ⟨m1, s1, a1s, b, hb1, hbe⟩ := lowE_ok (fp := fp) (K := Ks) σR σR (fun _ h => h) (P.requires f) s cq tq hq (by omega) m _
        ρ hpw
      have a1 := Agree.widen a1s hks
      have hWa1 : WeltAt m1 Y σR := hpw.wstab m m1 hWaR (a1s.mono (Nat.zero_le _))
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
        have hpb : PreS m1 _ fp K (frei (D.params f)) cb ρ :=
          ⟨Nat.le_refl _, hK, hF1, hc3, hf3, envAt_agree hE a1 hF (Nat.le_refl _) (by omega), trivial, wstab_true _ _⟩
        have hret := lowEnd_ok (O := O) (passes := passes) (σ0 := σR) ih hA (lo := s) rfl hens (pr := []) (P.rumpf f) cb tb hb
          (by omega) (by omega) hW m1 _ σR ρ hpb (Nat.le_refl _) hu hk hWa1 (fun _ h => nomatch h)
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
            obtain ⟨m', s', a', hw, hw'⟩ := hret
            exact ⟨m', spre.trans s', apre.trans a', hw, hw'⟩
        | logik e => exact Stops.prefix spre hret
        | why _ _ => exact hret.elim
        | leave h _ _ => exact absurd h Bool.false_ne_true
        | next h _ _ => exact absurd h Bool.false_ne_true
        | hardware e => exact Stops.prefix spre hret
    · simp at hlf

end Gabbro.Stage0.Senke
