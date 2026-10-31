/-
  File:      stage0/Stage0/Senke/Rekursion.lean
  Subject:   Every lowered function keeps its `FunSpec` against G's call semantics `rufAt n`, by induction over
             the depth `n`.

  The code of `f` (`lowFun`): the depth guard (slot 2 zero: `exit_group(105)`, G's `abstieg`), `requires` with
  its guard (`exit_group(101)`), the body (`lowEnd_ok`, whose calls go to depth `n - 1`). The stack each call
  needs is at most `L` slots (the largest `top` of all functions), so a call at depth `n` needs `(n + 1) * L`.
-/
import Stage0.Senke.Anweisung.Satz
import Stage0.Senke.Anweisung.Faelle.Schleifen.Relocate

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

theorem lowFun_spec {P : Programm D} {O : Orakel D} [TorOK Y O] [SichtOK O] {passes : Nat} {A : D.Fn → Nat} {C : D.Fn → List II} {L : Nat}
    (hLA : Y.fa = A) (hC : ∀ g, ∃ top, lowFun passes P A Y g = some (C g, top) ∧ top ≤ L) (hA : ∀ g, A g < 2 ^ 31)
    (hlen : ∀ g, 16 * (C g).length < 2 ^ 31) :
    ∀ n, n < 2 ^ 64 → FunSpec Y A C (rufAt P O passes n) (BitVec.ofNat 64 n) ((n + 1) * L) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨hLA, ?_⟩
    intro f m fp K Ks rp cfp σ ρ hc hW hK hF hP h0 h1 h2 hE hWa _
    have hks := hW.ks
    obtain ⟨top, hlf, htop⟩ := hC f
    simp only [lowFun] at hlf
    split at hlf
    · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at hlf
      obtain ⟨⟨cq, tq⟩, hq, ⟨cens, tens⟩, hens, ⟨cb, tb⟩, hb, cs, hcs, hCf, htf⟩ := hlf
      have hFB3 : FB = 4 := rfl
      have hcode := (hP f).1
      have hfar := (hP f).2
      rw [← hCf] at hcode hfar
      simp only [rufAt]
      refine guard_stop (codeAt_left (codeAt_left (codeAt_left (codeAt_left hcode)))) ?_ hF (by omega) (by omega) hK
        (by simp [logikCode]) h2
      have := codeFar_left (n := (guardC 2 105 (FB + (D.params f).length)).length)
        (k := cq.length + (guardC (FB + (D.params f).length) 101 (FB + (D.params f).length)).length + cs.length + ((D.params f).length + cb.length))
        (by simpa [Nat.add_assoc, relocateC_length] using hfar)
      simpa [guardC, stopC, sysC] using this
    · simp at hlf
  | succ k ih =>
    intro hn
    refine ⟨hLA, ?_⟩
    intro f m fp K Ks rp cfp σ ρ hc hW hK hF hP h0 h1 h2 hE hWa hy
    have hks := hW.ks
    have ih := ih (by omega)
    obtain ⟨top, hlf, htop⟩ := hC f
    simp only [lowFun] at hlf
    split at hlf
    · next hcond =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at hlf
      obtain ⟨⟨cq, tq⟩, hq, ⟨cens, tens⟩, hens, ⟨cb, tb⟩, hb, cs, hcs, hCf, htf⟩ := hlf
      have hFB3 : FB = 4 := rfl
      have hmul : (k + 1 + 1) * L = (k + 1) * L + L := Nat.succ_mul _ _
      have hroom := hF.room
      let s := FB + (D.params f).length
      have hcode0 := (hP f).1
      have hfar0 := (hP f).2
      rw [← hCf] at hcode0 hfar0
      have hlenf := hlen f
      rw [← hCf] at hlenf
      simp only [List.length_append, relocateC_length] at hlenf
      have hcode : CodeAt m (BitVec.ofNat 64 (A f))
          (guardC 2 105 s ++ (cq ++ (guardC s 101 s ++ (cs ++ (relocateC FB ((D.params f).length + 2) (D.params f).length ++ cb))))) := by simpa [List.append_assoc] using hcode0
      have hfar : CodeFar (BitVec.ofNat 64 (A f)) (guardC 2 105 s ++ (cq ++ (guardC s 101 s ++ (cs ++ (relocateC FB ((D.params f).length + 2) (D.params f).length ++ cb))))).length fp K := by
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
      have hpq : PreS Y m _ fp K s cq ρ :=
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
          (by have := codeFar_left (n := 5) (k := cs.length + ((D.params f).length + cb.length)) (by simpa only [List.length_append, relocateC_length, hgl] using hf2)
              simpa [hgl] using this) hF1 (by omega) (by omega) hK (by simp [logikCode]) hb1)
      · rw [if_neg hreq]
        have hbt : b = 1 := by
          split at hbe
          · exact hbe
          · next hn => simp only [Bool.not_eq_true] at hn; exact absurd hn hreq
        have sg2 := guard_pass (codeAt_left hc2) (by omega) hb1 (by rw [hbt]; decide)
        have hf3 := codeFar_tail hf2
        have hc3 := codeAt_right hc2
        -- Capture entry cells after requires, before the first body step.
        obtain ⟨mS, sS, aS, hSnap, hKeep⟩ := snapC_ok hcs hF1 hK (by omega)
          (codeAt_left hc3) (codeFar_left (by rw [← List.length_append]; exact hf3)) hWa1 hW.lay
          (by have := hW.top; omega)
        have hFS := hF1.agree aS
        have aPre : Agree fp 3 K m mS := (a1.mono (by unfold s FB; omega)).trans aS
        have hES : EnvAt Y mS fp ρ := by
          intro τ x
          obtain ⟨w, hw, he⟩ := (envAt_agree hE a1 hF (Nat.le_refl _) (by omega)) τ x
          have hx := vslot_lt (reserved := 0) x
          exact ⟨w, by rw [hKeep (vslot x) (by unfold frei at hx; omega)
            (by unfold vslot FB; omega)]; exact hw, he⟩
        have hWaS : WeltAt mS Y σR := weltAt_stab hW.lay (by have := hW.top; omega)
          m1 mS hWa1 (aS.mono (Nat.zero_le _))
        have hfB := codeFar_tail hf3
        have hcB := (codeAt_right hc3).agree aS hfB
        obtain ⟨mR, sR, aR, hER⟩ := relocate_env hFS hK
          (by simpa only [Nat.zero_add] using (show frei (D.params f) ((D.params f).length + 2) ≤ K by omega)) hES (codeAt_left hcB)
          (by simpa only [relocateC_length] using (codeFar_left (n := (relocateC FB ((D.params f).length + 2) (D.params f).length).length) (k := cb.length) (by simpa only [List.length_append] using hfB)))
        have aRW := Gabbro.Stage0.Senke.Agree.widen aR (show frei (D.params f) (0 + ((D.params f).length + 2)) ≤ K by simpa only [Nat.zero_add] using (show frei (D.params f) ((D.params f).length + 2) ≤ K by omega))
        have hFR := hFS.agree aRW
        have aEntry : Agree fp 3 K m mR := aPre.trans (aRW.mono (by unfold FB; omega))
        have hOriginal : EnvAt Y mR fp ρ := envAt_agree hES aRW hFS (by unfold frei FB; omega) (by omega)
        have hSnapR := hSnap.agree hFS aRW (by unfold FB; omega) (by omega)
        have hWaR' : WeltAt mR Y σR := weltAt_stab hW.lay (by have := hW.top; omega)
          mS mR hWaS (aRW.mono (Nat.zero_le _))
        have hfR := codeFar_tail hfB
        have hcR := (codeAt_right hcB).agree aRW hfR
        simp only [relocateC_length] at hcR hfR
        -- The body, its calls at depth `k`.
        have hu : Umf Y A C (BitVec.ofNat 64 k) mR fp Ks K :=
          ⟨pcode_agree hP aEntry, by
            rw [agree_rd_low aEntry hroom (by decide) (by omega), h2, ofNat_succ], by omega,
            hy.agree aEntry (by have := hW.top; have := hW.ord; omega), by have := hW.top; have := hW.ord; omega⟩
        have hk : Kopf Y f mR fp K rp cfp ρ P σR :=
          ⟨by rw [agree_rd_low aEntry hroom (by decide) (by omega)]; exact h0,
           by rw [agree_rd_low aEntry hroom (by decide) (by omega)]; exact h1,
           hOriginal, by omega, hSnapR⟩
        have hpb : PreS Y mR _ fp K (frei (D.params f) ((D.params f).length + 2)) cb ρ ((D.params f).length + 2) :=
          ⟨Nat.le_refl _, hK, hFR, hcR, hfR, by simpa only [Nat.zero_add] using hER, trivial, wstab_true _ _⟩
        have hret := lowEnd_ok (O := O) (passes := passes) (σ0 := σR) ih hA (lo := s) rfl hens (pr := []) (P.rumpf f) cb tb hb
          (by omega) (by omega) hW mR _ σR ρ hpb (by unfold frei s; omega) hu hk hWaR' (fun _ h => nomatch h)
        have spre := sg.trans (s1.trans (sg2.trans (sS.trans sR)))
        have apre : Agree fp 2 K m mR := aEntry.mono (by decide)
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
            exact ⟨m', spre.trans s', (agreeW_of apre).trans a', hw, hw'⟩
        | logik e => exact Stops.prefix spre hret
        | why σ' r => exact RetWhy.prefix spre (agreeW_of apre) hret
        | leave h _ _ => exact absurd h Bool.false_ne_true
        | next h _ _ => exact absurd h Bool.false_ne_true
        | hardware e => exact Stops.prefix spre hret
    · simp at hlf

end Gabbro.Stage0.Senke
