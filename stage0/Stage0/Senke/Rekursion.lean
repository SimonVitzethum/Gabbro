/- Every emitted function keeps the complete-value call protocol, by source call-depth induction. -/
module
public import Stage0.Senke.Anweisung.Satz
public import Stage0.Senke.Rueckkehr.Entry
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration}
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

theorem ofNat_succ (k : Nat) : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + 1 := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h1]
  omega

theorem lowFun_spec {P : Programm D} {O : Orakel D} [TorOK Y O] [SichtOK O]
    {passes : Nat} {A : D.Fn → Nat} {C : D.Fn → List II} {L : Nat}
    (hLA : Y.fa = A)
    (hC : ∀ g, ∃ top, lowFun passes P A Y g = some (C g, top) ∧ top ≤ L)
    (hA : ∀ g, A g < 2 ^ 31) (hlen : ∀ g, 16 * (C g).length < 2 ^ 31) :
    ∀ n, n < 2 ^ 64 → FunSpec Y A C (rufAt P O passes n) (BitVec.ofNat 64 n) ((n + 1) * L) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨hLA, ?_⟩
    intro f m fp K Ks rp cfp σ ρ hc hW hK hF hP h0 h1 h2 hE hWa _
    obtain ⟨top, lower, bound⟩ := hC f
    simp only [lowFun] at lower
    split at lower
    · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at lower
      obtain ⟨⟨cq, tq⟩, hq, ⟨cens, tens⟩, hens, ⟨cb, tb⟩, hb, snap, hsnap, codes, tops⟩ := lower
      let layout := functionFrame P f
      change max (retTop layout)
        (max tq (max (frei (D.params f) layout.bodyReserved) tb)) = top at tops
      let entry := relocateC FB layout.ensReserved layout.parameterWords ++
        (snap ++ relocateC layout.ensParams (layout.bodyReserved - layout.ensReserved) layout.parameterWords)
      have loaded : CodeAt m (BitVec.ofNat 64 (A f))
          (guardC 2 105 layout.canonicalResult ++ (cq ++
            (guardC layout.canonicalResult 101 layout.canonicalResult ++ (entry ++ cb)))) := by
        have := (hP f).1
        rw [← codes] at this
        simpa only [entry, layout, List.append_assoc] using this
      have far : CodeFar (BitVec.ofNat 64 (A f))
          (guardC 2 105 layout.canonicalResult ++ (cq ++
            (guardC layout.canonicalResult 101 layout.canonicalResult ++ (entry ++ cb)))).length fp K := by
        have := (hP f).2
        rw [← codes] at this
        simpa only [entry, layout, List.append_assoc] using this
      have sizes : retTop layout ≤ L := by
        have := tops
        have := bound
        omega
      have guardFits : layout.canonicalResult + 8 ≤ K := by
        have := layout.internal_offsets
        have status : layout.internalStatus = layout.internalResult + layout.returnSpan := rfl
        have := hW.ks
        simp only [retTop] at sizes
        simp only [Nat.zero_add, Nat.one_mul] at hc
        omega
      simp only [rufAt]
      apply guard_stop (codeAt_left loaded)
        (codeFar_left
          (n := (guardC 2 105 layout.canonicalResult).length)
          (k := (cq ++ (guardC layout.canonicalResult 101 layout.canonicalResult ++ (entry ++ cb))).length)
          (by simpa only [List.length_append] using far)) hF
        (by omega) guardFits hK (by simp [logikCode]) h2
    · simp at lower
  | succ k ih =>
    intro hn
    refine ⟨hLA, ?_⟩
    intro f m fp K Ks rp cfp σ ρ hc hW hK hF hP h0 h1 h2 hE hWa hy
    have hks := hW.ks
    have smaller := ih (by omega)
    obtain ⟨top, lower, bound⟩ := hC f
    simp only [lowFun] at lower
    split at lower
    · next invariantGate =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at lower
      obtain ⟨⟨cq, tq⟩, hq, ⟨cens, tens⟩, hens, ⟨cb, tb⟩, hb, snap, hsnap, codes, tops⟩ := lower
      let layout := functionFrame P f
      change max (retTop layout)
        (max tq (max (frei (D.params f) layout.bodyReserved) tb)) = top at tops
      let q := layout.canonicalResult
      let entry := relocateC FB layout.ensReserved layout.parameterWords ++
        (snap ++ relocateC layout.ensParams (layout.bodyReserved - layout.ensReserved) layout.parameterWords)
      have ownBound : max (retTop layout)
          (max tq (max (frei (D.params f) layout.bodyReserved) tb)) ≤ L := by
        have := tops
        omega
      have capacity : (k + 1) * L + L ≤ Ks := by simpa only [Nat.succ_mul] using hc
      have offsets := layout.internal_offsets
      have status : layout.internalStatus = layout.internalResult + layout.returnSpan := rfl
      have guardFits : q + 8 ≤ Ks := by simp only [retTop] at ownBound; omega
      have loaded : CodeAt m (BitVec.ofNat 64 (A f))
          (guardC 2 105 q ++ (cq ++ (guardC q 101 q ++ (entry ++ cb)))) := by
        have := (hP f).1
        rw [← codes] at this
        simpa only [entry, layout, q, List.append_assoc] using this
      have far : CodeFar (BitVec.ofNat 64 (A f))
          (guardC 2 105 q ++ (cq ++ (guardC q 101 q ++ (entry ++ cb)))).length fp K := by
        have := (hP f).2
        rw [← codes] at this
        simpa only [entry, layout, q, List.append_assoc] using this
      have lengthBound : 16 * (entry ++ cb).length < 2 ^ 31 := by
        have := hlen f
        rw [← codes] at this
        simp only [entry, layout, q, List.length_append] at this ⊢
        omega
      have nonzero : BitVec.ofNat 64 (k + 1) ≠ 0 := by
        intro equal
        have := congrArg BitVec.toNat equal
        have zero : (0 : BitVec 64).toNat = 0 := rfl
        simp only [BitVec.toNat_ofNat, zero] at this
        omega
      have depthRun := guard_pass (codeAt_left loaded) (by omega) h2 nonzero
      have far1 := codeFar_tail far
      have code1 := codeAt_right loaded
      simp only [rufAt]
      have requiresWorld : WeltAt m Y
          (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) := hWa
      generalize σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte = σR at requiresWorld ⊢
      have reqPre : PreS Y m _ fp K q cq ρ :=
        ⟨Nat.le_refl _, hK, hF, codeAt_left code1,
          codeFar_left (n := cq.length)
            (k := (guardC q 101 q ++ (entry ++ cb)).length)
            (by simpa only [List.length_append] using far1), hE, trivial, wstab_true _ _⟩
      have reqWorldPre := PreS.welt reqPre hks requiresWorld hW.lay hW.lo
      obtain ⟨m1, reqRun, reqChanged, b, reqRead, reqValue⟩ :=
        lowE_ok (fp := fp) (K := Ks) σR σR (fun _ h => h) hW.lay (P.requires f)
          q cq tq hq (by omega) m _ ρ reqWorldPre |>.word trivial
      have first := Agree.widen reqChanged hks
      have frame1 := hF.agree first
      have world1 := reqWorldPre.wstab m m1 requiresWorld (reqChanged.mono (Nat.zero_le _))
      have far2 := codeFar_tail far1
      have code2 := (codeAt_right code1).agree first far2
      simp only [Enc] at reqValue
      by_cases failure : wahr? (eval σR (P.requires f) σR ρ) = false
      · rw [if_pos failure]
        have zero : b = 0 := by
          split at reqValue
          · next h => exact (Bool.false_ne_true (failure.symm.trans h)).elim
          · exact reqValue
        have stopped := guard_stop (codeAt_left code2)
          (codeFar_left (n := (guardC q 101 q).length) (k := (entry ++ cb).length)
            (by simpa only [List.length_append] using far2))
          frame1 (by omega) (by omega) hK (by simp [logikCode])
          (by simpa only [zero] using reqRead)
        exact Stops.prefix (depthRun.trans reqRun) stopped
      · rw [if_neg failure]
        have one : b = 1 := by
          split at reqValue
          · exact reqValue
          · next h => simp only [Bool.not_eq_true] at h; exact absurd h failure
        have requiresRun := guard_pass (codeAt_left code2) (by omega) reqRead (by rw [one]; decide)
        have far3 := codeFar_tail far2
        have code3 := codeAt_right code2
        have params1 := envAt_agree hE first hF (Nat.le_refl _) (by omega)
        have entryFits : frei (D.params f) layout.bodyReserved ≤ K := by omega
        have internalFits : layout.internalResult ≤ K := by
          have body := layout.protected_prefix
          have bodyBound : layout.bodyParams + layout.parameterWords ≤ K := entryFits
          have statusBound : layout.internalResult ≤ layout.internalStatus := by
            simp only [FrameLayout.internalStatus]; omega
          omega
        have bodyFrontier : layout.internalResult ≤ frei (D.params f) layout.bodyReserved := by
          have body := layout.protected_prefix
          have bodySpace : layout.bodyParams ≤ frei (D.params f) layout.bodyReserved := by
            change layout.bodyParams ≤ layout.bodyParams + layout.parameterWords
            omega
          have statusBound : layout.internalResult ≤ layout.internalStatus := by
            simp only [FrameLayout.internalStatus]; omega
          omega
        obtain ⟨mR, entryRun, entryChanged, original, lexical, saved, worldR⟩ :=
          entryFrame_run P f hsnap frame1 hK entryFits
            (codeAt_left code3) (codeFar_left (n := entry.length) (k := cb.length)
              (by simpa only [List.length_append] using far3))
            params1 world1 hW.lay hW.top
        have low : FB ≤ q := by simp only [q, FrameLayout.canonicalResult]; omega
        have allChanged : Agree fp FB K m mR := (first.mono low).trans entryChanged
        have frameR := hF.agree allChanged
        have farR := codeFar_tail (a := entry) far3
        have codeR := (codeAt_right code3).agree entryChanged farR
        have entryLength : entry.length = 2 * contextWords (D.params f) + snap.length := by
          simp only [entry, List.length_append, relocateC_length, FrameLayout.parameterWords, layout, functionFrame]
          omega
        rw [entryLength] at codeR farR
        have surroundings : Umf Y A C (BitVec.ofNat 64 k) mR fp Ks K :=
          ⟨pcode_agree hP allChanged, by
            rw [agree_rd_low allChanged hF.room (by decide) (by omega), h2, ofNat_succ], by omega,
            hy.agree allChanged (by have := hW.top; have := hW.ord; omega),
            by have := hW.top; have := hW.ord; omega⟩
        have header : Kopf Y f mR fp K rp cfp ρ P σR := by
          refine ⟨?_, ?_, original, internalFits, saved⟩
          · rw [agree_rd_low allChanged hF.room (by decide) (by omega)]; exact h0
          · rw [agree_rd_low allChanged hF.room (by decide) (by omega)]; exact h1
        have bodyPre : PreS Y mR _ fp K (frei (D.params f) layout.bodyReserved)
            cb ρ layout.bodyReserved :=
          ⟨Nat.le_refl _, hK, frameR, codeR, farR, lexical, trivial, wstab_true _ _⟩
        have result := lowEnd_ok (O := O) (passes := passes) (σ0 := σR) smaller hA
          (lo := layout.internalResult) rfl hens (pr := []) (P.rumpf f) cb tb hb
          (by omega) (by simp only [List.length_append] at lengthBound; omega) hW
          mR _ σR ρ bodyPre
          bodyFrontier
          surroundings header worldR (fun _ h => nomatch h)
        have entryPrefix := depthRun.trans (reqRun.trans (requiresRun.trans entryRun))
        generalize execEnd O passes (rufAt P O passes k) (P.rumpf f) σR ρ = outcome at result ⊢
        cases outcome with
        | zurueck σ' v =>
          simp only [Ret, RetZ] at result
          split at result
          · next h => simp only [h, if_true]; exact Stops.prefix entryPrefix result
          · next h =>
            simp only [h, if_false]
            have empty : D.invs.filter (schuldet f) = [] := by
              simpa only [List.isEmpty_iff] using invariantGate
            have unowed : ∀ i ∈ D.invs, schuldet f i = false := by
              intro i hi
              have := List.filter_eq_nil_iff.mp empty i hi
              simpa using this
            have absent : ∀ test : D.Inv → Bool,
                D.invs.find? (fun i => schuldet f i && test i) = none :=
              fun test => List.find?_eq_none.mpr fun i hi => by simp [unowed i hi]
            simp only [empty, List.foldl_nil, absent]
            obtain ⟨m', steps, changed, value, world⟩ := result
            exact ⟨m', entryPrefix.trans steps,
              (agreeW_of (allChanged.mono (by decide))).trans changed, value, world⟩
        | logik error => exact Stops.prefix entryPrefix result
        | why σ' reason =>
          exact RetWhy.prefix entryPrefix (agreeW_of (allChanged.mono (by decide))) result
        | leave h _ _ => exact absurd h Bool.false_ne_true
        | next h _ _ => exact absurd h Bool.false_ne_true
        | hardware error => exact Stops.prefix entryPrefix result
    · simp at lower

end Gabbro.Stage0.Senke
