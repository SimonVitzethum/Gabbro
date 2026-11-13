/-
  File:      stage0/Stage0/Senke/Bild/Prolog.lean
  Subject:   A function's prologue up to its first body boundary (image theorem, piece T2). `lowFun` lays out the
             depth guard, the code of `requires`, the requires guard, the entry frame (original parameters, entry
             snapshots, lexical parameters) and then the body. `lowFun_spec` runs all of it to the return.
             `prolog_rand` stops in front of the body: from the entry of `f` with every premise `FunSpec.run` asks
             at depth `k + 1`, and with `requires` true at the entry world (`ReqAmEintritt`), the image reaches the
             start of the body's code, where `BodyFrame.RandIR` holds for the body `P.rumpf f` with the values
             `lowFun` uses (`pr = []`, `ex = (0, 0)`, `sc = []`, `reserved = bodyReserved`) in the frame
             `rumpfRahmen`, which also satisfies `BodyFrame.Ok`. The proof is the successor case of `lowFun_spec`
             up to its call of `lowEnd_ok`, unchanged.
-/
module
public import Stage0.Senke.Rekursion
public import Stage0.Senke.Bild.Rand
public import Grammatik.Logik.Ruf.RufLogik
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Stage0.Senke Runner.IR Runner.Mem

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {D : Deklaration}

/-- **The frame of the body of `f`** as `lowFun` lowers it and `lowFun_spec` runs it at depth `k + 1`: callees run as
    `rufAt k` with depth word `k` and call capacity `(k + 1) * Lm`; the protected prefix ends at `internalResult`; the
    ensures code `ens`; no protected slot, loop target or pending release; the body's reserved slots. -/
abbrev rumpfRahmen (Y : Lay D) (O : Orakel D) (passes : Nat) (P : Programm D) (A : D.Fn → Nat) (C : D.Fn → List II)
    (Lm k : Nat) (f : D.Fn) (fp : Runner.W) (K Ks : Nat) (rp cfp : Runner.W) (σ0 : World D)
    (ρ0 : Env D (D.params f)) (H : List D.Lock) (ens : List II × Nat) : BodyFrame D :=
  { L := Y, O := O, passes := passes, R := rufAt P O passes k, A := A, C := C, dv := BitVec.ofNat 64 k,
    cap := (k + 1) * Lm, P := P, f := f, fp := fp, K := K, Ks := Ks, lo := (functionFrame P f).internalResult,
    rp := rp, cfp := cfp, σ0 := σ0, ρ0 := ρ0, cens := ens.1, tens := ens.2, pr := [], ex := (0, 0), H := H,
    sc := [], reserved := (functionFrame P f).bodyReserved }

variable [Kern]

/-- **The prologue, to the first body boundary**: from the entry of `f` at depth `k + 1` (the premises of
    `FunSpec.run` with depth word `k + 1`), when `requires` holds at the entry world, the image runs the depth guard,
    the requires code and guard and the entry frame, and stands at the start of the body's code with `RandIR` of the
    whole body, at the entry world `σ` and the entry environment `ρ`, in a frame that satisfies `BodyFrame.Ok`. -/
theorem prolog_rand {Y : Lay D} {P : Programm D} {O : Orakel D} [TorOK Y O] [SichtOK O]
    {passes : Nat} {A : D.Fn → Nat} {C : D.Fn → List II} {Lm : Nat}
    (hLA : Y.fa = A)
    (hC : ∀ g, ∃ top, lowFun passes P A Y g = some (C g, top) ∧ top ≤ Lm)
    (hA : ∀ g, A g < 2 ^ 31) (hlen : ∀ g, 16 * (C g).length < 2 ^ 31) {k : Nat} (hk : k + 1 < 2 ^ 64)
    {f : D.Fn} {m : Runner.Mem} {fp : Runner.W} {K Ks : Nat} {rp cfp : Runner.W} {σ : World D}
    {ρ : Env D (D.params f)} {H : List D.Lock}
    (hc : (k + 1 + 1) * Lm ≤ Ks) (hW : WIn Y fp Ks K) (hK : K < 2 ^ 31) (hF : FrameOK m fp K)
    (hP : PCode m A C fp K) (h0 : m.rd64 (slot fp (BitVec.ofNat 64 0)) = some rp)
    (h1 : m.rd64 (slot fp (BitVec.ofNat 64 1)) = some cfp)
    (h2 : m.rd64 (slot fp (BitVec.ofNat 64 2)) = some (BitVec.ofNat 64 (k + 1)))
    (hE : EnvAt Y m fp ρ) (hWa : WeltAt m Y σ) (hy : TicketSync m Y fp Ks H)
    (hH : HeldIn H (Signatur.anfang D (D.signatur f)) (D.signatur f).boden)
    (hreq : ReqAmEintritt P f σ ρ) :
    ∃ (ens : List II × Nat) (pc : Runner.W) (mR : Runner.Mem),
      Star ⟨BitVec.ofNat 64 (A f), fp⟩ m ⟨pc, fp⟩ mR ∧
      (rumpfRahmen Y O passes P A C Lm k f fp K Ks rp cfp
        (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ H ens).Ok ∧
      (rumpfRahmen Y O passes P A C Lm k f fp K Ks rp cfp
        (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ H ens).RandIR
        (P.rumpf f) pc mR σ ρ := by
  have hks := hW.ks
  have smaller := lowFun_spec (P := P) (O := O) (passes := passes) hLA hC hA hlen k (by omega)
  obtain ⟨top, lower, bound⟩ := hC f
  simp only [lowFun] at lower
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at lower
  obtain ⟨⟨cq, tq⟩, hq, ⟨cens, tens⟩, hens, ⟨cb, tb⟩, hb, snap, hsnap, codes, tops⟩ := lower
  let layout := functionFrame P f
  change max (retTop layout)
    (max tq (max (frei (D.params f) layout.bodyReserved) tb)) = top at tops
  let q := layout.canonicalResult
  let entry := relocateC FB layout.ensReserved layout.parameterWords ++
    (snap ++ relocateC layout.ensParams (layout.bodyReserved - layout.ensReserved) layout.parameterWords)
  have ownBound : max (retTop layout)
      (max tq (max (frei (D.params f) layout.bodyReserved) tb)) ≤ Lm := by
    have := tops
    omega
  have capacity : (k + 1) * Lm + Lm ≤ Ks := by simpa only [Nat.succ_mul] using hc
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
  have requiresWorld : WeltAt m Y
      (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) := hWa
  have pass : wahr? (eval (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) (P.requires f)
      (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ) = true := by
    rw [req_lese]
    exact hreq
  generalize hσR : σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte = σR at requiresWorld pass ⊢
  have reqPre : PreS Y m _ fp K q cq ρ :=
    ⟨Nat.le_refl _, hK, hF, codeAt_left code1,
      codeFar_left (n := cq.length)
        (k := (guardC q 101 q ++ (entry ++ cb)).length)
        (by simpa only [List.length_append] using far1), hE, trivial, wstab_true _ _⟩
  have reqWorldPre := PreS.welt reqPre hks requiresWorld hW.lay hW.lo
  obtain ⟨m1, reqRun, reqChanged, b, reqRead, reqValue⟩ :=
    lowE_ok (same := by intro _; rfl) (fp := fp) (K := Ks) σR σR (fun _ h => h) hW.lay (P.requires f)
      q cq tq hq (by omega) m _ ρ reqWorldPre |>.word trivial
  have first := Agree.widen reqChanged hks
  have frame1 := hF.agree first
  have world1 := reqWorldPre.wstab m m1 requiresWorld (reqChanged.mono (Nat.zero_le _))
  have far2 := codeFar_tail far1
  have code2 := (codeAt_right code1).agree first far2
  simp only [Enc] at reqValue
  have one : b = 1 := by
    split at reqValue
    · exact reqValue
    · next h => exact absurd pass h
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
  have surroundings : Umf Y A C (BitVec.ofNat 64 k) mR fp Ks K H :=
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
  have entryPrefix := depthRun.trans (reqRun.trans (requiresRun.trans entryRun))
  -- the world the body starts in: the entry read only extends the trace (`WeltAt` reads slots and globals)
  have worldσ : WeltAt mR Y σ := by
    rw [← hσR] at worldR
    exact worldR
  have room : tb + (k + 1) * Lm ≤ Ks := by omega
  refine ⟨(cens, tens), _, mR, entryPrefix, ⟨smaller, hA, rfl, hens, (fun _ h => nomatch h), hW⟩,
    cb, tb, hb, room, by simp only [List.length_append] at lengthBound; omega, bodyPre, bodyFrontier,
    surroundings, header, worldσ, (fun _ h => nomatch h), hH⟩

end Gabbro.Stage0.Senke.BildLauf
