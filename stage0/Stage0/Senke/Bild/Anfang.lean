/-
  File:      stage0/Stage0/Senke/Bild/Anfang.lean
  Subject:   The image's start, up to the first body boundary of `main` (image theorem, piece T2, one thread). For an
             image without roots (`BildLage … main [] …`, so no spawn), `main`'s thread runs the start code: the depth
             `n + 1` into its slot 2, then the call tail into `main`'s frame at slot `FB` (`call_eintritt`), then
             `main`'s prologue (`prolog_rand`, at depth `n = (n - 1) + 1`). `bild_anfang`: there is a run from the
             loader's first instruction to the start of the body's code, where `RandIR` of the whole body holds in a
             frame satisfying `BodyFrame.Ok`, with the loaded world and `main`'s environment. The steps are those of
             `bild_kern` and `start_ok`, stopped at the call.
-/
module
public import Stage0.Senke.Images.StartupExecution
public import Stage0.Senke.Bild.Prolog
public import Stage0.Senke.Bild.Eintritt
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Stage0.Senke Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern] {D : Deklaration}

/-- **The start of `main`'s thread, to the first body boundary**: from the loader's first instruction the image runs
    the start code and `main`'s prologue and stands at the start of the code of `main`'s body, with `RandIR` of the
    whole body at the loaded world `σ` and `main`'s environment `ρ`, in the frame `rumpfRahmen` of `main` at depth
    `n` (callees at `n - 1`), which satisfies `BodyFrame.Ok`. -/
theorem bild_anfang {P : Programm D} {O : Orakel D} {Yb : Lay D} [TorOK Yb O] [SichtOK O] {passes : Nat}
    {fs : List D.Fn} {pos : D.Fn → Nat} {main : D.Fn} {K Ks : Nat} {A : D.Fn → Nat}
    {cs : List (List II × Nat)} {body : List II} {n fp0 : Nat} {sp : List (Nat × Nat)}
    {ρ : Env D (D.params main)} {rootArgs : List (List Runner.W)} {tail : List Runner.B}
    (h : BildLage passes P fs pos main [] K Ks Yb A cs body n fp0 sp ρ rootArgs) {m : Runner.Mem}
    (hm : BytesAt m codeBase ((spawnC (startScratch main) sp ++ startC A main n 231 true ++ rootsC A n [] ++
      body).flatMap encII ++ ((startStackBytes Ks (FB + FB) (encodeEnv Yb ρ :: rootArgs)).getD [] ++ tail)))
    (hval : ∀ τ (x : Var (D.params main) τ), ValueValid Yb τ (ρ.get x))
    {σ : World D} (hWa : WeltAt m Yb σ) (hy : TicketSync m Yb (BitVec.ofNat 64 fp0) Ks [])
    (hreq : ReqAmEintritt P main σ ρ) :
    ∃ (ens : List II × Nat) (rp pc : Runner.W) (mR : Runner.Mem),
      Star ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 fp0⟩ m
        ⟨pc, slot (BitVec.ofNat 64 fp0) (BitVec.ofNat 64 FB)⟩ mR ∧
      (rumpfRahmen Yb O passes P A (fun g => ((cs[pos g]?).map (·.1)).getD []) (maxTop cs) (n - 1) main
        (slot (BitVec.ofNat 64 fp0) (BitVec.ofNat 64 FB)) (Ks - FB) (Ks - FB) rp (BitVec.ofNat 64 fp0)
        (σ.lese (Signatur.anfang D (D.signatur main)) (P.requires main).orte) ρ [] ens).Ok ∧
      (rumpfRahmen Yb O passes P A (fun g => ((cs[pos g]?).map (·.1)).getD []) (maxTop cs) (n - 1) main
        (slot (BitVec.ofNat 64 fp0) (BitVec.ofNat 64 FB)) (Ks - FB) (Ks - FB) rp (BitVec.ofNat 64 fp0)
        (σ.lese (Signatur.anfang D (D.signatur main)) (P.requires main).orte) ρ [] ens).RandIR
        (P.rumpf main) pc mR σ ρ := by
  obtain ⟨c1, c2, c3, ⟨stackBytes, madeStacks, loadedStacks⟩, _⟩ := h.code hm
  obtain ⟨frame, made, hframe⟩ := startStackBytes_frame madeStacks fp0 loadedStacks 0 (by simp)
  simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero] at made hframe
  have hfit := h.hfit
  have hroom := h.hroom
  have hex := h.hex main (by simp)
  have hylo := h.hylo
  have hyhi := h.hyhi
  have hyord := h.hyord
  simp only [List.length_nil, Nat.zero_add, Nat.mul_one] at hylo
  have hK : Ks ≤ K := by omega
  have hge := startScratch_ge main
  have hF0 : FrameOK m (BitVec.ofNat 64 fp0) Ks := startFrameBytes_frame made hframe (by omega)
  have hρ : WordsAt m (slot (BitVec.ofNat 64 fp0) (BitVec.ofNat 64 FB)) FB (encodeEnv Yb ρ) :=
    startEnvBytes_words (reserved := 0) Yb ρ made hframe
  have hW0 : WIn Yb (BitVec.ofNat 64 fp0) Ks Ks := by simpa using h.win (j := 0) (Nat.zero_le _)
  have hfp := h.hfp
  have hFB3 : FB = 4 := rfl
  simp only [headLen, startLen, List.length_nil, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at hfp
  -- no root: no spawn
  have hsp0 : sp = [] := by simpa using h.hsp
  subst hsp0
  have hcM : CodeAt m (BitVec.ofNat 64 codeBase) (startC A main n 231 true) := by
    have := codeAt_left (a := spawnC (startScratch main) [] ++ startC A main n 231 true) c3
    simpa only [spawnC, List.nil_append] using this
  have hAm : A main < 2 ^ 31 := by have := (c2 main).2; omega
  have hAll : ∀ g, A g < 2 ^ 31 := fun g => by have := (c2 g).2; dsimp only at this ⊢; omega
  have hlen : ∀ g, 16 * (((cs[pos g]?).map (·.1)).getD []).length < 2 ^ 31 :=
    fun g => by have := (c2 g).2; dsimp only at this ⊢; omega
  have hPC : PCode m A (fun g => ((cs[pos g]?).map (·.1)).getD []) (BitVec.ofNat 64 fp0) Ks :=
    fun g => ⟨(c2 g).1, codeFar_nat' (c2 g).2 (by omega)⟩
  -- the depth
  have hKs : Ks < 2 ^ 31 := by omega
  have hroomF := hF0.room
  have hL1 := maxTop_pos cs
  have hq : 2 ≤ (Ks - FB) / maxTop cs := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hn1 : n + 1 = (Ks - FB) / maxTop cs := by rw [h.hdepth, depthOf]; omega
  have hdm := Nat.div_mul_le_self (Ks - FB) (maxTop cs)
  have hnK : n + 1 ≤ Ks := by have := Nat.div_le_self (Ks - FB) (maxTop cs); omega
  -- the start code: the depth, then the call tail
  have hpre : CodeAt m (BitVec.ofNat 64 codeBase) ([ci 1 2 ((n + 1 : Nat) : Int) 0] ++ callTail A main FB) :=
    codeAt_left hcM
  have s1 := const_step (j := 2) (k := ((n + 1 : Nat) : Int)) (codeAt_left hpre) hF0 (by omega) hKs
    (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega)
  let m1 := write m (slot (BitVec.ofNat 64 fp0) (BitVec.ofNat 64 2)) 8
    (BitVec.ofInt 64 ((n + 1 : Nat) : Int)).toNat
  have a1 : Agree (BitVec.ofNat 64 fp0) 2 Ks m m1 := agree_write hroomF (Nat.le_refl _) (by omega) _
  have hF1 := hF0.agree a1
  have hWa1 : WeltAt m1 Yb σ := weltAt_stab hW0.lay hW0.top m m1 hWa (a1.mono (Nat.zero_le _))
  have h4 : (callTail A main FB).length = 4 := rfl
  have hfC : CodeFar (BitVec.ofNat 64 codeBase + BitVec.ofNat 64 (16 * [ci 1 2 ((n + 1 : Nat) : Int) 0].length))
      (callTail A main FB).length (BitVec.ofNat 64 fp0) Ks := by
    rw [ofNat_add64]; exact codeFar_nat' (by simp [callTail, callTailN]; omega) (by omega)
  have hc1 := (codeAt_right hpre).agree a1 hfC
  have hdv : m1.rd64 (slot (BitVec.ofNat 64 fp0) (BitVec.ofNat 64 2)) = some (BitVec.ofNat 64 n + 1) := by
    have hconv : BitVec.ofInt 64 ((n + 1 : Nat) : Int) = BitVec.ofNat 64 n + 1 := by
      rw [BitVec.ofInt_natCast]; exact ofNat_succ n
    simp only [m1]
    rw [rd_same hF0 (by omega), hconv]
  have hρ1 : WordsAt m1 (slot (BitVec.ofNat 64 fp0) (BitVec.ofNat 64 FB)) (FB + 0) (encodeEnv Yb ρ) :=
    startEnvWords_depth (frameOffset := FB) (reserved := 0) (words := encodeEnv Yb ρ)
      (BitVec.ofInt 64 ((n + 1 : Nat) : Int)).toNat hF0 (by rw [encodeEnv_length]; omega) (by omega) hρ
  have hE : EnvAt Yb m1 (slot (BitVec.ofNat 64 fp0) (BitVec.ofNat 64 FB)) ρ :=
    (envAt_encoding (reserved := 0) ρ).mpr ⟨hval, hρ1⟩
  have hfC4 : CodeFar (BitVec.ofNat 64 codeBase + BitVec.ofNat 64 (16 * [ci 1 2 ((n + 1 : Nat) : Int) 0].length))
      4 (BitVec.ofNat 64 fp0) Ks := by
    rw [h4] at hfC
    exact hfC
  obtain ⟨m5, sC, _, hW5, hK5, hF5, hP5, g0, g1, g2, gE, gW, gy⟩ :=
    call_eintritt (L := Yb) (dv := BitVec.ofNat 64 n) (σ := σ) hc1 hfC4 hF1 hKs (Nat.le_refl _) (by omega)
      hAm (pcode_agree hPC a1) hdv hE hW0 hWa1 (hy.agree a1 (by have := hW0.top; have := hW0.ord; omega))
  -- `main`'s prologue at depth `n = (n - 1) + 1`
  have hn' : n - 1 + 1 = n := by omega
  have g2' : m5.rd64 (slot (slot (BitVec.ofNat 64 fp0) (BitVec.ofNat 64 FB)) (BitVec.ofNat 64 2)) =
      some (BitVec.ofNat 64 (n - 1 + 1)) := by
    rw [hn']
    exact g2
  have hcap : (n - 1 + 1 + 1) * maxTop cs ≤ Ks - FB := by
    rw [hn', hn1]
    exact hdm
  obtain ⟨ens, pc, mR, sP, hOk, hRand⟩ :=
    prolog_rand (Y := Yb) (P := P) (O := O) (passes := passes) (A := A)
      (C := fun g => ((cs[pos g]?).map (·.1)).getD []) (Lm := maxTop cs) h.hfa c1 hAll hlen (k := n - 1)
      (by omega) hcap hW5 hK5 hF5 hP5 g0 g1 g2' gE gW gy HeldIn.nil hreq
  exact ⟨ens, _, pc, mR, s1.trans (sC.trans sP), hOk, hRand⟩

end Gabbro.Stage0.Senke.BildLauf
