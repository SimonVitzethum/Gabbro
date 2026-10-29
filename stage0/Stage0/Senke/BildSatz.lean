/-
  File:      stage0/Stage0/Senke/BildSatz.lean
  Subject:   The whole program: where the image's bytes lie at `IMG`, the IR thread the loader starts (`pc = IMG + 16`,
             `fp` = the image's first word) runs `main` as G's `rufAt n main` (`n` the image's depth) and ends with
             `exit_group` of `main`'s result, or with the stop of G's logic outcome (`bild_ok`).
-/
import Stage0.Senke.BildLese

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

/-- `exit_group` with the word of slot `r`. -/
theorem exitw_ok {m : Runner.Mem} {pc fp : Runner.W} {K s r : Nat} {w : Runner.W}
    (hc : CodeAt m pc [ci 1 s 231 0, ci 2 ((s + 1 : Nat) : Int) r 0, ci 23 ((s + 7 : Nat) : Int) s 0])
    (hf : CodeFar pc 3 fp K) (hF : FrameOK m fp K) (hs : s + 8 ≤ K) (hr : r < s) (hK : K < 2 ^ 31)
    (hw : m.rd64 (slot fp (BitVec.ofNat 64 r)) = some w) :
    ∃ t' m' q, Star ⟨pc, fp⟩ m t' m' ∧ StopAt t' m' q ∧ q.nr = 231 ∧ q.a1 = w := by
  have hroom := hF.room
  have s1 := const_step (k := 231) (codeAt_left (a := [ci 1 s 231 0]) hc) hF (by omega) hK (by decide)
  let m1 := write m (slot fp (BitVec.ofNat 64 s)) 8 (BitVec.ofInt 64 231).toNat
  have a1 : Agree fp 0 K m m1 := agree_write hroom (Nat.zero_le _) (by omega) _
  have hc1 : CodeAt m1 (pc + 16) [ci 2 ((s + 1 : Nat) : Int) r 0, ci 23 ((s + 7 : Nat) : Int) s 0] := by
    have := (codeAt_right (a := [ci 1 s 231 0]) hc).agree a1 (codeFar_right (n := 1) (k := 2) hf)
    simpa using this
  have hF1 := hF.agree a1
  have hw1 : m1.rd64 (slot fp (BitVec.ofNat 64 r)) = some w := by
    simp only [m1]; rw [rd_other hroom (by omega) (by omega) (by omega)]; exact hw
  have s2 := mov_to (codeAt_left (a := [ci 2 ((s + 1 : Nat) : Int) r 0]) hc1) hF1 (j := s + 1) (s := r) (by omega)
    (by omega) hK hw1
  let m2 := write m1 (slot fp (BitVec.ofNat 64 (s + 1))) 8 w.toNat
  have a2 : Agree fp 0 K m1 m2 := agree_write hroom (Nat.zero_le _) (by omega) _
  have hc2 : CodeAt m2 (pc + 16 + 16) [ci 23 ((s + 7 : Nat) : Int) s 0] := by
    have := (codeAt_right (a := [ci 2 ((s + 1 : Nat) : Int) r 0]) hc1).agree a2 (by
      have := codeFar_right (n := 2) (k := 1) hf
      simp only [List.length_singleton, Nat.mul_one]
      rw [BitVec.add_assoc, show (16 : Runner.W) + BitVec.ofNat 64 16 = BitVec.ofNat 64 (16 * 2) by decide]
      exact this)
    simpa using this
  have hF2 := hF1.agree a2
  have hi := hc2 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  have hsx : sx (II.f (s : Int)) = BitVec.ofNat 64 s := sx_nat (by omega)
  have r0 : m2.rd64 (slot fp (BitVec.ofNat 64 s)) = some (BitVec.ofInt 64 231) := by
    simp only [m2]
    rw [rd64_write_far (slot_far hroom (by omega) (by omega) (by omega))]
    exact rd64_wr64 (wr64_some (hF.wr s (by omega))) (hF.rd s (by omega))
  have r1 : m2.rd64 (slot fp (BitVec.ofNat 64 (s + 1))) = some w :=
    rd64_wr64 (wr64_some (hF1.wr _ (by omega))) (hF1.rd _ (by omega))
  have rd : ∀ i, i < 7 → ∃ v, m2.rd64 (slot fp (BitVec.ofNat 64 (s + i))) = some v := fun i hi =>
    ⟨_, by simp only [Runner.Mem.rd64, hF2.rd (s + i) (by omega), ↓reduceIte]; rfl⟩
  obtain ⟨v2, r2⟩ := rd 2 (by decide)
  obtain ⟨v3, r3⟩ := rd 3 (by decide)
  obtain ⟨v4, r4⟩ := rd 4 (by decide)
  obtain ⟨v5, r5⟩ := rd 5 (by decide)
  obtain ⟨v6, r6⟩ := rd 6 (by decide)
  refine ⟨_, m2, ⟨BitVec.ofInt 64 231, w, v2, v3, v4, v5, v6⟩, s1.trans s2,
    runTo_sys (t := ⟨pc + 16 + 16, fp⟩) hi (by rw [hsx]; exact r0) ?_ ?_ ?_ ?_ ?_ ?_, rfl, rfl⟩
  · rw [hsx, show (8 : Runner.W) = BitVec.ofNat 64 (8 * 1) by rfl, slot_plus]; exact r1
  · rw [hsx, show (16 : Runner.W) = BitVec.ofNat 64 (8 * 2) by rfl, slot_plus]; exact r2
  · rw [hsx, show (24 : Runner.W) = BitVec.ofNat 64 (8 * 3) by rfl, slot_plus]; exact r3
  · rw [hsx, show (32 : Runner.W) = BitVec.ofNat 64 (8 * 4) by rfl, slot_plus]; exact r4
  · rw [hsx, show (40 : Runner.W) = BitVec.ofNat 64 (8 * 5) by rfl, slot_plus]; exact r5
  · rw [hsx, show (48 : Runner.W) = BitVec.ofNat 64 (8 * 6) by rfl, slot_plus]; exact r6

theorem leN_len (n v : Nat) : (Runner.Prog.leN n v).length = n := by simp [Runner.Prog.leN]

/-- The image's first word is the first frame: the loader starts the IR thread at `⟨IMG + 16, fp0⟩`. -/
theorem bild_kopf {b : Bild D} {m : Runner.Mem} (hm : BytesAt m Runner.Prog.IMG b.bytes) (hfp : b.fp0 < 2 ^ 64) :
    m.rd64 (BitVec.ofNat 64 Runner.Prog.IMG) = some (BitVec.ofNat 64 b.fp0) := by
  simp only [Bild.bytes, List.append_assoc] at hm
  exact rd64_leN hm hfp

theorem encErg_none {e : Option Ty} (h : e = none) (v : ErgVal D e) (w : Runner.W) : EncErg e v w := by
  subst h; trivial

theorem codeFar_nat {a k f K : Nat} (ha : a + 16 * k ≤ f) (hf : f + 8 * K < 2 ^ 64) :
    CodeFar (BitVec.ofNat 64 a) k (BitVec.ofNat 64 f) K := by
  simp only [CodeFar, BitVec.toNat_ofNat]
  omega

theorem bild_kern {P : Programm D} {O : Orakel D} {passes : Nat} {fs : List D.Fn} {pos : D.Fn → Nat} {main : D.Fn}
    {K Ks : Nat} {Yb : Lay D} {A : D.Fn → Nat} {cs : List (List II × Nat)} {body : List II} {L n fp0 : Nat}
    (hbody : body = cs.flatMap (·.1)) (hL : L = maxTop cs) (hn : n = depthOf Ks L)
    (hfp : fp0 = codeBase + 16 * (startLen + body.length))
    (hA : ∀ g, A g = (addrs (codeBase + 16 * startLen) (cs.map (·.1.length))).getD (pos g) 0)
    (hcl : cs.length = fs.length) (hcs : ∀ i (hi : i < fs.length) (hc : i < cs.length), lowFun P A Yb fs[i] = some cs[i])
    (hfs : ∀ g, fs[pos g]? = some g) (hpar : (D.params main).isEmpty = true) (hfit : fp0 + 8 * K < 2 ^ 31)
    (hroomK : FB + 2 * L ≤ Ks) (hexK : exitSlot + 8 ≤ Ks) (hks : Ks ≤ K) (hYlo : fp0 + 8 * Ks ≤ Yb.lo)
    (hYhi : Yb.hi ≤ fp0 + 8 * K) (hY : LayIn Yb) (hYd : LayDis Yb)
    (hops : (startC A main n ++ body).all (fun i => decide (i.o < 256)) = true)
    {m : Runner.Mem} (hm : BytesAt m codeBase ((startC A main n ++ body).flatMap encII ++ List.replicate (8 * K) 0))
    (σ : World D) (ρ : Env D (D.params main)) (hWa : WeltAt m Yb σ) :
    match rufAt P O passes n main σ ρ with
    | .ok _ v => ∃ t' m' q, Star ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 fp0⟩ m t' m' ∧ StopAt t' m' q ∧
        q.nr = 231 ∧ EncErg (D.erg main) v q.a1
    | .logik e => Stops ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 fp0⟩ m (logikCode e)
    | .hardware h => Stops ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 fp0⟩ m (hwCode h)
    | _ => False := by
  have hcb : codeBase = 268435472 := rfl
  have hFB3 : FB = 3 := rfl
  have hex : exitSlot = 8 := rfl
  have hsl : startLen = 8 := rfl
  have hL1 : 1 ≤ L := hL ▸ maxTop_pos cs
  have hK : K < 2 ^ 31 := by omega
  have hcode := hm.left
  rw [List.flatMap_append] at hcode
  have hSb := hcode.left
  have hBb := hcode.right
  rw [flatMap_enc_len, startC_len] at hBb
  rw [List.all_append, Bool.and_eq_true] at hops
  -- the functions, each at its address
  let C : D.Fn → List II := fun g => ((cs[pos g]?).map (·.1)).getD []
  have hpos : ∀ g, ∃ h : pos g < cs.length, lowFun P A Yb g = some cs[pos g] ∧ C g = cs[pos g].1 := by
    intro g
    obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.mp (hfs g)
    have hc : pos g < cs.length := by omega
    refine ⟨hc, ?_, ?_⟩
    · have := hcs (pos g) h1 hc; rwa [h2] at this
    · simp only [C, List.getElem?_eq_getElem hc, Option.map_some, Option.getD_some]
  have hseg : ∀ g, BytesAt m (A g) ((C g).flatMap encII) ∧ A g + 16 * (C g).length ≤ fp0 ∧
      (C g).all (fun i => decide (i.o < 256)) = true := by
    intro g
    obtain ⟨hc, _, hC⟩ := hpos g
    rw [hC]
    have hsp := flat_split cs (pos g) hc
    have htl := flat_take_len cs (pos g)
    have hAg : A g = codeBase + 16 * startLen + 16 * ((cs.map (·.1.length)).take (pos g)).sum := by
      rw [hA g, addrs_getD _ _ _ (by simpa using hc)]
    rw [hbody, hsp] at hBb
    rw [hbody, hsp] at hops
    rw [hbody, hsp] at hfp
    simp only [List.flatMap_append, List.length_append] at hBb hfp
    simp only [List.all_append, Bool.and_eq_true] at hops
    have hb := hBb.right.left
    rw [flatMap_enc_len, htl] at hb
    refine ⟨by rw [hAg]; exact hb, by rw [hAg, ← htl]; omega, hops.2.2.1⟩
  have hAlt : ∀ g, A g < 2 ^ 31 := fun g => by have := (hseg g).2.1; omega
  have hlen : ∀ g, 16 * (C g).length < 2 ^ 31 := fun g => by have := (hseg g).2.1; omega
  have hP : PCode m A C (BitVec.ofNat 64 fp0) K := fun g =>
    ⟨codeAt_bytes (C g) (A g) (hseg g).2.2 (hseg g).1, codeFar_nat (hseg g).2.1 (by omega)⟩
  have hC' : ∀ g, ∃ top, lowFun P A Yb g = some (C g, top) ∧ top ≤ L := fun g => by
    obtain ⟨hc, hl, hC⟩ := hpos g
    exact ⟨cs[pos g].2, by rw [hl, hC], hL ▸ maxTop_ge hc⟩
  -- the stack
  have hF : FrameOK m (BitVec.ofNat 64 fp0) K := by
    have hz := hm.right
    rw [List.flatMap_append, List.length_append, flatMap_enc_len, flatMap_enc_len, startC_len] at hz
    exact frameOK_bytes (by rw [hfp]; rwa [show codeBase + (16 * startLen + 16 * body.length) =
      codeBase + 16 * (startLen + body.length) by omega] at hz) (by simp) (by omega)
  have hroom := hF.room
  -- the depth
  have hq : 2 ≤ (Ks - FB) / L := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hn1 : n + 1 = (Ks - FB) / L := by rw [hn, depthOf]; omega
  have hdm := Nat.div_mul_le_self (Ks - FB) L
  have hnK : n + 1 ≤ Ks := by have := Nat.div_le_self (Ks - FB) L; omega
  have hS := lowFun_spec (Y := Yb) (P := P) (O := O) (passes := passes) hC' hAlt hlen n (by omega)
  -- the start code
  have hS0 := codeAt_bytes _ _ hops.1 hSb
  have hS0' : CodeAt m (BitVec.ofNat 64 codeBase) ([ci 1 2 ((n + 1 : Nat) : Int) 0] ++ (callTail A main FB ++
      [ci 1 exitSlot 231 0,
       if (D.erg main).isSome then ci 2 ((exitSlot + 1 : Nat) : Int) ((FB + 2 : Nat) : Int) 0
       else ci 1 ((exitSlot + 1 : Nat) : Int) 0 0,
       ci 23 ((exitSlot + 7 : Nat) : Int) exitSlot 0])) := by
    simpa [startC, List.append_assoc] using hS0
  have s1 := const_step (j := 2) (k := ((n + 1 : Nat) : Int)) (codeAt_left hS0') hF (by omega) hK
    (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; omega)
  let m1 := write m (slot (BitVec.ofNat 64 fp0) (BitVec.ofNat 64 2)) 8 (BitVec.ofInt 64 ((n + 1 : Nat) : Int)).toNat
  have a1 : Agree (BitVec.ofNat 64 fp0) 2 K m m1 := agree_write hroom (Nat.le_refl _) (by omega) _
  have hF1 := hF.agree a1
  have hfp0 : (BitVec.ofNat 64 fp0).toNat = fp0 := by simp only [BitVec.toNat_ofNat]; omega
  have hW : WIn Yb (BitVec.ofNat 64 fp0) Ks K := ⟨hY, hYd, by rw [hfp0]; omega, by rw [hfp0]; omega, hks⟩
  have hWa1 : WeltAt m1 Yb σ := weltAt_stab hY (by rw [hfp0]; omega) m m1 hWa
    ((agree_write (K := Ks) (by rw [hfp0]; omega) (Nat.le_refl 2) (by omega) _).mono (Nat.zero_le _))
  have hfC : CodeFar (BitVec.ofNat 64 codeBase + BitVec.ofNat 64 (16 * [ci 1 2 ((n + 1 : Nat) : Int) 0].length))
      (callTail A main FB ++ [ci 1 exitSlot 231 0,
       if (D.erg main).isSome then ci 2 ((exitSlot + 1 : Nat) : Int) ((FB + 2 : Nat) : Int) 0
       else ci 1 ((exitSlot + 1 : Nat) : Int) 0 0,
       ci 23 ((exitSlot + 7 : Nat) : Int) exitSlot 0]).length (BitVec.ofNat 64 fp0) K := by
    rw [ofNat_add64]; exact codeFar_nat (by simp [callTail]; omega) (by omega)
  have hc1 := (codeAt_right hS0').agree a1 hfC
  have hdv : m1.rd64 (slot (BitVec.ofNat 64 fp0) (BitVec.ofNat 64 2)) = some (BitVec.ofNat 64 n + 1) := by
    have hconv : BitVec.ofInt 64 ((n + 1 : Nat) : Int) = BitVec.ofNat 64 n + 1 := by
      rw [BitVec.ofInt_natCast]; exact ofNat_succ n
    simp only [m1]
    rw [rd_same hF (by omega), hconv]
  have hnp : (D.params main).length = 0 := by simpa using hpar
  have hE : EnvAt m1 (slot (BitVec.ofNat 64 fp0) (BitVec.ofNat 64 FB)) ρ := fun τ x => by
    have := idx_lt x; omega
  have hcall := call_ok (σ := σ) hS (codeAt_left hc1) (codeFar_left (k := 3) (by have h4 : (callTail A main FB).length = 4 := rfl; simpa [h4] using hfC)) hF1 hK (Nat.le_refl _)
    (by omega) (by rw [hn1]; omega) (hAlt main) (pcode_agree hP a1) hdv hE hW hWa1
  generalize rufAt P O passes n main σ ρ = o at hcall ⊢
  cases o with
  | ok σ' v =>
    obtain ⟨m2, s2, a2, ⟨w, hw, hew⟩, _⟩ := hcall
    have a12 : Agree (BitVec.ofNat 64 fp0) 2 K m m2 := a1.trans (a2.mono (by omega))
    have hfE := codeFar_tail (a := callTail A main FB) hfC
    have hexC := (codeAt_right (a := callTail A main FB) hc1).agree (a2.mono (Nat.zero_le _)) hfE
    have hF2 := hF1.agree a2
    by_cases hs : (D.erg main).isSome = true
    · simp only [hs, ite_true] at hexC hfE
      obtain ⟨t', m', q, sx, hq, hnr, ha⟩ := exitw_ok hexC hfE hF2 (by omega) (by omega) hK hw
      exact ⟨t', m', q, s1.trans (s2.trans sx), hq, hnr, by rw [ha]; exact hew⟩
    · simp only [hs, Bool.false_eq_true, ite_false] at hexC hfE
      obtain ⟨t', m', q, sx, hq, hnr, _⟩ := stop_ok (c := 0) (s := exitSlot) hexC hfE hF2 (by omega) hK (by decide)
      exact ⟨t', m', q, s1.trans (s2.trans sx), hq, hnr,
        encErg_none (by simpa using hs) v _⟩
  | logik e => exact Stops.prefix s1 hcall
  | why _ _ => exact hcall.elim
  | hardware e => exact Stops.prefix s1 hcall

/-- **The program theorem.** For every world `σ` the image's world bytes hold (`WeltAt`), under a world layout
    `Y` that keeps every cell in the world once it ends below `2^31` (`LayIn`) and gives no two cells one word
    (`LayDis`); `layU` is such a layout (`layU_in`, `layU_dis`). -/
theorem bild_ok {P : Programm D} {O : Orakel D} {passes : Nat} {fs : List D.Fn} {pos : D.Fn → Nat}
    {name : D.Fn → String} {main : D.Fn} {Ks : Nat} {Y : Nat → Lay D} {b : Bild D}
    (hb : bild P Y fs pos name main Ks = .ok b) (hfs : ∀ g, fs[pos g]? = some g)
    (hYin : ∀ x, (Y x).hi < 2 ^ 31 → LayIn (Y x)) (hYdis : ∀ x, LayDis (Y x))
    {m : Runner.Mem} (hm : BytesAt m Runner.Prog.IMG b.bytes) (σ : World D) (ρ : Env D (D.params main))
    (hWa : WeltAt m b.Y σ) :
    match rufAt P O passes b.depth main σ ρ with
    | .ok _ v => ∃ t' m' q, Star ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 b.fp0⟩ m t' m' ∧ StopAt t' m' q ∧
        q.nr = 231 ∧ EncErg (D.erg main) v q.a1
    | .logik e => Stops ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 b.fp0⟩ m (logikCode e)
    | .hardware h => Stops ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 b.fp0⟩ m (hwCode h)
    | _ => False := by
  simp only [bild] at hb
  split at hb
  · cases hb
  · next cs0 h0 =>
    split at hb
    · cases hb
    · next cs h1 =>
      split at hb
      · next hg =>
        simp only [Except.ok.injEq] at hb
        subst hb
        obtain ⟨⟨hpar, hlens, hfit, hroomK, hexK, hops, hYlo, hYhi, hks⟩, hfp⟩ := hg
        have hY := hYin (codeBase + 16 * (startLen + (List.map (fun x => x.1.length) cs0).sum) + 8 * Ks)
          (Nat.lt_of_le_of_lt hYhi hfit)
        have hYd := hYdis (codeBase + 16 * (startLen + (List.map (fun x => x.1.length) cs0).sum) + 8 * Ks)
        obtain ⟨hcl, hcs⟩ := lowAll_ok fs cs h1
        have hm' := hm
        simp only [Bild.bytes, List.append_assoc] at hm'
        have hm2 := hm'.right.right
        simp only [leN_len] at hm2
        exact bild_kern rfl rfl rfl hfp (fun g => by rw [hlens]) hcl hcs hfs hpar hfit hroomK hexK hks hYlo hYhi hY hYd
          hops (by simpa [codeBase] using hm2) σ ρ hWa
      · exfalso
        revert hb
        repeat' split
        all_goals intro hb; cases hb

end Gabbro.Stage0.Senke
