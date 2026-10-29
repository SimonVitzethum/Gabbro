/-
  File:      stage0/Stage0/Senke/BildSatz.lean
  Subject:   The whole program: where the image's bytes lie at `IMG`. The IR thread the loader starts (`pc = IMG + 16`,
             `fp` = the image's first word) spawns every root on a stack of its own, runs `main` as G's `rufAt n main`
             (`n` the image's depth) and ends with `exit_group` of `main`'s result, or with the stop of G's outcome
             (`bild_ok`); the thread of root `j` runs it as `rufAt n` and ends with `exit` (`bild_wurzel_ok`).
-/
import Stage0.Senke.Start

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

theorem leN_len (n v : Nat) : (Runner.Prog.leN n v).length = n := by simp [Runner.Prog.leN]

/-- The image's first word is the first frame: the loader starts the IR thread at `⟨IMG + 16, fp0⟩`. -/
theorem bild_kopf {b : Bild D} {m : Runner.Mem} (hm : BytesAt m Runner.Prog.IMG b.bytes) (hfp : b.fp0 < 2 ^ 64) :
    m.rd64 (BitVec.ofNat 64 Runner.Prog.IMG) = some (BitVec.ofNat 64 b.fp0) := by
  simp only [Bild.bytes, List.append_assoc] at hm
  exact rd64_leN hm hfp

theorem encErg_none {e : Option Ty} (h : e = none) (v : ErgVal D e) (w : Runner.W) : EncErg Yb e v w := by
  subst h; trivial

theorem codeFar_nat {a k f K : Nat} (ha : a + 16 * k ≤ f) (hf : f + 8 * K < 2 ^ 64) :
    CodeFar (BitVec.ofNat 64 a) k (BitVec.ofNat 64 f) K := by
  simp only [CodeFar, BitVec.toNat_ofNat]
  omega

/-- The code of an image: the head `hd`, then every function at its address, all below the stacks. -/
theorem bild_code {P : Programm D} {fs : List D.Fn} {pos : D.Fn → Nat} {A : D.Fn → Nat}
    {cs : List (List II × Nat)} {body hd : List II} {Yb : Lay D} {fp0 : Nat} {C : D.Fn → List II}
    (hC : ∀ g, C g = ((cs[pos g]?).map (·.1)).getD [])
    (hbody : body = cs.flatMap (·.1)) (hfp : fp0 = codeBase + 16 * (hd.length + body.length))
    (hA : ∀ g, A g = (addrs (codeBase + 16 * hd.length) (cs.map (·.1.length))).getD (pos g) 0)
    (hcl : cs.length = fs.length)
    (hcs : ∀ i (hi : i < fs.length) (hc : i < cs.length), lowFun P A Yb fs[i] = some cs[i])
    (hfs : ∀ g, fs[pos g]? = some g) (hops : (hd ++ body).all (fun i => decide (i.o < 256)) = true)
    {m : Runner.Mem} (hcode : BytesAt m codeBase ((hd ++ body).flatMap encII)) :
    (∀ g, ∃ top, lowFun P A Yb g = some (C g, top) ∧ top ≤ maxTop cs) ∧
    (∀ g, CodeAt m (BitVec.ofNat 64 (A g)) (C g) ∧ A g + 16 * (C g).length ≤ fp0) ∧
    CodeAt m (BitVec.ofNat 64 codeBase) hd := by
  rw [List.flatMap_append] at hcode
  have hSb := hcode.left
  have hBb := hcode.right
  rw [flatMap_enc_len] at hBb
  rw [List.all_append, Bool.and_eq_true] at hops
  have hpos : ∀ g, ∃ h : pos g < cs.length, lowFun P A Yb g = some cs[pos g] ∧ C g = cs[pos g].1 := by
    intro g
    obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.mp (hfs g)
    have hc : pos g < cs.length := by omega
    refine ⟨hc, ?_, ?_⟩
    · have := hcs (pos g) h1 hc; rwa [h2] at this
    · simp only [hC, List.getElem?_eq_getElem hc, Option.map_some, Option.getD_some]
  have hseg : ∀ g, BytesAt m (A g) ((C g).flatMap encII) ∧ A g + 16 * (C g).length ≤ fp0 ∧
      (C g).all (fun i => decide (i.o < 256)) = true := by
    intro g
    obtain ⟨hc, _, hCg⟩ := hpos g
    rw [hCg]
    have hsp := flat_split cs (pos g) hc
    have htl := flat_take_len cs (pos g)
    have hAg : A g = codeBase + 16 * hd.length + 16 * ((cs.map (·.1.length)).take (pos g)).sum := by
      rw [hA g, addrs_getD _ _ _ (by simpa using hc)]
    have hBb' := hBb
    have hops' := hops.2
    have hfp' := hfp
    rw [hbody, hsp] at hBb' hops' hfp'
    simp only [List.flatMap_append, List.length_append] at hBb' hfp'
    simp only [List.all_append, Bool.and_eq_true] at hops'
    have hb := hBb'.right.left
    rw [flatMap_enc_len, htl] at hb
    refine ⟨by rw [hAg]; exact hb, by rw [hAg, ← htl]; omega, hops'.2.1⟩
  refine ⟨fun g => ?_, fun g => ⟨codeAt_bytes (C g) (A g) (hseg g).2.2 (hseg g).1, (hseg g).2.1⟩,
    codeAt_bytes hd codeBase hops.1 hSb⟩
  obtain ⟨hc, hl, hCg⟩ := hpos g
  exact ⟨cs[pos g].2, by rw [hl, hCg], maxTop_ge hc⟩

theorem rootsC_at (A : D.Fn → Nat) (n : Nat) {m : Runner.Mem} :
    (roots : List D.Fn) → (p j : Nat) → (hj : j < roots.length) → CodeAt m (BitVec.ofNat 64 p) (rootsC A n roots) →
    CodeAt m (BitVec.ofNat 64 (p + 16 * (startLen * j))) (startC A roots[j] n 60 false)
  | [], _, _, hj, _ => absurd hj (by simp)
  | f :: r, p, 0, _, hc => by simpa [rootsC] using codeAt_left (a := startC A f n 60 false) hc
  | f :: r, p, j + 1, hj, hc => by
    have h := codeAt_right (a := startC A f n 60 false) (b := rootsC A n r) hc
    rw [startC_len, ofNat_add64] at h
    have := rootsC_at A n r (p + 16 * startLen) j (by simpa using hj) h
    rw [show p + 16 * startLen + 16 * (startLen * j) = p + 16 * (startLen * (j + 1)) by rw [Nat.mul_succ]; omega]
      at this
    simpa using this

/-- The frame of the `j`-th stack: `Ks` zero slots readable and writable. -/
theorem frame_stack {m : Runner.Mem} {fp0 K Ks j : Nat} (hz : BytesAt m fp0 (List.replicate (8 * K) 0))
    (hj : Ks * (j + 1) ≤ K) (hfit : fp0 + 8 * K < 2 ^ 31) :
    FrameOK m (BitVec.ofNat 64 (fp0 + 8 * (Ks * j))) Ks := by
  have hs : Ks * (j + 1) = Ks * j + Ks := Nat.mul_succ Ks j
  have e : List.replicate (8 * K) (0 : Runner.B) =
      List.replicate (8 * (Ks * j)) 0 ++ List.replicate (8 * K - 8 * (Ks * j)) 0 := by
    rw [List.replicate_append_replicate]; congr 1; omega
  rw [e] at hz
  have h := hz.right
  simp only [List.length_replicate] at h
  exact frameOK_bytes h (by simp only [List.length_replicate]; omega) (by omega)

section Bild
variable {P : Programm D} {O : Orakel D} {passes : Nat} {fs : List D.Fn} {pos : D.Fn → Nat} {main : D.Fn}
  {roots : List D.Fn} {K Ks : Nat} {Yb : Lay D} {A : D.Fn → Nat} {cs : List (List II × Nat)} {body : List II}
  {n fp0 : Nat} {sp : List (Nat × Nat)}

/-- What `bild` lays out, as hypotheses on one image. -/
structure BildLage (P : Programm D) (fs : List D.Fn) (pos : D.Fn → Nat) (main : D.Fn) (roots : List D.Fn)
    (K Ks : Nat) (Yb : Lay D) (A : D.Fn → Nat) (cs : List (List II × Nat)) (body : List II) (n fp0 : Nat)
    (sp : List (Nat × Nat)) : Prop where
  hfa : Yb.fa = A
  hbody : body = cs.flatMap (·.1)
  hdepth : n = depthOf Ks (maxTop cs)
  hsp : sp = (List.range roots.length).map fun j =>
    (codeBase + 16 * (3 * roots.length + startLen + startLen * j), fp0 + 8 * (Ks * (j + 1)))
  hfp : fp0 = codeBase + 16 * (headLen roots.length + body.length)
  haddr : ∀ g, A g = (addrs (codeBase + 16 * headLen roots.length) (cs.map (·.1.length))).getD (pos g) 0
  hlen : cs.length = fs.length
  hlow : ∀ i (hi : i < fs.length) (hc : i < cs.length), lowFun P A Yb fs[i] = some cs[i]
  hpos : ∀ g, fs[pos g]? = some g
  hpar : (D.params main).isEmpty = true
  hrpar : roots.all (fun f => (D.params f).isEmpty) = true
  hwhy : D.gruende main = 0
  hrwhy : roots.all (fun f => decide (D.gruende f = 0)) = true
  hfit : fp0 + 8 * K < 2 ^ 31
  hroom : FB + 2 * maxTop cs ≤ Ks
  hex : exitSlot + 8 ≤ Ks
  hylo : fp0 + 8 * (Ks * (roots.length + 1)) ≤ Yb.lo
  hyhi : Yb.hi ≤ fp0 + 8 * K
  hyord : Yb.lo ≤ Yb.hi
  hlay : LayIn Yb
  hdis : LayDis Yb
  hsb : Yb.sb = fp0
  hst : Yb.st = 8 * Ks
  hsync : LaySync Yb
  hysye : Yb.sye ≤ fp0 + 8 * K
  hops : (spawnC sp ++ startC A main n 231 true ++ rootsC A n roots ++ body).all (fun i => decide (i.o < 256)) = true

theorem BildLage.head (h : BildLage P fs pos main roots K Ks Yb A cs body n fp0 sp) :
    (spawnC sp ++ startC A main n 231 true ++ rootsC A n roots).length = headLen roots.length := by
  rw [h.hsp]
  simp only [List.length_append, spawnC_len, List.length_map, List.length_range, startC_len, rootsC_len, headLen]

/-- The functions of an image and their code below the stacks. -/
theorem BildLage.code (h : BildLage P fs pos main roots K Ks Yb A cs body n fp0 sp) {m : Runner.Mem}
    (hm : BytesAt m codeBase ((spawnC sp ++ startC A main n 231 true ++ rootsC A n roots ++ body).flatMap encII ++
      List.replicate (8 * K) 0)) :
    let C : D.Fn → List II := fun g => ((cs[pos g]?).map (·.1)).getD []
    (∀ g, ∃ top, lowFun P A Yb g = some (C g, top) ∧ top ≤ maxTop cs) ∧
    (∀ g, CodeAt m (BitVec.ofNat 64 (A g)) (C g) ∧ A g + 16 * (C g).length ≤ fp0) ∧
    CodeAt m (BitVec.ofNat 64 codeBase) (spawnC sp ++ startC A main n 231 true ++ rootsC A n roots) ∧
    BytesAt m fp0 (List.replicate (8 * K) 0) := by
  intro C
  have hl := h.head
  obtain ⟨c1, c2, c3⟩ := bild_code (C := C) (fp0 := fp0) (fun _ => rfl) h.hbody (by rw [hl]; exact h.hfp)
    (by rw [hl]; exact h.haddr) h.hlen h.hlow h.hpos h.hops hm.left
  refine ⟨c1, c2, c3, ?_⟩
  have hz := hm.right
  rw [flatMap_enc_len, List.length_append, hl] at hz
  rwa [show codeBase + 16 * (headLen roots.length + body.length) = fp0 from h.hfp.symm] at hz

/-- The world above the stacks, for the frame of stack `j`. -/
theorem BildLage.win (h : BildLage P fs pos main roots K Ks Yb A cs body n fp0 sp) {j : Nat}
    (hj : j ≤ roots.length) : WIn Yb (BitVec.ofNat 64 (fp0 + 8 * (Ks * j))) Ks Ks := by
  have hs : Ks * (roots.length + 1) = Ks * roots.length + Ks := Nat.mul_succ Ks _
  have hm : Ks * j ≤ Ks * roots.length := Nat.mul_le_mul_left Ks hj
  have := h.hylo; have := h.hyhi; have := h.hfit
  refine ⟨h.hlay, h.hdis, ?_, h.hyord, Nat.le_refl _⟩
  simp only [BitVec.toNat_ofNat]; omega

theorem le_zero {m : Runner.Mem} {a : Runner.W} :
    ∀ {n : Nat}, (∀ j, j < n → m.b (a + BitVec.ofNat 64 j) = 0) → Runner.Mem.le m a n = 0
  | 0, _ => rfl
  | n + 1, h => by
    simp only [Runner.Mem.le, h n (by omega), le_zero (n := n) (fun j hj => h j (by omega))]
    simp

/-- A word of the zero area reads 0 and may be written. -/
theorem zero_word {m : Runner.Mem} {p n y : Nat} (hz : BytesAt m p (List.replicate n 0)) (h1 : p ≤ y)
    (h2 : y + 8 ≤ p + n) (h3 : p + n < 2 ^ 31) :
    m.rd64 (BitVec.ofNat 64 y) = some 0 ∧ all m.wr (BitVec.ofNat 64 y) 8 = true := by
  have hb : ∀ j, j < 8 → m.rd (BitVec.ofNat 64 y + BitVec.ofNat 64 j) = true ∧
      m.wr (BitVec.ofNat 64 y + BitVec.ofNat 64 j) = true ∧ m.b (BitVec.ofNat 64 y + BitVec.ofNat 64 j) = 0 := by
    intro j hj
    have := hz (y - p + j) (by simp only [List.length_replicate]; omega)
    rw [ofNat_add64, show y + j = p + (y - p + j) by omega]
    simpa using this
  refine ⟨?_, all_of fun j hj => (hb j hj).2.1⟩
  simp only [Runner.Mem.rd64, all_of fun j hj => (hb j hj).1, ite_true, le_zero fun j hj => (hb j hj).2.2]
  rfl

/-- The locks at the start: every word 0 in the zero area, every frame of a stack in its band. -/
theorem BildLage.sync (h : BildLage P fs pos main roots K Ks Yb A cs body n fp0 sp) {m : Runner.Mem}
    (hz : BytesAt m fp0 (List.replicate (8 * K) 0)) {j : Nat} (hj : j ≤ roots.length) :
    SyncOK m Yb (BitVec.ofNat 64 (fp0 + 8 * (Ks * j))) Ks := by
  have hs : Ks * (roots.length + 1) = Ks * roots.length + Ks := Nat.mul_succ Ks _
  have hm : Ks * j ≤ Ks * roots.length := Nat.mul_le_mul_left Ks hj
  have hylo := h.hylo; have hyhi := h.hyhi; have hfit := h.hfit; have hyord := h.hyord
  have hroom := h.hroom; have hmt := maxTop_pos cs; have hsye := h.hysye
  have hfp : (BitVec.ofNat 64 (fp0 + 8 * (Ks * j))).toNat = fp0 + 8 * (Ks * j) := by
    simp only [BitVec.toNat_ofNat]; omega
  have hq : (fp0 + 8 * (Ks * j) - Yb.sb) / Yb.st = j := by
    rw [h.hsb, h.hst, show fp0 + 8 * (Ks * j) - fp0 = 8 * Ks * j by rw [Nat.mul_assoc]; omega]
    exact Nat.mul_div_cancel_left j (by omega)
  have hl := h.hsync
  refine ⟨by rw [h.hsb]; omega, by rw [h.hst]; omega, by rw [h.hst]; omega, by rw [hfp, h.hsb]; omega,
    by rw [hfp]; omega, by rw [hfp, hq, h.hsb, h.hst, Nat.mul_succ, ← Nat.mul_assoc]; omega, hl.1,
    by omega, hl.2, fun Lk k hk => ?_, fun Lk => ?_⟩
  · have := hl.1 Lk
    exact (zero_word hz (by omega) (by omega) hfit).2
  · have := hl.1 Lk
    exact ⟨0, 0, (zero_word hz (by omega) (by omega) hfit).1, (zero_word hz (by omega) (by omega) hfit).1,
      (zero_word hz (by omega) (by omega) hfit).1, Or.inl ⟨rfl, rfl⟩⟩

/-- **`main`'s thread**: the spawns of the roots, then `main` as `rufAt n main`, then `exit_group`. -/
theorem bild_kern [CloneOK] {O : Orakel D} [hT : TorOK Yb O] [hV : SichtOK O] {passes : Nat}
    (h : BildLage P fs pos main roots K Ks Yb A cs body n fp0 sp) {m : Runner.Mem}
    (hm : BytesAt m codeBase ((spawnC sp ++ startC A main n 231 true ++ rootsC A n roots ++ body).flatMap encII ++
      List.replicate (8 * K) 0))
    (σ : World D) (ρ : Env D (D.params main)) (hWa : WeltAt m Yb σ) :
    match rufAt P O passes n main σ ρ with
    | .ok _ v => ∃ t' m' q, Star ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 fp0⟩ m t' m' ∧ StopAt t' m' q ∧
        q.nr = BitVec.ofNat 64 231 ∧ EncErg Yb (D.erg main) v q.a1
    | .logik e => Stops ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 fp0⟩ m (logikCode e)
    | .hardware e => Stops ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 fp0⟩ m (hwCode e)
    | _ => False := by
  obtain ⟨c1, c2, c3, hz⟩ := h.code hm
  have hfit := h.hfit
  have hroom := h.hroom
  have hex := h.hex
  have hylo := h.hylo
  have hyhi := h.hyhi
  have hs : Ks * (roots.length + 1) = Ks * roots.length + Ks := Nat.mul_succ Ks _
  have hK : Ks ≤ K := by
    have := Nat.le_mul_of_pos_right Ks (Nat.succ_pos roots.length); have := h.hyord; omega
  have hF0 : FrameOK m (BitVec.ofNat 64 fp0) Ks := by
    simpa using frame_stack (j := 0) hz (by omega) hfit
  have hW0 : WIn Yb (BitVec.ofNat 64 fp0) Ks Ks := by simpa using h.win (j := 0) (Nat.zero_le _)
  have hfp := h.hfp
  have hcb : codeBase = 268435472 := rfl
  have hsl8 : startLen = 8 := rfl
  simp only [headLen, startLen] at hfp
  have hl := h.head
  -- the spawns
  have hcS : CodeAt m (BitVec.ofNat 64 codeBase) (spawnC sp) := codeAt_left (codeAt_left c3)
  have hsl : (spawnC sp).length = 3 * roots.length := by rw [spawnC_len, h.hsp]; simp
  have hspb : ∀ x ∈ sp, x.1 < 2 ^ 31 ∧ x.2 < 2 ^ 31 := by
    intro x hx
    rw [h.hsp] at hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have : Ks * (j + 1) ≤ Ks * roots.length := Nat.mul_le_mul_left Ks (by omega)
    have := h.hyord
    simp only [startLen]
    constructor <;> omega
  obtain ⟨m1, s1, a1⟩ := spawnC_ok (fp := BitVec.ofNat 64 fp0) (K := Ks) (by omega) (by omega) sp hspb m _ hcS hF0
    (codeFar_nat' (by rw [hsl]; omega) (by omega))
  -- `main`
  have hcM : CodeAt m (BitVec.ofNat 64 (codeBase + 16 * (3 * roots.length))) (startC A main n 231 true) := by
    have := codeAt_right (codeAt_left (a := spawnC sp ++ startC A main n 231 true) c3)
    rw [ofNat_add64, hsl] at this
    exact this
  have hcM1 := hcM.agree a1 (codeFar_nat' (by rw [startC_len]; simp only [startLen]; omega) (by omega))
  have hPC : PCode m1 A (fun g => ((cs[pos g]?).map (·.1)).getD []) (BitVec.ofNat 64 fp0) Ks := fun g =>
    ⟨(c2 g).1.agree a1 (codeFar_nat' (c2 g).2 (by omega)), codeFar_nat' (c2 g).2 (by omega)⟩
  have hst := start_ok (Y := Yb) (P := P) (O := O) (passes := passes) (f := main) (e := 231) (keep := true)
    (pc := codeBase + 16 * (3 * roots.length)) (fpI := fp0) (m := m1) h.hfa c1
    (fun g => by have := (c2 g).2; dsimp only at this ⊢; omega) (fun g => by have := (c2 g).2; dsimp only at this ⊢; omega) h.hpar h.hwhy hroom hex
    (maxTop_pos cs) h.hdepth (by decide) (by omega) hcM1 (by simp only [startLen]; omega)
    (hF0.agree a1) hPC hW0 σ ρ (weltAt_stab hW0.lay hW0.top m m1 hWa (a1.mono (Nat.zero_le _)))
    ((by simpa using h.sync hz (j := 0) (Nat.zero_le _) : SyncOK m Yb (BitVec.ofNat 64 fp0) Ks).agree a1
      (by have := hW0.top; have := hW0.ord; omega))
  rw [show BitVec.ofNat 64 codeBase + BitVec.ofNat 64 (16 * (spawnC sp).length) =
    BitVec.ofNat 64 (codeBase + 16 * (3 * roots.length)) by rw [ofNat_add64, hsl]] at s1
  generalize rufAt P O passes n main σ ρ = o at hst ⊢
  cases o with
  | ok σ' v =>
    obtain ⟨t', m', q, sx, hq, hnr, he⟩ := hst
    exact ⟨t', m', q, s1.trans sx, hq, hnr, he rfl⟩
  | logik e => exact Stops.prefix s1 hst
  | hardware e => exact Stops.prefix s1 hst
  | why _ _ => exact hst.elim

/-- **The thread of root `j`**, from its start code on its stack: the root as `rufAt n`, then `exit`. -/
theorem bild_wurzel {O : Orakel D} [hT : TorOK Yb O] [hV : SichtOK O] {passes : Nat}
    (h : BildLage P fs pos main roots K Ks Yb A cs body n fp0 sp) {m : Runner.Mem}
    (hm : BytesAt m codeBase ((spawnC sp ++ startC A main n 231 true ++ rootsC A n roots ++ body).flatMap encII ++
      List.replicate (8 * K) 0))
    (j : Nat) (hj : j < roots.length) (σ : World D) (ρ : Env D (D.params roots[j])) (hWa : WeltAt m Yb σ) :
    match rufAt P O passes n roots[j] σ ρ with
    | .ok _ _ => ∃ t' m' q, Star ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * roots.length + startLen + startLen * j)),
        BitVec.ofNat 64 (fp0 + 8 * (Ks * (j + 1)))⟩ m t' m' ∧ StopAt t' m' q ∧ q.nr = BitVec.ofNat 64 60
    | .logik e => Stops ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * roots.length + startLen + startLen * j)),
        BitVec.ofNat 64 (fp0 + 8 * (Ks * (j + 1)))⟩ m (logikCode e)
    | .hardware e => Stops ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * roots.length + startLen + startLen * j)),
        BitVec.ofNat 64 (fp0 + 8 * (Ks * (j + 1)))⟩ m (hwCode e)
    | _ => False := by
  obtain ⟨c1, c2, c3, hz⟩ := h.code hm
  have hfit := h.hfit
  have hfp := h.hfp
  have hcb : codeBase = 268435472 := rfl
  have hsl8 : startLen = 8 := rfl
  simp only [headLen, startLen] at hfp
  have hylo := h.hylo
  have hyhi := h.hyhi
  have hs : Ks * (roots.length + 1) = Ks * roots.length + Ks := Nat.mul_succ Ks _
  have hjj : Ks * (j + 1) ≤ Ks * roots.length := Nat.mul_le_mul_left Ks (by omega)
  have hs2 : Ks * (j + 1 + 1) = Ks * (j + 1) + Ks := Nat.mul_succ Ks _
  have hyord := h.hyord
  have hF : FrameOK m (BitVec.ofNat 64 (fp0 + 8 * (Ks * (j + 1)))) Ks :=
    frame_stack hz (by have := h.hyord; omega) hfit
  have hsl : (spawnC sp).length = 3 * roots.length := by rw [spawnC_len, h.hsp]; simp
  have hcR : CodeAt m (BitVec.ofNat 64 (codeBase + 16 * (3 * roots.length + startLen + startLen * j)))
      (startC A roots[j] n 60 false) := by
    have h1 := codeAt_right (a := spawnC sp ++ startC A main n 231 true) c3
    rw [ofNat_add64, List.length_append, hsl, startC_len] at h1
    have := rootsC_at A n roots _ j hj h1
    rwa [show codeBase + 16 * (3 * roots.length + startLen) + 16 * (startLen * j) =
      codeBase + 16 * (3 * roots.length + startLen + startLen * j) by omega] at this
  have hrp : (D.params roots[j]).isEmpty = true := by
    have := h.hrpar; rw [List.all_eq_true] at this; exact this _ (List.getElem_mem hj)
  have hPC : PCode m A (fun g => ((cs[pos g]?).map (·.1)).getD []) (BitVec.ofNat 64 (fp0 + 8 * (Ks * (j + 1)))) Ks :=
    fun g => ⟨(c2 g).1, codeFar_nat' (by have := (c2 g).2; dsimp only at this ⊢; omega) (by omega)⟩
  have hst := start_ok (Y := Yb) (P := P) (O := O) (passes := passes) (f := roots[j]) (e := 60) (keep := false)
    (m := m) h.hfa c1 (fun g => by have := (c2 g).2; dsimp only at this ⊢; omega) (fun g => by have := (c2 g).2; dsimp only at this ⊢; omega) hrp (by have := List.all_eq_true.mp h.hrwhy roots[j] (List.getElem_mem hj); simpa using this) h.hroom h.hex
    (maxTop_pos cs) h.hdepth (by decide) (by omega) hcR (by simp only [startLen]; omega)
    hF hPC (h.win (by omega)) σ ρ hWa (h.sync hz (by omega))
  generalize rufAt P O passes n roots[j] σ ρ = o at hst ⊢
  cases o with
  | ok σ' v => obtain ⟨t', m', q, sx, hq, hnr, _⟩ := hst; exact ⟨t', m', q, sx, hq, hnr⟩
  | logik e => exact hst
  | hardware e => exact hst
  | why _ _ => exact hst.elim

end Bild

/-- What `bild` lays out holds of its image. -/
theorem bild_lage {P : Programm D} {fs : List D.Fn} {pos : D.Fn → Nat} {name : D.Fn → String} {main : D.Fn}
    {roots : List D.Fn} {Ks : Nat} {Y : Nat → Lay D} {b : Bild D}
    (hb : bild P Y fs pos name main roots Ks = .ok b) (hfs : ∀ g, fs[pos g]? = some g)
    (hYin : ∀ x, (Y x).hi < 2 ^ 31 → LayIn (Y x)) (hYdis : ∀ x, LayDis (Y x)) (hYord : ∀ x, (Y x).lo ≤ (Y x).hi)
    (hYsync : ∀ x, LaySync (Y x)) :
    ∃ cs body sp, BildLage P fs pos main roots b.K b.Ks b.Y b.A cs body b.depth b.fp0 sp ∧
      b.code = spawnC sp ++ startC b.A main b.depth 231 true ++ rootsC b.A b.depth roots ++ body ∧
      b.roots = roots := by
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
        obtain ⟨⟨hpar, hrpar, hwhy, hrwhy, hlens, hfit, hroomK, hexK, hops, hYlo, hYhi, hYsye⟩, hfp⟩ := hg
        obtain ⟨hcl, hcs⟩ := lowAll_ok fs cs h1
        refine ⟨cs, cs.flatMap (·.1), _, ⟨rfl, rfl, rfl, rfl, hfp, fun g => by rw [hlens], hcl, hcs, hfs, hpar, hrpar, hwhy, hrwhy,
          hfit, hroomK, hexK, hYlo, hYhi, hYord _, hYin _ (Nat.lt_of_le_of_lt hYhi hfit),
          ⟨(hYdis _).inj, (hYdis _).grid⟩, rfl, rfl, hYsync _, hYsye, hops⟩, rfl, rfl⟩
      · exfalso
        revert hb
        repeat' split
        all_goals intro hb; cases hb

theorem bild_bytes {b : Bild D} {m : Runner.Mem} (hm : BytesAt m Runner.Prog.IMG b.bytes) :
    BytesAt m codeBase (b.code.flatMap encII ++ List.replicate (8 * b.K) 0) := by
  have hm' := hm
  simp only [Bild.bytes, List.append_assoc] at hm'
  have hm2 := hm'.right.right
  simp only [leN_len] at hm2
  simpa [codeBase] using hm2

/-- **The program theorem**, `main`'s thread: from the loader's first instruction, the roots spawned, `main` as
    `rufAt b.depth main`, then `exit_group` of its result -- or the stop of G's outcome. -/
theorem bild_ok [CloneOK] {P : Programm D} {O : Orakel D} {passes : Nat} {fs : List D.Fn} {pos : D.Fn → Nat}
    {name : D.Fn → String} {main : D.Fn} {roots : List D.Fn} {Ks : Nat} {Y : Nat → Lay D} {b : Bild D}
    (hb : bild P Y fs pos name main roots Ks = .ok b) (hfs : ∀ g, fs[pos g]? = some g)
    (hYin : ∀ x, (Y x).hi < 2 ^ 31 → LayIn (Y x)) (hYdis : ∀ x, LayDis (Y x)) (hYord : ∀ x, (Y x).lo ≤ (Y x).hi)
    (hYsync : ∀ x, LaySync (Y x)) {m : Runner.Mem} (hm : BytesAt m Runner.Prog.IMG b.bytes) (σ : World D) (ρ : Env D (D.params main))
    (hWa : WeltAt m b.Y σ) (hT : TorOK b.Y O) (hV : SichtOK O) :
    match rufAt P O passes b.depth main σ ρ with
    | .ok _ v => ∃ t' m' q, Star ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 b.fp0⟩ m t' m' ∧ StopAt t' m' q ∧
        q.nr = 231 ∧ EncErg b.Y (D.erg main) v q.a1
    | .logik e => Stops ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 b.fp0⟩ m (logikCode e)
    | .hardware h => Stops ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 b.fp0⟩ m (hwCode h)
    | _ => False := by
  obtain ⟨cs, body, sp, hl, hc, _⟩ := bild_lage hb hfs hYin hYdis hYord hYsync
  have hm2 := bild_bytes hm
  rw [hc] at hm2
  exact bild_kern (hT := hT) (hV := hV) (passes := passes) hl hm2 σ ρ hWa

/-- **The program theorem**, the thread of root `j`: from its start code on its stack, the root as
    `rufAt b.depth`, then `exit` -- or the stop of G's outcome. -/
theorem bild_wurzel_ok {P : Programm D} {O : Orakel D} {passes : Nat} {fs : List D.Fn} {pos : D.Fn → Nat}
    {name : D.Fn → String} {main : D.Fn} {roots : List D.Fn} {Ks : Nat} {Y : Nat → Lay D} {b : Bild D}
    (hb : bild P Y fs pos name main roots Ks = .ok b) (hfs : ∀ g, fs[pos g]? = some g)
    (hYin : ∀ x, (Y x).hi < 2 ^ 31 → LayIn (Y x)) (hYdis : ∀ x, LayDis (Y x)) (hYord : ∀ x, (Y x).lo ≤ (Y x).hi)
    (hYsync : ∀ x, LaySync (Y x)) {m : Runner.Mem} (hm : BytesAt m Runner.Prog.IMG b.bytes) (j : Nat) (hj : j < roots.length) (σ : World D)
    (ρ : Env D (D.params roots[j])) (hWa : WeltAt m b.Y σ) (hT : TorOK b.Y O) (hV : SichtOK O) :
    match rufAt P O passes b.depth roots[j] σ ρ with
    | .ok _ _ => ∃ t' m' q, Star ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * roots.length + startLen + startLen * j)),
        BitVec.ofNat 64 (b.fp0 + 8 * (b.Ks * (j + 1)))⟩ m t' m' ∧ StopAt t' m' q ∧ q.nr = 60
    | .logik e => Stops ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * roots.length + startLen + startLen * j)),
        BitVec.ofNat 64 (b.fp0 + 8 * (b.Ks * (j + 1)))⟩ m (logikCode e)
    | .hardware e => Stops ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * roots.length + startLen + startLen * j)),
        BitVec.ofNat 64 (b.fp0 + 8 * (b.Ks * (j + 1)))⟩ m (hwCode e)
    | _ => False := by
  obtain ⟨cs, body, sp, hl, hc, _⟩ := bild_lage hb hfs hYin hYdis hYord hYsync
  have hm2 := bild_bytes hm
  rw [hc] at hm2
  exact bild_wurzel (hT := hT) (hV := hV) (passes := passes) hl hm2 j hj σ ρ hWa

end Gabbro.Stage0.Senke
