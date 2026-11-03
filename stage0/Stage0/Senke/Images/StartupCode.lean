/- Shared code-location and frame facts for the single image startup path. -/
module
public import Stage0.Senke.Start
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern]
variable {D : Deklaration} {passes : Nat}

theorem leN_len (n v : Nat) : (Runner.Prog.leN n v).length = n := by simp [Runner.Prog.leN]

/-- The image's first word is the first frame: the loader starts the IR thread at `⟨IMG + 16, fp0⟩`. -/
theorem bild_kopf {b : Bild D} {m : Runner.Mem} (hm : BytesAt m Runner.Prog.IMG b.bytes) (hfp : b.fp0 < 2 ^ 64) :
    m.rd64 (BitVec.ofNat 64 Runner.Prog.IMG) = some (BitVec.ofNat 64 b.fp0) := by
  simp only [Bild.bytes, List.append_assoc] at hm
  exact rd64_leN hm hfp

theorem encErg_none {e : Option Ty} (h : e = none) (v : ErgVal D e) (w : Runner.W) : ExitErg Yb e v w := by
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
    (hcs : ∀ i (hi : i < fs.length) (hc : i < cs.length), lowFun passes P A Yb fs[i] = some cs[i])
    (hfs : ∀ g, fs[pos g]? = some g) (hops : (hd ++ body).all (fun i => decide (i.o < 256)) = true)
    {m : Runner.Mem} (hcode : BytesAt m codeBase ((hd ++ body).flatMap encII)) :
    (∀ g, ∃ top, lowFun passes P A Yb g = some (C g, top) ∧ top ≤ maxTop cs) ∧
    (∀ g, CodeAt m (BitVec.ofNat 64 (A g)) (C g) ∧ A g + 16 * (C g).length ≤ fp0) ∧
    CodeAt m (BitVec.ofNat 64 codeBase) hd := by
  rw [List.flatMap_append] at hcode
  have hSb := hcode.left
  have hBb := hcode.right
  rw [flatMap_enc_len] at hBb
  rw [List.all_append, Bool.and_eq_true] at hops
  have hpos : ∀ g, ∃ h : pos g < cs.length, lowFun passes P A Yb g = some cs[pos g] ∧ C g = cs[pos g].1 := by
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

/-- A frame whose parameter span and header lie below the changed slots keeps its words. -/
theorem wordsAt_frame_agree {m m' : Runner.Mem} {fp : Runner.W} {lo K F base : Nat} {ws : List Runner.W}
    (h : WordsAt m (slot fp (BitVec.ofNat 64 F)) base ws) (a : Agree fp lo K m m')
    (room : fp.toNat + 8 * K ≤ 2 ^ 64) (below : F + base + ws.length ≤ lo) (inside : lo ≤ K) :
    WordsAt m' (slot fp (BitVec.ofNat 64 F)) base ws := by
  intro i hi
  have read := h i hi
  rw [slot_slot] at read ⊢
  rw [agree_rd_low a room (by omega) inside]
  exact read

/-- A root without parameters has no parameter word and no variable. -/
theorem emptyParams_env {f : D.Fn} (hp : (D.params f).isEmpty = true) (L : Lay D) (ρ : Env D (D.params f))
    (m : Runner.Mem) (fp : Runner.W) (base : Nat) :
    (∀ τ (x : Var (D.params f) τ), ValueValid L τ (ρ.get x)) ∧ WordsAt m fp base (encodeEnv L ρ) := by
  have np : contextWords (D.params f) = 0 := by
    cases hq : D.params f with
    | nil => rfl
    | cons a l => rw [hq] at hp; simp at hp
  refine ⟨fun τ x => ?_, fun i hi => ?_⟩
  · exfalso
    have := variableOffset_bound x
    have := valueWords_pos τ
    omega
  · rw [encodeEnv_length] at hi
    omega

/-- A frame offered `base + words` slots has bytes for the words. -/
theorem startFrameBytes_some {slots base : Nat} {words : List Runner.W} (room : base + words.length ≤ slots) :
    ∃ bytes, startFrameBytes slots base words = some bytes := by
  unfold startFrameBytes
  simp only [room, ↓reduceIte]
  exact ⟨_, rfl⟩

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

end Gabbro.Stage0.Senke
