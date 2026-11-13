/- Checked image layout and initialized stacks for every root occurrence. -/
module
public import Stage0.Senke.Images.StartupCode
public import Stage0.Senke.Images.StartupBytes
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration}
variable {P : Programm D} {O : Orakel D} {passes : Nat} {fs : List D.Fn} {pos : D.Fn → Nat} {main : D.Fn}
  {roots : List D.Fn} {K Ks : Nat} {Yb : Lay D} {A : D.Fn → Nat} {cs : List (List II × Nat)} {body : List II}
  {n fp0 : Nat} {sp : List (Nat × Nat)} {rootArgs : List (List Runner.W)}

/-- What `bild` lays out, as hypotheses on one image. -/
structure BildLage (passes : Nat) (P : Programm D) (fs : List D.Fn) (pos : D.Fn → Nat) (main : D.Fn) (roots : List D.Fn)
    (K Ks : Nat) (Yb : Lay D) (A : D.Fn → Nat) (cs : List (List II × Nat)) (body : List II) (n fp0 : Nat)
    (sp : List (Nat × Nat)) (ρ : Env D (D.params main)) (rootArgs : List (List Runner.W)) : Prop where
  hfa : Yb.fa = A
  hbody : body = cs.flatMap (·.1)
  hdepth : n = depthOf Ks (maxTop cs)
  hsp : sp = (List.range roots.length).map fun j =>
    (codeBase + 16 * (3 * roots.length + startLen + startLen * j), fp0 + 8 * (Ks * (j + 1)))
  hfp : fp0 = codeBase + 16 * (headLen roots.length + body.length)
  haddr : ∀ g, A g = (addrs (codeBase + 16 * headLen roots.length) (cs.map (·.1.length))).getD (pos g) 0
  hlen : cs.length = fs.length
  hlow : ∀ i (hi : i < fs.length) (hc : i < cs.length), lowFun passes P A Yb fs[i] = some cs[i]
  hpos : ∀ g, fs[pos g]? = some g
  hargsLength : rootArgs.length = roots.length
  hargsFit : ∀ words ∈ rootArgs, FB + FB + words.length ≤ Ks
  hwhy : D.gruende main = 0
  hrwhy : roots.all (fun f => decide (D.gruende f = 0)) = true
  hfit : fp0 + 8 * K < 2 ^ 31
  hroom : FB + 2 * maxTop cs ≤ Ks
  hex : ∀ f ∈ main :: roots, startScratch f + 8 ≤ Ks
  hylo : fp0 + 8 * (Ks * (roots.length + 1)) ≤ Yb.lo
  hyhi : Yb.hi ≤ fp0 + 8 * K
  hyord : Yb.lo ≤ Yb.hi
  hlay : LayIn Yb
  hdis : LayDis Yb
  hsb : Yb.sb = fp0
  hst : Yb.st = 8 * Ks
  hsync : LaySync Yb
  hysye : Yb.sye ≤ fp0 + 8 * K
  hops : (spawnC (startScratch main) sp ++ startC A main n 231 true ++ rootsC A n roots ++ body).all
    (fun i => decide (i.o < 256)) = true

omit [Kern] in
theorem BildLage.head (h : BildLage passes P fs pos main roots K Ks Yb A cs body n fp0 sp ρ rootArgs) :
    (spawnC (startScratch main) sp ++ startC A main n 231 true ++ rootsC A n roots).length = headLen roots.length := by
  rw [h.hsp]
  simp only [List.length_append, spawnC_len, List.length_map, List.length_range, startC_len, rootsC_len, headLen]

omit [Kern] in
/-- Every admitted start serializes successfully; the complete stack band has exactly
    the byte length reserved by the source-independent image geometry. -/
theorem BildLage.stacks (h : BildLage passes P fs pos main roots K Ks Yb A cs body n fp0 sp ρ rootArgs) :
    ∃ stackBytes, startStackBytes Ks (FB + FB) (encodeEnv Yb ρ :: rootArgs) = some stackBytes ∧
      stackBytes.length = 8 * (Ks * (roots.length + 1)) := by
  have hexm := h.hex main (by simp)
  have hge : FB + FB + contextWords (D.params main) + 1 ≤ startScratch main := by
    rw [startScratch_eq]
    omega
  obtain ⟨stackBytes, made⟩ := startStackBytes_some (slots := Ks) (base := FB + FB) (encodeEnv Yb ρ :: rootArgs)
    (by
      intro words member
      rcases List.mem_cons.mp member with rfl | member
      · rw [encodeEnv_length]; omega
      · exact h.hargsFit words member)
  refine ⟨stackBytes, made, ?_⟩
  simpa only [List.length_cons, h.hargsLength, Nat.mul_assoc] using startStackBytes_length made

/-- The functions of an image and their code below the stacks. -/
theorem BildLage.code (h : BildLage passes P fs pos main roots K Ks Yb A cs body n fp0 sp ρ rootArgs)
    {m : Runner.Mem} {tail : List Runner.B}
    (hm : BytesAt m codeBase ((spawnC (startScratch main) sp ++ startC A main n 231 true ++ rootsC A n roots ++ body).flatMap encII ++
      ((startStackBytes Ks (FB + FB) (encodeEnv Yb ρ :: rootArgs)).getD [] ++ tail))) :
    let C : D.Fn → List II := fun g => ((cs[pos g]?).map (·.1)).getD []
    (∀ g, ∃ top, lowFun passes P A Yb g = some (C g, top) ∧ top ≤ maxTop cs) ∧
    (∀ g, CodeAt m (BitVec.ofNat 64 (A g)) (C g) ∧ A g + 16 * (C g).length ≤ fp0) ∧
    CodeAt m (BitVec.ofNat 64 codeBase) (spawnC (startScratch main) sp ++ startC A main n 231 true ++ rootsC A n roots) ∧
    (∃ stackBytes, startStackBytes Ks (FB + FB) (encodeEnv Yb ρ :: rootArgs) = some stackBytes ∧
      BytesAt m fp0 stackBytes) ∧
    BytesAt m (fp0 + 8 * (Ks * (roots.length + 1))) tail := by
  intro C
  have hl := h.head
  obtain ⟨c1, c2, c3⟩ := bild_code (C := C) (fp0 := fp0) (fun _ => rfl) h.hbody (by rw [hl]; exact h.hfp)
    (by rw [hl]; exact h.haddr) h.hlen h.hlow h.hpos h.hops hm.left
  have hz := hm.right
  rw [flatMap_enc_len, List.length_append, hl] at hz
  rw [show codeBase + 16 * (headLen roots.length + body.length) = fp0 from h.hfp.symm] at hz
  obtain ⟨stackBytes, made, _⟩ := h.stacks
  rw [made, Option.getD_some] at hz
  refine ⟨c1, c2, c3, ⟨stackBytes, made, hz.left⟩, ?_⟩
  have tail := startStackBytes_tail made hz
  simpa only [List.length_cons, h.hargsLength, Nat.mul_assoc] using tail

/-- The world above the stacks, for the frame of stack `j`. -/
theorem BildLage.win (h : BildLage passes P fs pos main roots K Ks Yb A cs body n fp0 sp ρ rootArgs) {j : Nat}
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

/-- The ticket-lock invariant of a thread that holds no lock, from the unchanged zero lock span above the
    typed world (next = serving = 0, no waiters). Only these bytes must be zero; initialized source memory is
    unrestricted. -/
theorem BildLage.sync (h : BildLage passes P fs pos main roots K Ks Yb A cs body n fp0 sp ρ rootArgs) {m : Runner.Mem}
    (hz : BytesAt m Yb.hi (List.replicate (Yb.sye - Yb.hi) 0)) {j : Nat} (hj : j ≤ roots.length) :
    TicketSync m Yb (BitVec.ofNat 64 (fp0 + 8 * (Ks * j))) Ks [] := by
  have hs : Ks * (roots.length + 1) = Ks * roots.length + Ks := Nat.mul_succ Ks _
  have hm : Ks * j ≤ Ks * roots.length := Nat.mul_le_mul_left Ks hj
  have hylo := h.hylo; have hyhi := h.hyhi; have hfit := h.hfit; have hyord := h.hyord
  have hroom := h.hroom; have hmt := maxTop_pos cs; have hsye := h.hysye
  have hKs : Ks ≤ K := by have := Nat.le_mul_of_pos_right Ks (Nat.succ_pos roots.length); omega
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
    exact (zero_word hz (by omega) (by omega) (by omega)).2
  · have := hl.1 Lk
    exact ⟨0, 0, (zero_word hz (by omega) (by omega) (by omega)).1, (zero_word hz (by omega) (by omega) (by omega)).1,
      (zero_word hz (by omega) (by omega) (by omega)).1, fun hin => (List.not_mem_nil hin).elim, fun _ => rfl⟩

end Gabbro.Stage0.Senke
