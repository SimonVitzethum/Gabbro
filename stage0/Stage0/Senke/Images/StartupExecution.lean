/- Main and root execution from the same initialized image stacks. -/
module
public import Stage0.Senke.Images.StartupLayout
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration}
variable {P : Programm D} {O : Orakel D} {passes : Nat} {fs : List D.Fn} {pos : D.Fn → Nat} {main : D.Fn}
  {roots : List D.Fn} {K Ks : Nat} {Yb : Lay D} {A : D.Fn → Nat} {cs : List (List II × Nat)} {body : List II}
  {n fp0 : Nat} {sp : List (Nat × Nat)} {rootArgs : List (List Runner.W)} {tail : List Runner.B}

/-- **`main`'s thread**: the spawns of the roots, then `main` as `rufAt n main`, then `exit_group`. -/
theorem bild_kern [CloneOK] {O : Orakel D} [hT : TorOK Yb O] [hV : SichtOK O] {passes : Nat} {ρ : Env D (D.params main)}
    (h : BildLage passes P fs pos main roots K Ks Yb A cs body n fp0 sp ρ rootArgs) {m : Runner.Mem}
    (hm : BytesAt m codeBase ((spawnC (startScratch main) sp ++ startC A main n 231 true ++ rootsC A n roots ++ body).flatMap encII ++
      ((startStackBytes Ks (FB + FB) (encodeEnv Yb ρ :: rootArgs)).getD [] ++ tail)))
    (hval : ∀ τ (x : Var (D.params main) τ), ValueValid Yb τ (ρ.get x))
    (σ : World D) (hWa : WeltAt m Yb σ) (hy : SyncOK m Yb (BitVec.ofNat 64 fp0) Ks) :
    match rufAt P O passes n main σ ρ with
    | .ok _ v => ∃ t' m' q, Star ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 fp0⟩ m t' m' ∧ StopAt t' m' q ∧
        q.nr = BitVec.ofNat 64 231 ∧ ExitErg Yb (D.erg main) v q.a1
    | .logik e => Stops ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 fp0⟩ m (logikCode e)
    | .hardware e => Stops ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 fp0⟩ m (hwCode e)
    | _ => False := by
  obtain ⟨c1, c2, c3, ⟨stacks, madeStacks, loadedStacks⟩, _⟩ := h.code hm
  obtain ⟨frame, made, hframe⟩ := startStackBytes_frame madeStacks fp0 loadedStacks 0 (by simp)
  simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero] at made hframe
  have hfit := h.hfit
  have hroom := h.hroom
  have hex := h.hex main (by simp)
  have hylo := h.hylo
  have hyhi := h.hyhi
  have hs : Ks * (roots.length + 1) = Ks * roots.length + Ks := Nat.mul_succ Ks _
  have hK : Ks ≤ K := by
    have := Nat.le_mul_of_pos_right Ks (Nat.succ_pos roots.length); have := h.hyord; omega
  have hge := startScratch_ge main
  have hF0 : FrameOK m (BitVec.ofNat 64 fp0) Ks := startFrameBytes_frame made hframe (by omega)
  have hρ : WordsAt m (slot (BitVec.ofNat 64 fp0) (BitVec.ofNat 64 FB)) FB (encodeEnv Yb ρ) :=
    startEnvBytes_words (reserved := 0) Yb ρ made hframe
  have hW0 : WIn Yb (BitVec.ofNat 64 fp0) Ks Ks := by simpa using h.win (j := 0) (Nat.zero_le _)
  have hfp := h.hfp
  have hcb : codeBase = 268435472 := rfl
  have hsl8 : startLen = 8 := rfl
  simp only [headLen, startLen] at hfp
  have hl := h.head
  -- the spawns
  have hcS : CodeAt m (BitVec.ofNat 64 codeBase) (spawnC (startScratch main) sp) := codeAt_left (codeAt_left c3)
  have hsl : (spawnC (startScratch main) sp).length = 3 * roots.length := by rw [spawnC_len, h.hsp]; simp
  have hspb : ∀ x ∈ sp, x.1 < 2 ^ 31 ∧ x.2 < 2 ^ 31 := by
    intro x hx
    rw [h.hsp] at hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have : Ks * (j + 1) ≤ Ks * roots.length := Nat.mul_le_mul_left Ks (by omega)
    have := h.hyord
    simp only [startLen]
    constructor <;> omega
  obtain ⟨m1, s1, a1⟩ := spawnC_ok (fp := BitVec.ofNat 64 fp0) (K := Ks) (s := startScratch main) (by omega) (by omega)
    sp hspb m _ hcS hF0
    (codeFar_nat' (by rw [hsl]; omega) (by omega))
  -- `main`
  have hcM : CodeAt m (BitVec.ofNat 64 (codeBase + 16 * (3 * roots.length))) (startC A main n 231 true) := by
    have := codeAt_right (codeAt_left (a := spawnC (startScratch main) sp ++ startC A main n 231 true) c3)
    rw [ofNat_add64, hsl] at this
    exact this
  have hcM1 := hcM.agree a1 (codeFar_nat' (by rw [startC_len]; simp only [startLen]; omega) (by omega))
  have hPC : PCode m1 A (fun g => ((cs[pos g]?).map (·.1)).getD []) (BitVec.ofNat 64 fp0) Ks := fun g =>
    ⟨(c2 g).1.agree a1 (codeFar_nat' (c2 g).2 (by omega)), codeFar_nat' (c2 g).2 (by omega)⟩
  have hst := start_ok (Y := Yb) (P := P) (O := O) (passes := passes) (f := main) (e := 231) (keep := true)
    (pc := codeBase + 16 * (3 * roots.length)) (fpI := fp0) (m := m1) h.hfa c1
    (fun g => by have := (c2 g).2; dsimp only at this ⊢; omega) (fun g => by have := (c2 g).2; dsimp only at this ⊢; omega) h.hwhy hroom hex
    (maxTop_pos cs) h.hdepth (by decide) (by omega) hcM1 (by simp only [startLen]; omega)
    (hF0.agree a1) hPC hW0 σ ρ hval
    (wordsAt_frame_agree (base := FB) hρ a1 hF0.room (by rw [encodeEnv_length]; omega) (by omega))
    (weltAt_stab hW0.lay hW0.top m m1 hWa (a1.mono (Nat.zero_le _)))
    (hy.agree a1
      (by have := hW0.top; have := hW0.ord; omega))
  rw [show BitVec.ofNat 64 codeBase + BitVec.ofNat 64 (16 * (spawnC (startScratch main) sp).length) =
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
theorem bild_wurzel {O : Orakel D} [hT : TorOK Yb O] [hV : SichtOK O] {passes : Nat} {ρm : Env D (D.params main)}
    (h : BildLage passes P fs pos main roots K Ks Yb A cs body n fp0 sp ρm rootArgs) {m : Runner.Mem}
    (hm : BytesAt m codeBase ((spawnC (startScratch main) sp ++ startC A main n 231 true ++ rootsC A n roots ++ body).flatMap encII ++
      ((startStackBytes Ks (FB + FB) (encodeEnv Yb ρm :: rootArgs)).getD [] ++ tail)))
    (j : Nat) (hj : j < roots.length) (σ : World D) (ρ : Env D (D.params (getElem roots j hj)))
    (hargs : rootArgs[j]'(by rw [h.hargsLength]; exact hj) = encodeEnv Yb ρ)
    (hval : ∀ τ (x : Var (D.params roots[j]) τ), ValueValid Yb τ (ρ.get x))
    (hWa : WeltAt m Yb σ)
    (hy : SyncOK m Yb (BitVec.ofNat 64 (fp0 + 8 * (Ks * (j + 1)))) Ks) :
    match rufAt P O passes n (getElem roots j hj) σ ρ with
    | .ok _ _ => ∃ t' m' q, Star ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * roots.length + startLen + startLen * j)),
        BitVec.ofNat 64 (fp0 + 8 * (Ks * (j + 1)))⟩ m t' m' ∧ StopAt t' m' q ∧ q.nr = BitVec.ofNat 64 60
    | .logik e => Stops ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * roots.length + startLen + startLen * j)),
        BitVec.ofNat 64 (fp0 + 8 * (Ks * (j + 1)))⟩ m (logikCode e)
    | .hardware e => Stops ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * roots.length + startLen + startLen * j)),
        BitVec.ofNat 64 (fp0 + 8 * (Ks * (j + 1)))⟩ m (hwCode e)
    | _ => False := by
  obtain ⟨c1, c2, c3, ⟨stacks, madeStacks, loadedStacks⟩, _⟩ := h.code hm
  obtain ⟨frame, made, hframe⟩ := startStackBytes_frame madeStacks fp0 loadedStacks (j + 1)
    (by simp only [List.length_cons, h.hargsLength]; omega)
  simp only [List.getElem_cons_succ, hargs] at made
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
  have loadedFrame : BytesAt m (fp0 + 8 * (Ks * (j + 1))) frame := by
    simpa only [Nat.mul_assoc] using hframe
  have hF : FrameOK m (BitVec.ofNat 64 (fp0 + 8 * (Ks * (j + 1)))) Ks :=
    startFrameBytes_frame made loadedFrame (by omega)
  have hρ : WordsAt m (slot (BitVec.ofNat 64 (fp0 + 8 * (Ks * (j + 1)))) (BitVec.ofNat 64 FB))
      FB (encodeEnv Yb ρ) := startEnvBytes_words (reserved := 0) Yb ρ made loadedFrame
  have hsl : (spawnC (startScratch main) sp).length = 3 * roots.length := by rw [spawnC_len, h.hsp]; simp
  have hcR : CodeAt m (BitVec.ofNat 64 (codeBase + 16 * (3 * roots.length + startLen + startLen * j)))
      (startC A roots[j] n 60 false) := by
    have h1 := codeAt_right (a := spawnC (startScratch main) sp ++ startC A main n 231 true) c3
    rw [ofNat_add64, List.length_append, hsl, startC_len] at h1
    have := rootsC_at A n roots _ j hj h1
    rwa [show codeBase + 16 * (3 * roots.length + startLen) + 16 * (startLen * j) =
      codeBase + 16 * (3 * roots.length + startLen + startLen * j) by omega] at this
  have hPC : PCode m A (fun g => ((cs[pos g]?).map (·.1)).getD []) (BitVec.ofNat 64 (fp0 + 8 * (Ks * (j + 1)))) Ks :=
    fun g => ⟨(c2 g).1, codeFar_nat' (by have := (c2 g).2; dsimp only at this ⊢; omega) (by omega)⟩
  have hst := start_ok (Y := Yb) (P := P) (O := O) (passes := passes) (f := roots[j]) (e := 60) (keep := false)
    (m := m) h.hfa c1 (fun g => by have := (c2 g).2; dsimp only at this ⊢; omega) (fun g => by have := (c2 g).2; dsimp only at this ⊢; omega) (by have := List.all_eq_true.mp h.hrwhy roots[j] (List.getElem_mem hj); simpa using this) h.hroom
    (h.hex _ (List.mem_cons_of_mem _ (List.getElem_mem hj)))
    (maxTop_pos cs) h.hdepth (by decide) (by omega) hcR (by simp only [startLen]; omega)
    hF hPC (h.win (by omega)) σ ρ hval hρ hWa
    hy
  generalize rufAt P O passes n roots[j] σ ρ = o at hst ⊢
  cases o with
  | ok σ' v => obtain ⟨t', m', q, sx, hq, hnr, _⟩ := hst; exact ⟨t', m', q, sx, hq, hnr⟩
  | logik e => exact hst
  | hardware e => exact hst
  | why _ _ => exact hst.elim

end Gabbro.Stage0.Senke
