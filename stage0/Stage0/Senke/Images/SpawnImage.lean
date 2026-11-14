/-
  File:      stage0/Stage0/Senke/Images/SpawnImage.lean
  Subject:   The startup's spawns read by the kernel's answers (premise (d) for Stage-0 images, plan A5).

  `Start.lean` proves the startup of a spawn site for EVERY answer the kernel may give (`spawn1_cases`) and under
  the one named environment assumption `CloneAnswers` the disjunction "all sites run through, or the process stops
  with `cloneCode`" (`spawnC_ok`). This module reads that dichotomy from the kernel's side, for the image the
  builder emitted:
  * `bild_initialized_spawned_u`: a kernel that answers every `clone` with a thread id (a positive word) lets the
    main thread run through all spawn sites; the j-th site spawns exactly the thread whose entry state
    `bild_wurzel` proves (`BildLage.spawn_entry`);
  * `bild_initialized_refused_u`: a kernel that refuses every `clone` (a negative word) lets the main thread stop
    at the first site with the declared exit code `cloneCode`.
  Neither says which kernel the host is: the disjunction under `CloneAnswers` is `bild_kern`. A refused thread
  creation is therefore a declared stop of the image, never a silently missing root.
-/
module
public import Stage0.Senke.Images.InitialExecution
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration}
variable {P : Programm D} {passes : Nat} {fs : List D.Fn} {pos : D.Fn → Nat} {main : D.Fn}
  {roots : List D.Fn} {K Ks : Nat} {Yb : Lay D} {A : D.Fn → Nat} {cs : List (List II × Nat)} {body : List II}
  {n fp0 : Nat} {sp : List (Nat × Nat)} {rootArgs : List (List Runner.W)} {tail : List Runner.B}

/-- **Every kernel answer is a thread id**: the spawn sites of the startup are run through, one after the other,
    and only the frame's scratch slots from `s` on change. -/
theorem spawnC_created [CloneAnswers] {fp : Runner.W} {K s : Nat} (hK : s + 8 ≤ K) (hK2 : K < 2 ^ 31)
    (hcreate : ∀ (m : Runner.Mem) (r x : Runner.W), r ≠ 0 → Kern.ans Runner.cloneReq m (some (r, x)) m → 0 < r.toInt) :
    (l : List (Nat × Nat)) → (∀ x ∈ l, x.1 < 2 ^ 31 ∧ x.2 < 2 ^ 31) → (m : Runner.Mem) → (pc : Runner.W) →
    CodeAt m pc (spawnC s l) → FrameOK m fp K → CodeFar pc (spawnC s l).length fp K →
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (spawnC s l).length), fp⟩ m' ∧ Agree fp s K m m'
  | [], _, m, pc, _, _, _ => ⟨m, by simpa [spawnC] using Star.refl _ m, Agree.refl _ _ _ _⟩
  | (a, f) :: r, hl, m, pc, hc, hF, hcf => by
    have h0 := hl (a, f) (by simp)
    have hc' : CodeAt m pc (spawnOne s a f ++ spawnC s r) := hc
    have hcf' : CodeFar pc ((spawnOne s a f).length + (spawnC s r).length) fp K := by
      have h := hcf
      rw [spawnC_cons, List.length_append] at h
      exact h
    rw [spawnOne_len] at hcf'
    obtain ⟨m2, _, _, hcases⟩ := spawn1_cases (codeAt_left hc') hF hK hK2 h0.1 h0.2 (codeFar_left hcf')
    obtain ⟨r0, x0, hr0, hk⟩ := CloneAnswers.ans m2
    obtain ⟨m1, s1, a1⟩ := (hcases r0 x0 hr0 hk).1 (hcreate m2 r0 x0 hr0 hk)
    have hc1 : CodeAt m1 (pc + BitVec.ofNat 64 (16 * 10)) (spawnC s r) := by
      have := (codeAt_right hc').agree a1 (codeFar_right (n := 10) (k := (spawnC s r).length) hcf')
      rwa [spawnOne_len] at this
    obtain ⟨m3, s2, a2⟩ := spawnC_created hK hK2 hcreate r (fun x hx => hl x (by simp [hx])) m1 _ hc1
      (hF.agree a1) (codeFar_right hcf')
    refine ⟨m3, s1.trans (star_cast s2 rfl ?_), a1.trans a2⟩
    simp only [T.mk.injEq, and_true, spawnC_cons, List.length_append, spawnOne_len, addr_norm]
    congr 2
    omega

/-- **Every kernel answer is a refusal** (a word that is not 0 and not positive): the first spawn site stops the
    process with the declared `cloneCode`. -/
theorem spawnC_refused [CloneAnswers] {fp : Runner.W} {K s : Nat} (hK : s + 8 ≤ K) (hK2 : K < 2 ^ 31)
    (hrefuse : ∀ (m : Runner.Mem) (r x : Runner.W), r ≠ 0 → Kern.ans Runner.cloneReq m (some (r, x)) m → r.toInt ≤ 0)
    {a f : Nat} {l : List (Nat × Nat)} (ha : a < 2 ^ 31) (hf : f < 2 ^ 31) {m : Runner.Mem} {pc : Runner.W}
    (hc : CodeAt m pc (spawnC s ((a, f) :: l))) (hF : FrameOK m fp K)
    (hcf : CodeFar pc (spawnC s ((a, f) :: l)).length fp K) : Stops ⟨pc, fp⟩ m cloneCode := by
  have hc' : CodeAt m pc (spawnOne s a f ++ spawnC s l) := hc
  have hcf' : CodeFar pc ((spawnOne s a f).length + (spawnC s l).length) fp K := by
    have h := hcf
    rw [spawnC_cons, List.length_append] at h
    exact h
  rw [spawnOne_len] at hcf'
  obtain ⟨m2, _, _, hcases⟩ := spawn1_cases (codeAt_left hc') hF hK hK2 ha hf (codeFar_left hcf')
  obtain ⟨r0, x0, hr0, hk⟩ := CloneAnswers.ans m2
  exact (hcases r0 x0 hr0 hk).2 (hrefuse m2 r0 x0 hr0 hk)

omit [Kern] in
/-- The j-th spawn site spawns the thread whose entry state `bild_wurzel` proves for root `j`: its start code and
    its own stack frame. -/
theorem BildLage.spawn_entry (h : BildLage passes P fs pos main roots K Ks Yb A cs body n fp0 sp ρ rootArgs)
    (j : Nat) (hj : j < roots.length) :
    sp[j]? = some (codeBase + 16 * (10 * roots.length + startLen + startLen * j), fp0 + 8 * (Ks * (j + 1))) := by
  rw [h.hsp]
  simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some]

omit [Kern] in
theorem BildLage.spawn_length (h : BildLage passes P fs pos main roots K Ks Yb A cs body n fp0 sp ρ rootArgs) :
    sp.length = roots.length := by
  rw [h.hsp]; simp only [List.length_map, List.length_range]

/-- What the startup's spawn sites need of the loaded image. -/
theorem spawn_ready {ρ : Env D (D.params main)}
    (h : BildLage passes P fs pos main roots K Ks Yb A cs body n fp0 sp ρ rootArgs) {m : Runner.Mem}
    (hm : BytesAt m codeBase ((spawnC (startScratch main) sp ++ startC A main n 231 true ++ rootsC A n roots ++
      body).flatMap encII ++ ((startStackBytes Ks (FB + FB) (encodeEnv Yb ρ :: rootArgs)).getD [] ++ tail))) :
    CodeAt m (BitVec.ofNat 64 codeBase) (spawnC (startScratch main) sp) ∧ FrameOK m (BitVec.ofNat 64 fp0) Ks ∧
    (∀ x ∈ sp, x.1 < 2 ^ 31 ∧ x.2 < 2 ^ 31) ∧
    CodeFar (BitVec.ofNat 64 codeBase) (spawnC (startScratch main) sp).length (BitVec.ofNat 64 fp0) Ks ∧
    startScratch main + 8 ≤ Ks ∧ Ks < 2 ^ 31 := by
  obtain ⟨c1, c2, c3, ⟨stackBytes, madeStacks, loadedStacks⟩, _⟩ := h.code hm
  obtain ⟨frame, made, hframe⟩ := startStackBytes_frame madeStacks fp0 loadedStacks 0 (by simp)
  simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero] at made hframe
  have hfit := h.hfit
  have hex := h.hex main (by simp)
  have hylo := h.hylo
  have hyhi := h.hyhi
  have hs : Ks * (roots.length + 1) = Ks * roots.length + Ks := Nat.mul_succ Ks _
  have hK : Ks ≤ K := by
    have := Nat.le_mul_of_pos_right Ks (Nat.succ_pos roots.length); have := h.hyord; omega
  have hge := startScratch_ge main
  have hF0 : FrameOK m (BitVec.ofNat 64 fp0) Ks := startFrameBytes_frame made hframe (by omega)
  have hfp := h.hfp
  have hcb : codeBase = 268435472 := rfl
  have hsl8 : startLen = 8 := rfl
  simp only [headLen, startLen] at hfp
  have hcS : CodeAt m (BitVec.ofNat 64 codeBase) (spawnC (startScratch main) sp) := codeAt_left (codeAt_left c3)
  have hsl : (spawnC (startScratch main) sp).length = 10 * roots.length := by rw [spawnC_len, h.hsp]; simp
  have hspb : ∀ x ∈ sp, x.1 < 2 ^ 31 ∧ x.2 < 2 ^ 31 := by
    intro x hx
    rw [h.hsp] at hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have : Ks * (j + 1) ≤ Ks * roots.length := Nat.mul_le_mul_left Ks (by omega)
    have := h.hyord
    simp only [startLen]
    constructor <;> omega
  exact ⟨hcS, hF0, hspb, codeFar_nat' (by rw [hsl]; omega) (by omega), by omega, by omega⟩

/-- **Premise (d) at the first instruction, kernel that creates threads.** From the initialized payload, if the
    kernel answers every `clone` with a thread id, `main`'s thread runs through the spawn sites of all roots and
    stands in front of `main`'s start code (only scratch slots of its frame changed). The j-th site spawned the
    thread of `BildLage.spawn_entry`. -/
theorem bild_initialized_spawned_u [CloneAnswers] {u : UProg} {P : Programm (declOf u)}
    {passes : Nat} {fs : List (declOf u).Fn}
    {pos : (declOf u).Fn → Nat} {name : (declOf u).Fn → String} {main : (declOf u).Fn}
    {ρ : Env (declOf u) ((declOf u).params main)}
    {starts : List (Σ f : (declOf u).Fn, Env (declOf u) ((declOf u).params f))}
    {Ks req : Nat} {tor : (declOf u).Ax → Option TorB} {b : Bild (declOf u)}
    (valid : GabbroV.sp0OkB u = true)
    (hb : bild passes P (layU u tor) fs pos name main ρ starts Ks req = .ok b)
    (hfs : ∀ g, fs[pos g]? = some g) {m : Runner.Mem}
    (loaded : BytesAt m Runner.Prog.IMG (b.initializedBytes u valid))
    (hcreate : ∀ (m' : Runner.Mem) (r x : Runner.W), r ≠ 0 → Kern.ans Runner.cloneReq m' (some (r, x)) m' →
      0 < r.toInt) :
    ∃ m1, Star ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 b.fp0⟩ m
      ⟨BitVec.ofNat 64 (codeBase + 16 * (10 * starts.length)), BitVec.ofNat 64 b.fp0⟩ m1 ∧
      Agree (BitVec.ofNat 64 b.fp0) (startScratch main) b.Ks m m1 := by
  obtain ⟨_, _, _, stackPayload, made, _, _, startup, _⟩ := bild_initialized_loaded_u valid hb hfs loaded
  obtain ⟨cs, body, sp, h, code, roots, args, rootArgs⟩ := bild_lage hb hfs
    (fun base bound => layU_in u tor base bound) (fun base => layU_dis u tor base)
    (fun base => by simp only [layU]; omega) (fun base => layU_sync u tor base)
  have startup' : BytesAt m codeBase (b.code.flatMap encII ++
      ((startStackBytes b.Ks (FB + FB) (b.args :: b.rootArgs)).getD [] ++ [])) := by
    simpa only [made, Option.getD_some, List.append_nil] using startup
  rw [code, args, rootArgs] at startup'
  obtain ⟨hcS, hF0, hspb, hcf, hsc, hK2⟩ := spawn_ready h startup'
  obtain ⟨m1, s1, a1⟩ := spawnC_created (s := startScratch main) hsc hK2 hcreate sp hspb m _ hcS hF0 hcf
  have hsl : (spawnC (startScratch main) sp).length = 10 * starts.length := by
    rw [spawnC_len, h.spawn_length]; simp
  refine ⟨m1, ?_, a1⟩
  rw [show BitVec.ofNat 64 codeBase + BitVec.ofNat 64 (16 * (spawnC (startScratch main) sp).length) =
    BitVec.ofNat 64 (codeBase + 16 * (10 * starts.length)) by rw [ofNat_add64, hsl]] at s1
  exact s1

/-- **Premise (d) at the first instruction, kernel that refuses threads.** If the kernel refuses every `clone`
    and the program declares a root, `main`'s thread stops with the declared `cloneCode` (nothing else of the image
    ran, no root thread exists). -/
theorem bild_initialized_refused_u [CloneAnswers] {u : UProg} {P : Programm (declOf u)}
    {passes : Nat} {fs : List (declOf u).Fn}
    {pos : (declOf u).Fn → Nat} {name : (declOf u).Fn → String} {main : (declOf u).Fn}
    {ρ : Env (declOf u) ((declOf u).params main)}
    {starts : List (Σ f : (declOf u).Fn, Env (declOf u) ((declOf u).params f))}
    {Ks req : Nat} {tor : (declOf u).Ax → Option TorB} {b : Bild (declOf u)}
    (valid : GabbroV.sp0OkB u = true)
    (hb : bild passes P (layU u tor) fs pos name main ρ starts Ks req = .ok b)
    (hfs : ∀ g, fs[pos g]? = some g) {m : Runner.Mem}
    (loaded : BytesAt m Runner.Prog.IMG (b.initializedBytes u valid)) (hroot : starts ≠ [])
    (hrefuse : ∀ (m' : Runner.Mem) (r x : Runner.W), r ≠ 0 → Kern.ans Runner.cloneReq m' (some (r, x)) m' →
      r.toInt ≤ 0) :
    Stops ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 b.fp0⟩ m cloneCode := by
  obtain ⟨_, _, _, stackPayload, made, _, _, startup, _⟩ := bild_initialized_loaded_u valid hb hfs loaded
  obtain ⟨cs, body, sp, h, code, roots, args, rootArgs⟩ := bild_lage hb hfs
    (fun base bound => layU_in u tor base bound) (fun base => layU_dis u tor base)
    (fun base => by simp only [layU]; omega) (fun base => layU_sync u tor base)
  have startup' : BytesAt m codeBase (b.code.flatMap encII ++
      ((startStackBytes b.Ks (FB + FB) (b.args :: b.rootArgs)).getD [] ++ [])) := by
    simpa only [made, Option.getD_some, List.append_nil] using startup
  rw [code, args, rootArgs] at startup'
  obtain ⟨hcS, hF0, hspb, hcf, hsc, hK2⟩ := spawn_ready h startup'
  have hlen : 0 < sp.length := by
    rw [h.spawn_length, List.length_map]
    exact List.length_pos_iff.mpr hroot
  obtain ⟨⟨a, f⟩, l, hsp⟩ := List.exists_cons_of_length_pos hlen
  rw [hsp] at hcS hcf hspb
  have hbd := hspb (a, f) (by simp)
  exact spawnC_refused (s := startScratch main) hsc hK2 hrefuse hbd.1 hbd.2 hcS hF0 hcf

end Gabbro.Stage0.Senke
