/- Builder-derived initialized image facts and execution, without an emitter dependency. -/
module
public import Stage0.Senke.Images.InitialRead
public import Stage0.Senke.Images.BildSatz
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR

variable [Kern]

/-- An accepted canonical builder and its single loaded initialized payload establish
    the exact source initial world, free locks for every stack, and the actual complete
    typed startup bytes. Every layout, capacity and serialization premise is derived
    from that builder; callers supply no independent memory or geometry witness. -/
theorem bild_initialized_loaded_u {u : UProg} {P : Programm (declOf u)} {passes : Nat}
    {fs : List (declOf u).Fn} {pos : (declOf u).Fn → Nat} {name : (declOf u).Fn → String}
    {main : (declOf u).Fn} {ρ : Env (declOf u) ((declOf u).params main)}
    {starts : List (Σ f : (declOf u).Fn, Env (declOf u) ((declOf u).params f))}
    {Ks req : Nat} {tor : (declOf u).Ax → Option TorB} {b : Bild (declOf u)}
    (valid : GabbroV.sp0OkB u = true)
    (hb : bild passes P (layU u tor) fs pos name main ρ starts Ks req = .ok b)
    (hfs : ∀ g, fs[pos g]? = some g) {m : Runner.Mem}
    (loaded : BytesAt m Runner.Prog.IMG (b.initializedBytes u valid)) :
    WeltAt m b.Y (initialWorld u valid) ∧
    BytesAt m b.Y.hi (List.replicate (b.Y.sye - b.Y.hi) 0) ∧
    (∀ j, j ≤ b.roots.length →
      SyncOK m b.Y (BitVec.ofNat 64 (b.fp0 + 8 * (b.Ks * j))) b.Ks) ∧
    ∃ stackPayload, startStackBytes b.Ks (FB + FB) (b.args :: b.rootArgs) = some stackPayload ∧
      stackPayload.length = 8 * (b.Ks * (b.roots.length + 1)) ∧
      BytesAt m Runner.Prog.IMG (Runner.Prog.leN 8 b.fp0 ++ Runner.Prog.leN 8 b.baseReq) ∧
      BytesAt m codeBase (b.code.flatMap encII ++ stackPayload) ∧ BytesAt m b.fp0 stackPayload := by
  obtain ⟨cs, body, sp, h, code, roots, args, rootArgs⟩ := bild_lage hb hfs
    (fun base bound => layU_in u tor base bound) (fun base => layU_dis u tor base)
    (fun base => by simp only [layU]; omega) (fun base => layU_sync u tor base)
  obtain ⟨stackPayload, made, length⟩ := h.stacks
  have actualStacks : startStackBytes b.Ks (FB + FB) (b.args :: b.rootArgs) = some stackPayload := by
    simpa only [args, rootArgs] using made
  have rootCount : b.rootArgs.length = b.roots.length := by
    simp only [rootArgs, roots, List.length_map]
  have codeLength : b.code.length = headLen (starts.map (·.1)).length + body.length := by
    rw [code, List.length_append, h.head]
  have codeEnd : b.fp0 = codeBase + 16 * b.code.length := by
    rw [codeLength]
    exact h.hfp
  have separate : b.fp0 + 8 * (b.Ks * (b.roots.length + 1)) ≤ b.Y.lo := by
    simpa only [roots] using h.hylo
  obtain ⟨header, startup, world, locks⟩ := b.initializedBytes_loaded valid (initialLayout_bild hb)
    actualStacks rootCount codeEnd separate h.hyhi h.hysye loaded
  have stackMemory := startup.right
  rw [flatMap_enc_len, ← codeEnd] at stackMemory
  refine ⟨world, locks, ?_, stackPayload, actualStacks, ?_, header, startup, stackMemory⟩
  · intro j hj
    exact h.sync locks (by simpa only [roots] using hj)
  · simpa only [roots] using length

/-- Every admitted start has its entire frame readable and writable in the same
    loaded initialized image. The builder supplies capacity and address bounds;
    the exact stack constructor supplies the frame bytes, including every root. -/
theorem bild_initialized_frames_u {u : UProg} {P : Programm (declOf u)} {passes : Nat}
    {fs : List (declOf u).Fn} {pos : (declOf u).Fn → Nat} {name : (declOf u).Fn → String}
    {main : (declOf u).Fn} {ρ : Env (declOf u) ((declOf u).params main)}
    {starts : List (Σ f : (declOf u).Fn, Env (declOf u) ((declOf u).params f))}
    {Ks req : Nat} {tor : (declOf u).Ax → Option TorB} {b : Bild (declOf u)}
    (valid : GabbroV.sp0OkB u = true)
    (hb : bild passes P (layU u tor) fs pos name main ρ starts Ks req = .ok b)
    (hfs : ∀ g, fs[pos g]? = some g) {m : Runner.Mem}
    (loaded : BytesAt m Runner.Prog.IMG (b.initializedBytes u valid)) :
    ∀ j, j ≤ b.roots.length →
      FrameOK m (BitVec.ofNat 64 (b.fp0 + 8 * (b.Ks * j))) b.Ks := by
  obtain ⟨_, _, _, stackPayload, made, _, _, _, stackMemory⟩ :=
    bild_initialized_loaded_u valid hb hfs loaded
  obtain ⟨cs, body, sp, h, _, roots, _, rootArgs⟩ := bild_lage hb hfs
    (fun base bound => layU_in u tor base bound) (fun base => layU_dis u tor base)
    (fun base => by simp only [layU]; omega) (fun base => layU_sync u tor base)
  have rootCount : b.rootArgs.length = b.roots.length := by
    simp only [rootArgs, roots, List.length_map]
  have separate : b.fp0 + 8 * (b.Ks * (b.roots.length + 1)) ≤ b.Y.lo := by
    simpa only [roots] using h.hylo
  have capacity : b.Ks * (b.roots.length + 1) ≤ b.K := by
    have := h.hyord
    have := h.hyhi
    omega
  intro j bound
  have index : j < (b.args :: b.rootArgs).length := by
    simp only [List.length_cons, rootCount]
    omega
  obtain ⟨frame, frameMade, frameMemory⟩ :=
    startStackBytes_frame made b.fp0 stackMemory j index
  have band : b.Ks * (j + 1) ≤ b.Ks * (b.roots.length + 1) :=
    Nat.mul_le_mul_left b.Ks (Nat.succ_le_succ bound)
  have room : b.fp0 + 8 * b.Ks * j + 8 * b.Ks < 2 ^ 64 := by
    have bytesBound : 8 * (b.Ks * (j + 1)) ≤ 8 * b.K :=
      Nat.mul_le_mul_left 8 (Nat.le_trans band capacity)
    have := h.hfit
    have endpoint : b.fp0 + 8 * b.Ks * j + 8 * b.Ks =
        b.fp0 + 8 * (b.Ks * (j + 1)) := by
      simp only [Nat.mul_succ, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
    rw [endpoint]
    omega
  have result := startFrameBytes_frame frameMade frameMemory room
  simpa only [Nat.mul_assoc] using result

omit [Kern] in
/-- Initialized payload length follows from the successful image, without a separate
    InitialLayout or world-end capacity premise at the source emitter. -/
theorem bild_initialized_length_u {u : UProg} {P : Programm (declOf u)} {passes : Nat}
    {fs : List (declOf u).Fn} {pos : (declOf u).Fn → Nat} {name : (declOf u).Fn → String}
    {main : (declOf u).Fn} {ρ : Env (declOf u) ((declOf u).params main)}
    {starts : List (Σ f : (declOf u).Fn, Env (declOf u) ((declOf u).params f))}
    {Ks req : Nat} {tor : (declOf u).Ax → Option TorB} {b : Bild (declOf u)}
    (valid : GabbroV.sp0OkB u = true)
    (hb : bild passes P (layU u tor) fs pos name main ρ starts Ks req = .ok b)
    (hfs : ∀ g, fs[pos g]? = some g) :
    (b.initializedBytes u valid).length = 16 + 16 * b.code.length + 8 * b.K := by
  obtain ⟨cs, body, sp, h, code, _, _, _⟩ := bild_lage hb hfs
    (fun base bound => layU_in u tor base bound) (fun base => layU_dis u tor base)
    (fun base => by simp only [layU]; omega) (fun base => layU_sync u tor base)
  have imageLength := bild_length hb hfs
    (fun base bound => layU_in u tor base bound) (fun base => layU_dis u tor base)
    (fun base => by simp only [layU]; omega) (fun base => layU_sync u tor base)
  have codeLength : b.code.length = headLen (starts.map (·.1)).length + body.length := by
    rw [code, List.length_append, h.head]
  have codeEnd : b.fp0 = codeBase + 16 * b.code.length := by
    rw [codeLength]
    exact h.hfp
  have lower : Runner.Prog.IMG ≤ b.Y.lo := by
    have := h.hylo
    simp only [codeBase] at codeEnd
    omega
  have upper : b.Y.hi ≤ Runner.Prog.IMG + b.bytes.length := by
    have := h.hyhi
    simp only [codeBase] at codeEnd
    omega
  rw [b.initializedBytes_length valid (initialLayout_bild hb) lower upper, imageLength]

/-- Main execution from the initialized payload keeps the existing generic world
    relation: a caller may simulate any source world represented by those same bytes.
    Canonical source startup uses the world fact from bild_initialized_loaded_u. -/
theorem bild_initialized_ok_u [CloneOK] {u : UProg} {P : Programm (declOf u)}
    {O : Orakel (declOf u)} {passes : Nat} {fs : List (declOf u).Fn}
    {pos : (declOf u).Fn → Nat} {name : (declOf u).Fn → String} {main : (declOf u).Fn}
    {ρ : Env (declOf u) ((declOf u).params main)}
    {starts : List (Σ f : (declOf u).Fn, Env (declOf u) ((declOf u).params f))}
    {Ks req : Nat} {tor : (declOf u).Ax → Option TorB} {b : Bild (declOf u)}
    (valid : GabbroV.sp0OkB u = true)
    (hb : bild passes P (layU u tor) fs pos name main ρ starts Ks req = .ok b)
    (hfs : ∀ g, fs[pos g]? = some g) {m : Runner.Mem}
    (loaded : BytesAt m Runner.Prog.IMG (b.initializedBytes u valid)) (σ : World (declOf u))
    (hval : ∀ τ (x : Var ((declOf u).params main) τ), ValueValid b.Y τ (ρ.get x))
    (world : WeltAt m b.Y σ) (hT : TorOK b.Y O) (hV : SichtOK O) :
    match (rufAt (D := declOf u) P O b.passes b.depth main σ ρ :
        RufAusgang (D := declOf u) main) with
    | .ok _ v => ∃ t' m' q, Star ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 b.fp0⟩ m t' m' ∧
        StopAt t' m' q ∧ q.nr = 231 ∧ ExitErg b.Y ((declOf u).erg main) v q.a1
    | .logik e => Stops ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 b.fp0⟩ m (logikCode e)
    | .hardware e => Stops ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 b.fp0⟩ m (hwCode e)
    | _ => False := by
  obtain ⟨_, _, sync, stackPayload, made, _, _, startup, _⟩ := bild_initialized_loaded_u valid hb hfs loaded
  obtain ⟨cs, body, sp, h, code, roots, args, rootArgs⟩ := bild_lage hb hfs
    (fun base bound => layU_in u tor base bound) (fun base => layU_dis u tor base)
    (fun base => by simp only [layU]; omega) (fun base => layU_sync u tor base)
  have startup' : BytesAt m codeBase (b.code.flatMap encII ++
      ((startStackBytes b.Ks (FB + FB) (b.args :: b.rootArgs)).getD [] ++ [])) := by
    simpa only [made, Option.getD_some, List.append_nil] using startup
  rw [code, args, rootArgs] at startup'
  have result := bild_kern (hT := hT) (hV := hV) h startup' hval σ world
    (by simpa only [Nat.mul_zero, Nat.add_zero] using sync 0 (Nat.zero_le _))
  generalize rufAt (D := declOf u) P O b.passes b.depth main σ ρ = outcome at result ⊢
  cases outcome <;> simpa only [BitVec.ofNat_eq_ofNat] using result

/-- Each root receives its own complete environment and the same derived free-lock
    invariant. No extra SyncOK or initialized-world assumption is introduced. -/
theorem bild_initialized_wurzel_ok_u {u : UProg} {P : Programm (declOf u)}
    {O : Orakel (declOf u)} {passes : Nat} {fs : List (declOf u).Fn}
    {pos : (declOf u).Fn → Nat} {name : (declOf u).Fn → String} {main : (declOf u).Fn}
    {ρ : Env (declOf u) ((declOf u).params main)}
    {starts : List (Σ f : (declOf u).Fn, Env (declOf u) ((declOf u).params f))}
    {Ks req : Nat} {tor : (declOf u).Ax → Option TorB} {b : Bild (declOf u)}
    (valid : GabbroV.sp0OkB u = true)
    (hb : bild passes P (layU u tor) fs pos name main ρ starts Ks req = .ok b)
    (hfs : ∀ g, fs[pos g]? = some g) {m : Runner.Mem}
    (loaded : BytesAt m Runner.Prog.IMG (b.initializedBytes u valid)) (j : Nat) (hj : j < starts.length)
    (σ : World (declOf u))
    (hval : ∀ τ (x : Var ((declOf u).params starts[j].1) τ), ValueValid b.Y τ (starts[j].2.get x))
    (world : WeltAt m b.Y σ) (hT : TorOK b.Y O) (hV : SichtOK O) :
    match (rufAt (D := declOf u) P O b.passes b.depth (starts[j]'hj).1 σ (starts[j]'hj).2 :
        RufAusgang (D := declOf u) (starts[j]'hj).1) with
    | .ok _ _ => ∃ t' m' q,
        Star ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * starts.length + startLen + startLen * j)),
          BitVec.ofNat 64 (b.fp0 + 8 * (b.Ks * (j + 1)))⟩ m t' m' ∧ StopAt t' m' q ∧ q.nr = 60
    | .logik e => Stops ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * starts.length + startLen + startLen * j)),
        BitVec.ofNat 64 (b.fp0 + 8 * (b.Ks * (j + 1)))⟩ m (logikCode e)
    | .hardware e => Stops ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * starts.length + startLen + startLen * j)),
        BitVec.ofNat 64 (b.fp0 + 8 * (b.Ks * (j + 1)))⟩ m (hwCode e)
    | _ => False := by
  obtain ⟨_, _, sync, stackPayload, made, _, _, startup, _⟩ := bild_initialized_loaded_u valid hb hfs loaded
  obtain ⟨cs, body, sp, h, code, roots, args, rootArgs⟩ := bild_lage hb hfs
    (fun base bound => layU_in u tor base bound) (fun base => layU_dis u tor base)
    (fun base => by simp only [layU]; omega) (fun base => layU_sync u tor base)
  have startup' : BytesAt m codeBase (b.code.flatMap encII ++
      ((startStackBytes b.Ks (FB + FB) (b.args :: b.rootArgs)).getD [] ++ [])) := by
    simpa only [made, Option.getD_some, List.append_nil] using startup
  rw [code, args, rootArgs] at startup'
  have rootBound : j < (starts.map (·.1)).length := by
    simpa only [List.length_map] using hj
  let rootValid : (Σ f : (declOf u).Fn, Env (declOf u) ((declOf u).params f)) → Prop := fun root =>
    ∀ τ (x : Var ((declOf u).params root.1) τ), ValueValid b.Y τ (root.2.get x)
  let rootOutcome : (Σ f : (declOf u).Fn, Env (declOf u) ((declOf u).params f)) → Prop := fun root =>
    match (rufAt (D := declOf u) P O b.passes b.depth root.1 σ root.2 :
        RufAusgang (D := declOf u) root.1) with
    | .ok _ _ => ∃ t' m' q,
        Star ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * starts.length + startLen + startLen * j)),
          BitVec.ofNat 64 (b.fp0 + 8 * (b.Ks * (j + 1)))⟩ m t' m' ∧ StopAt t' m' q ∧ q.nr = 60
    | .logik e => Stops ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * starts.length + startLen + startLen * j)),
        BitVec.ofNat 64 (b.fp0 + 8 * (b.Ks * (j + 1)))⟩ m (logikCode e)
    | .hardware e => Stops ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * starts.length + startLen + startLen * j)),
        BitVec.ofNat 64 (b.fp0 + 8 * (b.Ks * (j + 1)))⟩ m (hwCode e)
    | _ => False
  have completed : rootOutcome (starts[j]'hj) := by
    change rootValid (starts[j]'hj) at hval
    generalize rootEq : (starts[j]'hj) = root at hval ⊢
    rcases root with ⟨rootFn, rootEnv⟩
    have functionEq : (starts.map (·.1))[j]'rootBound = rootFn := by
      rw [List.getElem_map, rootEq]
    have argumentsEq : (starts.map (fun start => encodeEnv b.Y start.2))[j]'
        (by simpa only [List.length_map] using hj) = encodeEnv b.Y rootEnv := by
      rw [List.getElem_map, rootEq]
    subst rootFn
    have result := bild_wurzel (hT := hT) (hV := hV) (passes := b.passes) h startup' j
      rootBound σ rootEnv argumentsEq hval world
      (sync (j + 1) (by simp only [roots, List.length_map]; omega))
    dsimp only [rootOutcome]
    generalize rufAt (D := declOf u) P O b.passes b.depth
      ((starts.map (·.1))[j]'rootBound) σ rootEnv = outcome at result ⊢
    cases outcome <;> simpa only [List.length_map, BitVec.ofNat_eq_ofNat] using result
  dsimp only [rootOutcome] at completed
  generalize rufAt (D := declOf u) P O b.passes b.depth
    (starts[j]'hj).1 σ (starts[j]'hj).2 = outcome at completed ⊢
  cases outcome <;> exact completed

end Gabbro.Stage0.Senke
