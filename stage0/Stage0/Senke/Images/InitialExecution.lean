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
    ∃ stacks, startStackBytes b.Ks (FB + FB) (b.args :: b.rootArgs) = some stacks ∧
      stacks.length = 8 * (b.Ks * (b.roots.length + 1)) ∧
      BytesAt m Runner.Prog.IMG (Runner.Prog.leN 8 b.fp0 ++ Runner.Prog.leN 8 b.baseReq) ∧
      BytesAt m codeBase (b.code.flatMap encII ++ stacks) ∧ BytesAt m b.fp0 stacks := by
  obtain ⟨cs, body, sp, h, code, roots, args, rootArgs⟩ := bild_lage hb hfs
    (fun base bound => layU_in u tor base bound) (fun base => layU_dis u tor base)
    (fun base => by simp only [layU]; omega) (fun base => layU_sync u tor base)
  obtain ⟨stacks, made, length⟩ := h.stacks
  have actualStacks : startStackBytes b.Ks (FB + FB) (b.args :: b.rootArgs) = some stacks := by
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
  refine ⟨world, locks, ?_, stacks, actualStacks, ?_, header, startup, stackMemory⟩
  · intro j hj
    exact h.sync locks (by simpa only [roots] using hj)
  · simpa only [roots] using length

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
    match rufAt P O b.passes b.depth main σ ρ with
    | .ok _ v => ∃ t' m' q, Star ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 b.fp0⟩ m t' m' ∧
        StopAt t' m' q ∧ q.nr = 231 ∧ ExitErg b.Y ((declOf u).erg main) v q.a1
    | .logik e => Stops ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 b.fp0⟩ m (logikCode e)
    | .hardware e => Stops ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 b.fp0⟩ m (hwCode e)
    | _ => False := by
  obtain ⟨_, _, sync, stacks, made, _, _, startup, _⟩ := bild_initialized_loaded_u valid hb hfs loaded
  obtain ⟨cs, body, sp, h, code, roots, args, rootArgs⟩ := bild_lage hb hfs
    (fun base bound => layU_in u tor base bound) (fun base => layU_dis u tor base)
    (fun base => by simp only [layU]; omega) (fun base => layU_sync u tor base)
  have startup' : BytesAt m codeBase (b.code.flatMap encII ++
      ((startStackBytes b.Ks (FB + FB) (b.args :: b.rootArgs)).getD [] ++ [])) := by
    simpa only [made, Option.getD_some, List.append_nil] using startup
  rw [code, args, rootArgs] at startup'
  exact bild_kern (hT := hT) (hV := hV) h startup' hval σ world
    (by simpa only [Nat.mul_zero, Nat.add_zero] using sync 0 (Nat.zero_le _))

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
    match rufAt P O b.passes b.depth starts[j].1 σ starts[j].2 with
    | .ok _ _ => ∃ t' m' q,
        Star ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * starts.length + startLen + startLen * j)),
          BitVec.ofNat 64 (b.fp0 + 8 * (b.Ks * (j + 1)))⟩ m t' m' ∧ StopAt t' m' q ∧ q.nr = 60
    | .logik e => Stops ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * starts.length + startLen + startLen * j)),
        BitVec.ofNat 64 (b.fp0 + 8 * (b.Ks * (j + 1)))⟩ m (logikCode e)
    | .hardware e => Stops ⟨BitVec.ofNat 64 (codeBase + 16 * (3 * starts.length + startLen + startLen * j)),
        BitVec.ofNat 64 (b.fp0 + 8 * (b.Ks * (j + 1)))⟩ m (hwCode e)
    | _ => False := by
  obtain ⟨_, _, sync, stacks, made, _, _, startup, _⟩ := bild_initialized_loaded_u valid hb hfs loaded
  obtain ⟨cs, body, sp, h, code, roots, args, rootArgs⟩ := bild_lage hb hfs
    (fun base bound => layU_in u tor base bound) (fun base => layU_dis u tor base)
    (fun base => by simp only [layU]; omega) (fun base => layU_sync u tor base)
  have startup' : BytesAt m codeBase (b.code.flatMap encII ++
      ((startStackBytes b.Ks (FB + FB) (b.args :: b.rootArgs)).getD [] ++ [])) := by
    simpa only [made, Option.getD_some, List.append_nil] using startup
  rw [code, args, rootArgs] at startup'
  have result := bild_wurzel (hT := hT) (hV := hV) h startup' j
    (by simpa only [List.length_map] using hj) σ
    (by simpa only [List.getElem_map] using starts[j].2)
    (by simp only [List.getElem_map])
    (by simpa only [List.getElem_map] using hval) world
    (sync (j + 1) (by simp only [roots, List.length_map]; omega))
  simpa only [List.length_map, List.getElem_map] using result

end Gabbro.Stage0.Senke
