/- Retain pure word inputs once, then run the same IR on certified slot loads. -/
module
public import Stage0.Senke.Ausdruck.Gleit.Slots.SlotBasics
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem

/-- Sequential input code; its ceiling includes the complete retained prefix. -/
def retainWordInputsL : Nat → List (Nat → Option (List II × Nat)) →
    Option (List II × Nat)
  | d, [] => some ([], d)
  | d, input :: inputs => do
      let first ← input d
      let rest ← retainWordInputsL (d + 1) inputs
      pure (first.1 ++ rest.1, max first.2 rest.2)

/-- Evaluate each input in its own retained slot. The continuation uses only
    loads from that prefix and writes beyond it, before the final result copy. -/
def withWordInputsL (d : Nat) (inputs : List (Nat → Option (List II × Nat)))
    (body : (Fin inputs.length → Nat → Option (List II × Nat)) →
      Nat → Option (List II × Nat)) : Option (List II × Nat) := do
  let leadingCode ← retainWordInputsL d inputs
  let result ← body (fun i j => some ([ci 2 j (d + i.val) 0], j + 1)) (d + inputs.length)
  pure (leadingCode.1 ++ (result.1 ++ [ci 2 d (d + inputs.length) 0]),
    max leadingCode.2 (max result.2 (d + inputs.length + 1)))

private theorem retainWordInputsL_room {d top : Nat} {code : List II}
    {inputs : List (Nat → Option (List II × Nat))}
    (emitted : retainWordInputsL d inputs = some (code, top)) : d + inputs.length ≤ top := by
  induction inputs generalizing d code top with
  | nil => cases emitted; simp
  | cons input inputs ih =>
      simp only [retainWordInputsL, bind, Option.bind_eq_some_iff, pure,
        Option.some.injEq] at emitted
      obtain ⟨first, hf, rest, hr, emitted⟩ := emitted
      cases emitted
      have := ih hr
      simp only [List.length_cons]
      omega

variable [Kern] {D : Deklaration} {L : Lay D}

/-- The prefix preserves the original environment and world by ordinary
    `Agree`; each stored result remains below the following temporary interval. -/
private theorem retainWordInputsL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {reserved : Nat} (inputs : List (Nat → Option (List II × Nat)))
    (values : Fin inputs.length → Runner.W)
    (runs : ∀ i, WordCode (L := L) (reserved := reserved) ρ W (inputs.get i) (values i))
    {d top : Nat} {code : List II} {m : Runner.Mem} {pc fp : Runner.W} {K : Nat}
    (emitted : retainWordInputsL d inputs = some (code, top)) (fits : top ≤ K)
    (pre : Pre L m pc fp K d code ρ W reserved) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * code.length), fp⟩ m' ∧
      Agree fp d K m m' ∧
      ∀ i, m'.rd64 (slot fp (BitVec.ofNat 64 (d + i.val))) = some (values i) := by
  induction inputs generalizing d top code m pc with
  | nil =>
      cases emitted
      exact ⟨m, by simpa using Star.refl ⟨pc, fp⟩ m, Agree.refl _ _ _ _, fun i => i.elim0⟩
  | cons input inputs ih =>
      simp only [retainWordInputsL, bind, Option.bind_eq_some_iff, pure,
        Option.some.injEq] at emitted
      obtain ⟨⟨first, ft⟩, hf, ⟨rest, rt⟩, hr, emitted⟩ := emitted
      cases emitted
      have room := retainWordInputsL_room hr
      obtain ⟨m1, s1, a1, w, read, eq⟩ := runs ⟨0, by simp⟩ hf (by omega) m pc pre.left
      subst w
      have next := pre.next a1 (Nat.le_succ d) (by omega)
      obtain ⟨m2, s2, a2, reads⟩ := ih (fun i => values i.succ)
        (fun i => runs i.succ) hr (by omega) next
      refine ⟨m2, ?_, a1.trans (a2.mono (Nat.le_succ d)), ?_⟩
      · simpa only [List.length_append, pc_add] using s1.trans s2
      · intro ⟨i, hi⟩
        cases i with
        | zero =>
            exact slotRead_agree next.frame a2 (Nat.lt_succ_self d) (by omega) read
        | succ i =>
            have address : d + 1 + i = d + (i + 1) := by omega
            simpa only [address, Fin.succ] using
              reads ⟨i, Nat.lt_of_succ_lt_succ hi⟩

/-- A fixed load is certified only by an actual readable frame environment
    and the concrete value observed there, independently of the source context. -/
private theorem retainedWordLoad {n i : Nat} {m : Runner.Mem} {fp : Runner.W}
    (ρ : Env D (frameWordCtx n)) (env : EnvAt L m fp ρ)
    (lower : FB ≤ i) (upper : i < FB + n) (w : Runner.W)
    (read : m.rd64 (slot fp (BitVec.ofNat 64 i)) = some w) :
    WordCode (L := L) ρ (fun _ => True) (fun j => some ([ci 2 j i 0], j + 1)) w := by
  have less : i - FB < n := by omega
  let v := frameWordVar n (i - FB) less
  obtain ⟨actual, rd, encoded⟩ := ValueAt.word frameWordTy (ρ.get v) (by trivial) (env _ v)
  have position : vslot v = i := by rw [frameWordVar_slot]; omega
  rw [position, read] at rd
  have same := Option.some.inj rd
  rw [← same] at encoded
  change w = BitVec.ofInt 64 (ρ.get v).n at encoded
  rw [encoded]
  have slotInt : (FB : Int) + ((i - FB : Nat) : Int) = i := by omega
  intro fp' K j c top emitted fits mm pc pre
  exact frameWordLoad (L := L) n (i - FB) less ρ
    (by simpa only [slotInt] using emitted) fits mm pc pre

/-- Universal retention composition. The body is proved for certified pure
    loads in any word environment; it is instantiated with actual frame words.
    The caller's original environment, reserved prefix and outside world are
    preserved by the resulting `Agree`, not postulated for the fixed loads. -/
theorem withWordInputsL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {reserved : Nat} {inputs : List (Nat → Option (List II × Nat))}
    {body : (Fin inputs.length → Nat → Option (List II × Nat)) → Nat → Option (List II × Nat)}
    (values : Fin inputs.length → Runner.W) {result : Runner.W}
    (runs : ∀ i, WordCode (L := L) (reserved := reserved) ρ W (inputs.get i) (values i))
    (continuation : ∀ {Δ : Ctx} (ρw : Env D Δ)
      (loads : Fin inputs.length → Nat → Option (List II × Nat)),
      (∀ i, WordCode (L := L) ρw (fun _ => True) (loads i) (values i)) →
      WordCode (L := L) ρw (fun _ => True) (body loads) result) :
    WordCode (L := L) (reserved := reserved) ρ W
      (fun d => withWordInputsL d inputs body) result := by
  intro fp K d code top emitted fits m pc pre
  simp only [withWordInputsL, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq] at emitted
  obtain ⟨⟨leadingCode, pt⟩, hp, ⟨assembly, ceiling⟩, ha, emitted⟩ := emitted
  cases emitted
  have room := retainWordInputsL_room hp
  obtain ⟨m1, s1, a1, reads⟩ := retainWordInputsL_ok inputs values runs hp (by omega) pre.left
  have next := pre.next a1 (show d ≤ d + inputs.length by omega) (by omega)
  have lower : FB ≤ d := by have := pre.ctx; unfold frei at this; omega
  let n := d + inputs.length - FB
  obtain ⟨ρw, env⟩ := frameWordEnv (L := L) (n := n) next.frame (by dsimp only [n]; omega)
  have loads (i : Fin inputs.length) : WordCode (L := L) ρw (fun _ => True)
      (fun j => some ([ci 2 j (d + i.val) 0], j + 1)) (values i) :=
    retainedWordLoad ρw env (by omega) (by dsimp only [n]; omega) _ (reads i)
  have bodyPre : Pre L m1 _ fp K (d + inputs.length) assembly ρw (fun _ => True) :=
    ⟨by simp [frei, frameWordCtx, n]; omega, next.small, next.frame,
      next.left.code, next.left.far, env, trivial, wstab_true _ _⟩
  obtain ⟨m2, s2, a2, w, read, eq⟩ := continuation ρw _ loads
    (fp := fp) (K := K) (d := d + inputs.length) (c := assembly) (top := ceiling)
    ha (by omega) m1 _ bodyPre
  have finalPre := next.next a2 (Nat.le_refl _) (by omega)
  have copyPre : Pre L m2 _ fp K d [ci 2 d (d + inputs.length) 0] ρ W reserved :=
    ⟨pre.ctx, finalPre.small, finalPre.frame, finalPre.code, finalPre.far,
      finalPre.env, finalPre.welt, finalPre.wstab⟩
  obtain ⟨m3, s3, a3, output, rd, he⟩ := mov_ok copyPre (by omega) (by omega) read
  refine ⟨m3, ?_, (a1.trans (a2.mono (show d ≤ d + inputs.length by omega))).trans a3,
    output, rd, he.trans eq⟩
  simpa only [List.length_append, List.length_singleton, pc_add, Nat.add_assoc] using
    (s1.trans s2).trans s3

#print axioms withWordInputsL_ok
end Gabbro.Stage0.Senke
