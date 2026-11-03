/- Evaluate source operands once and run the adder on their retained words. -/
module
public import Stage0.Senke.Gleit.Normal.Model
public import Stage0.Senke.Ausdruck.Gleit.Slots.SlotContext
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Two retained operands precede all routine temporaries. The final copy
    places the result in the ordinary expression destination. -/
def softAddContinuationL (input : Nat) : Option (List II × Nat) := do
  let routine ← softAddRoutineL (input + 2)
    (fun j => some ([ci 2 j input 0], j + 1))
    (fun j => some ([ci 2 j (input + 1) 0], j + 1))
  pure (routine.1 ++ [ci 2 input (input + 2) 0], max routine.2 (input + 3))

def softAddWordsL (d : Nat) (left right : Nat → Option (List II × Nat)) :
    Option (List II × Nat) := do
  let a ← left d
  let b ← right (d + 1)
  let suffix ← softAddContinuationL d
  pure (a.1 ++ (b.1 ++ suffix.1), max a.2 (max b.2 suffix.2))

/-- Successful emission reserves both retained words and the routine result. -/
theorem softAddWordsL_room {d top : Nat} {left right : Nat → Option (List II × Nat)}
    {code : List II} (hc : softAddWordsL d left right = some (code, top)) : d + 3 ≤ top := by
  simp only [softAddWordsL, softAddContinuationL, bind, Option.bind_eq_some_iff,
    pure, Option.some.injEq] at hc
  obtain ⟨a, ha, b, hb, suffix, hs, hc⟩ := hc
  obtain ⟨routine, hr, hs⟩ := hs
  cases hs
  cases hc
  omega

/-- Reify only the actual readable frame words. No fixed-slot producer is
    assumed movable to an arbitrary destination without its environment. -/
theorem softAddContinuationL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K input top reserved : Nat} {code : List II}
    (a b : GFloat) (hA : wf f64 a) (hB : wf f64 b)
    (hc : softAddContinuationL input = some (code, top))
    (hp : Pre L m pc fp K input code ρ W reserved) (ht : top ≤ K)
    (ra : m.rd64 (slot fp (BitVec.ofNat 64 input)) = some (BitVec.ofNat 64 (zuBits f64 a)))
    (rb : m.rd64 (slot fp (BitVec.ofNat 64 (input + 1))) = some (BitVec.ofNat 64 (zuBits f64 b))) :
    Ok m pc fp K input code (· = BitVec.ofNat 64 (zuBits f64 (add f64 a b))) := by
  simp only [softAddContinuationL, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq] at hc
  obtain ⟨⟨assembly, ceiling⟩, ha, hc⟩ := hc
  cases hc
  have hi : FB ≤ input := by have := hp.ctx; unfold frei at this; omega
  let n := input + 2 - FB
  obtain ⟨ρw, env⟩ := frameWordEnv (L := L) (n := n) hp.frame (by dsimp only [n]; omega)
  have load (i : Nat) (lo : FB ≤ i) (upper : i < input + 2) (w : Runner.W)
      (read : m.rd64 (slot fp (BitVec.ofNat 64 i)) = some w) :
      WordCode (L := L) ρw (fun _ => True)
        (fun j => some ([ci 2 j i 0], j + 1)) w := by
    have less : i - FB < n := by dsimp only [n]; omega
    let v := frameWordVar n (i - FB) less
    obtain ⟨actual, rd, encoded⟩ := ValueAt.word frameWordTy (ρw.get v) (by trivial) (env _ v)
    have position : vslot v = i := by rw [frameWordVar_slot]; omega
    rw [position, read] at rd
    have same := Option.some.inj rd
    subst actual
    change w = BitVec.ofInt 64 (ρw.get v).n at encoded
    have result := frameWordLoad (L := L) n (i - FB) less ρw
    have slotEq : FB + (i - FB) = i := by omega
    rw [slotEq, ← encoded] at result
    exact result
  have pre : Pre L m pc fp K (input + 2) assembly ρw (fun _ => True) :=
    ⟨by simp [frei, frameWordCtx, n]; omega, hp.small, hp.frame, hp.left.code,
      hp.left.far, env, trivial, wstab_true _ _⟩
  have run := softAddRoutineL_ok (L := L) a b hA hB
    (load input hi (by omega) _ ra) (load (input + 1) (by omega) (by omega) _ rb)
  obtain ⟨m1, s1, a1, w, r1, hw⟩ := run ha (by omega) m pc pre
  have next := hp.next (a1.mono (show input ≤ input + 2 by omega)) (Nat.le_refl _) (by omega)
  obtain ⟨m2, s2, a2, r, rr, eq⟩ := mov_ok (s := input + 2) (d := input)
    next (by omega) (by omega) r1
  refine ⟨m2, ?_, (a1.mono (show input ≤ input + 2 by omega)).trans a2, r, rr, eq.trans hw⟩
  simpa only [List.length_append, List.length_singleton, pc_add] using s1.trans s2

/-- Ordinary source producers may use any reserved prefix. Their concrete
    results are retained while the integer-only routine uses a fresh suffix. -/
theorem softAddWordsL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {left right : Nat → Option (List II × Nat)} {reserved : Nat} {fp : Runner.W} {K : Nat}
    (a b : GFloat)
    (hl : ∀ j c t, left j = some (c, t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K j c ρ W reserved → Ok m pc fp K j c
        (fun w => wf f64 a ∧ w = BitVec.ofNat 64 (zuBits f64 a)))
    (hr : ∀ j c t, right j = some (c, t) → t ≤ K → ∀ m pc,
      Pre L m pc fp K j c ρ W reserved → Ok m pc fp K j c
        (fun w => wf f64 b ∧ w = BitVec.ofNat 64 (zuBits f64 b)))
    {d top : Nat} {code : List II} (hc : softAddWordsL d left right = some (code, top))
    (ht : top ≤ K) {m : Runner.Mem} {pc : Runner.W} (hp : Pre L m pc fp K d code ρ W reserved) :
    Ok m pc fp K d code (fun w => wf f64 (add f64 a b) ∧
      w = BitVec.ofNat 64 (zuBits f64 (add f64 a b))) := by
  have room := softAddWordsL_room hc
  simp only [softAddWordsL, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hc
  obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, ⟨suffix, ts⟩, hs, hc⟩ := hc
  cases hc
  obtain ⟨m1, s1, a1, wa, ra, ea⟩ := hl _ _ _ ha (by omega) m pc hp.left
  obtain ⟨hA, ea⟩ := ea
  subst wa
  have hp1 := hp.next a1 (show d ≤ d + 1 by omega) (by omega)
  obtain ⟨m2, s2, a2, wb, rb, eb⟩ := hr _ _ _ hb (by omega) m1 _ hp1.left
  obtain ⟨hB, eb⟩ := eb
  subst wb
  have hp2 := hp1.next a2 (Nat.le_refl _) (by omega)
  have leftRead := slotRead_agree hp1.frame a2 (Nat.lt_succ_self d) (by omega) ra
  have pre : Pre L m2 _ fp K d suffix ρ W reserved :=
    ⟨hp.ctx, hp2.small, hp2.frame, hp2.code, hp2.far, hp2.env, hp2.welt, hp2.wstab⟩
  obtain ⟨m3, s3, a3, w, rw, ew⟩ := softAddContinuationL_ok a b hA hB hs pre
    (by omega) leftRead rb
  refine ⟨m3, ?_, (a1.trans (a2.mono (Nat.le_succ d))).trans a3, w, rw, ⟨add_wf f64 f64_p a b hA hB, ew⟩⟩
  simpa only [List.length_append, pc_add] using (s1.trans s2).trans s3

#print axioms softAddContinuationL_ok
#print axioms softAddWordsL_ok
end Gabbro.Stage0.Senke
