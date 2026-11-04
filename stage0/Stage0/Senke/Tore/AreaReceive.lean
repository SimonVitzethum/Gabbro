/- Tag checking and complete result transport share the ordinary call ABI. -/
module
public import Stage0.Senke.Tore.AreaRun
public import Stage0.Senke.Anweisung.Bindung.Pruefung
public import Stage0.Senke.Anweisung.Puffer.Tor
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- The success-tag test touches only the ten request/scratch words below the
    result area. The payload remains available for the common value copy. -/
theorem areaCheck_ok {s reserved : Nat} {m : Runner.Mem} {pc fp : Runner.W}
    {Γ : Ctx} {ρ : Env D Γ} {tag : Runner.W}
    (pre : PreS L m pc fp (s + 10) (s + 1) (areaCheck s) ρ reserved)
    (input : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some tag) :
    (tag = 0 → ∃ m', Star ⟨pc, fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (areaCheck s).length), fp⟩ m' ∧
      Agree fp (s + 1) (s + 10) m m') ∧
    (tag ≠ 0 → Stops ⟨pc, fp⟩ m 110) := by
  have pre0 : PreS L m pc fp (s + 10) (s + 1)
      (([ci 1 (s + 1) 0 0] ++ [ci 14 (s + 1) s (s + 1)]) ++
        guardC (s + 1) 110 (s + 2)) ρ reserved := pre
  obtain ⟨m1, run1, change1, w1, read1, encoded1⟩ := const_ok pre0.left.left (by decide) (by omega)
  have zeroWord : BitVec.ofInt 64 0 = (0 : Runner.W) := rfl
  have next := pre0.left.next change1 (Nat.le_refl _) (by omega)
  have tagRead : m1.rd64 (slot fp (BitVec.ofNat 64 s)) = some tag := by
    rw [agree_rd_low change1 pre.frame.room (by omega) (by omega)]
    exact input
  obtain ⟨m2, run2, change2, w2, read2, encoded2⟩ := eng_bin_ok
    (d := s + 1) (a := s) (b := s + 1) next (by omega) (by omega) (by omega) tagRead read1
    (g := fun x y => some (Runner.IR.bool (x == y))) rfl (by decide) rfl
  have tested : Ok m pc fp (s + 10) (s + 1)
      ([ci 1 (s + 1) 0 0] ++ [ci 14 (s + 1) s (s + 1)])
      (· = Runner.IR.bool (tag == 0)) := by
    refine ⟨m2, ?_, change1.trans change2, w2, read2, ?_⟩
    · simpa only [List.length_append, List.length_singleton, pc_add] using run1.trans run2
    · simpa only [encoded1, zeroWord] using encoded2
  have checked := test_ok pre0 tested (by omega) (by omega)
  refine ⟨fun success => checked.1 ?_, fun failure => checked.2 ?_⟩
  · subst tag
    decide
  · have different : (tag == 0) = false := beq_eq_false_iff_ne.mpr failure
    rw [different]
    rfl

/-- A zero tag copies every limb of the provider's value with `copyValue_run`.
    A nonzero unhandled tag stops before any payload word is consumed. -/
theorem areaReceive_ok {τ : Ty} {v : Wert D τ} {s reserved : Nat}
    {m : Runner.Mem} {pc fp : Runner.W} {K Ks : Nat} {Γ : Ctx} {ρ : Env D Γ}
    {tag : Runner.W} (layout : WIn L fp Ks K)
    (capacity : foreignResultBase s + valueWords τ ≤ Ks)
    (pre : PreS L m pc fp K s (areaReceive τ s) ρ reserved)
    (input : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some tag) :
    (tag = 0 → ValueAt L m fp (foreignResultBase s) τ v →
      ∃ m', Star ⟨pc, fp⟩ m
          ⟨pc + BitVec.ofNat 64 (16 * (areaReceive τ s).length), fp⟩ m' ∧
        Agree fp s Ks m m' ∧ ValueAt L m' fp s τ v) ∧
    (tag ≠ 0 → Stops ⟨pc, fp⟩ m 110) := by
  have baseEquation : foreignResultBase s = s + 10 := rfl
  have ks := layout.ks
  have positive := valueWords_pos τ
  have enough : s + 10 ≤ Ks := by unfold foreignResultBase at capacity; omega
  have pre0 : PreS L m pc fp K s
      (areaCheck s ++ copyWords (valueWords τ) s (foreignResultBase s)) ρ reserved := pre
  have short : PreS L m pc fp (s + 10) (s + 1) (areaCheck s) ρ reserved :=
    ⟨by have := pre.ctx; omega, by have := pre.small; omega,
      frameOK_sub pre.frame (by omega), pre0.left.code,
      codeFar_sub2 pre0.left.far (by omega), pre.env, trivial, wstab_true _ _⟩
  have checked := areaCheck_ok short input
  refine ⟨fun success value => ?_, checked.2⟩
  obtain ⟨m1, run1, change1⟩ := checked.1 success
  have change1s := Agree.widen (change1.mono (Nat.le_succ s)) enough
  have next := pre0.next (Agree.widen change1s ks) (Nat.le_refl _) (by omega)
  have value1 : ValueAt L m1 fp (foreignResultBase s) τ v := by
    refine ⟨value.1, ?_⟩
    intro i hi
    have length := encodeWords_length L τ v
    rw [agree_rd_high change1 (frameOK_sub pre.frame ks).room
      (by unfold foreignResultBase; omega) (by omega)]
    exact value.2 i hi
  obtain ⟨m2, run2, change2, output⟩ := copyValue_run
    (frameOK_sub next.frame ks) (by have := pre.small; omega)
    (by unfold foreignResultBase at capacity; omega) capacity
    (Or.inl (by unfold foreignResultBase; omega)) next.code
    (by simpa only [copyWords_length] using codeFar_sub2 next.far ks) value1
  refine ⟨m2, ?_, change1s.trans (Agree.widen change2 (by omega)), output⟩
  rw [areaReceive, List.length_append, ← pc_add]
  simpa only [copyWords_length] using run1.trans run2

/-- Invalid tags stop even when the declared type has no inhabitant. -/
theorem areaReceive_nonzero {τ : Ty} {s reserved : Nat}
    {m : Runner.Mem} {pc fp : Runner.W} {K Ks : Nat} {Γ : Ctx} {ρ : Env D Γ}
    {tag : Runner.W} (layout : WIn L fp Ks K)
    (capacity : foreignResultBase s + valueWords τ ≤ Ks)
    (pre : PreS L m pc fp K s (areaReceive τ s) ρ reserved)
    (input : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some tag) (nonzero : tag ≠ 0) :
    Stops ⟨pc, fp⟩ m 110 := by
  have positive := valueWords_pos τ
  have ks := layout.ks
  have enough : s + 10 ≤ Ks := by unfold foreignResultBase at capacity; omega
  have short : PreS L m pc fp (s + 10) (s + 1) (areaCheck s) ρ reserved :=
    ⟨by have := pre.ctx; omega, by have := pre.small; omega,
      frameOK_sub pre.frame (by unfold foreignResultBase at capacity; omega),
      pre.left.code, codeFar_sub2 pre.left.far (by unfold foreignResultBase at capacity; omega),
      pre.env, trivial, wstab_true _ _⟩
  exact (areaCheck_ok short input).2 nonzero

end Gabbro.Stage0.Senke
