/- Integer interval changes preserve the common limb encoding and extend its sign. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Materialize
public import Stage0.Senke.Ausdruck.Aggregat.Scalar
public import Stage0.Senke.Ausdruck.Tops.Eng
public import Stage0.Senke.Ausdruck.Wenn
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- The sign test reads the source's last limb without modifying its prefix. -/
theorem integerSign_ok {m : Runner.Mem} {pc fp : Runner.W} {K base : Nat}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} {w : Runner.W}
    (positive : 0 < base) (fits : base + 2 ≤ K)
    (read : m.rd64 (slot fp (BitVec.ofNat 64 (base - 1))) = some w)
    (pre : Pre L m pc fp K base
      [ci 1 (base + 1) 0 0, ci 13 base (base - 1 : Nat) (base + 1)] ρ W reserved) :
    Ok m pc fp K base [ci 1 (base + 1) 0 0, ci 13 base (base - 1 : Nat) (base + 1)]
      (· = Runner.IR.bool (w.slt 0)) := by
  have start : Pre L m pc fp K base
      ([ci 1 (base + 1) 0 0] ++ [ci 13 base (base - 1 : Nat) (base + 1)]) ρ W reserved := pre
  obtain ⟨m1, run1, changed1, zero, readZero, equal⟩ := const_ok (d := base + 1)
    { start.left with ctx := by have := pre.ctx; omega } (by decide) (by omega)
  subst zero
  have next := start.next (changed1.mono (Nat.le_succ base)) (Nat.le_refl _) (by omega)
  have preserved : m1.rd64 (slot fp (BitVec.ofNat 64 (base - 1))) = some w := by
    rw [agree_rd_low changed1 pre.frame.room (by omega) (by omega)]
    exact read
  obtain ⟨m2, run2, changed2, flag, readFlag, encoded⟩ := eng_bin_ok next
    (d := base) (a := base - 1) (b := base + 1) (by omega) (by omega) (by omega)
    preserved readZero (g := fun a b => some (Runner.IR.bool (a.slt b))) rfl (by decide) rfl
  refine ⟨m2, ?_, (changed1.mono (Nat.le_succ base)).trans changed2, flag, readFlag, encoded⟩
  simpa only [List.length_append, List.length_singleton, List.length_cons, List.length_nil, pc_add] using run1.trans run2

/-- The last canonical signed limb exposes the mathematical sign, even when all
    lower limbs have high bits set. -/
theorem integerTop_read {lo hi : Int} {v : Zahl lo hi} {m : Runner.Mem} {fp : Runner.W} {base : Nat}
    (negative : lo < 0) (value : ValueAt L m fp base (.int lo hi) v) :
    ∃ w, m.rd64 (slot fp (BitVec.ofNat 64 (base + (integerWords lo hi - 1)))) = some w ∧
      w.slt 0 = decide (v.n < 0) := by
  have positive : 0 < integerWords lo hi := valueWords_pos (.int lo hi)
  have bounds := integerWords_signed negative v.lo_le v.le_hi
  have top := integerEncoding_top_signed positive v.n bounds.1 bounds.2
  have words := value.2
  erw [encodeWords_int] at words
  rw [integerEncoding_last positive v.n, wordsAt_append] at words
  have read := words.2 0 (by simp)
  simp only [integerEncoding_length, Nat.add_zero, List.getElem_cons_zero] at read
  refine ⟨_, read, ?_⟩
  rw [BitVec.slt_eq_decide, BitVec.toInt_ofInt_eq_self (by decide) top.1 top.2.1]
  change decide (v.n / 2 ^ (64 * (integerWords lo hi - 1)) < 0) = decide (v.n < 0)
  simp only [top.2.2]

/-- Constant sign extension is selected by actual IR execution over the complete
    source encoding. Both branches share the ordinary word materializer. -/
theorem integerExtensionL_ok {lo hi : Int} (v : Zahl lo hi)
    {m : Runner.Mem} {pc fp : Runner.W} {K d extra top : Nat} {c : List II}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (source : ValueAt L m fp d (.int lo hi) v)
    (lower : integerExtensionL lo extra (d + integerWords lo hi) = some (c, top))
    (fits : top ≤ K)
    (pre : Pre L m pc fp K (d + integerWords lo hi) c ρ W reserved) :
    Executes m pc fp K (d + integerWords lo hi) c
      (fun m' => WordsAt m' fp (d + integerWords lo hi)
        (List.replicate extra (if v.n < 0 then BitVec.ofInt 64 (-1) else 0))) := by
  have width : 0 < integerWords lo hi := valueWords_pos (.int lo hi)
  by_cases signed : lo < 0
  · simp only [integerExtensionL, if_pos signed, wennL, bind, Option.bind_some] at lower
    split at lower
    · next length =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj lower)
      obtain ⟨word, read, sign⟩ := integerTop_read signed source
      have address : d + (integerWords lo hi - 1) = d + integerWords lo hi - 1 := by omega
      rw [address] at read
      refine wenn_ok (bc := decide (v.n < 0)) pre length (by omega) ?_ ?_ ?_
      · intro preSign
        exact (integerSign_ok (by omega) (by omega) read preSign).mono fun flag encoded => by
          rw [encoded, sign, bool_word]
      · intro negative m' pc' preWords
        have hn : v.n < 0 := of_decide_eq_true negative
        simpa only [Executes, if_pos hn] using
          (constWords_ok (List.replicate extra (BitVec.ofInt 64 (-1))) (by omega) preWords)
      · intro nonnegative m' pc' preWords
        have hn : ¬v.n < 0 := by simpa only [decide_eq_false_iff_not] using nonnegative
        simpa only [Executes, if_neg hn] using
          (constWords_ok (List.replicate extra 0) (by omega) preWords)
    · cases lower
  · simp only [integerExtensionL, if_neg signed, Option.some.injEq] at lower
    have codeEq := congrArg Prod.fst lower
    have topEq := congrArg Prod.snd lower
    dsimp only at codeEq topEq
    subst c
    subst top
    have hn : ¬v.n < 0 := by have := v.lo_le; omega
    simpa only [Executes, if_neg hn] using constWords_ok (List.replicate extra 0) fits pre

/-- Actual integer widening preserves every existing limb and executes the common
    extension when needed. Its only child premise is the structural simulation
    supplied by lowE_ok, for every accepted child and actual input memory. -/
theorem resizeIntegerL_ok {lo hi lo' hi' : Int} (v : Zahl lo hi) (result : Zahl lo' hi')
    (same : result.n = v.n) {fp : Runner.W} {K d top : Nat} {c : List II}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} {child : Option (List II × Nat)}
    {m : Runner.Mem} {pc : Runner.W}
    (ih : ∀ cc tt, child = some (cc, tt) → tt ≤ K →
      Pre L m pc fp K d cc ρ W reserved → ValueOk L m pc fp K d cc (.int lo hi) v)
    (lower : resizeIntegerL lo hi lo' hi' d child = some (c, top)) (fits : top ≤ K)
    (pre : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int lo' hi') result := by
  simp only [resizeIntegerL, bind, Option.bind_eq_some_iff] at lower
  obtain ⟨⟨cc, tt⟩, hc, lower⟩ := lower
  split at lower
  · next shorter =>
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at lower
    obtain ⟨rfl, rfl⟩ := lower
    obtain ⟨m', run, changed, source⟩ := ih cc tt hc (by omega) pre
    refine ⟨m', run, changed, trivial, ?_⟩
    erw [encodeWords_int]
    rw [same, ← integerEncoding_take v.n shorter]
    intro i indexBound
    have sourceWords := source.2
    erw [encodeWords_int] at sourceWords
    have bound : i < integerWords lo hi := by
      simp only [List.length_take, integerEncoding_length] at indexBound
      omega
    simpa only [List.getElem_take] using sourceWords i (by simpa only [integerEncoding_length] using bound)
  · next larger =>
    change (integerExtensionL lo (integerWords lo' hi' - integerWords lo hi) (d + integerWords lo hi)).bind
      (fun extension => some (cc ++ extension.1, max tt extension.2)) = some (c, top) at lower
    rw [Option.bind_eq_some_iff] at lower
    obtain ⟨⟨ce, te⟩, he, out⟩ := lower
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj out)
    have span := integerExtensionL_span he
    obtain ⟨m1, run1, changed1, source⟩ := ih cc tt hc (by omega) pre.left
    have next := pre.next changed1 (by omega : d ≤ d + integerWords lo hi) (by omega)
    obtain ⟨m2, run2, changed2, extension⟩ := integerExtensionL_ok v source he (by omega) next
    have keptSource := source.agree changed2 next.frame (Nat.le_refl _) (by omega)
    have range := integerWords_range v.lo_le v.le_hi
    have encoding := integerEncoding_extend (integerWords lo' hi' - integerWords lo hi) v.n range.1 range.2
    rw [show integerWords lo hi + (integerWords lo' hi' - integerWords lo hi) = integerWords lo' hi' by omega] at encoding
    refine ⟨m2, ?_, changed1.trans (changed2.mono (by omega)), trivial, ?_⟩
    · simpa only [List.length_append, pc_add] using run1.trans run2
    · erw [encodeWords_int]
      rw [same, encoding, wordsAt_append]
      exact ⟨by have k2 := keptSource.2; erw [encodeWords_int] at k2; exact k2, by simpa only [integerEncoding_length] using extension⟩

end Gabbro.Stage0.Senke
