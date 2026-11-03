/- Normalization and shared evaluation of long-string operand spans. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Frame.String.Code
public import Stage0.Senke.Ausdruck.Aggregat.Frame.StringExpandOk
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}
variable {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
variable {fp : Runner.W} {K : Nat}

@[simp] theorem stringCapacity_ge (n : Nat) : 2 ≤ stringCapacity n := Nat.le_max_left _ _
@[simp] theorem stringCapacity_bound (n : Nat) : n ≤ stringCapacity n := Nat.le_max_right _ _

def stringSpanValue {n : Nat} (v : Wert D (.str n)) : Wert D (.str (stringCapacity n)) :=
  ⟨v.1, Nat.le_trans v.2 (stringCapacity_bound n)⟩

theorem stringSpan_ok {n d top : Nat} {c : List II} {m : Runner.Mem} {pc : Runner.W}
    (v : Wert D (.str n)) (child : Option (List II × Nat))
    (ih : ∀ ca ta, child = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.str n) v)
    (made : stringSpanL n d child = some (c, top)) (fits : top ≤ K)
    (pre : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.str (stringCapacity n)) (stringSpanValue v) := by
  unfold stringSpanL at made
  split at made
  · next short =>
    have cap : stringCapacity n = 2 := Nat.max_eq_left (by omega)
    have value : strWeitW (n := n) 2 v = (⟨v.1, by have := v.2; omega⟩ : Wert D (.str 2)) := by
      apply Subtype.ext
      exact List.take_of_length_le (by have := v.2; omega)
    have run := strExpand_ok short (by omega : 2 ≤ 2) v child (constWords [0] (d + 2))
      rfl ih made fits pre
    simpa only [cap, stringSpanValue, value] using run
  · next long =>
    simp only [Option.map_eq_some_iff] at made
    obtain ⟨⟨cs, ts⟩, childMade, out⟩ := made
    cases out
    obtain ⟨m', run, changed, value⟩ := ih cs ts childMade (by omega) m pc pre
    have cap : stringCapacity n = n := Nat.max_eq_right (by omega)
    refine ⟨m', run, changed, trivial, ?_⟩
    simpa only [encodeWords, cap, stringSpanValue] using value.2

/-- Shared sequential operand evaluation. The continuation sees both complete spans;
    all input words lie below the second child's destination and survive its writes. -/
theorem stringPair_ok {n q d a b need top : Nat} {s t : Option (List II × Nat)}
    {c tail : List II} {m : Runner.Mem} {pc : Runner.W}
    (vs : Wert D (.str n)) (vt : Wert D (.str q)) (R : Runner.Mem → Prop)
    (da : d ≤ a) (ab : b = a + (stringCapacity n + 1))
    (endFits : b + (stringCapacity q + 1) ≤ need)
    (ihs : ∀ ca ta, s = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K a ca ρ W reserved → ValueOk L m pc fp K a ca (.str n) vs)
    (iht : ∀ ca ta, t = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K b ca ρ W reserved → ValueOk L m pc fp K b ca (.str q) vt)
    (made : (do
      let cs ← stringSpanL n a s
      let ct ← stringSpanL q b t
      pure (cs.1 ++ ct.1 ++ tail, max (max cs.2 ct.2) need)) = some (c, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d c ρ W reserved)
    (finish : ∀ m pc, Pre L m pc fp K d tail ρ W reserved → need ≤ K →
      ValueAt L m fp a (.str (stringCapacity n)) (stringSpanValue vs) →
      ValueAt L m fp b (.str (stringCapacity q)) (stringSpanValue vt) →
      Executes m pc fp K d tail R) : Executes m pc fp K d c R := by
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at made
  obtain ⟨⟨cs, ts⟩, hs, ⟨ct, tt⟩, ht, rfl, rfl⟩ := made
  have p : Pre L m pc fp K a (cs ++ (ct ++ tail)) ρ W reserved :=
    { (show Pre L m pc fp K d (cs ++ (ct ++ tail)) ρ W reserved from
        by simpa only [List.append_assoc] using pre) with ctx := Nat.le_trans pre.ctx da }
  obtain ⟨m1, s1, ch1, v1⟩ := stringSpan_ok vs s ihs hs (by omega) p.left
  have p1 := p.next ch1 (by have := stringCapacity_ge n; omega : a ≤ b) (by omega)
  obtain ⟨m2, s2, ch2, v2⟩ := stringSpan_ok (m := m1) vt t iht ht (by omega) p1.left
  have p2 : Pre L m2 _ fp K d tail ρ W reserved :=
    { p1.next ch2 (Nat.le_refl _) (by omega) with ctx := pre.ctx }
  have kept := v1.agree_low ch2 p1.frame.room
    (by simp only [valueWords, if_neg (show ¬ stringCapacity n ≤ 1 by have := stringCapacity_ge n; omega)]; omega)
    (by omega)
  obtain ⟨m3, s3, ch3, out⟩ := finish m2 _ p2 (by omega) kept v2
  refine ⟨m3, ?_, (ch1.mono da).trans ((ch2.mono (by omega)).trans ch3), out⟩
  simpa only [List.length_append, pc_add, BitVec.add_assoc] using s1.trans (s2.trans s3)

end Gabbro.Stage0.Senke
