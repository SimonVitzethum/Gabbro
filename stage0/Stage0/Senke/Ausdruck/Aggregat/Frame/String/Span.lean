/- Normalization and shared evaluation of long-string operand spans. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Frame.String.Code
public import Stage0.Senke.Ausdruck.Aggregat.Frame.StringExpandOk
public import Stage0.Senke.Ausdruck.Aggregat.Frame.StringTakeOka
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

def stringBytes (n : Nat) (bs : List (Zahl 0 255)) : List Runner.W :=
  bs.map (fun b => BitVec.ofInt 64 b.n) ++ List.replicate (n - bs.length) 0

@[simp] theorem stringBytes_length {n : Nat} (bs : List (Zahl 0 255)) (h : bs.length ≤ n) :
    (stringBytes n bs).length = n := by simp only [stringBytes, List.length_append,
      List.length_map, List.length_replicate]; omega

theorem stringBytes_get {n : Nat} (bs : List (Zahl 0 255)) (h : bs.length ≤ n)
    (j : Nat) (hj : j < n) :
    (stringBytes n bs)[j]? = some (BitVec.ofInt 64 ((bs[j]?).getD ⟨0, by omega, by omega⟩).n) := by
  have read := strBytes_word (n := n) ⟨bs, h⟩ j hj
  simpa only [List.cons_append, List.getElem?_cons_succ, strGetW,
    Int.natCast_nonneg, Int.toNat_natCast, ↓reduceIte, stringBytes] using read

theorem stringSpan_bytes {D : Deklaration} {L : Lay D} {cap n base : Nat}
    {m : Runner.Mem} {fp : Runner.W} (capLong : 2 ≤ cap) (fits : n ≤ cap)
    (v : Wert D (.str cap)) (length : v.1.length ≤ n)
    (span : ValueAt L m fp base (.str cap) v) : WordsAt m fp (base + 1) (stringBytes n v.1) := by
  intro j hj
  have bound : j < n := by simpa only [stringBytes_length v.1 length] using hj
  have read := span.2 (j + 1)
    (by rw [encodeWords_length]; simp only [valueWords, if_neg (show ¬ cap ≤ 1 by omega)]; omega)
  have capGet : (encodeWords L (.str cap) v)[j + 1]? =
      some (BitVec.ofInt 64 (strGetW v (j : Int)).n) := by
    simpa only [encodeWords, if_neg (show ¬ cap ≤ 1 by omega)] using strBytes_word v j (by omega)
  rw [List.getElem?_eq_getElem (by rw [encodeWords_length];
    simp only [valueWords, if_neg (show ¬ cap ≤ 1 by omega)]; omega)] at capGet
  have get := stringBytes_get v.1 length j bound
  rw [List.getElem?_eq_getElem hj] at get
  rw [show base + 1 + j = base + (j + 1) by omega, read]
  rw [Option.some.inj capGet, Option.some.inj get]
  rfl

theorem stringCat_encoding {D : Deklaration} (L : Lay D) {n q : Nat} (long : 2 ≤ n + q)
    (vs : Wert D (.str n)) (vt : Wert D (.str q)) :
    encodeWords L (.str (n + q)) (strCatW vs vt) =
      BitVec.ofNat 64 (vs.1.length + vt.1.length) ::
        (vs.1.map (fun b => BitVec.ofInt 64 b.n) ++
          stringBytes q vt.1 ++ List.replicate (n - vs.1.length) 0) := by
  have la := vs.2
  have lb := vt.2
  simp only [encodeWords, if_neg (show ¬ n + q ≤ 1 by omega), strCatW,
    List.length_append, List.map_append, stringBytes, List.cons_append, List.append_assoc]
  rw [List.replicate_append_replicate]
  congr 3
  omega

/-- Overlay the padded second span on the first span's zero padding. The untouched
    prefix and suffix complete the exact canonical concatenation encoding. -/
theorem wordsAt_cat {m m' : Runner.Mem} {fp : Runner.W} {base ptr n q : Nat}
    (as bs : List Runner.W) (la : as.length ≤ n) (lb : bs.length ≤ q)
    (fits : base + n + q ≤ ptr)
    (old : WordsAt m fp base (as ++ List.replicate (n - as.length + q) 0))
    (written : WordsAt m' fp (base + as.length) (bs ++ List.replicate (q - bs.length) 0))
    (kept : ∀ s, s < ptr → (s < base + as.length ∨ base + as.length + q ≤ s) →
      m'.rd64 (slot fp (BitVec.ofNat 64 s)) = m.rd64 (slot fp (BitVec.ofNat 64 s))) :
    WordsAt m' fp base (as ++ (bs ++ List.replicate (q - bs.length) 0) ++ List.replicate (n - as.length) 0) := by
  rw [wordsAt_append, wordsAt_append]
  refine ⟨⟨?_, written⟩, ?_⟩
  · intro i hi
    rw [kept (base + i) (by omega) (Or.inl (by omega))]
    have h := old i (by simp only [List.length_append, List.length_replicate]; omega)
    simpa only [List.getElem_append_left hi] using h
  · intro i hi
    have len : (bs ++ List.replicate (q - bs.length) 0).length = q := by
      simp only [List.length_append, List.length_replicate]; omega
    have bound : i < n - as.length := by simpa using hi
    have address : base + (as ++ (bs ++ List.replicate (q - bs.length) 0)).length + i =
        base + (as.length + q + i) := by simp only [List.length_append, len]; omega
    rw [address, kept _ (by omega) (Or.inr (by omega))]
    have index : as.length + q + i < (as ++ List.replicate (n - as.length + q) (0 : Runner.W)).length := by
      simp only [List.length_append, List.length_replicate]; omega
    rw [old _ index]
    simp only [List.getElem_append_right (by omega : as.length ≤ as.length + q + i),
      List.getElem_replicate]


end Gabbro.Stage0.Senke
