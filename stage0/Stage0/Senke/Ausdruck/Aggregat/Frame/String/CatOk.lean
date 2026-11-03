/- The actual concatenation kernel copies both spans and preserves their headers. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Frame.String.Span
public import Stage0.Senke.Ausdruck.Aggregat.Frame.String.Append
public import Stage0.Senke.Welt.WeltAt
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}
variable {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
variable {fp : Runner.W} {K : Nat}

private theorem zeros_top (q z : Nat) : (constWords (List.replicate q 0) z).2 = z + q := by
  induction q generalizing z with
  | zero => simp [constWords]
  | succ q ih =>
    simp only [List.replicate_succ, constWords, ih]
    simp [wordConst, lit32, Nat.max_eq_right (by omega : z + 1 ≤ z + 1 + q)]

private theorem trimPre {m : Runner.Mem} {pc : Runner.W} {d bound : Nat} {code : List II}
    (pre : Pre L m pc fp K d code ρ W reserved) (fits : bound ≤ K) :
    Pre L m pc fp bound d code ρ W reserved :=
  ⟨pre.ctx, by have := pre.small; omega, frameOK_sub pre.frame fits, pre.code,
    codeFar_sub2 pre.far fits, pre.env, pre.welt,
    fun m m' hw changed => pre.wstab m m' hw (Agree.widen changed fits)⟩

theorem stringCatC_ok {n q d a b ptr need : Nat} {m : Runner.Mem} {pc : Runner.W}
    (vs : Wert D (.str n)) (vt : Wert D (.str q))
    (long : 2 ≤ n + q) (pa : a = d + (n + q + 1))
    (pb : b = a + (stringCapacity n + 1)) (pt : ptr = b + (stringCapacity q + 1))
    (needFits : max (ptr + 2) (constWords (List.replicate q 0) (d + 1 + n)).2 ≤ need)
    (fits : need ≤ K)
    (spanA : ValueAt L m fp a (.str (stringCapacity n)) (stringSpanValue vs))
    (spanB : ValueAt L m fp b (.str (stringCapacity q)) (stringSpanValue vt))
    (pre : Pre L m pc fp K d (stringCatC n q d a b ptr) ρ W reserved) :
    ValueOk L m pc fp K d (stringCatC n q d a b ptr) (.str (n + q)) (strCatW vs vt) := by
  have la := vs.2
  have lb := vt.2
  have cn := stringCapacity_bound n
  have cq := stringCapacity_bound q
  have small := pre.small
  have room := pre.frame.room
  have widthA := stringBytes_length vs.1 la
  have widthB := stringBytes_length vt.1 lb
  have bytesA := stringSpan_bytes (stringCapacity_ge n) cn (stringSpanValue vs) la spanA
  have bytesB := stringSpan_bytes (stringCapacity_ge q) cq (stringSpanValue vt) lb spanB
  have lenA := span_len_read (stringCapacity_ge n) (stringSpanValue vs) spanA
  have lenB := span_len_read (stringCapacity_ge q) (stringSpanValue vt) spanB
  have p : Pre L m pc fp K d
      (copyWords n (d + 1) (a + 1) ++
        ((constWords (List.replicate q 0) (d + 1 + n)).1 ++
          (stringAppendC q (d + 1) (b + 1) a ptr 0 ++ [ci 3 d a b]))) ρ W reserved := by
    simpa only [stringCatC, List.append_assoc] using pre
  obtain ⟨m1, s1, ch1, copied⟩ := copyWords_run (stringBytes n vs.1) pre.frame small
    (by omega) (by omega) (Or.inl (by omega))
    (by simpa only [widthA] using p.left.code)
    (by simpa only [widthA, copyWords_length] using p.left.far) bytesA
  simp only [widthA] at s1
  have ch1' : Agree fp (d + 1) (d + 1 + n) m m1 := by simpa only [widthA] using ch1
  have p1 := p.next ((Agree.widen ch1' (by omega)).mono (by omega : d ≤ d + 1))
    (by omega : d ≤ d + 1 + n) (by omega)
  simp only [copyWords_length] at p1
  have pz := trimPre p1.left (by omega : a ≤ K)
  obtain ⟨m2, s2, ch2, zeros⟩ := constWords_ok (L := L) (List.replicate q 0)
    (by rw [zeros_top]; omega) pz
  have ch2' : Agree fp (d + 1 + n) a m1 m2 := ch2
  have ch12 : Agree fp (d + 1) a m m2 :=
    (Agree.widen ch1' (by omega)).trans (ch2'.mono (by omega))
  have p2 := p1.next ((Agree.widen ch2' (by omega)).mono (by omega : d + 1 + n ≤ d + 1 + n))
    (Nat.le_refl _) (by omega)
  have p2' : Pre L m2 _ fp K (d + 1)
      (stringAppendC q (d + 1) (b + 1) a ptr 0 ++ [ci 3 d a b]) ρ W reserved :=
    { p2 with ctx := by have := pre.ctx; omega }
  have old : WordsAt m2 fp (d + 1) (stringBytes n vs.1 ++ List.replicate q 0) := by
    rw [wordsAt_append]
    refine ⟨copied.agree_low ch2' (by omega) (by omega) (by omega), ?_⟩
    simpa only [widthA, Nat.add_assoc] using zeros
  have lenA2 : m2.rd64 (slot fp (BitVec.ofNat 64 a)) = some (BitVec.ofNat 64 vs.1.length) := by
    rw [agree_rd_above ch12 room (Nat.le_refl _) (by omega)]; exact lenA
  have bytesB2 : WordsAt m2 fp (b + 1) (stringBytes q vt.1) := by
    intro i hi
    rw [agree_rd_above ch12 room (by omega) (by omega)]
    exact bytesB i hi
  obtain ⟨m3, s3, ch3, appended, kept⟩ := stringAppend_ok (L := L) (stringBytes q vt.1)
    (by omega) (by omega) (by omega) (by omega) lenA2 bytesB2
    (by simpa only [widthB] using p2'.left)
  simp only [widthB] at s3
  have p3 : Pre L m3 _ fp K d [ci 3 d a b] ρ W reserved :=
    { p2'.next ch3 (Nat.le_refl _) (by omega) with ctx := pre.ctx }
  have readA : m3.rd64 (slot fp (BitVec.ofNat 64 a)) = some (BitVec.ofNat 64 vs.1.length) := by
    rw [kept a (by omega) (Or.inr (by omega))]; exact lenA2
  have readB : m3.rd64 (slot fp (BitVec.ofNat 64 b)) = some (BitVec.ofNat 64 vt.1.length) := by
    rw [kept b (by omega) (Or.inr (by omega)), agree_rd_above ch12 room (by omega) (by omega)]
    exact lenB
  obtain ⟨m4, s4, ch4, header⟩ := bin_exact_ok p3 (by omega) (by omega) (by omega)
    readA readB (g := fun a b => some (a + b)) rfl (by decide) rfl
  have bytes3 : WordsAt m3 fp (d + 1)
      (vs.1.map (fun b => BitVec.ofInt 64 b.n) ++ stringBytes q vt.1 ++ List.replicate (n - vs.1.length) 0) := by
    apply wordsAt_cat _ _ (by simpa using la) (by simpa using lb) (by omega)
    · simpa only [stringBytes, List.append_assoc, List.replicate_append_replicate, List.length_map] using old
    · simpa only [stringBytes, List.length_map, Nat.add_zero] using appended
    · simpa only [List.length_map, widthB, Nat.add_zero] using kept
  refine ⟨m4, ?_, ((Agree.widen ch12 (by omega)).mono (by omega)).trans
    ((ch3.mono (by omega)).trans (Agree.widen ch4 (by omega))), trivial, ?_⟩
  · simpa only [stringCatC, List.length_append, copyWords_length, widthA, widthB,
      stringAppendC_length, List.length_cons, List.length_nil, pc_add, Nat.reduceAdd,
      BitVec.add_assoc] using s1.trans (s2.trans (s3.trans s4))
  · rw [stringCat_encoding L long vs vt]
    intro i hi
    cases i with
    | zero => simpa only [Nat.add_zero, List.getElem_cons_zero, BitVec.ofNat_add] using header
    | succ i =>
      rw [show d + (i + 1) = d + 1 + i by omega,
        agree_rd_above ch4 room (by omega) (by simp at hi; simp only [List.length_append,
          List.length_map, stringBytes_length vt.1 lb, List.length_replicate] at hi; omega)]
      exact bytes3 i (by simpa using hi)

end Gabbro.Stage0.Senke
