/- Stored reads preserve the complete expression simulation and its write footprint. -/
module
public import Stage0.Senke.Ausdruck.Quant.Selection
public import Stage0.Senke.Welt.Spans.CellStore
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- A private address into existing storage, together with the complete value
    there in every memory representing the same environment and world. -/
def StoredOk {Γ : Ctx} (m : Runner.Mem) (pc fp : Runner.W) (K d : Nat)
    (c : List II) (ρ : Env D Γ) (W : Runner.Mem → Prop) (reserved : Nat)
    (τ : Ty) (v : Wert D τ) : Prop :=
  ∃ a, Ok m pc fp K d c (· = a) ∧
    ∀ m', EnvAt L m' fp ρ reserved → W m' → ValueAt L m' a 0 τ v

/-- An element read depends on its element width, never on the enclosing array
    width. The source remains stable through all destination and scratch writes. -/
theorem arrReadL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {fp pc : Runner.W} {K d top reserved n : Nat} {τ : Ty}
    {v : Wert D (.arr τ n)} (j : Zahl 0 (n - 1))
    {address index : Option (List II × Nat)} {c : List II} {m : Runner.Mem}
    (made : arrReadL τ n d address index = some (c, top)) (fits : top ≤ K)
    (addressOk : ∀ ca ta, address = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K (d + valueWords τ) ca ρ W reserved →
      StoredOk (L := L) m pc fp K (d + valueWords τ) ca ρ W reserved (.arr τ n) v)
    (indexOk : ∀ ci' ti, index = some (ci', ti) → ti ≤ K → ∀ m pc,
      Pre L m pc fp K (d + valueWords τ + 1) ci' ρ W reserved →
      ValueOk L m pc fp K (d + valueWords τ + 1) ci' (.index n) j)
    (pre : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c τ (v j.fin) := by
  unfold arrReadL at made
  split at made
  · next available =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at made
    obtain ⟨⟨ca, ta⟩, ha, ⟨ci', ti⟩, hi, rfl, rfl⟩ := made
    let ptr := d + valueWords τ
    let ix := ptr + 1
    let tmp := ptr + 2
    let tail := [ci 1 tmp (8 * valueWords τ) 0, ci 5 ix ix tmp, ci 3 ptr ptr ix] ++
      loadPointerSpan (valueWords τ) d ptr tmp 0
    have hp : Pre L m pc fp K d (ca ++ (ci' ++ tail)) ρ W reserved := by
      simp only [List.append_assoc] at pre
      exact pre
    obtain ⟨a, runA, source⟩ := addressOk ca ta ha (by omega) m pc
      (hp.left.raise (by omega))
    obtain ⟨m1, s1, a1, w1, r1, e1⟩ := runA
    subst w1
    have p1 : Pre L m1 _ fp K ix (ci' ++ tail) ρ W reserved :=
      hp.next (a1.mono (by omega)) (by dsimp only [ix, ptr]; omega) (by omega)
    obtain ⟨m2, s2, a2, valI⟩ := indexOk ci' ti hi (by omega) m1 _ p1.left
    obtain ⟨word, r2, e2⟩ := ValueAt.word (.index n) j trivial valI
    change word = BitVec.ofInt 64 j.n at e2
    subst word
    have p2 := p1.next a2 (Nat.le_refl _) (by dsimp only [ix, ptr]; omega)
    have multiply : Pre L m2 _ fp K ix
        ([ci 1 tmp (8 * valueWords τ) 0, ci 5 ix ix tmp] ++
          ([ci 3 ptr ptr ix] ++ loadPointerSpan (valueWords τ) d ptr tmp 0)) ρ W reserved := p2
    obtain ⟨m3, s3, a3, w3, r3, e3⟩ := binK_ok multiply.left r2
      (by simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega)
      (g := fun x y => some (x * y)) rfl (by decide) rfl
      (by dsimp only [tmp, ix, ptr] at *; omega)
    subst w3
    have p3 := multiply.next a3 (Nat.le_refl _) (by dsimp only [ix, ptr]; omega)
    have addPre : Pre L m3 _ fp K ptr
        ([ci 3 ptr ptr ix] ++ loadPointerSpan (valueWords τ) d ptr tmp 0) ρ W reserved :=
      { p3 with ctx := by have := pre.ctx; dsimp only [ptr]; omega }
    have address3 : m3.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some a := by
      rw [agree_rd_low a3 p2.frame.room (by omega) (by omega),
        agree_rd_low a2 p1.frame.room (by omega) (by omega)]
      exact r1
    obtain ⟨m4, s4, a4, w4, r4, e4⟩ := eng_bin_ok
      addPre.left
      (d := ptr) (by dsimp only [ptr] at *; omega)
      (by dsimp only [ptr] at *; omega) (by dsimp only [ix, ptr] at *; omega)
      address3 r3 (g := fun x y => some (x + y)) rfl (by decide) rfl
    subst w4
    have addressEq : a + BitVec.ofInt 64 j.n * BitVec.ofInt 64 (8 * valueWords τ) =
        slot a (BitVec.ofNat 64 (j.fin.val * valueWords τ)) := by
      have indexWord : BitVec.ofInt 64 j.n = BitVec.ofNat 64 j.n.toNat := by
        rw [← BitVec.ofInt_natCast, Int.toNat_of_nonneg j.lo_le]
      rw [indexWord]
      simp only [Zahl.fin, slot, BitVec.ofInt_mul, BitVec.ofInt_natCast,
        BitVec.ofNat_mul, BitVec.mul_assoc]
      congr 1
      change BitVec.ofNat 64 j.n.toNat * ((8 : Runner.W) * BitVec.ofNat 64 (valueWords τ)) =
        BitVec.ofNat 64 j.n.toNat * (BitVec.ofNat 64 (valueWords τ) * 8)
      rw [BitVec.mul_comm (8 : Runner.W)]
    rw [addressEq] at r4
    have a12 := (a1.mono (by dsimp only [ptr]; omega : d ≤ ptr)).trans
      (a2.mono (by dsimp only [ix, ptr]; omega : d ≤ ix))
    have a123 := a12.trans (a3.mono (by dsimp only [ix, ptr]; omega : d ≤ ix))
    have allChanged := a123.trans (a4.mono (by dsimp only [ptr]; omega : d ≤ ptr))
    have p4 := addPre.next a4 (Nat.le_refl _) (by dsimp only [ptr] at *; omega)
    have frame4 := pre.frame.agree allChanged
    let selected := v j.fin
    let words := encodeWords L τ selected
    obtain ⟨m5, s5, effect, output, _⟩ := loadPointerSpan_core_run words frame4 pre.small
      (dst := d) (ptr := ptr) (tmp := tmp) (offset := 0)
      (by simp only [words, encodeWords_length, ptr]; omega)
      (by dsimp only [tmp]; omega) (by dsimp only [tmp, ptr] at *; omega)
      (by simpa only [Nat.zero_add, words, encodeWords_length] using available.2)
      (by simpa only [words, encodeWords_length] using p4.code)
      (by simpa only [words, encodeWords_length, loadPointerSpan_length] using p4.far) r4
      (fun m' k hk changed => by
        have width : words.length = valueWords τ := encodeWords_length L τ selected
        have ch : Agree fp d K m4 m' := changed.agreeFrame (by dsimp only [tmp, ptr]; omega)
          (by dsimp only [tmp, ptr] at *; omega) (by omega) (by have := frame4.room; omega)
        have total := allChanged.trans ch
        have env := envAt_agree pre.env total pre.frame pre.ctx (by omega)
        have value := (source m' env (pre.wstab _ _ pre.welt (total.mono (Nat.zero_le _)))).array_element j.fin
        simpa only [Nat.zero_add, selected, words, slot_nested] using value.rebase.2 k hk)
    have effect' : SpanEffect fp tmp (fp.toNat + 8 * d) (valueWords τ) m4 m5 := by
      simpa only [words, encodeWords_length] using effect
    have a5 : Agree fp d K m4 m5 := effect'.agreeFrame (by dsimp only [tmp, ptr]; omega)
      (by dsimp only [tmp, ptr] at *; omega) (by omega) (by have := frame4.room; omega)
    refine ⟨m5, ?_, allChanged.trans a5, ?_, output⟩
    · have combined := s1.trans (s2.trans (s3.trans (s4.trans s5)))
      simp only [words, encodeWords_length] at combined
      have pcEq : pc + BitVec.ofNat 64 (16 * ca.length) + BitVec.ofNat 64 (16 * ci'.length) +
          BitVec.ofNat 64 32 + BitVec.ofNat 64 16 + BitVec.ofNat 64 (48 * valueWords τ) =
          pc + BitVec.ofNat 64 (16 * (ca.length + ci'.length + 3 + 3 * valueWords τ)) := by
        simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
        congr 2
        omega
      change Star ⟨pc, fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * ca.length) + BitVec.ofNat 64 (16 * ci'.length) +
          BitVec.ofNat 64 32 + BitVec.ofNat 64 16 + BitVec.ofNat 64 (48 * valueWords τ), fp⟩ m5 at combined
      rw [pcEq] at combined
      simpa only [List.length_append, List.length_cons, List.length_nil,
        loadPointerSpan_length, Nat.reduceAdd, Nat.add_assoc] using combined
    · exact ((source m pre.env pre.welt).array_element j.fin).1
  · cases made

end Gabbro.Stage0.Senke
