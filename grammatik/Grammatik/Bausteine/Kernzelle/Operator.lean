module

public import Grammatik.Isabelle.AccumulatesMonoid
public import Grammatik.Kern.Syntax.Typen.Teil1
public import Grammatik.Kern.Semantik.Semantik.T2.Teil2

@[expose] public section



namespace Gabbro.Grammatik.Kernzelle

open Gabbro.Grammatik Gabbro.Grammatik.Isabelle.AccumulatesMonoid

/-! ## 1. The closed merge vocabulary -/

/-- The five closed merge operators of `accumulates` (SYNTAX.md §11.4,
    `beispiele/0023-akkumulatoren.gab`): `max`, `min`, `add` and the bitwise
    `or`/`and`. No other operator is admitted. -/
inductive AccOperator where
  | max
  | min
  | add
  | or
  | and
  deriving DecidableEq, Repr

/-- The merge on mathematical integers. Bitwise operators read their
    operands as natural numbers (the caller owes nonnegativity, from the
    validity below) and return a natural number. -/
def mergeInt : AccOperator → Int → Int → Int
  | .max, a, b => max a b
  | .min, a, b => min a b
  | .add, a, b => a + b
  | .or, a, b => (a.toNat ||| b.toNat : Nat)
  | .and, a, b => (a.toNat &&& b.toNat : Nat)

/-- The neutral element of the operator: `max` starts at the range floor,
    `min` at its ceiling, `add` and `or` at zero, `and` at the `w`-bit
    all-ones pattern. A restricted range lacking its neutral is rejected
    (`akkuGueltig`), never silently started at zero. -/
def neutralInt : AccOperator → Int → Int → Nat → Int
  | .max, lo, _, _ => lo
  | .min, _, hi, _ => hi
  | .add, _, _, _ => 0
  | .or, _, _, _ => 0
  | .and, _, _, w => ((2 ^ w - 1 : Nat) : Int)

/-- **Validity of an accumulator schema**: the range is inhabited, the
    storage width is positive, bitwise operators fit their encoding, and the
    neutral element inhabits the declared range. The signed reading of a bit
    pattern is explicit (`musterAlsInt`, below); the range positions it. -/
def akkuGueltig : AccOperator → Int → Int → Nat → Prop
  | .max, lo, hi, _ => lo ≤ hi
  | .min, lo, hi, _ => lo ≤ hi
  | .add, lo, hi, _ => lo ≤ hi ∧ lo ≤ 0 ∧ 0 ≤ hi
  | .or, lo, hi, w => lo ≤ hi ∧ 1 ≤ w ∧ lo ≤ 0 ∧ 0 ≤ hi ∧ 0 ≤ lo ∧ hi < 2 ^ w
  | .and, lo, hi, w => lo ≤ hi ∧ 1 ≤ w ∧ 0 ≤ lo ∧ hi < 2 ^ w ∧
      lo ≤ ((2 ^ w - 1 : Nat) : Int) ∧ ((2 ^ w - 1 : Nat) : Int) ≤ hi

/-- The neutral element inhabits the declared range. -/
theorem neutralBewohnt {op : AccOperator} {lo hi : Int} {w : Nat}
    (h : akkuGueltig op lo hi w) : lo ≤ neutralInt op lo hi w ∧ neutralInt op lo hi w ≤ hi := by
  cases op with
  | max => exact ⟨Int.le_refl _, h⟩
  | min => exact ⟨h, Int.le_refl _⟩
  | add => exact ⟨h.2.1, h.2.2⟩
  | or => exact ⟨h.2.2.1, h.2.2.2.1⟩
  | and => exact ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- Two's complement reading of a `w`-bit pattern: the signed
    interpretation the declaration names (`vorzeichen`), explicit. -/
def musterAlsInt (w x : Nat) : Int :=
  if x < 2 ^ (w - 1) then (x : Int) else (x : Int) - 2 ^ w

/-- The signed reading lands in the two's complement range. -/
theorem musterBereich (w x : Nat) (hw : 1 ≤ w) (hx : x < 2 ^ w) :
    -(2 ^ (w - 1) : Int) ≤ musterAlsInt w x ∧ musterAlsInt w x < 2 ^ (w - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  have h2 : (2 : Int) ^ (k + 1) = 2 ^ k * 2 := Int.pow_succ 2 k
  have hN : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
  rw [hN] at hx
  unfold musterAlsInt
  simp only [Nat.add_sub_cancel]
  rw [h2]
  have hc : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := Int.natCast_pow 2 k
  split
  · constructor <;> omega
  · constructor <;> omega

/-! ## 2. The typed monoids -/

/-- Equality of two range values from equality of their numbers. -/
theorem Zahl.ext {lo hi : Int} {a b : Zahl lo hi} (h : a.n = b.n) : a = b := by
  obtain ⟨an, alo, ahi⟩ := a
  obtain ⟨bn, blo, bhi⟩ := b
  simp only at h
  subst h
  rfl

/-- `max` on range values: closed, associative, commutative, neutral at the
    floor. (The abstract facts are `maxMonoid` over `Nat` in
    `AccumulatesMonoid.lean`; those do not prove the signed word case.) -/
def maxZahlOp (lo hi : Int) (a b : Zahl lo hi) : Zahl lo hi :=
  ⟨max a.n b.n, by have := a.lo_le; have := b.lo_le; omega,
    by have := a.le_hi; have := b.le_hi; omega⟩

def maxZahlMonoid (lo hi : Int) (h : lo ≤ hi) : MergeMonoid (Zahl lo hi) where
  op := maxZahlOp lo hi
  neutral := ⟨lo, Int.le_refl lo, h⟩
  assoz a b c := Zahl.ext (Int.max_assoc a.n b.n c.n)
  komm a b := Zahl.ext (Int.max_comm a.n b.n)
  links a := Zahl.ext (by
    show max lo a.n = a.n
    have := a.lo_le
    omega)

/-- `min` on range values: neutral at the ceiling. -/
def minZahlOp (lo hi : Int) (a b : Zahl lo hi) : Zahl lo hi :=
  ⟨min a.n b.n, by have := a.lo_le; have := b.lo_le; omega,
    by have := a.le_hi; have := b.le_hi; omega⟩

def minZahlMonoid (lo hi : Int) (h : lo ≤ hi) : MergeMonoid (Zahl lo hi) where
  op := minZahlOp lo hi
  neutral := ⟨hi, h, Int.le_refl hi⟩
  assoz a b c := Zahl.ext (Int.min_assoc a.n b.n c.n)
  komm a b := Zahl.ext (Int.min_comm a.n b.n)
  links a := Zahl.ext (by
    show min hi a.n = a.n
    have := a.le_hi
    omega)

/-- `(+)` on mathematical integers: the total monoid. It is NOT a monoid on
    a bounded subtype; checked addition keeps every prefix in range by user
    duty (`addKetteImBereich`, below), never by wrapping. -/
def addIntMonoid : MergeMonoid Int where
  op a b := a + b
  neutral := 0
  assoz := Int.add_assoc
  komm := Int.add_comm
  links := Int.zero_add

/-- `(|||)` on `Nat`: the total monoid with neutral `0`. -/
def orNatMonoid : MergeMonoid Nat where
  op a b := a ||| b
  neutral := 0
  assoz := Nat.or_assoc
  komm := Nat.or_comm
  links := Nat.zero_or

/-- `(&&&)` below `2 ^ w`: neutral at the all-ones pattern. -/
def andMaskMonoid (w : Nat) (hw : 1 ≤ w) : MergeMonoid { x : Nat // x < 2 ^ w } where
  op a b := ⟨a.val &&& b.val, by
    have h := Nat.and_le_left (n := a.val) (m := b.val)
    have := a.property
    omega⟩
  neutral := ⟨2 ^ w - 1, by
    have h1 : (1 : Nat) < 2 ^ w := Nat.one_lt_two_pow (by omega)
    omega⟩
  assoz a b c := Subtype.ext (Nat.and_assoc a.val b.val c.val)
  komm a b := Subtype.ext (Nat.and_comm a.val b.val)
  links a := Subtype.ext (by
    show (2 ^ w - 1) &&& a.val = a.val
    rw [Nat.and_comm]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow a.property)

/-- `(|||)` below `2 ^ w`: closed and neutral at zero. -/
def orMaskMonoid (w : Nat) (hw : 1 ≤ w) : MergeMonoid { x : Nat // x < 2 ^ w } where
  op a b := ⟨a.val ||| b.val, Nat.or_lt_two_pow a.property b.property⟩
  neutral := ⟨0, by
    have h1 : (1 : Nat) < 2 ^ w := Nat.one_lt_two_pow (by omega)
    omega⟩
  assoz a b c := Subtype.ext (Nat.or_assoc a.val b.val c.val)
  komm a b := Subtype.ext (Nat.or_comm a.val b.val)
  links a := Subtype.ext (Nat.zero_or a.val)

/-! ## 3. Checked addition: the prefix duty -/

/-- Every prefix sum of the contributions, from `z`, stays in range: the
    user duty for checked addition (all compared prefixes in range). -/
def addKetteOk (lo hi z : Int) : List Int → Prop
  | [] => lo ≤ z ∧ z ≤ hi
  | x :: xs => lo ≤ z ∧ z ≤ hi ∧ lo ≤ z + x ∧ z + x ≤ hi ∧ addKetteOk lo hi (z + x) xs

/-- The RMW chain over the contributions equals the start plus their sum. -/
theorem addKetteGleichSumme (z : Int) (xs : List Int) :
    rmwKette addIntMonoid z xs = z + xs.sum := by
  induction xs generalizing z with
  | nil => simp only [rmwKette, List.sum_nil, Int.add_zero]
  | cons x xs ih =>
      simp only [rmwKette, List.sum_cons]
      rw [ih]
      show z + x + xs.sum = z + (x + xs.sum)
      exact Int.add_assoc z x xs.sum

/-- Under the prefix duty the chain stays in range. -/
theorem addKetteImBereich {lo hi z : Int} {xs : List Int}
    (h : addKetteOk lo hi z xs) : lo ≤ rmwKette addIntMonoid z xs ∧ rmwKette addIntMonoid z xs ≤ hi := by
  induction xs generalizing z with
  | nil =>
      simp only [rmwKette] at h ⊢
      exact h
  | cons x xs ih =>
      simp only [rmwKette, addKetteOk] at h ⊢
      obtain ⟨hlo, hhi, hlo', hhi', hrest⟩ := h
      exact ih hrest

/-- A sum of nonnegative contributions is nonnegative. -/
theorem sumNonneg {xs : List Int} (h : ∀ x ∈ xs, 0 ≤ x) : 0 ≤ xs.sum := by
  induction xs with
  | nil => simp only [List.sum_nil]; exact Int.le_refl 0
  | cons x xs ih =>
      simp only [List.sum_cons]
      have hx : 0 ≤ x := h x List.mem_cons_self
      have hr := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
      omega

/-- Nonnegative contributions suffice when the total fits: every prefix lies
    between the start and the total. Mixed signs need the stronger prefix
    duty above. -/
theorem addNichtnegGenuegt {lo hi z : Int} {xs : List Int}
    (h0 : lo ≤ z ∧ z ≤ hi) (hnn : ∀ x ∈ xs, 0 ≤ x)
    (htot : z + xs.sum ≤ hi) : addKetteOk lo hi z xs := by
  induction xs generalizing z with
  | nil => exact h0
  | cons x xs ih =>
      have hx : 0 ≤ x := hnn x List.mem_cons_self
      have hrest : ∀ y ∈ xs, 0 ≤ y := fun y hy => hnn y (List.mem_cons_of_mem _ hy)
      simp only [List.sum_cons] at htot
      have hxs_nn : 0 ≤ xs.sum := sumNonneg hrest
      refine ⟨h0.1, h0.2, by omega, by omega, ih ⟨by omega, by omega⟩ hrest (by omega)⟩

/-! ## 4. Merge duties at the cell update -/

/-- `max` of two in-range values stays in range: the update's conditional
    selection needs no check, never wraps or saturates. -/
theorem maxMergeImBereich {lo hi a b : Int} (ha : lo ≤ a ∧ a ≤ hi)
    (hb : lo ≤ b ∧ b ≤ hi) :
    lo ≤ mergeInt .max a b ∧ mergeInt .max a b ≤ hi := by
  simp only [mergeInt]
  constructor <;> omega

/-- `min` of two in-range values stays in range: the update's conditional
    selection needs no check, never wraps or saturates. -/
theorem minMergeImBereich {lo hi a b : Int} (ha : lo ≤ a ∧ a ≤ hi)
    (hb : lo ≤ b ∧ b ≤ hi) :
    lo ≤ mergeInt .min a b ∧ mergeInt .min a b ≤ hi := by
  simp only [mergeInt]
  constructor <;> omega

/-- Checked `add`: under the single-step prefix duty the merge stays in
    range. The elaborated update and fold enforce the duty with required
    narrowing (`trimReq`): a violated duty stops with `Logik.kapazitaet`,
    never a dropped contribution or a restart from neutral. -/
theorem addMergeSchritt {lo hi z x : Int}
    (h : lo ≤ z ∧ z ≤ hi ∧ lo ≤ z + x ∧ z + x ≤ hi) :
    lo ≤ mergeInt .add z x ∧ mergeInt .add z x ≤ hi := by
  simp only [mergeInt]
  omega

/-- Bitwise `or` of two values below `2 ^ w` stays below `2 ^ w`: the
    encoding is closed, while the declared `[lo, hi]` bound stays a required
    (`trimReq`) duty of the update and the fold. -/
theorem orMergeWeite {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    0 ≤ mergeInt .or (a : Int) (b : Int) ∧
      mergeInt .or (a : Int) (b : Int) < ((2 ^ w : Nat) : Int) := by
  have h := Nat.or_lt_two_pow ha hb
  simp only [mergeInt, Int.toNat_natCast]
  exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr h⟩

/-- Bitwise `and` of natural values stays non-negative and below each
    operand: the upper range bound is free, the lower bound and the width
    stay required (`trimReq`) duties of the update and the fold. -/
theorem andMergeSchranke {a b : Nat} :
    0 ≤ mergeInt .and (a : Int) (b : Int) ∧
      mergeInt .and (a : Int) (b : Int) ≤ (b : Int) := by
  have h := Nat.and_le_right (n := a) (m := b)
  simp only [mergeInt, Int.toNat_natCast]
  exact ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr h⟩

/-! ## 5. The named traps -/

/-- The named trap: `min` started at `0` drags every nonnegative result to `0`
    (the word case of `min_mit_null_start_zieht_auf_null`). -/
theorem minStartBeiNullFalle (T : Int) (hT : 0 ≤ T) : min T 0 = 0 := by
  omega

/-- The named trap: `and` started at `0` drags every result to `0`. -/
theorem andStartBeiNullFalle (x : Nat) : x &&& 0 = 0 :=
  Nat.and_zero x

#print axioms Gabbro.Grammatik.Kernzelle.neutralBewohnt
#print axioms Gabbro.Grammatik.Kernzelle.musterBereich
#print axioms Gabbro.Grammatik.Kernzelle.addKetteGleichSumme
#print axioms Gabbro.Grammatik.Kernzelle.addKetteImBereich
#print axioms Gabbro.Grammatik.Kernzelle.sumNonneg
#print axioms Gabbro.Grammatik.Kernzelle.addNichtnegGenuegt
#print axioms Gabbro.Grammatik.Kernzelle.maxMergeImBereich
#print axioms Gabbro.Grammatik.Kernzelle.minMergeImBereich
#print axioms Gabbro.Grammatik.Kernzelle.addMergeSchritt
#print axioms Gabbro.Grammatik.Kernzelle.orMergeWeite
#print axioms Gabbro.Grammatik.Kernzelle.andMergeSchranke

/-- The unsigned byte accumulator starts bitwise AND at all eight bits set. -/
theorem neutralAndByte_zeuge : neutralInt .and 0 255 8 = 255 := by decide

/-! ## 6. Required narrowing: overflow stops -/

/-- Out of range at a required narrowing is a capacity failure: the generic
    half of the accumulator's overflow duty. The generated update narrows the
    merge to the cell range and the fold narrows the running total to the
    result range; either step outside its range is `Logik.kapazitaet`,
    excluded by the caller's capacity duty (`KoerperGutS/SA`) -- never a
    dropped contribution, a restart from neutral, a wrap or a saturation. -/
theorem narrowRequiredAusserhalb {D : Deklaration} (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {lo hi lo' hi' : Int} (e : Expr D Γ Λ (.int lo hi))
    (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ)
    (h : ¬ (lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi')) :
    execBlock (V := V) O passes R (Block.narrowRequired e lo' hi' rest) σ ρ
      = .logik .kapazitaet := by
  simp only [execBlock]
  rw [dif_neg h]

#print axioms Gabbro.Grammatik.Kernzelle.narrowRequiredAusserhalb

end Gabbro.Grammatik.Kernzelle
