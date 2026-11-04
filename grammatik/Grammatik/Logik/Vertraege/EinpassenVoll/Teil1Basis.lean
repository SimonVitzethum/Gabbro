module
public import Grammatik.Kern.Syntax.Typen.Fall
public import NativeFloat.Transport

public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Kern.Semantik.Semantik.T1.SummeTransport

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Sums -/

/-- The payload of a case as a raw number (a bare case: `0`). -/
def nutzRoh : (c : Option Ty) → Nutzlast D.Fn D.passt c → Int
  | Option.none, _ => 0
  | Option.some (.int _ _), z => z.n
  | Option.some _, _ => 0

theorem nutzPasst_nutzRoh : ∀ (c : Option Ty) (x : Nutzlast D.Fn D.passt c),
    nutzWort c → nutzPasst c (nutzRoh c x) = some x
  | none, x, _ => by cases x; rfl
  | some τ, x, h => by
      cases τ <;> try exact h.elim
      rename_i lo hi
      show (if h : lo ≤ x.n ∧ x.n ≤ hi then some ⟨x.n, h.1, h.2⟩ else none) = some x
      rw [dif_pos ⟨x.lo_le, x.le_hi⟩]
      rfl

/-- A decoded raw payload has exactly a supported payload shape. -/
theorem nutzPasst_wort (c : Option Ty) (n : Int) (v : Nutzlast D.Fn D.passt c)
    (h : nutzPasst c n = some v) : nutzWort c := by
  cases c with
  | none => trivial
  | some τ => cases τ <;> first | trivial | cases h

/-- **The raw word of a `tagged` value**: `marke + |cases| * last`. -/
def summeRoh (cs : List (Option Ty)) (v : Σ i : Fin cs.length, Fall D.Fn D.passt cs i) :
    Int :=
  (v.1.val : Int) + fallZahl cs * nutzRoh (cs.get v.1) (Fall.toNutzlast _ _ _ _ v.2)

/-- **Every `tagged` value is the decoding of its raw word.** -/
theorem summePasst_voll (cs : List (Option Ty))
    (v : Σ i : Fin cs.length, Fall D.Fn D.passt cs i) (hv : sumWort cs = true) : summePasst cs (summeRoh cs v) = some v := by
  have hk : (0 : Int) < fallZahl cs := by
    have := v.1.2
    unfold fallZahl
    omega
  have hi0 : (0 : Int) ≤ (v.1.val : Int) := Int.natCast_nonneg _
  have hi1 : (v.1.val : Int) < fallZahl cs := by
    have := v.1.2
    unfold fallZahl
    omega
  have hmod : summeRoh cs v % fallZahl cs = (v.1.val : Int) := by
    unfold summeRoh
    rw [Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt hi0 hi1
  have hdiv : summeRoh cs v / fallZahl cs = nutzRoh (cs.get v.1) (Fall.toNutzlast _ _ _ _ v.2) := by
    unfold summeRoh
    rw [Int.add_mul_ediv_left _ _ (Int.ne_of_gt hk), Int.ediv_eq_zero_of_lt hi0 hi1, Int.zero_add]
  rw [summePasst_eq cs _ v.1 _ hv hmod hdiv, nutzPasst_nutzRoh _ _ (sumWort_get cs hv v.1)]
  show some (⟨v.1, Fall.ofNutzlast _ _ _ _ (Fall.toNutzlast _ _ _ _ v.2)⟩ :
    Val D.Fn D.passt (.sum cs)) = some v
  rw [Fall.of_to]

/-! ## 2. Floats -/

/-- Every native finite in-range value is decoded from its own CPU word. -/
theorem gleitWortPasst_voll (lo hi : Int × Int) (v : Gleit lo hi) :
    gleitWortPasst lo hi (v.x.toBits.toNat : Int) = some v := by
  have hlt : v.x.toBits.toNat < 18446744073709551616 := v.x.toBits.toNat_lt_size
  unfold gleitWortPasst
  rw [if_pos ⟨Int.natCast_nonneg _, by unfold gleitWortGrenze; omega⟩,
    Int.toNat_natCast, UInt64.ofNat_toNat, RootNativeFloat.bits_roundtrip]
  unfold gleitPasst
  rw [dif_pos ⟨v.endlich, v.lo_le, v.le_hi⟩]

/-! ## 3. Function pointers -/

/-- **Every function conforming to `fnptr m` is the answer of an image that places it at `0`.** -/
theorem zeigerPasst_voll (m : Nat) (v : {f : D.Fn // D.passt f m = true}) :
    zeigerPasst (fun _ => some v.1) m 0 = some v := by
  show (if h : D.passt v.1 m = true then some ⟨v.1, h⟩ else Option.none) = some v
  rw [dif_pos v.2]

/-! ## 4. Every type -/

/-- The values the scalar answer boundary can carry. Native float representation
    validity is inherent in `Float`; its finite/range facts are already in `Gleit`. -/
def WertOk : (τ : Ty) → Wert D τ → Prop
  | .sum cs, _ => sumWort cs = true
  | .fl _ _, _ => True
  -- an aggregate is not one raw word: no answer has such a value
  | .arr _ _, _ => False
  | .str _, _ => False
  | .prod _ _, _ => False
  | _, _ => True

/-- Every scalar-boundary value, including every native in-range float, is
    decoded from some raw word under some image. -/
theorem einpassen_voll : ∀ (τ : Ty) (v : Wert D τ), WertOk τ v →
    ∃ (z : Int → Option D.Fn) (n : Int), einpassen z τ n = some v
  | .int lo hi, v, _ => ⟨fun _ => Option.none, (v : Zahl lo hi).n, by
      simp only [einpassen]
      rw [dif_pos ⟨(v : Zahl lo hi).lo_le, (v : Zahl lo hi).le_hi⟩]
      rfl⟩
  | .bool, b, _ => by
      cases b
      · exact ⟨fun _ => Option.none, 0, rfl⟩
      · exact ⟨fun _ => Option.none, 1, rfl⟩
  | .opt m, o, _ => by
      cases o with
      | none =>
          refine ⟨fun _ => Option.none, -1, ?_⟩
          simp only [einpassen]
          rw [dif_neg (by omega), if_pos (by omega)]
      | some k =>
          refine ⟨fun _ => Option.none, k.n, ?_⟩
          simp only [einpassen]
          rw [dif_pos ⟨k.lo_le, k.le_hi⟩]
  | .sum cs, v, h => ⟨fun _ => Option.none, summeRoh cs v, summePasst_voll cs v h⟩
  | .why m, r, _ => ⟨fun _ => Option.none, ((r : Fin m).val : Int), by
      simp only [einpassen]
      rw [dif_pos ⟨Int.natCast_nonneg _, by have := (r : Fin m).2; omega⟩]
      exact congrArg some (Fin.ext (Int.toNat_natCast _))⟩
  | .never, v, _ => (v : Empty).elim
  | .fl lo hi, v, _ => ⟨fun _ => Option.none, _, gleitWortPasst_voll lo hi v⟩
  | .fnptr m, v, _ => ⟨fun _ => some (v : {f : D.Fn // D.passt f m = true}).1, 0, zeigerPasst_voll m v⟩
  | .ptr _, _, _ => ⟨fun _ => Option.none, 0, rfl⟩
  | .ref _, r, _ => ⟨fun _ => Option.none, ((Val.zelle r : Nat) : Int), by
      simp only [einpassen, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]
      rfl⟩
  | .arr _ _, _, h => h.elim
  | .str _, _, h => h.elim
  | .prod _ _, _, h => h.elim

/-- Every decoded value is a value an answer can have. -/

theorem einpassen_wertOk : ∀ (z : Int → Option D.Fn) (τ : Ty) (n : Int) (v : Wert D τ),
    einpassen z τ n = some v → WertOk τ v
  | _, .fl _ _, _, _, _ => trivial
  | _, .int _ _, _, _, _ => trivial
  | _, .bool, _, _, _ => trivial
  | _, .opt _, _, _, _ => trivial
  | _, .sum cs, n, v, h => by
      have h' : summePasst cs n = some v := h
      unfold summePasst at h'
      split at h'
      · assumption
      · cases h'
  | _, .why _, _, _, _ => trivial
  | _, .never, _, _, _ => trivial
  | _, .fnptr _, _, _, _ => trivial
  | _, .ptr _, _, _, _ => trivial
  | _, .ref _, _, _, _ => trivial

/-- **The answer class is empty EXACTLY when the type is** (G1 repair): no raw word decodes
    under any image iff the declared type has no value an answer can have. The model decides
    no stop the declared type does not. -/
theorem antwortLeer_iff (τ : Ty) : AntwortLeer D (some τ) ↔ ∀ v : Wert D τ, ¬ WertOk τ v := by
  constructor
  · intro hL v hv
    obtain ⟨z, n, h⟩ := einpassen_voll τ v hv
    have h' : einpassenErg z (some τ) n = some v := h
    rw [hL z n] at h'
    cases h'
  · intro h z n
    show einpassen z τ n = Option.none
    cases he : einpassen z τ n with
    | none => rfl
    | some v => exact absurd (einpassen_wertOk z τ n v he) (h v)

/-- `never` has no value: an axiom returning `never` never returns. -/
theorem antwortLeer_never : AntwortLeer D (some .never) := fun _ _ => rfl

/-- A reason channel without reasons has no value. -/
theorem antwortLeer_grund0 : AntwortLeer D (some (.why 0)) :=
  (antwortLeer_iff _).mpr fun v _ => (v : Fin 0).elim0

/-- An empty range has no value. -/
theorem antwortLeer_int_leer {lo hi : Int} (h : hi < lo) : AntwortLeer D (some (.int lo hi)) :=
  (antwortLeer_iff _).mpr fun v _ => by
    have h1 := (v : Zahl lo hi).lo_le
    have h2 := (v : Zahl lo hi).le_hi
    omega

/-- An axiom without a result always answers (its answer class is `{()}`). -/
theorem antwortLeer_keinErg : ¬ AntwortLeer D Option.none := fun h =>
  nomatch h (fun _ => Option.none) 0

/-- The G1 types have answers: an admitted sum, an inhabited native float range,
    or a function-pointer type with a conforming function. -/
theorem nicht_leer_von (τ : Ty) (v : Wert D τ) (hv : WertOk τ v) : ¬ AntwortLeer D (some τ) :=
  fun h => (antwortLeer_iff τ).mp h v hv


end Gabbro.Grammatik
