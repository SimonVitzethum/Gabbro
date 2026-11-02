module

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

/-- A decoded raw payload has exactly a supported payload shape. -/
theorem nutzPasst_wort (c : Option Ty) (n : Int) (v : Nutzlast D.Fn D.passt c)
    (h : nutzPasst c n = some v) : nutzWort c := by
  cases c with
  | none => trivial
  | some τ => cases τ <;> first | trivial | cases h

/-- **The raw word of a `tagged` value**: `marke + |cases| * last`. -/
def summeRoh (cs : List (Option Ty)) (v : Σ i : Fin cs.length, Nutzlast D.Fn D.passt (cs.get i)) :
    Int :=
  (v.1.val : Int) + fallZahl cs * nutzRoh (cs.get v.1) v.2

/-- **Every `tagged` value is the decoding of its raw word.** -/
theorem summePasst_voll (cs : List (Option Ty))
    (v : Σ i : Fin cs.length, Nutzlast D.Fn D.passt (cs.get i)) (hv : sumWort cs = true) : summePasst cs (summeRoh cs v) = some v := by
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
  have hdiv : summeRoh cs v / fallZahl cs = nutzRoh (cs.get v.1) v.2 := by
    unfold summeRoh
    rw [Int.add_mul_ediv_left _ _ (Int.ne_of_gt hk), Int.ediv_eq_zero_of_lt hi0 hi1, Int.zero_add]
  rw [summePasst_eq cs _ v.1 _ hv hmod hdiv, nutzPasst_nutzRoh _ _ (sumWort_get cs hv v.1)]
  rfl

/-! ## 2. Floats -/

/-- Every bit pattern reads back as a well-formed triple (exponent field exactly full). -/
theorem ausBits_wf (F : Gleitkomma.Format) (hF : F.dicht) (m : Nat) :
    Gleitkomma.wf F (Gleitkomma.ausBits F m) := by
  refine ⟨?_, ?_⟩
  · show (m / 2 ^ F.fracBits) % 2 ^ F.ebits ≤ F.bexpMax
    have := Nat.mod_lt (m / 2 ^ F.fracBits) (Nat.two_pow_pos F.ebits)
    unfold Gleitkomma.Format.dicht at hF
    omega
  · exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem f64_wortGrenze :
    2 ^ (Gleitkomma.f64.ebits + Gleitkomma.f64.fracBits + 1) = 18446744073709551616 := by
  decide

/-- **Every well-formed float in range is the decoding of its bit pattern.** -/
theorem gleitWortPasst_voll (lo hi : Int × Int) (v : Gleit lo hi)
    (hw : Gleitkomma.wf Gleitkomma.f64 v.x) :
    gleitWortPasst lo hi (Gleitkomma.zuBits Gleitkomma.f64 v.x : Int) = some v := by
  have hlt := Gleitkomma.zuBits_lt Gleitkomma.f64 Gleitkomma.f64_dicht v.x hw
  rw [f64_wortGrenze] at hlt
  unfold gleitWortPasst
  rw [if_pos ⟨Int.natCast_nonneg _, by unfold gleitWortGrenze; omega⟩, Int.toNat_natCast,
    Gleitkomma.ausBits_zuBits Gleitkomma.f64 Gleitkomma.f64_dicht v.x hw]
  unfold gleitPasst
  rw [dif_pos ⟨v.endlich, v.lo_le, v.le_hi⟩]

/-- Every decoded float is well-formed. -/
theorem gleitWortPasst_wf {lo hi : Int × Int} {n : Int} {v : Gleit lo hi}
    (h : gleitWortPasst lo hi n = some v) : Gleitkomma.wf Gleitkomma.f64 v.x := by
  unfold gleitWortPasst at h
  split at h
  · unfold gleitPasst at h
    split at h
    · cases h
      exact ausBits_wf Gleitkomma.f64 Gleitkomma.f64_dicht _
    · cases h
  · cases h

/-! ## 3. Function pointers -/

/-- **Every function conforming to `fnptr m` is the answer of an image that places it at `0`.** -/
theorem zeigerPasst_voll (m : Nat) (v : {f : D.Fn // D.passt f m = true}) :
    zeigerPasst (fun _ => some v.1) m 0 = some v := by
  show (if h : D.passt v.1 m = true then some ⟨v.1, h⟩ else Option.none) = some v
  rw [dif_pos v.2]

/-! ## 4. Every type -/

/-- The values an answer can have: every value, and for a float a well-formed one (every
    value the kernel IEEE model computes is well-formed, `GleitkommaBits.lean`). -/
def WertOk : (τ : Ty) → Wert D τ → Prop
  | .sum cs, _ => sumWort cs = true
  | .fl _ _, v => Gleitkomma.wf Gleitkomma.f64 (v : Gleit _ _).x
  -- an aggregate is not one raw word: no answer has such a value
  | .arr _ _, _ => False
  | .str _, _ => False
  | _, _ => True

/-- **Every value is an answer** (G1 repair): for every type and every value of it
    (floats: well-formed), some image and some raw word decode to it. The model's decoding
    refuses no value the type admits. -/
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
  | .fl lo hi, v, hw => ⟨fun _ => Option.none, _, gleitWortPasst_voll lo hi v hw⟩
  | .fnptr m, v, _ => ⟨fun _ => some (v : {f : D.Fn // D.passt f m = true}).1, 0, zeigerPasst_voll m v⟩
  | .ptr _, _, _ => ⟨fun _ => Option.none, 0, rfl⟩
  | .ref _, r, _ => ⟨fun _ => Option.none, ((Val.zelle r : Nat) : Int), by
      simp only [einpassen, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]
      rfl⟩
  | .arr _ _, _, h => h.elim
  | .str _, _, h => h.elim

/-- Every decoded value is a value an answer can have. -/

theorem einpassen_wertOk : ∀ (z : Int → Option D.Fn) (τ : Ty) (n : Int) (v : Wert D τ),
    einpassen z τ n = some v → WertOk τ v
  | _, .fl _ _, _, _, h => gleitWortPasst_wf h
  | _, .int _ _, _, _, _ => trivial
  | _, .bool, _, _, _ => trivial
  | _, .opt _, _, _, _ => trivial
  | _, .sum cs, n, v, h => by
      unfold einpassen summePasst at h
      split at h
      · assumption
      · cases h
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

/-- The G1 types have answers: an `ok | err` sum, a float range containing a well-formed
    float, a function-pointer type some function has. -/
theorem nicht_leer_von (τ : Ty) (v : Wert D τ) (hv : WertOk τ v) : ¬ AntwortLeer D (some τ) :=
  fun h => (antwortLeer_iff τ).mp h v hv

/-! ## 5. Deciding the answer class (round-6 finding W1)

  The checker refuses an answer site whose declared type is empty, unless it is an axiom
  returning `never` (`AkzeptiertSpec.antworten`, Spec.lean). So emptiness must be DECIDED,
  from the declaration and the program's function list: a range by its bounds, a reason
  channel by its count, a sum by its cases, a function-pointer type by the functions of its
  signature -- and a float range by three candidate witnesses (the rounded bounds and `+0`),
  which is complete because the kernel IEEE order is transitive on finite values
  (`flt_trans_endlich`). -/

section Gleit

open Gleitkomma

/-- A finite float is zero, subnormal or normal. -/
theorem endlich_klasse {x : GFloat} (h : gleitEndlich x = true) :
    klasse f64 x = .null ∨ klasse f64 x = .subnormal ∨ klasse f64 x = .normal := by
  unfold gleitEndlich at h
  cases hk : klasse f64 x <;> rw [hk] at h <;> simp_all

theorem endlich_nicht_nan {x : GFloat} (h : gleitEndlich x = true) : klasse f64 x ≠ .nan := by
  rcases endlich_klasse h with e | e | e <;> rw [e] <;> decide

theorem endlich_nicht_unendlich {x : GFloat} (h : gleitEndlich x = true) :
    klasse f64 x ≠ .unendlich := by
  rcases endlich_klasse h with e | e | e <;> rw [e] <;> decide

/-- A finite float has an exact dyadic value. -/
theorem wertExakt_endlich {x : GFloat} (h : gleitEndlich x = true) :
    ∃ u, wertExakt f64 x = some u := by
  rcases endlich_klasse h with e | e | e <;> exact ⟨_, by unfold wertExakt; rw [e]⟩

/-- `fle` with a NaN on the left is false. -/
theorem fle_nan_links {a b : GFloat} (h : klasse f64 a = .nan) : fle f64 a b = false := by
  unfold fle
  rw [h]

/-- `fle` with a NaN on the right is false. -/
theorem fle_nan_rechts {a b : GFloat} (h : klasse f64 b = .nan) : fle f64 a b = false := by
  unfold fle
  rw [h]
  cases klasse f64 a <;> rfl

/-- Without NaN, `fle` is the negated reverse `flt`. -/
theorem fle_flt {a b : GFloat} (ha : klasse f64 a ≠ .nan) (hb : klasse f64 b ≠ .nan) :
    fle f64 a b = !flt f64 b a := by
  unfold fle
  cases h1 : klasse f64 a <;> cases h2 : klasse f64 b <;> simp_all

/-- An infinity on the right of `flt`, a finite value on the left: the sign decides. -/
theorem flt_unendlich_rechts {x b : GFloat} (hx : gleitEndlich x = true)
    (hb : klasse f64 b = .unendlich) : flt f64 x b = !b.sign := by
  unfold flt
  rcases endlich_klasse hx with e | e | e <;> rw [e, hb]

/-- An infinity on the left of `flt`, a finite value on the right: the sign decides. -/
theorem flt_unendlich_links {a x : GFloat} (ha : klasse f64 a = .unendlich)
    (hx : gleitEndlich x = true) : flt f64 a x = a.sign := by
  unfold flt
  rcases endlich_klasse hx with e | e | e <;> rw [e, ha]

/-- The cross-multiplied comparison of `flt`, as a Prop. -/
abbrev exaktLt (u v : Exakt) : Prop :=
  u.zaehler * ((2 ^ (u.zweierExp -
      (if u.zweierExp ≤ v.zweierExp then u.zweierExp else v.zweierExp)).toNat : Nat) : Int) <
    v.zaehler * ((2 ^ (v.zweierExp -
      (if u.zweierExp ≤ v.zweierExp then u.zweierExp else v.zweierExp)).toNat : Nat) : Int)

/-- `flt` on two finite floats is the exact comparison. -/
theorem flt_exakt {a b : GFloat} (ha : gleitEndlich a = true) (hb : gleitEndlich b = true)
    {u v : Exakt} (hu : wertExakt f64 a = some u) (hv : wertExakt f64 b = some v) :
    flt f64 a b = decide (exaktLt u v) := by
  unfold flt
  rcases endlich_klasse ha with e1 | e1 | e1 <;> rcases endlich_klasse hb with e2 | e2 | e2 <;>
    rw [e1, e2] <;> simp only [hu, hv] <;> rfl

/-- Scaling a common exponent down. -/
theorem skal (A e m K : Int) (hm : m ≤ e) (hK : K ≤ m) :
    A * ((2 ^ (e - K).toNat : Nat) : Int) =
      (A * ((2 ^ (e - m).toNat : Nat) : Int)) * ((2 ^ (m - K).toNat : Nat) : Int) := by
  have h : (e - K).toNat = (e - m).toNat + (m - K).toNat := by omega
  rw [h, Nat.pow_add, Int.natCast_mul, Int.mul_assoc]

/-- The exact comparison at ANY common exponent below both. -/
theorem exaktLt_bei (u v : Exakt) (K : Int) (hu : K ≤ u.zweierExp) (hv : K ≤ v.zweierExp) :
    exaktLt u v ↔ u.zaehler * ((2 ^ (u.zweierExp - K).toNat : Nat) : Int) <
      v.zaehler * ((2 ^ (v.zweierExp - K).toNat : Nat) : Int) := by
  unfold exaktLt
  generalize hm : (if u.zweierExp ≤ v.zweierExp then u.zweierExp else v.zweierExp) = m
  have hmu : m ≤ u.zweierExp := by rw [← hm]; split <;> omega
  have hmv : m ≤ v.zweierExp := by rw [← hm]; split <;> omega
  have hKm : K ≤ m := by rw [← hm]; split <;> omega
  rw [skal u.zaehler u.zweierExp m K hmu hKm, skal v.zaehler v.zweierExp m K hmv hKm]
  have hpos : (0 : Int) < ((2 ^ (m - K).toNat : Nat) : Int) :=
    Int.natCast_pos.mpr (Nat.two_pow_pos _)
  exact (Int.mul_lt_mul_right hpos).symm

/-- **The kernel IEEE order is transitive on finite values** (the one fact the float
    emptiness decision needs): if `b < a`, then `x < a` or `b < x`. -/
theorem flt_trans_endlich {a x b : GFloat} (ha : gleitEndlich a = true)
    (hx : gleitEndlich x = true) (hb : gleitEndlich b = true) (h : flt f64 b a = true) :
    flt f64 x a = true ∨ flt f64 b x = true := by
  obtain ⟨u, hu⟩ := wertExakt_endlich ha
  obtain ⟨w, hw⟩ := wertExakt_endlich hx
  obtain ⟨v, hv⟩ := wertExakt_endlich hb
  rw [flt_exakt hb ha hv hu] at h
  rw [flt_exakt hx ha hw hu, flt_exakt hb hx hv hw]
  simp only [decide_eq_true_eq] at h ⊢
  let K := min u.zweierExp (min w.zweierExp v.zweierExp)
  have h1 : K ≤ u.zweierExp := Int.min_le_left _ _
  have h2 : K ≤ w.zweierExp := Int.le_trans (Int.min_le_right _ _) (Int.min_le_left _ _)
  have h3 : K ≤ v.zweierExp := Int.le_trans (Int.min_le_right _ _) (Int.min_le_right _ _)
  rw [exaktLt_bei v u K h3 h1] at h
  rw [exaktLt_bei w u K h2 h1, exaktLt_bei v w K h3 h2]
  generalize u.zaehler * ((2 ^ (u.zweierExp - K).toNat : Nat) : Int) = A at h ⊢
  generalize w.zaehler * ((2 ^ (w.zweierExp - K).toNat : Nat) : Int) = X at h ⊢
  generalize v.zaehler * ((2 ^ (v.zweierExp - K).toNat : Nat) : Int) = B at h ⊢
  omega

/-- `flt` is irreflexive on finite values. -/
theorem flt_irrefl_endlich {a : GFloat} (ha : gleitEndlich a = true) : flt f64 a a = false := by
  obtain ⟨u, hu⟩ := wertExakt_endlich ha
  rw [flt_exakt ha ha hu hu]
  simp only [decide_eq_false_iff_not]
  exact Int.lt_irrefl _

/-- A candidate witness of a float range: well-formed, finite, inside. -/
def gleitZeugeB (lo hi : Int × Int) (x : GFloat) : Bool :=
  decide (wf f64 x) && gleitEndlich x && gleitLe (bruch lo) x && gleitLe x (bruch hi)

/-- `+0`. -/
def gleitNull : GFloat := ⟨false, 0, 0⟩

/-- **A float range has a well-formed value, decided**: one of the rounded bounds or `+0`
    is inside. -/
def gleitBarB (lo hi : Int × Int) : Bool :=
  gleitZeugeB lo hi (bruch lo) || gleitZeugeB lo hi (bruch hi) || gleitZeugeB lo hi gleitNull

theorem gleitNull_endlich : gleitEndlich gleitNull = true := by decide

theorem gleitBarB_iff (lo hi : Int × Int) :
    gleitBarB lo hi = true ↔ ∃ v : Gleit lo hi, wf f64 v.x := by
  constructor
  · intro h
    have hz : ∀ x, gleitZeugeB lo hi x = true → ∃ v : Gleit lo hi, wf f64 v.x := by
      intro x hx
      simp only [gleitZeugeB, Bool.and_eq_true, decide_eq_true_eq] at hx
      exact ⟨⟨x, hx.1.1.2, hx.1.2, hx.2⟩, hx.1.1.1⟩
    simp only [gleitBarB, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · exact hz _ h
    · exact hz _ h
    · exact hz _ h
  · rintro ⟨v, -⟩
    have hwa : wf f64 (bruch lo) := rundeBruch_wf f64 f64_p _
    have hwb : wf f64 (bruch hi) := rundeBruch_wf f64 f64_p _
    have hx := v.endlich
    have hax : fle f64 (bruch lo) v.x = true := v.lo_le
    have hxb : fle f64 v.x (bruch hi) = true := v.le_hi
    have hxn := endlich_nicht_nan hx
    simp only [gleitBarB, gleitZeugeB, gleitLe, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq]
    -- the lower bound's class
    cases hka : klasse f64 (bruch lo) with
    | nan => rw [fle_nan_links hka] at hax; cases hax
    | unendlich =>
        have hs : (bruch lo).sign = true := by
          rw [fle_flt (by rw [hka]; decide) hxn, flt_unendlich_rechts hx hka] at hax
          simpa using hax
        have hla : ∀ y, gleitEndlich y = true → fle f64 (bruch lo) y = true := fun y hy => by
          rw [fle_flt (by rw [hka]; decide) (endlich_nicht_nan hy), flt_unendlich_rechts hy hka,
            hs]
          rfl
        cases hkb : klasse f64 (bruch hi) with
        | nan => rw [fle_nan_rechts hkb] at hxb; cases hxb
        | unendlich =>
            have hs' : (bruch hi).sign = false := by
              rw [fle_flt hxn (by rw [hkb]; decide), flt_unendlich_links hkb hx] at hxb
              simpa using hxb
            refine Or.inr ⟨⟨⟨wf_null f64 false, gleitNull_endlich⟩, hla _ gleitNull_endlich⟩, ?_⟩
            rw [fle_flt (endlich_nicht_nan gleitNull_endlich) (by rw [hkb]; decide),
              flt_unendlich_links hkb gleitNull_endlich, hs']
            rfl
        | _ =>
            have hbE : gleitEndlich (bruch hi) = true := by
              unfold gleitEndlich; rw [hkb]
            refine Or.inl (Or.inr ⟨⟨⟨hwb, hbE⟩, hla _ hbE⟩, ?_⟩)
            rw [fle_flt (endlich_nicht_nan hbE) (endlich_nicht_nan hbE), flt_irrefl_endlich hbE]
            rfl
    | _ =>
        have haE : gleitEndlich (bruch lo) = true := by
          unfold gleitEndlich; rw [hka]
        refine Or.inl (Or.inl ⟨⟨⟨hwa, haE⟩, ?_⟩, ?_⟩)
        · rw [fle_flt (endlich_nicht_nan haE) (endlich_nicht_nan haE), flt_irrefl_endlich haE]
          rfl
        · cases hkb : klasse f64 (bruch hi) with
          | nan => rw [fle_nan_rechts hkb] at hxb; cases hxb
          | unendlich =>
              have hs' : (bruch hi).sign = false := by
                rw [fle_flt hxn (by rw [hkb]; decide), flt_unendlich_links hkb hx] at hxb
                simpa using hxb
              rw [fle_flt (endlich_nicht_nan haE) (by rw [hkb]; decide),
                flt_unendlich_links hkb haE, hs']
              rfl
          | _ =>
              have hbE : gleitEndlich (bruch hi) = true := by
                unfold gleitEndlich; rw [hkb]
              rw [fle_flt (endlich_nicht_nan haE) (endlich_nicht_nan hbE)]
              rw [fle_flt (endlich_nicht_nan haE) hxn] at hax
              rw [fle_flt hxn (endlich_nicht_nan hbE)] at hxb
              cases hba : flt f64 (bruch hi) (bruch lo)
              · rfl
              · rcases flt_trans_endlich haE hx hbE hba with h | h
                · rw [h] at hax; cases hax
                · rw [h] at hxb; cases hxb

end Gleit

end Gabbro.Grammatik
