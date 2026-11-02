module

public import Grammatik.Logik.Vertraege.EinpassenVoll.Teil1Basis
import all Grammatik.Logik.Vertraege.EinpassenVoll.Teil1Basis

public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Kern.Semantik.Semantik.T1.SummeTransport

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}
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
