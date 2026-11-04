module

public import Grammatik.Logik.Vertraege.EinpassenVoll.Teil1Basis
public import Grammatik.Kern.Syntax.Typen.FloatOrder
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
  which is complete by transitivity and the finite endpoint facts of the
  toolchain-native comparison. -/

section Gleit

/-- A native candidate retains exactly the existing finite/range predicates. -/
def gleitZeugeB (lo hi : Int × Int) (x : GFloat) : Bool :=
  gleitEndlich x && gleitLe (bruch lo) x && gleitLe x (bruch hi)

/-- Native positive zero. -/
def gleitNull : GFloat := Float.ofBits 0

/-- The same three candidates decide the native float range. -/
def gleitBarB (lo hi : Int × Int) : Bool :=
  gleitZeugeB lo hi (bruch lo) || gleitZeugeB lo hi (bruch hi) || gleitZeugeB lo hi gleitNull

theorem gleitNull_endlich : gleitEndlich gleitNull = true := by decide

theorem gleitBarB_iff (lo hi : Int × Int) :
    gleitBarB lo hi = true ↔ ∃ v : Gleit lo hi, True := by
  constructor
  · intro h
    have candidate (x : GFloat) (hx : gleitZeugeB lo hi x = true) : ∃ v : Gleit lo hi, True := by
      simp only [gleitZeugeB, Bool.and_eq_true_iff] at hx
      exact ⟨⟨x, hx.1.1, hx.1.2, hx.2⟩, trivial⟩
    simp only [gleitBarB, Bool.or_eq_true_iff] at h
    rcases h with (h | h) | h
    · exact candidate _ h
    · exact candidate _ h
    · exact candidate _ h
  · rintro ⟨v, _⟩
    simp only [gleitBarB, gleitZeugeB, Bool.or_eq_true_iff, Bool.and_eq_true_iff]
    cases ha : gleitEndlich (bruch lo) with
    | true =>
        exact Or.inl (Or.inl ⟨⟨rfl, NativeFloat.le_refl ha⟩,
          NativeFloat.le_trans v.lo_le v.le_hi⟩)
    | false =>
        cases hb : gleitEndlich (bruch hi) with
        | true =>
            exact Or.inl (Or.inr ⟨⟨rfl, NativeFloat.le_trans v.lo_le v.le_hi⟩,
              NativeFloat.le_refl hb⟩)
        | false =>
            exact Or.inr ⟨⟨gleitNull_endlich,
              NativeFloat.lower_le ha v.endlich gleitNull_endlich v.lo_le⟩,
              NativeFloat.le_upper hb v.endlich gleitNull_endlich v.le_hi⟩

end Gleit

end Gabbro.Grammatik
