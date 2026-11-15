/-
  Neutral compilers inherit correctness from coverage of the cells of accepted programs. Cell-only checker equivalence is not claimed.
-/
module
public import Grammatik.Gen.Abdeckung.Satz.ErzeugtVoll
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section


namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Adaequanz

/-- **A neutral checker**: its answer on every program is one fixed table read over the program's cells. -/
def Neutral (C : Einsatz → Bool) : Prop := ∃ φ : Zelle → Bool, ∀ e, C e = true ↔ akzeptiert Einsatz.Hat φ e


/-- **A neutral compiler**: it is correct on a program exactly when it is correct on each of the program's cells. -/
def NeutralKorrekt (K : Einsatz → Prop) : Prop := ∃ ψ : Zelle → Prop, ∀ e, K e ↔ ∀ z, e.Hat z → ψ z

/-- **The compiler theorem.** A neutral compiler correct on every program of M is correct on every valid program of the
    source: every cell of a valid program has a witness in M (`gut` of the table). -/
theorem compiler_hinreichend (nc : Nat) (er : List Zelle)
    (hG : GutGedeckt nc) (hB : SchlechtGedeckt nc er) (hE : ∀ w ∈ er, RaumGut nc w)
    (K : Einsatz → Prop) (hK : NeutralKorrekt K) (hM : ∀ m ∈ mGen nc, K m) (e : Einsatz)
    (hv : e.gueltig = true) : K e := by
  obtain ⟨ψ, hψ⟩ := hK
  have t := tafel_erzeugt nc er hG hB hE
  refine (hψ e).2 fun z hz => ?_
  obtain ⟨m, hm, hmz⟩ := zellen_deckt t.gut e hv z hz
  exact (hψ m).1 (hM m hm) z hmz

end Gabbro.Grammatik.Gen
