/-
  File:      Grammatik/Gen/Abdeckung/Satz/Neutral.lean
  Subject:   WHAT M AND N BUY FOR A REAL CHECKER AND A REAL COMPILER. A checker is a function `C : Einsatz → Bool`: as a
             function it terminates and is deterministic (the same program, the same answer). It is NEUTRAL when it
             decides every program by one table over the program's cells (`Neutral`: no branch on a particular
             program, the hypotheses H1-H8 of `CHECKER.md` §16.1 in the form Theorem 5 uses). Then:

    * `pruefer_hinreichend`  a neutral checker that answers like the model on every program of M and N answers like
                             the model (`AkzeptiertX`) on EVERY program of the source;
    * `compiler_hinreichend` a compiler whose correctness on a program is the conjunction of its correctness on the
                             program's cells (neutral in the same sense), correct on every program of M, is correct
                             on EVERY valid program of the source.

  Both rest on the cell table (`tafel_erzeugt`): one fact per cell, a witness in the space or a theorem.
-/
import Grammatik.Gen.Abdeckung.Satz.ErzeugtVoll

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Adaequanz

/-- **A neutral checker**: its answer on every program is one fixed table read over the program's cells. -/
def Neutral (C : Einsatz → Bool) : Prop := ∃ φ : Zelle → Bool, ∀ e, C e = true ↔ akzeptiert Einsatz.Hat φ e

/-- **Theorem 5 for a checker.** A neutral checker that answers like the model on M and N answers like the model on
    every program of the source. -/
theorem pruefer_hinreichend (nc : Nat) (er : List Zelle)
    (hG : GutGedeckt nc) (hB : SchlechtGedeckt nc er) (hE : ∀ w ∈ er, RaumGut nc w)
    (C : Einsatz → Bool) (hC : Neutral C)
    (hM : ∀ m ∈ mGen nc, C m = m.gueltig) (hN : ∀ n ∈ nGen nc, C n = n.gueltig) (e : Einsatz) :
    C e = e.gueltig := by
  obtain ⟨φ, hφ⟩ := hC
  have h := erzeugt_hinreichend nc er hG hB hE φ
    (fun m hm => by rw [← hφ m, hM m hm]) (fun n hn => by rw [← hφ n, hN n hn]) e
  rw [Bool.eq_iff_iff, hφ e]
  exact h

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
  obtain ⟨m, hm, hmz⟩ := (vollstaendig_aus_tafel t).gut e z hz ((einsatz_akzeptiert e).2 hv)
  exact (hψ m).1 (hM m hm) z hmz

end Gabbro.Grammatik.Gen
