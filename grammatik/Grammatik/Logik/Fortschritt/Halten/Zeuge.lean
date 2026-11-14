/-
  File:      Grammatik/Logik/Fortschritt/Halten/Zeuge.lean
  Subject:   WITNESSES of the derived hold time.

  * A section with a nested lock (`hzAussen`: `locks false { locks true { } }` over `grobD`, two locks,
    `rang false < rang true`): the walker accepts it at `N false = 4`, `N true = 1` and refuses it at
    `N false = 3` (the outer body costs `4` in `kostenBlock`: the inner section `2 + 1`, the close `1`);
    the derived hold times are `haltSchranke [false, true] N false = 7`, `… true = 4`.
  * `haltezeit_aus_zeuge`: on the two-thread witness run of `wartezeit_zeuge` (LebendigkeitZeuge), whose
    thread 0 holds the lock for six scheduler steps, the program passes `haltPasst` (sections at most
    `20`, `setze` declared at `14`: body `5` plus its return predicates `9`, C05), and `haltezeit_aus`
    gives `Haltezeit` with `h = k = 22` -- every premise of the theorem
    discharged on a non-degenerate run.
-/
module
public import Grammatik.Logik.Fortschritt.Halten.Haltezeit
public import Grammatik.Logik.Fortschritt.LebendigkeitZeuge
public import Grammatik.Nebenlaeufigkeit.Sperren.SperrstreifenBasis
@[expose] public section

namespace Gabbro.Grammatik

open Sperrstreifen

/-! ## 1. A section with a nested lock -/

/-- The contract of the one function of `grobD`. -/
abbrev hzV : Vertrag grobD := vertragVon grobD ()

/-- The inner section `locks true { }`, taken while `false` is held (`rang false < rang true`). -/
def hzInnen : Stmt grobD hzV false [] [Res.held false] [Res.held false] :=
  .locks true (fun M h => by
    have hM : M = false := Res.held.inj (D := grobD) (List.mem_singleton.mp h)
    subst M
    decide) .nil

/-- `locks false { locks true { } }`. -/
def hzAussen : Block grobD hzV false [] [] [] :=
  .cons (.locks false (fun _ h => absurd h List.not_mem_nil) (.cons hzInnen .nil)) .nil

/-- The declared bounds: `4` for a section of `false`, `1` for a section of `true`. -/
def hzN (L : Bool) : Nat := if L then 1 else 4

/-- **The checker accepts the nested section at its bounds.** -/
theorem hzAussen_geprueft :
    haltB (fun (L : Bool) => some (hzN L)) 0 (fun _ => 0) (fun _ => false) 0 hzAussen = true := by
  simp [hzAussen, hzInnen, hzN, haltB, haltS, kostenBlock, kostenStmt, rufeB, rufeS]

/-- **The check is not vacuous**: one step less for the outer lock and the nested section is refused. -/
theorem hzAussen_eng :
    haltB (fun (L : Bool) => some (if L then 1 else 3)) 0 (fun _ => 0) (fun _ => false) 0 hzAussen =
      false := by
  simp [hzAussen, hzInnen, haltB, haltS, kostenBlock, kostenStmt, rufeB, rufeS]

/-- **The derived hold times**: `4 + 1 + 2` own steps for `false`, `1 + 1 + 2` for `true`. -/
theorem hzSchranke :
    haltSchranke (D := grobD) [false, true] (fun (L : Bool) => hzN L) false = 7 ∧
      haltSchranke (D := grobD) [false, true] (fun (L : Bool) => hzN L) true = 4 := by
  decide

/-! ## 2. The theorem on a run -/

/-- **`haltezeit_aus` on the witness run.** The run of `wartezeit_zeuge` (thread 0 holds the lock at steps
    6-11) belongs to a program the hold-bound check accepts, and the derived hold time holds on it. -/
theorem haltezeit_aus_zeuge : ∃ R : PlanLauf mP mO 0,
    R.M 0 = RufStartG mP mSp mInit ∧
    haltPasst mP 0 (fun _ => 20) (fun _ => 14) mFs [mSetze] = true ∧
    Haltezeit R (haltSchranke [()] (fun _ => 20)) (haltSchranke [()] (fun _ => 20)) ∧
    (∀ j, 6 ≤ j → j ≤ 11 → () ∈ offen ((R.M j).faeden 0).spur) ∧
    haltSchranke (D := mD) [()] (fun _ => 20) () = 22 := by
  obtain ⟨R, h0, -, -, -, -, -, -, -, halt0, -, -⟩ := lZeuge
  have hK : haltPasst mP 0 (fun _ => 20) (fun _ => 14) mFs [mSetze] = true := by
    simp [haltPasst, kostenPasst, mFs, mP, mSetze, mHauptA, mHauptB, mPruefeA, mRuhe,
      mRumpfSetze, mRumpfA, mRumpfB, mLocksA, mLocksB, mRufA, mRufB, mRestA,
      haltE, haltS, haltB, rufeE, rufeS, rufeB, kostenEnd, kostenStmt, kostenBlock,
      kostenEpilog, kostenExpr, kostenErg, kostenArgs, entfZ, GEntfaltbar,
      mGleich, mAGleich, mA7, mI0, mI1, m7, m5, m30, m70,
      schuldet, Deklaration.schreibt, Deklaration.gschreibt, Deklaration.signatur,
      mD, mSigOf, mSigNr, mSig]
    all_goals decide
  exact ⟨R, h0, hK,
    haltezeit_aus R mO_gut mP_stufen mSp mInit mInit_leer (by rw [h0]; exact .start) (ls := [()])
      (fun L => by cases L; exact List.mem_singleton_self _) mFs_voll hK,
    halt0, rfl⟩

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.haltezeit_aus
#print axioms Gabbro.Grammatik.haltezeit_aus_zeuge
#print axioms Gabbro.Grammatik.hzAussen_geprueft
