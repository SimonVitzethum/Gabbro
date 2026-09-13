/-
  File:     Grammatik/ZeugnisStmt2.lean
  Subject:  Certificate soundness for the REMAINING statement/block
            constructors (T1 of PLAN-UEBERSETZUNGSVALIDIERUNG.md, part 2).

  Extends `ZeugnisStmt.lean` (38 of 50 constructors) with the shapes that
  fit the current certificate data (`CertExpr` for the int fragment,
  `CertCut3` sum/ground rows, `CertCut4` pointer rows, `CertFl` float
  rows): `Stmt`: assignDurch, callInd (nullary, the R-2 fragment),
  onTag, onGrund; `Block`: bindCallInd (nullary), gleit, gleitLit,
  gleitVon, gleitNarrow. `axiomCall`/`bindAxiom`/`transition` stay listed
  (see CUTS): no rule-13 witness exists on the reference fixture.
-/
import Grammatik.ZeugnisStmt

namespace Gabbro.Grammatik

/-- Case-list certificates for `Stmt.onTag`: one `CertSeq` per `sum` case,
    the case pinned in the constructor (the `Arms` correspondence). -/
inductive CertArms2 (D : Deklaration) (V : Vertrag D) : List (Option (Int × Int)) → Type where
  | nil : CertArms2 D V []
  | cons (c : Option (Int × Int)) (b : CertSeq D V) {cs : List (Option (Int × Int))}
    (rest : CertArms2 D V cs) : CertArms2 D V (c :: cs)

/-- Reason-list certificates for `Stmt.onGrund`: one `CertSeq` per reason
    (the `GrundArms` correspondence, length `n`). -/
inductive CertGrundArms2 (D : Deklaration) (V : Vertrag D) : Nat → Type where
  | nil : CertGrundArms2 D V 0
  | cons (b : CertSeq D V) {n : Nat} (rest : CertGrundArms2 D V n) :
    CertGrundArms2 D V (n + 1)

/-- The four remaining `Stmt` shapes as plain data. `assignDurch` names the
    table number (the `tabNr` equation recomputes, the pointer is rebuilt
    from it); `callInd` names the callee and its signature number (the
    `sig` equation recomputes, nullary only, the R-2 fragment, `RufPasst`
    travels as proof); `onTag`/`onGrund` carry the scrutinee shapes the
    CUT-3 rows already print (`fall` payload check, `r < n`). -/
inductive CertStmt2 (D : Deklaration) (V : Vertrag D) where
  | assignDurch (t : D.Tab) (f : D.Feld t) (n : Nat) (rw : Bool) (i e : CertExpr D)
  | callInd (f : D.Fn) (n : Nat) (Λc : List (Res D)) (hp : RufPasst D V (D.sigNr n) Λc)
  | onTag (cs : List (Option (Int × Int))) (i : Nat) (p : Option (CertExpr D))
    (arms : CertArms2 D V cs)
  | onGrund (n r : Nat) (arms : CertGrundArms2 D V n)

end Gabbro.Grammatik
