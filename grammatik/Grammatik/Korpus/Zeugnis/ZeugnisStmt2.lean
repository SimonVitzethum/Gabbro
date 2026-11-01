/-
  File:     Grammatik/ZeugnisStmt2.lean
  Subject:  Certificate soundness for the REMAINING statement/block
            constructors (T1 of PLAN-TRANSLATION-VALIDATION.md, part 2).

  Extends `ZeugnisStmt.lean` (38 of 50 constructors) with the shapes that
  fit the current certificate data (`CertExpr` for the int fragment,
  `CertCut3` sum/ground rows, `CertCut4` pointer rows, `CertFl` float
  rows): `Stmt`: assignDurch, callInd (nullary, the R-2 fragment),
  onTag, onGrund; `Block`: bindCallInd (nullary), gleit, gleitLit,
  gleitVon, gleitNarrow. `axiomCall`/`bindAxiom`/`transition` stay listed
  (see CUTS): no rule-13 witness exists on the reference fixture.
-/
module

public import Grammatik.Korpus.Zeugnis.ZeugnisStmt2.Teil1
public import Grammatik.Korpus.Zeugnis.ZeugnisStmt2.Teil2
public import Grammatik.Korpus.Zeugnis.ZeugnisStmt2.Teil3
