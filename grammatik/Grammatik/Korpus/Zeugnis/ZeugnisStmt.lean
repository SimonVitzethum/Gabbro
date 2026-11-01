/-
  File:     Grammatik/ZeugnisStmt.lean
  Subject:  Certificate soundness for STATEMENTS (T1 of PLAN-TRANSLATION-VALIDATION.md).

  Extends `Zeugnis.lean` (expressions) to statements: `CertCond`/`CertStmt`/
  `CertSeq`/`CertEnd` are plain-data certificates, the `*Gueltig` predicates
  recompute every side condition (`darf`, `V.schreibt`, rank order, index
  shapes, linear balance), and `zeugnisStmt_sound` elaborates a valid
  certificate to a well-typed `Endblock` (the run statement).
  The Rust printer (`certemit.rs`) covers expressions only; the statement
  print format is designed in the docstrings below for the transfer phase.
-/

module
public import Grammatik.Korpus.Zeugnis.ZeugnisStmt.T1
public import Grammatik.Korpus.Zeugnis.ZeugnisStmt.T2
public import Grammatik.Korpus.Zeugnis.ZeugnisStmt.T3
@[expose] public section

