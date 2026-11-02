module

public import Grammatik.Kern.Syntax.Extensions.Zucker.Transition

public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}

/-- A finite constant edge of one table field, with the proofs that make the
    primitive `Stmt.shift` legal: both endpoints in the field's range, the
    edge in `D.erlaubt`, the write permission and the held guard. Generated
    functions for such a declaration end in this shift. -/
structure ConstEdge (D : Deklaration) (V : Vertrag D) (Γ : Ctx) (Λ : List (Res D)) where
  table : D.Tab
  field : D.Feld table
  lo : Int
  hi : Int
  numeric : D.typ table field = .int lo hi
  index : Var Γ (.index (D.count table))
  source : Int
  target : Int
  sourceRange : lo ≤ source ∧ source ≤ hi
  targetRange : lo ≤ target ∧ target ≤ hi
  erlaubt : D.erlaubt table field source target = true
  right : V.schreibt table = true
  guard : darf D table Λ

namespace ConstEdge

variable {V : Vertrag D}

/-- The same edge as an ordinary snapshot store. -/
@[expose] def write (edge : ConstEdge D V Γ Λ) : TransitionWrite D Γ Λ :=
  TransitionWrite.constEdge edge.table edge.field edge.numeric edge.index edge.source
    edge.target edge.sourceRange edge.targetRange edge.guard

/-- The primitive shift: it re-checks the current stage (`Logik.vorzustand`). -/
@[expose] def statement {l : Bool} (edge : ConstEdge D V Γ Λ) : Stmt D V l Γ Λ Λ :=
  Stmt.shift edge.table edge.field edge.numeric (.var edge.index) edge.source edge.target
    edge.targetRange edge.erlaubt edge.right edge.guard

end ConstEdge

/-- The declaration certificate of a generated function whose body is the
    primitive shift: the function's real requires is the source-stage equality
    conjoined with the declaration clause, so a call that reaches the shift is
    always a legal entry (failure at the requires is code 101, a primitive
    shift on an illegal entry is 106). -/
structure TransitionShiftExpansion (P : Programm D) (function : D.Fn) where
  shift : ConstEdge D (vertragVon D function) (D.params function)
    (Signatur.anfang D (D.signatur function))
  clause : Expr D (D.params function) (Signatur.anfang D (D.signatur function)) .bool
  result_none : D.erg function = none
  resources : Signatur.anfang D (D.signatur function) = (vertragVon D function).ende
  requires_exact : P.requires function = transitionRequires [shift.write] clause
  ensures_exact : HEq (P.ensures function) (transitionEnsures [shift.write])
  body_exact : P.rumpf function = .cons shift.statement
    (transitionReturn (vertragVon D function) result_none
      (by rw [resources]))

/-- Transport a shift expansion built in a context and resource list that are
    only propositionally equal to the function's. -/
@[expose] def TransitionShiftExpansion.ofHEq {P : Programm D} {function : D.Fn}
    (hΓ : Γ = D.params function) (hΛ : Λ = Signatur.anfang D (D.signatur function))
    (shift : ConstEdge D (vertragVon D function) Γ Λ) (clause : Expr D Γ Λ .bool)
    (result_none : D.erg function = none)
    (resources : Λ = (vertragVon D function).ende)
    (requires_exact : HEq (P.requires function) (transitionRequires [shift.write] clause))
    (ensures_exact : HEq (P.ensures function) (transitionEnsures [shift.write]))
    (body_exact : HEq (P.rumpf function) (Endblock.cons shift.statement
      (transitionReturn (vertragVon D function) result_none
        (by rw [resources])))) :
    TransitionShiftExpansion P function := by
  subst hΓ
  subst hΛ
  exact { shift, clause, result_none, resources, ensures_exact, requires_exact := eq_of_heq requires_exact, body_exact := eq_of_heq body_exact }

end Gabbro.Grammatik
