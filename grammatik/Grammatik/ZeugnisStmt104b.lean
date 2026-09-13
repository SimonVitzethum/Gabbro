/-
  File:     Grammatik/ZeugnisStmt104b.lean
  Subject:  TRANSFER certificates for `beispiele/104-referenz.gab` (lane 155).

  The `CertEnd104` layer below extends `CertEnd2` (`ZeugnisStmt2.lean`) with
  exactly what the reference program needs beyond it: calls with arguments
  (`consCall`: the count recomputes, the `RufPasst` and the elaborated
  `Args` travel as proof, the `CertBlock5`/`Block5Args` precedent of
  `Zeugnis.lean` at body level) and a return through a pointer (`retDurch`:
  the table-number equation, the generated index shape, the field-type
  equation and the guard recompute, the pointer travels as proof, the
  `durch` precedent of `cut4_sound`). Old shapes reuse through `lift2`
  (whole old bodies), `cons1`/`cons2` (single old steps) and `bind`/the two
  terminals. Section 4 pastes the verbatim printer output for both bodies
  of `beispiele/104-referenz.gab` (proofs filled beside the printed `?hp`),
  each accepted by `decide` and pushed through `zeugnisStmt104b_sound`.
-/
import Grammatik.ZeugnisStmt2
import Grammatik.Export104

namespace Gabbro.Grammatik

/-- Body prints with calls-with-arguments and pointer returns: reuse
    (`lift2`), single old steps (`cons1` for `CertStmt`, `cons2` for
    `CertStmt2`), integer bindings (`bind`), calls with arguments
    (`consCall`: callee, argument count, carried resources, carried
    `RufPasst`), plain terminals (`ret`, `retWert`) and the pointer return
    (`retDurch`: table, field, table number, index certificate). -/
inductive CertEnd104 (D : Deklaration) (V : Vertrag D) where
  | lift2 (e : CertEnd2 D V)
  | cons1 (s : CertStmt D V) (Λm : List (Res D)) (rest : CertEnd104 D V)
  | cons2 (s : CertStmt2 D V) (Λm : List (Res D)) (rest : CertEnd104 D V)
  | bind (e : CertExpr D) (lo hi : Int) (rest : CertEnd104 D V)
  | consCall (f : D.Fn) (nargs : Nat) (Λc : List (Res D))
    (hp : RufPasst D V (D.signatur f) Λc) (rest : CertEnd104 D V)
  | ret
  | retWert (e : CertExpr D) (lo hi : Int)
  | retDurch (t : D.Tab) (f : D.Feld t) (n : Nat) (i : CertExpr D)

end Gabbro.Grammatik
