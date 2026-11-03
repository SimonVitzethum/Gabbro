module

public import Grammatik.Parser.Elab.UebersetzeAllg3.Kopf

@[expose] public section
namespace Gabbro.Grammatik.Parser.UebersetzeAllg2
open Uebersetze UebersetzeAllg

/-- Discard the success value, bind only the failure reason and erase handler
    locals at the statement boundary. All obligations come from the pointer type. -/
def lowCallIndElse {l : Bool} (u : UProg) (caller : Fin u.fns.length)
    (R : LowStufe u caller) (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (pe : AtTop u caller Λ) (pointer : String) (args : List UArg) (reason : String)
    (rest : List UStmt) :
    Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ × List UStmt) := do
  let ⟨n, v⟩ ← lowZeigerN u Γ fn pointer
  let k ← lowRufKopfN u caller Γ fn Λ n args
  if hr : 0 < ((declOf u).sigNr n).gruende then
    withErgN u n fun _ he =>
      match R.ende (l := l) (Ty.why (((declOf u).sigNr n).gruende) :: Γ)
          (fn.mitWhy reason 0 (((declOf u).sigNr n).gruende)) Λ pe rest with
      | .error error => .error error
      | .ok (handler, .blkEnd :: tail) =>
        .ok (by
          have handler' : Endblock (declOf u) (verOf u caller) l
              (Ty.why (((declOf u).sigNr n).gruende) :: Γ)
              (nachSig (declOf u) ((declOf u).sigNr n) Λ) := by
            rw [nachSigAt_eq u n Λ]
            exact handler
          have statement := Stmt.callIndElse (D := declOf u) (Expr.var v) k.args he k.hp hr handler'
          rw [nachSigAt_eq u n Λ] at statement
          exact statement, tail)
      | .ok (_, _) => .error "lower: an indirect call else is not closed"
  else .error "lower: indirect call else needs a fallible function pointer"

end Gabbro.Grammatik.Parser.UebersetzeAllg2
