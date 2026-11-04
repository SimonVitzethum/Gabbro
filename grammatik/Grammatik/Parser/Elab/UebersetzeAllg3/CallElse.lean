module

public import Grammatik.Parser.Elab.UebersetzeAllg3.Kopf
public import Grammatik.Parser.Elab.UebersetzeAllg3.IndirectElse

@[expose] public section
namespace Gabbro.Grammatik.Parser.UebersetzeAllg2
open Uebersetze UebersetzeAllg

/-- Lower the shared flat statement handler into the canonical scope-erasing
    constructor. Both the handler and the following statement keep their own scope. -/
def lowAxCallElse {l : Bool} (u : UProg) (caller : Fin u.fns.length)
    (R : LowStufe u caller) (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (pe : AtTop u caller Λ) (name : String) (args : List UArg) (reason : String)
    (rest : List UStmt) :
    Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ × List UStmt) := do
  let k ← lowAxKopf u caller Γ fn Λ name args
  if hp : rufPasstB u (verOf u caller) ((declOf u).asignatur k.ax) Λ = true then
    if hr : 0 < (declOf u).agruende k.ax then
      match R.ende (l := l) (reasonTy ((declOf u).agruende k.ax) :: Γ)
          (fn.mitWhy reason 0 ((declOf u).agruende k.ax)) Λ pe rest with
      | .error error => .error error
      | .ok (handler, .blkEnd :: tail) =>
        .ok (by
          simpa [nachSig, Deklaration.asignatur, Signatur.inputMarks, Signatur.outputMarks,
            OwnerFlow.inputs, OwnerFlow.outputs] using
            (Stmt.axiomCallElse (D := declOf u) (V := verOf u caller) (l := l) (Γ := Γ) (Λ := Λ)
              ((declOf u).aerg k.ax) k.ax k.args rfl
              (rufPasstB_ok hp) k.hd k.hgd hr
              (by simpa [nachSig, Deklaration.asignatur, Signatur.inputMarks,
                Signatur.outputMarks, OwnerFlow.inputs, OwnerFlow.outputs] using handler)), tail)
      | .ok (_, _) => .error "lower: a call else is not closed"
    else .error "lower: call else needs a fallible axiom callee"
  else .error "foreign call does not conform to caller contract"

/-- Resolve the first local binding, just as `lowZeigerN` does; a foreign callee
    keeps the existing handler. The flat marker is shared, without a new syntax constructor. -/
def lowCallElse {l : Bool} (u : UProg) (caller : Fin u.fns.length)
    (R : LowStufe u caller) (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (pe : AtTop u caller Λ) (name : String) (args : List UArg) (reason : String)
    (rest : List UStmt) :
    Except String ((Σ Λ', Stmt (declOf u) (verOf u caller) l Γ Λ Λ') × List UStmt) :=
  match (fn.params.find? (fun binding : String × Ty => strEq binding.1 name)).map
      (fun binding : String × Ty => binding.2) with
  | some (Ty.fnptr _) => lowCallIndElse u caller R Γ fn Λ pe name args reason rest
  | _ => (lowAxCallElse u caller R Γ fn Λ pe name args reason rest).map fun (st, tail) => (⟨Λ, st⟩, tail)

end Gabbro.Grammatik.Parser.UebersetzeAllg2
