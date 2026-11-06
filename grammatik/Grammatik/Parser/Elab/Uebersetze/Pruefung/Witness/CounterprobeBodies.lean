module

public import Grammatik.Parser.Elab.UebersetzeAllg3.FunctionResults
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
import all Grammatik.Parser.Elab.UebersetzeAllg3.Kopf

public section
namespace Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

-- A certificate of the existing reader at its complete dependent endpoint.
private abbrev CounterprobeBodyPacket (u : UProg) (caller : Fin u.fns.length)
    (Γ : Ctx) (fn : UFn) (fuel : Nat) (Λ : List (Res (declOf u)))
    (statements : List UStmt) (returning : URet) :=
  {body : Endblock (declOf u) (verOf u caller) false Γ Λ //
    lowBodyF u caller Γ fn fuel Λ statements returning = .ok body}

-- Constructor composition is proved with abstract carriers. Neither proof
-- evaluates the continuation or rebuilds its actual context/resource proofs.
private def counterprobe_body_integer (u : UProg) (caller : Fin u.fns.length)
    (Γ : Ctx) (fn : UFn) (fuel : Nat) (Λ : List (Res (declOf u)))
    (name : String) (annotation : Option (Int × Int)) (value : USide)
    (rest : List UStmt) (returning : URet)
    (side : {actual : LowSide u Γ Λ // lowBindWert u Γ Λ fn annotation value = .ok actual})
    (tail : CounterprobeBodyPacket u caller (.int side.val.range.1 side.val.range.2 :: Γ)
      (fn.mitBindung name side.val.range) fuel Λ rest returning) :
    CounterprobeBodyPacket u caller Γ fn (fuel + 1) Λ (.bind name annotation value :: rest) returning := by
  refine ⟨Endblock.bind side.val.term tail.val, ?_⟩
  change (match lowBindWert u Γ Λ fn annotation value with
    | .error error => .error error
    | .ok actual => match lowBodyF u caller (.int actual.range.1 actual.range.2 :: Γ)
        (fn.mitBindung name actual.range) fuel Λ rest returning with
      | .error error => .error error
      | .ok ending => .ok (Endblock.bind actual.term ending)) = _
  simp only [side.property, tail.property]

private def counterprobe_body_boolean (u : UProg) (caller : Fin u.fns.length)
    (Γ : Ctx) (fn : UFn) (fuel : Nat) (Λ : List (Res (declOf u)))
    (name : String) (value : UEns) (rest : List UStmt) (returning : URet)
    (term : {actual : Expr (declOf u) Γ Λ .bool // lowEns u Γ Λ fn none value = .ok actual})
    (tail : CounterprobeBodyPacket u caller (.bool :: Γ) (fn.mitBindungB name) fuel Λ rest returning) :
    CounterprobeBodyPacket u caller Γ fn (fuel + 1) Λ (.bindB name value :: rest) returning := by
  refine ⟨Endblock.bind term.val tail.val, ?_⟩
  change (match lowEns u Γ Λ fn none value with
    | .error error => .error error
    | .ok actual => match lowBodyF u caller (.bool :: Γ) (fn.mitBindungB name) fuel Λ rest returning with
      | .error error => .error error
      | .ok ending => .ok (Endblock.bind actual ending)) = _
  simp only [term.property, tail.property]

private theorem counterprobe_with_result {α : Type} (u : UProg) (callee : Fin u.fns.length)
    (ty : Ty) (result : (declOf u).erg callee = some ty)
    (callback : (actual : Ty) → (declOf u).erg callee = some actual → Except String α) :
    withErg u callee callback = callback ty result := by
  unfold withErg
  generalize source : (declOf u).erg callee = recorded at callback result ⊢
  cases result
  rfl

private def counterprobe_body_call (u : UProg) (caller : Fin u.fns.length)
    (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (name calleeName : String) (arguments : List UArg) (returning : URet)
    (head : {actual : RufKopf u caller Γ Λ //
      lowRufKopf u caller Γ fn Λ calleeName arguments = .ok actual})
    (result : (declOf u).erg head.val.callee = some .bool)
    (reason : (declOf u).gruende head.val.callee = 0)
    (ending : {actual : Endblock (declOf u) (verOf u caller) false (.bool :: Γ)
        (nach (declOf u) head.val.callee Λ) //
      lowEnd u caller (.bool :: Γ) (nach (declOf u) head.val.callee Λ)
        (fn.mitTy name .bool) returning = .ok actual}) :
    CounterprobeBodyPacket u caller Γ fn 2 Λ [.bindCall name calleeName arguments] returning := by
  refine ⟨Endblock.bindCall head.val.callee head.val.args result head.val.hp reason ending.val, ?_⟩
  change (match lowRufKopf u caller Γ fn Λ calleeName arguments with
    | .error error => .error error
    | .ok call => withErg u call.callee fun ty found =>
      match lowBodyF u caller (ty :: Γ) (fn.mitTy name ty) 1
          (nach (declOf u) call.callee Λ) [] returning with
      | .error error => .error error
      | .ok tail =>
        if noReason : (declOf u).gruende call.callee = 0 then
          .ok (Endblock.bindCall call.callee call.args found call.hp noReason tail)
        else .error "call of a function with a reason channel needs `let .. else`") = _
  simp only [head.property]
  rw [counterprobe_with_result u head.val.callee .bool result]
  change (match lowEnd u caller (.bool :: Γ) (nach (declOf u) head.val.callee Λ)
      (fn.mitTy name .bool) returning with
    | .error error => .error error
    | .ok tail =>
      if noReason : (declOf u).gruende head.val.callee = 0 then
        .ok (Endblock.bindCall head.val.callee head.val.args result head.val.hp noReason tail)
      else .error "call of a function with a reason channel needs `let .. else`") = _
  simp only [ending.property, dif_pos reason]

end Gabbro.Grammatik.Parser.Uebersetze
