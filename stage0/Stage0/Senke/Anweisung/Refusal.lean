/- Named diagnostics for the six deliberately unsupported device constructors.
   This traversal never decides admission: lowFun remains the only producer.
   Exhaustive matches make additions to the source syntax visible here too. -/
module
public import Grammatik.Kern.Syntax.Syntax.Teil2

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}

mutual
private def refusedS {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → List String
  | .regWrite .. => ["Stmt.regWrite"]
  | .transition .. => ["Stmt.transition"]
  | .ite _ t e => refusedB t ++ refusedB e
  | .onOption _ p a => refusedB p ++ refusedB a
  | .onTag _ arms => refusedTags arms
  | .onWhy _ arms => refusedReasons arms
  | .locks _ _ body => refusedB body
  | .breaking _ body => refusedB body
  | .traverse _ _ body => refusedB body
  | .retry _ _ body overflow => refusedB body ++ refusedB overflow
  | .forever _ _ body => refusedB body
  | .consumeTraverse _ _ _ _ _ _ body => refusedB body
  | .axiomCallElse _ _ _ _ _ _ _ _ err => refusedEnd err
  | .callIndElse _ _ _ _ _ err => refusedEnd err
  | .assignSlot .. | .assignThru .. | .assignThruOwn .. | .assignGlob ..
  | .putBytes .. | .assignVar .. | .shift .. | .call .. | .callInd ..
  | .axiomCall .. | .publish .. | .advances .. | .retires .. | .ret ..
  | .retWhy .. | .leave .. | .next .. | .assignSlotRef .. | .retScoped ..
  | .retWhyScoped .. => []

private def refusedB {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → List String
  | .regRead .. => ["Block.regRead"]
  | .regReadElse .. => ["Block.regReadElse"]
  | .nil => []
  | .cons s rest => refusedS s ++ refusedB rest
  | .bind _ rest => refusedB rest
  | .bindCall _ _ _ _ _ rest => refusedB rest
  | .bindCallInd _ _ _ _ _ rest => refusedB rest
  | .bindCallElse _ _ _ _ _ err rest => refusedEnd err ++ refusedB rest
  | .bindCallIndElse _ _ _ _ _ err rest => refusedEnd err ++ refusedB rest
  | .bindAxiom _ _ _ _ _ _ _ rest => refusedB rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => refusedEnd err ++ refusedB rest
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => refusedB rest
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => refusedEnd err ++ refusedB rest
  | .awaits _ _ _ _ _ rest => refusedB rest
  | .exchange _ _ _ _ rest => refusedB rest
  | .narrow _ _ _ err rest => refusedEnd err ++ refusedB rest
  | .narrowRequired _ _ _ rest => refusedB rest
  | .check _ err rest => refusedEnd err ++ refusedB rest
  | .float _ _ _ _ _ rest => refusedB rest
  | .floatLit _ _ _ rest => refusedB rest
  | .floatOf _ _ _ rest => refusedB rest
  | .floatNarrow _ _ _ err rest => refusedEnd err ++ refusedB rest

private def refusedEnd {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → List String
  | .regRead .. => ["Endblock.regRead"]
  | .regReadElse .. => ["Endblock.regReadElse"]
  | .ret .. | .retWhy .. | .leave .. | .next .. | .retScoped ..
  | .retWhyScoped .. => []
  | .cons s rest => refusedS s ++ refusedEnd rest
  | .bind _ rest => refusedEnd rest
  | .bindCall _ _ _ _ _ rest => refusedEnd rest
  | .bindCallInd _ _ _ _ _ rest => refusedEnd rest
  | .bindCallElse _ _ _ _ _ err rest => refusedEnd err ++ refusedEnd rest
  | .bindCallIndElse _ _ _ _ _ err rest => refusedEnd err ++ refusedEnd rest
  | .bindAxiom _ _ _ _ _ _ _ rest => refusedEnd rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => refusedEnd err ++ refusedEnd rest
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => refusedEnd rest
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => refusedEnd err ++ refusedEnd rest
  | .awaits _ _ _ _ _ rest => refusedEnd rest
  | .exchange _ _ _ _ rest => refusedEnd rest
  | .narrow _ _ _ err rest => refusedEnd err ++ refusedEnd rest
  | .narrowRequired _ _ _ rest => refusedEnd rest
  | .ite _ t e => refusedEnd t ++ refusedEnd e
  | .float _ _ _ _ _ rest => refusedEnd rest
  | .floatLit _ _ _ rest => refusedEnd rest
  | .floatOf _ _ _ rest => refusedEnd rest
  | .floatNarrow _ _ _ err rest => refusedEnd err ++ refusedEnd rest

private def refusedTags {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} : Arms D V l Γ Λ Λ' cs → List String
  | .nil => []
  | .cons body rest => refusedB body ++ refusedTags rest

private def refusedReasons {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} : GrundArms D V l Γ Λ Λ' n → List String
  | .nil => []
  | .cons body rest => refusedB body ++ refusedReasons rest
end

/-- Name a deliberately unsupported constructor in a failed function's body.
    Parameter/layout refusals retain the existing function-level diagnostic. -/
public def refusedForm {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (body : Endblock D V l Γ Λ) : Option String := (refusedEnd body).head?

end Gabbro.Stage0.Senke
