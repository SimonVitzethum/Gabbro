module
public import Grammatik.Kern.Syntax.Konst.ReinBKlangAnweisung
public section
namespace Gabbro.Grammatik
mutual
theorem constExprB_complete (c : ConstProgram) {Γ : Ctx} {τ : Ty} {e : Expr c.D Γ [] τ} :
    ConstExpr c e → constExprB c e = true
  | .pureLit => by
      simp only [constExprB, Bool.and_self]
  | .pureTru => by
      simp only [constExprB, Bool.and_self]
  | .pureFls => by
      simp only [constExprB, Bool.and_self]
  | .pureVar => by
      simp only [constExprB, Bool.and_self]
  | .pureWiden h0 => by
      simp only [constExprB, constExprB_complete c h0, Bool.and_self]
  | .pureAdd h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureSub h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureNeg h0 => by
      simp only [constExprB, constExprB_complete c h0, Bool.and_self]
  | .pureMul h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureDiv h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureRem h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureSdiv h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureSrem h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureBand h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureBor h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureBxor h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureShl h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureShr h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureLt h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureLe h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureEq h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureAnd h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureOr h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureNot h0 => by
      simp only [constExprB, constExprB_complete c h0, Bool.and_self]
  | .pureNone => by
      simp only [constExprB, Bool.and_self]
  | .pureSome h0 => by
      simp only [constExprB, constExprB_complete c h0, Bool.and_self]
  | .pureIstSome h0 => by
      simp only [constExprB, constExprB_complete c h0, Bool.and_self]
  | .pureCase h0 => by
      simp only [constExprB, constPayloadB_complete c h0, Bool.and_self]
  | .pureWhy => by
      simp only [constExprB, Bool.and_self]
  | .pureForallSlots h0 => by
      simp only [constExprB, constExprB_complete c h0, Bool.and_self]
  | .pureExistsSlots h0 => by
      simp only [constExprB, constExprB_complete c h0, Bool.and_self]
  | .pureArrNil => by
      simp only [constExprB, Bool.and_self]
  | .pureArrCons h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureArrGet h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureArrSet h0 h1 h2 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, constExprB_complete c h2, Bool.and_self]
  | .pureStrLit => by
      simp only [constExprB, Bool.and_self]
  | .pureStrLen h0 => by
      simp only [constExprB, constExprB_complete c h0, Bool.and_self]
  | .pureStrCat h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureStrGet h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureStrEq h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureStrLt h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureStrWeit h0 => by
      simp only [constExprB, constExprB_complete c h0, Bool.and_self]
  | .pureWenn h0 h1 h2 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, constExprB_complete c h2, Bool.and_self]
  | .pureEng h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureIntBuiltin1 h0 => by
      simp only [constExprB, constExprB_complete c h0, Bool.and_self]
  | .pureIntBuiltin2 h0 h1 => by
      simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
  | .pureCount h0 => by
      simp only [constExprB, constExprB_complete c h0, Bool.and_self]
  | .pureProd h0 => by simp only [constExprB, constArgsB_complete c h0, Bool.and_self]
  | .pureProdGet h0 => by simp only [constExprB, constExprB_complete c h0, Bool.and_self]
  | .pureProdSet h0 h1 => by simp only [constExprB, constExprB_complete c h0, constExprB_complete c h1, Bool.and_self]
theorem constPayloadB_complete (c : ConstProgram) {Γ : Ctx} {k : Option Ty} {e : NutzlastExpr c.D Γ [] k} :
    ConstPayload c e → constPayloadB c e = true
  | .empty => by
      simp only [constPayloadB, Bool.and_self]
  | .val h0 => by
      simp only [constPayloadB, constExprB_complete c h0, Bool.and_self]
theorem constArgsB_complete (c : ConstProgram) {Γ : Ctx} {ts : List Ty} {e : Args c.D Γ [] ts} :
    ConstArgs c e → constArgsB c e = true
  | .nil => by
      simp only [constArgsB, Bool.and_self]
  | .cons h0 h1 => by
      simp only [constArgsB, constExprB_complete c h0, constArgsB_complete c h1, Bool.and_self]
theorem constResultB_complete (c : ConstProgram) {Γ : Ctx} {τ : Option Ty} {e : ErgExpr c.D Γ [] τ} :
    ConstResult c e → constResultB c e = true
  | .empty => by
      simp only [constResultB, Bool.and_self]
  | .val h0 => by
      simp only [constResultB, constExprB_complete c h0, Bool.and_self]
theorem constStmtB_complete (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {e : Stmt c.D V l Γ [] []} :
    ConstStmt c e → constStmtB c e = true
  | .assignVar h0 => by
      simp only [constStmtB, constExprB_complete c h0, Bool.and_self]
  | .ite h0 h1 h2 => by
      simp only [constStmtB, constExprB_complete c h0, constBlockB_complete c h1, constBlockB_complete c h2, Bool.and_self]
  | .onOption h0 h1 h2 => by
      simp only [constStmtB, constExprB_complete c h0, constBlockB_complete c h1, constBlockB_complete c h2, Bool.and_self]
  | .onTag h0 h1 => by
      simp only [constStmtB, constExprB_complete c h0, constArmsB_complete c h1, Bool.and_self]
  | .onWhy h0 h1 => by
      simp only [constStmtB, constExprB_complete c h0, constReasonArmsB_complete c h1, Bool.and_self]
  | .ret h0 => by
      simp only [constStmtB, constResultB_complete c h0, Bool.and_self]
  | .call f args hp hr resourceEq h0 => by
      revert resourceEq
      generalize hn : nach c.D f [] = out
      intro resourceEq
      cases resourceEq
      dsimp only
      simp only [constStmtB, constArgsB_complete c h0, Bool.and_self]
theorem constBlockB_complete (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {e : Block c.D V l Γ [] []} :
    ConstBlock c e → constBlockB c e = true
  | .nil => by
      simp only [constBlockB, Bool.and_self]
  | .cons h0 h1 => by
      simp only [constBlockB, constStmtB_complete c h0, constBlockB_complete c h1, Bool.and_self]
  | .bind h0 h1 => by
      simp only [constBlockB, constExprB_complete c h0, constBlockB_complete c h1, Bool.and_self]
  | .bindCall f args he hp hr resourceEq rest h0 h1 => by
      revert resourceEq rest h1
      generalize hn : nach c.D f [] = out
      intro resourceEq rest h1
      cases resourceEq
      dsimp only at h1
      simp only [constBlockB, constArgsB_complete c h0, constBlockB_complete c h1, Bool.and_self]
theorem constEndB_complete (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {e : Endblock c.D V l Γ []} :
    ConstEnd c e → constEndB c e = true
  | .ret h0 => by
      simp only [constEndB, constResultB_complete c h0, Bool.and_self]
  | .cons h0 h1 => by
      simp only [constEndB, constStmtB_complete c h0, constEndB_complete c h1, Bool.and_self]
  | .bind h0 h1 => by
      simp only [constEndB, constExprB_complete c h0, constEndB_complete c h1, Bool.and_self]
  | .ite h0 h1 h2 => by
      simp only [constEndB, constExprB_complete c h0, constEndB_complete c h1, constEndB_complete c h2, Bool.and_self]
  | .bindCall f args he hp hr resourceEq rest h0 h1 => by
      revert resourceEq rest h1
      generalize hn : nach c.D f [] = out
      intro resourceEq rest h1
      cases resourceEq
      dsimp only at h1
      simp only [constEndB, constArgsB_complete c h0, constEndB_complete c h1, Bool.and_self]
theorem constArmsB_complete (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {cs : List (Option Ty)} {e : Arms c.D V l Γ [] [] cs} :
    ConstArms c e → constArmsB c e = true
  | .nil => by
      simp only [constArmsB, Bool.and_self]
  | .cons h0 h1 => by
      simp only [constArmsB, constBlockB_complete c h0, constArmsB_complete c h1, Bool.and_self]
theorem constReasonArmsB_complete (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {n : Nat} {e : GrundArms c.D V l Γ [] [] n} :
    ConstReasonArms c e → constReasonArmsB c e = true
  | .nil => by
      simp only [constReasonArmsB, Bool.and_self]
  | .cons h0 h1 => by
      simp only [constReasonArmsB, constBlockB_complete c h0, constReasonArmsB_complete c h1, Bool.and_self]
end

theorem constAdmissibleB_iff (c : ConstProgram) :
    constAdmissibleB c = true ↔ ConstAdmissible c := by
  simp only [constAdmissibleB, List.all_eq_true]
  constructor
  · intro accepted f
    exact constEndB_sound c _ (accepted f (c.functions_complete f))
  · intro accepted f _
    exact constEndB_complete c (accepted f)

end Gabbro.Grammatik
