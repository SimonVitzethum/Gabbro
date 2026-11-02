module
public import Grammatik.Kern.Syntax.Konst.ReinB
public section
namespace Gabbro.Grammatik
private theorem emptyResources (c : ConstProgram) (rs : List (Res c.D)) : rs = [] := by
  cases rs with
  | nil => rfl
  | cons r rest =>
    cases r with
    | held lock => exact (c.noLocks lock).elim
    | marke mark stage => exact (c.noMarks mark).elim
mutual
theorem constExprB_sound (c : ConstProgram) {Γ : Ctx} {τ : Ty} (e : Expr c.D Γ [] τ) :
    constExprB c e = true → ConstExpr c e :=
  match e with
  | .lit n => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      exact .pureLit
  | .tru => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      exact .pureTru
  | .fls => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      exact .pureFls
  | .var x => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      exact .pureVar
  | .widen h1 h2 e => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      exact .pureWiden (constExprB_sound c e accepted)
  | .add a b => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureAdd (constExprB_sound c a h0) (constExprB_sound c b h1)
  | .sub a b => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureSub (constExprB_sound c a h0) (constExprB_sound c b h1)
  | .neg a => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      exact .pureNeg (constExprB_sound c a accepted)
  | .mul a b => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureMul (constExprB_sound c a h0) (constExprB_sound c b h1)
  | .div h0 h1p a b => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureDiv (constExprB_sound c a h0) (constExprB_sound c b h1)
  | .rem h0 h1p a b => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureRem (constExprB_sound c a h0) (constExprB_sound c b h1)
  | .sdiv hb a b => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureSdiv (constExprB_sound c a h0) (constExprB_sound c b h1)
  | .srem hb a b => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureSrem (constExprB_sound c a h0) (constExprB_sound c b h1)
  | .band h0 h0p a b => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureBand (constExprB_sound c a h0) (constExprB_sound c b h1)
  | .bor w h0 h0p hw1 hw2 a b => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureBor (constExprB_sound c a h0) (constExprB_sound c b h1)
  | .bxor w h0 h0p hw1 hw2 a b => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureBxor (constExprB_sound c a h0) (constExprB_sound c b h1)
  | .shl w hw1 hw2 h0 h0p a b => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureShl (constExprB_sound c a h0) (constExprB_sound c b h1)
  | .shr w hw1 hw2 h0 h0p a b => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureShr (constExprB_sound c a h0) (constExprB_sound c b h1)
  | .lt a b => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureLt (constExprB_sound c a h0) (constExprB_sound c b h1)
  | .le a b => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureLe (constExprB_sound c a h0) (constExprB_sound c b h1)
  | .eq a b => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureEq (constExprB_sound c a h0) (constExprB_sound c b h1)
  | .and a b => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureAnd (constExprB_sound c a h0) (constExprB_sound c b h1)
  | .or a b => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureOr (constExprB_sound c a h0) (constExprB_sound c b h1)
  | .not a => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      exact .pureNot (constExprB_sound c a accepted)
  | .none n => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      exact .pureNone
  | .some e => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      exact .pureSome (constExprB_sound c e accepted)
  | .istSome e => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      exact .pureIstSome (constExprB_sound c e accepted)
  | .case cs i payload => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      exact .pureCase (constPayloadB_sound c payload accepted)
  | .why n r => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      exact .pureWhy
  | .forallSlots t body hL => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      exact .pureForallSlots (constExprB_sound c body accepted)
  | .existsSlots t body hL => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      exact .pureExistsSlots (constExprB_sound c body accepted)
  | .arrNil => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      exact .pureArrNil
  | .arrCons a rest => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureArrCons (constExprB_sound c a h0) (constExprB_sound c rest h1)
  | .arrGet a i => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureArrGet (constExprB_sound c a h0) (constExprB_sound c i h1)
  | .arrSet a i v => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨⟨h0, h1⟩, h2⟩ := accepted
      exact .pureArrSet (constExprB_sound c a h0) (constExprB_sound c i h1) (constExprB_sound c v h2)
  | .strLit bs h => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      exact .pureStrLit
  | .strLen s => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      exact .pureStrLen (constExprB_sound c s accepted)
  | .strCat s t => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureStrCat (constExprB_sound c s h0) (constExprB_sound c t h1)
  | .strGet s i => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureStrGet (constExprB_sound c s h0) (constExprB_sound c i h1)
  | .strEq s t => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureStrEq (constExprB_sound c s h0) (constExprB_sound c t h1)
  | .strLt s t => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureStrLt (constExprB_sound c s h0) (constExprB_sound c t h1)
  | .strWeit m s => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      exact .pureStrWeit (constExprB_sound c s accepted)
  | .wenn condition a b => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨⟨h0, h1⟩, h2⟩ := accepted
      exact .pureWenn (constExprB_sound c condition h0) (constExprB_sound c a h1) (constExprB_sound c b h2)
  | .eng e lo hi fallback => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureEng (constExprB_sound c e h0) (constExprB_sound c fallback h1)
  | .intBuiltin1 op a => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      exact .pureIntBuiltin1 (constExprB_sound c a accepted)
  | .intBuiltin2 op a b => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureIntBuiltin2 (constExprB_sound c a h0) (constExprB_sound c b h1)
  | .count n body => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      exact .pureCount (constExprB_sound c body accepted)
  | .prod r args => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      exact .pureProd (constArgsB_sound c args accepted)
  | .prodGet v _ => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      exact .pureProdGet (constExprB_sound c v accepted)
  | .prodSet v _ e => by
      intro accepted; simp only [constExprB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .pureProdSet (constExprB_sound c v h0) (constExprB_sound c e h1)
  | _ => by simp [constExprB]
theorem constPayloadB_sound (c : ConstProgram) {Γ : Ctx} {k : Option (Int × Int)} (e : NutzlastExpr c.D Γ [] k) :
    constPayloadB c e = true → ConstPayload c e :=
  match e with
  | .empty => by
      intro accepted; simp only [constPayloadB, Bool.and_eq_true] at accepted
      exact .empty
  | .num e => by
      intro accepted; simp only [constPayloadB, Bool.and_eq_true] at accepted
      exact .num (constExprB_sound c e accepted)
theorem constArgsB_sound (c : ConstProgram) {Γ : Ctx} {ts : List Ty} (e : Args c.D Γ [] ts) :
    constArgsB c e = true → ConstArgs c e :=
  match e with
  | .nil => by
      intro accepted; simp only [constArgsB, Bool.and_eq_true] at accepted
      exact .nil
  | .cons e rest => by
      intro accepted; simp only [constArgsB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .cons (constExprB_sound c e h0) (constArgsB_sound c rest h1)
theorem constResultB_sound (c : ConstProgram) {Γ : Ctx} {τ : Option Ty} (e : ErgExpr c.D Γ [] τ) :
    constResultB c e = true → ConstResult c e :=
  match e with
  | .empty => by
      intro accepted; simp only [constResultB, Bool.and_eq_true] at accepted
      exact .empty
  | .val e => by
      intro accepted; simp only [constResultB, Bool.and_eq_true] at accepted
      exact .val (constExprB_sound c e accepted)
theorem constStmtB_sound (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} (e : Stmt c.D V l Γ [] []) :
    constStmtB c e = true → ConstStmt c e :=
  match e with
  | .assignVar x e => by
      intro accepted; simp only [constStmtB, Bool.and_eq_true] at accepted
      exact .assignVar (constExprB_sound c e accepted)
  | .ite condition yes no => by
      intro accepted; simp only [constStmtB, Bool.and_eq_true] at accepted
      obtain ⟨⟨h0, h1⟩, h2⟩ := accepted
      exact .ite (constExprB_sound c condition h0) (constBlockB_sound c yes h1) (constBlockB_sound c no h2)
  | .onOption value present absent => by
      intro accepted; simp only [constStmtB, Bool.and_eq_true] at accepted
      obtain ⟨⟨h0, h1⟩, h2⟩ := accepted
      exact .onOption (constExprB_sound c value h0) (constBlockB_sound c present h1) (constBlockB_sound c absent h2)
  | .onTag value arms => by
      intro accepted; simp only [constStmtB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .onTag (constExprB_sound c value h0) (constArmsB_sound c arms h1)
  | .onWhy reason arms => by
      intro accepted; simp only [constStmtB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .onWhy (constExprB_sound c reason h0) (constReasonArmsB_sound c arms h1)
  | .ret value h => by
      intro accepted; simp only [constStmtB, Bool.and_eq_true] at accepted
      exact .ret (constResultB_sound c value accepted)
  | .call f args hp hr => by
      have resourceEq := emptyResources c (nach c.D f [])
      cases resourceEq
      intro accepted; simp only [constStmtB, Bool.and_eq_true] at accepted
      exact ConstStmt.call f args hp hr rfl (constArgsB_sound c args accepted)
  | _ => by simp [constStmtB]
theorem constBlockB_sound (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} (e : Block c.D V l Γ [] []) :
    constBlockB c e = true → ConstBlock c e :=
  match e with
  | .nil => by
      intro accepted; simp only [constBlockB, Bool.and_eq_true] at accepted
      exact .nil
  | .cons stmt rest => by
      rename_i middle
      have resourceEq := emptyResources c middle
      cases resourceEq
      intro accepted; simp only [constBlockB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .cons (constStmtB_sound c stmt h0) (constBlockB_sound c rest h1)
  | .bind value rest => by
      intro accepted; simp only [constBlockB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .bind (constExprB_sound c value h0) (constBlockB_sound c rest h1)
  | .bindCall f args he hp hr rest => by
      have resourceEq := emptyResources c (nach c.D f [])
      cases resourceEq
      intro accepted; simp only [constBlockB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact ConstBlock.bindCall f args he hp hr rfl rest (constArgsB_sound c args h0) (constBlockB_sound c rest h1)
  | _ => by simp [constBlockB]
theorem constEndB_sound (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} (e : Endblock c.D V l Γ []) :
    constEndB c e = true → ConstEnd c e :=
  match e with
  | .ret value h => by
      intro accepted; simp only [constEndB, Bool.and_eq_true] at accepted
      exact .ret (constResultB_sound c value accepted)
  | .cons stmt rest => by
      rename_i middle
      have resourceEq := emptyResources c middle
      cases resourceEq
      intro accepted; simp only [constEndB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .cons (constStmtB_sound c stmt h0) (constEndB_sound c rest h1)
  | .bind value rest => by
      intro accepted; simp only [constEndB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .bind (constExprB_sound c value h0) (constEndB_sound c rest h1)
  | .ite condition yes no => by
      intro accepted; simp only [constEndB, Bool.and_eq_true] at accepted
      obtain ⟨⟨h0, h1⟩, h2⟩ := accepted
      exact .ite (constExprB_sound c condition h0) (constEndB_sound c yes h1) (constEndB_sound c no h2)
  | .bindCall f args he hp hr rest => by
      have resourceEq := emptyResources c (nach c.D f [])
      cases resourceEq
      intro accepted; simp only [constEndB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact ConstEnd.bindCall f args he hp hr rfl rest (constArgsB_sound c args h0) (constEndB_sound c rest h1)
  | _ => by simp [constEndB]
theorem constArmsB_sound (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {cs : List (Option (Int × Int))} (e : Arms c.D V l Γ [] [] cs) :
    constArmsB c e = true → ConstArms c e :=
  match e with
  | .nil => by
      intro accepted; simp only [constArmsB, Bool.and_eq_true] at accepted
      exact .nil
  | .cons body rest => by
      intro accepted; simp only [constArmsB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .cons (constBlockB_sound c body h0) (constArmsB_sound c rest h1)
theorem constReasonArmsB_sound (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {n : Nat} (e : GrundArms c.D V l Γ [] [] n) :
    constReasonArmsB c e = true → ConstReasonArms c e :=
  match e with
  | .nil => by
      intro accepted; simp only [constReasonArmsB, Bool.and_eq_true] at accepted
      exact .nil
  | .cons body rest => by
      intro accepted; simp only [constReasonArmsB, Bool.and_eq_true] at accepted
      obtain ⟨h0, h1⟩ := accepted
      exact .cons (constBlockB_sound c body h0) (constReasonArmsB_sound c rest h1)
end


end Gabbro.Grammatik
