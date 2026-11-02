module

public import Grammatik.Kern.Syntax.Konst.Rein

@[expose] public section
namespace Gabbro.Grammatik

/-! Structural Boolean whitelist. Resource indices are irrelevant to the scan;
    the equivalence below is stated on the certified empty-resource fragment. -/

mutual
def constExprB (c : ConstProgram) {Γ : Ctx} {Λ : List (Res c.D)} {τ : Ty} : Expr c.D Γ Λ τ → Bool
  | .lit n => true
  | .tru => true
  | .fls => true
  | .var x => true
  | .widen h1 h2 e => constExprB c e
  | .add a b => constExprB c a && constExprB c b
  | .sub a b => constExprB c a && constExprB c b
  | .neg a => constExprB c a
  | .mul a b => constExprB c a && constExprB c b
  | .div h0 h1p a b => constExprB c a && constExprB c b
  | .rem h0 h1p a b => constExprB c a && constExprB c b
  | .sdiv hb a b => constExprB c a && constExprB c b
  | .srem hb a b => constExprB c a && constExprB c b
  | .band h0 h0p a b => constExprB c a && constExprB c b
  | .bor w h0 h0p hw1 hw2 a b => constExprB c a && constExprB c b
  | .bxor w h0 h0p hw1 hw2 a b => constExprB c a && constExprB c b
  | .shl w hw1 hw2 h0 h0p a b => constExprB c a && constExprB c b
  | .shr w hw1 hw2 h0 h0p a b => constExprB c a && constExprB c b
  | .lt a b => constExprB c a && constExprB c b
  | .le a b => constExprB c a && constExprB c b
  | .eq a b => constExprB c a && constExprB c b
  | .and a b => constExprB c a && constExprB c b
  | .or a b => constExprB c a && constExprB c b
  | .not a => constExprB c a
  | .none n => true
  | .some e => constExprB c e
  | .istSome e => constExprB c e
  | .case cs i payload => constPayloadB c payload
  | .why n r => true
  | .forallSlots t body hL => constExprB c body
  | .existsSlots t body hL => constExprB c body
  | .arrNil => true
  | .arrCons a rest => constExprB c a && constExprB c rest
  | .arrGet a i => constExprB c a && constExprB c i
  | .arrSet a i v => constExprB c a && constExprB c i && constExprB c v
  | .strLit bs h => true
  | .strLen s => constExprB c s
  | .strCat s t => constExprB c s && constExprB c t
  | .strGet s i => constExprB c s && constExprB c i
  | .strEq s t => constExprB c s && constExprB c t
  | .strLt s t => constExprB c s && constExprB c t
  | .strWeit m s => constExprB c s
  | .wenn condition a b => constExprB c condition && constExprB c a && constExprB c b
  | .eng e lo hi fallback => constExprB c e && constExprB c fallback
  | .intBuiltin1 op a => constExprB c a
  | .intBuiltin2 op a b => constExprB c a && constExprB c b
  | .count n body => constExprB c body
  | .glob .. => false
  | .slot .. => false
  | .thru .. => false
  | .ptrOf .. => false
  | .fnref .. => false
  | .oldG .. => false
  | .oldS .. => false
  | .getBytes .. => false
  | .fllt .. => false
  | .flle .. => false
  | .reaches .. => false
  | .refEq .. => false
  | .slotRef .. => false
def constPayloadB (c : ConstProgram) {Γ : Ctx} {Λ : List (Res c.D)} {k : Option Ty} : NutzlastExpr c.D Γ Λ k → Bool
  | .empty => true
  | .val e => constExprB c e
def constArgsB (c : ConstProgram) {Γ : Ctx} {Λ : List (Res c.D)} {ts : List Ty} : Args c.D Γ Λ ts → Bool
  | .nil => true
  | .cons e rest => constExprB c e && constArgsB c rest
def constResultB (c : ConstProgram) {Γ : Ctx} {Λ : List (Res c.D)} {τ : Option Ty} : ErgExpr c.D Γ Λ τ → Bool
  | .empty => true
  | .val e => constExprB c e
def constStmtB (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {Λ Λout : List (Res c.D)} : Stmt c.D V l Γ Λ Λout → Bool
  | .assignVar x e => constExprB c e
  | .ite condition yes no => constExprB c condition && constBlockB c yes && constBlockB c no
  | .onOption value present absent => constExprB c value && constBlockB c present && constBlockB c absent
  | .onTag value arms => constExprB c value && constArmsB c arms
  | .onWhy reason arms => constExprB c reason && constReasonArmsB c arms
  | .ret value h => constResultB c value
  | .call f args hp hr => constArgsB c args
  | .assignSlot .. => false
  | .assignThru .. => false
  | .assignGlob .. => false
  | .putBytes .. => false
  | .shift .. => false
  | .callInd .. => false
  | .locks .. => false
  | .breaking .. => false
  | .traverse .. => false
  | .retry .. => false
  | .forever .. => false
  | .axiomCall .. => false
  | .regWrite .. => false
  | .transition .. => false
  | .publish .. => false
  | .advances .. => false
  | .retires .. => false
  | .retWhy .. => false
  | .leave .. => false
  | .next .. => false
  | .consumeTraverse .. => false
  | .retScoped .. => false
  | .retWhyScoped .. => false
  | .axiomCallElse .. => false
  | .callIndElse .. => false
  | .assignSlotRef .. => false
def constBlockB (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {Λ Λout : List (Res c.D)} : Block c.D V l Γ Λ Λout → Bool
  | .nil => true
  | .cons stmt rest => constStmtB c stmt && constBlockB c rest
  | .bind value rest => constExprB c value && constBlockB c rest
  | .bindCall f args he hp hr rest => constArgsB c args && constBlockB c rest
  | .bindCallInd .. => false
  | .bindCallElse .. => false
  | .bindAxiom .. => false
  | .bindAxiomElse .. => false
  | .regRead .. => false
  | .regReadElse .. => false
  | .awaits .. => false
  | .exchange .. => false
  | .narrow .. => false
  | .narrowRequired .. => false
  | .bindAxiomOpt .. => false
  | .bindAxiomOptElse .. => false
  | .bindCallIndElse .. => false
  | .check .. => false
  | .float .. => false
  | .floatLit .. => false
  | .floatOf .. => false
  | .floatNarrow .. => false
def constEndB (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {Λ : List (Res c.D)} : Endblock c.D V l Γ Λ → Bool
  | .ret value h => constResultB c value
  | .cons stmt rest => constStmtB c stmt && constEndB c rest
  | .bind value rest => constExprB c value && constEndB c rest
  | .ite condition yes no => constExprB c condition && constEndB c yes && constEndB c no
  | .bindCall f args he hp hr rest => constArgsB c args && constEndB c rest
  | .retWhy .. => false
  | .leave .. => false
  | .next .. => false
  | .narrowRequired .. => false
  | .retScoped .. => false
  | .retWhyScoped .. => false
  | .bindAxiomOpt .. => false
  | .bindAxiomOptElse .. => false
  | .bindCallIndElse .. => false
  | .bindCallElse .. => false
  | .bindAxiom .. => false
  | .bindAxiomElse .. => false
  | .regRead .. => false
  | .regReadElse .. => false
  | .awaits .. => false
  | .bindCallInd .. => false
  | .narrow .. => false
  | .exchange .. => false
def constArmsB (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {Λ Λout : List (Res c.D)} {cs : List (Option Ty)} : Arms c.D V l Γ Λ Λout cs → Bool
  | .nil => true
  | .cons body rest => constBlockB c body && constArmsB c rest
def constReasonArmsB (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {Λ Λout : List (Res c.D)} {n : Nat} : GrundArms c.D V l Γ Λ Λout n → Bool
  | .nil => true
  | .cons body rest => constBlockB c body && constReasonArmsB c rest
end

/-- Every declared function body passes the structural whitelist. -/
def constAdmissibleB (c : ConstProgram) : Bool :=
  c.functions.all fun f => constEndB c (c.emptyEntry f ▸ c.P.rumpf f)

end Gabbro.Grammatik
