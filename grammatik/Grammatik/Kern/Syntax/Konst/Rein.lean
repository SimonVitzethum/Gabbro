module

public import Grammatik.Kern.Syntax.Konst.Programm

@[expose] public section

namespace Gabbro.Grammatik

/-! Structural whitelist for the first, loop-free const slice. Calls are
    indexed by the same closed program. Source mutability provenance remains
    an obligation of the source derivation; typed G variables carry no such bit.
    Auxiliary judgments inspect every argument, payload and dispatch arm. -/

mutual

inductive ConstExpr (c : ConstProgram) : {Γ : Ctx} → {τ : Ty} → Expr c.D Γ [] τ → Prop where
  | pureLit : ConstExpr c (.lit n)
  | pureTru : ConstExpr c (.tru)
  | pureFls : ConstExpr c (.fls)
  | pureVar : ConstExpr c (.var x)
  | pureWiden : ConstExpr c e → ConstExpr c (.widen h1 h2 e)
  | pureAdd : ConstExpr c a → ConstExpr c b → ConstExpr c (.add a b)
  | pureSub : ConstExpr c a → ConstExpr c b → ConstExpr c (.sub a b)
  | pureNeg : ConstExpr c a → ConstExpr c (.neg a)
  | pureMul : ConstExpr c a → ConstExpr c b → ConstExpr c (.mul a b)
  | pureDiv : ConstExpr c a → ConstExpr c b → ConstExpr c (.div h0 h1p a b)
  | pureRem : ConstExpr c a → ConstExpr c b → ConstExpr c (.rem h0 h1p a b)
  | pureSdiv : ConstExpr c a → ConstExpr c b → ConstExpr c (.sdiv hb a b)
  | pureSrem : ConstExpr c a → ConstExpr c b → ConstExpr c (.srem hb a b)
  | pureBand : ConstExpr c a → ConstExpr c b → ConstExpr c (.band h0 h0p a b)
  | pureBor : ConstExpr c a → ConstExpr c b → ConstExpr c (.bor w h0 h0p hw1 hw2 a b)
  | pureBxor : ConstExpr c a → ConstExpr c b → ConstExpr c (.bxor w h0 h0p hw1 hw2 a b)
  | pureShl : ConstExpr c a → ConstExpr c b → ConstExpr c (.shl w hw1 hw2 h0 h0p a b)
  | pureShr : ConstExpr c a → ConstExpr c b → ConstExpr c (.shr w hw1 hw2 h0 h0p a b)
  | pureLt : ConstExpr c a → ConstExpr c b → ConstExpr c (.lt a b)
  | pureLe : ConstExpr c a → ConstExpr c b → ConstExpr c (.le a b)
  | pureEq : ConstExpr c a → ConstExpr c b → ConstExpr c (.eq a b)
  | pureAnd : ConstExpr c a → ConstExpr c b → ConstExpr c (.and a b)
  | pureOr : ConstExpr c a → ConstExpr c b → ConstExpr c (.or a b)
  | pureNot : ConstExpr c a → ConstExpr c (.not a)
  | pureNone : ConstExpr c (.none n)
  | pureSome : ConstExpr c e → ConstExpr c (.some e)
  | pureIstSome : ConstExpr c e → ConstExpr c (.istSome e)
  | pureCase {Γ : Ctx} {cs : List (Option Ty)} {i : Fin cs.length}
      {payload : NutzlastExpr c.D Γ [] (cs.get i)} :
      ConstPayload c payload → ConstExpr c (.case cs i payload)
  | pureWhy : ConstExpr c (.why n r)
  | pureForallSlots {Γ : Ctx} {t : c.D.Tab} {body : Expr c.D (.index (c.D.count t) :: Γ) [] .bool}
      {hL : darf c.D t []} : ConstExpr c body → ConstExpr c (.forallSlots t body hL)
  | pureExistsSlots {Γ : Ctx} {t : c.D.Tab} {body : Expr c.D (.index (c.D.count t) :: Γ) [] .bool}
      {hL : darf c.D t []} : ConstExpr c body → ConstExpr c (.existsSlots t body hL)
  | pureArrNil : ConstExpr c (.arrNil)
  | pureArrCons : ConstExpr c a → ConstExpr c rest → ConstExpr c (.arrCons a rest)
  | pureArrGet : ConstExpr c a → ConstExpr c i → ConstExpr c (.arrGet a i)
  | pureArrSet : ConstExpr c a → ConstExpr c i → ConstExpr c v → ConstExpr c (.arrSet a i v)
  | pureStrLit : ConstExpr c (.strLit bs h)
  | pureStrLen : ConstExpr c s → ConstExpr c (.strLen s)
  | pureStrCat : ConstExpr c s → ConstExpr c t → ConstExpr c (.strCat s t)
  | pureStrGet : ConstExpr c s → ConstExpr c i → ConstExpr c (.strGet s i)
  | pureStrEq : ConstExpr c s → ConstExpr c t → ConstExpr c (.strEq s t)
  | pureStrLt : ConstExpr c s → ConstExpr c t → ConstExpr c (.strLt s t)
  | pureStrWeit : ConstExpr c s → ConstExpr c (.strWeit m s)
  | pureWenn : ConstExpr c condition → ConstExpr c a → ConstExpr c b → ConstExpr c (.wenn condition a b)
  | pureEng {Γ : Ctx} {lo hi lo' hi' : Int} {e : Expr c.D Γ [] (.int lo hi)}
      {fallback : Expr c.D Γ [] (.int lo' hi')} :
      ConstExpr c e → ConstExpr c fallback → ConstExpr c (.eng e lo' hi' fallback)
  | pureIntBuiltin1 : ConstExpr c a → ConstExpr c (.intBuiltin1 op a)
  | pureIntBuiltin2 : ConstExpr c a → ConstExpr c b → ConstExpr c (.intBuiltin2 op a b)
  | pureCount {Γ : Ctx} {n : Nat} {body : Expr c.D (.index (n : Int) :: Γ) [] .bool} :
      ConstExpr c body → ConstExpr c (.count n body)

inductive ConstPayload (c : ConstProgram) : {Γ : Ctx} → {k : Option Ty} →
    NutzlastExpr c.D Γ [] k → Prop where
  | empty : ConstPayload c .empty
  | val : ConstExpr c e → ConstPayload c (.val e)

inductive ConstArgs (c : ConstProgram) : {Γ : Ctx} → {ts : List Ty} → Args c.D Γ [] ts → Prop where
  | nil : ConstArgs c .nil
  | cons : ConstExpr c e → ConstArgs c rest → ConstArgs c (.cons e rest)

inductive ConstResult (c : ConstProgram) : {Γ : Ctx} → {τ : Option Ty} → ErgExpr c.D Γ [] τ → Prop where
  | empty : ConstResult c .empty
  | val : ConstExpr c e → ConstResult c (.val e)

inductive ConstStmt (c : ConstProgram) : {V : Vertrag c.D} → {l : Bool} → {Γ : Ctx} →
    Stmt c.D V l Γ [] [] → Prop where
  | assignVar : ConstExpr c e → ConstStmt c (.assignVar x e)
  | ite : ConstExpr c condition → ConstBlock c yes → ConstBlock c no →
      ConstStmt c (.ite condition yes no)
  | onOption : ConstExpr c value → ConstBlock c present → ConstBlock c absent →
      ConstStmt c (.onOption value present absent)
  | onTag : ConstExpr c value → ConstArms c arms → ConstStmt c (.onTag value arms)
  | onWhy : ConstExpr c reason → ConstReasonArms c arms → ConstStmt c (.onWhy reason arms)
  | call {V l Γ} (f : c.D.Fn) (args : Args c.D Γ [] (c.D.params f))
      (hp : RufPasst c.D V (c.D.signatur f) []) (hr : c.D.gruende f = 0)
      (h : nach c.D f [] = []) :
      ConstArgs c args → ConstStmt c (h ▸ Stmt.call (D := c.D) (V := V) (l := l) f args hp hr)
  | ret : ConstResult c value → ConstStmt c (.ret value h)

inductive ConstBlock (c : ConstProgram) : {V : Vertrag c.D} → {l : Bool} → {Γ : Ctx} →
    Block c.D V l Γ [] [] → Prop where
  | nil : ConstBlock c .nil
  | cons : ConstStmt c stmt → ConstBlock c rest → ConstBlock c (.cons stmt rest)
  | bind : ConstExpr c value → ConstBlock c rest → ConstBlock c (.bind value rest)
  | bindCall {V l Γ τ} (f : c.D.Fn) (args : Args c.D Γ [] (c.D.params f))
      (he : c.D.erg f = some τ) (hp : RufPasst c.D V (c.D.signatur f) [])
      (hr : c.D.gruende f = 0) (h : nach c.D f [] = [])
      (rest : Block c.D V l (τ :: Γ) (nach c.D f []) []) :
      ConstArgs c args → ConstBlock c (h ▸ rest) →
      ConstBlock c (.bindCall f args he hp hr rest)

inductive ConstEnd (c : ConstProgram) : {V : Vertrag c.D} → {l : Bool} → {Γ : Ctx} →
    Endblock c.D V l Γ [] → Prop where
  | ret : ConstResult c value → ConstEnd c (.ret value h)
  | cons : ConstStmt c stmt → ConstEnd c rest → ConstEnd c (.cons stmt rest)
  | bind : ConstExpr c value → ConstEnd c rest → ConstEnd c (.bind value rest)
  | bindCall {V l Γ τ} (f : c.D.Fn) (args : Args c.D Γ [] (c.D.params f))
      (he : c.D.erg f = some τ) (hp : RufPasst c.D V (c.D.signatur f) [])
      (hr : c.D.gruende f = 0) (h : nach c.D f [] = [])
      (rest : Endblock c.D V l (τ :: Γ) (nach c.D f [])) :
      ConstArgs c args → ConstEnd c (h ▸ rest) →
      ConstEnd c (.bindCall f args he hp hr rest)
  | ite : ConstExpr c condition → ConstEnd c yes → ConstEnd c no →
      ConstEnd c (.ite condition yes no)

inductive ConstArms (c : ConstProgram) : {V : Vertrag c.D} → {l : Bool} → {Γ : Ctx} →
    {cs : List (Option Ty)} → Arms c.D V l Γ [] [] cs → Prop where
  | nil : ConstArms c .nil
  | cons : ConstBlock c body → ConstArms c rest → ConstArms c (.cons body rest)

inductive ConstReasonArms (c : ConstProgram) : {V : Vertrag c.D} → {l : Bool} → {Γ : Ctx} →
    {n : Nat} → GrundArms c.D V l Γ [] [] n → Prop where
  | nil : ConstReasonArms c .nil
  | cons : ConstBlock c body → ConstReasonArms c rest → ConstReasonArms c (.cons body rest)

end

/-- Bodies are end blocks in canonical G, rather than falling-through blocks.
    Entry resources are transported using the closed-program certificate. -/
def ConstAdmissible (c : ConstProgram) : Prop :=
  ∀ f, ConstEnd c (c.emptyEntry f ▸ c.P.rumpf f)

end Gabbro.Grammatik
