module

public import Grammatik.Kern.Syntax.Konst.ReinBBeweis

@[expose] public section
namespace Gabbro.Grammatik

/-- Direct callees in the admitted structural fragment; rejected forms contribute no edges.
    This scan must be paired with ConstAdmissible. Expressions contain no calls. -/
mutual
def constStmtCalls (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {Λ Λout : List (Res c.D)} : Stmt c.D V l Γ Λ Λout → List c.D.Fn
  | .assignVar x e => []
  | .ite condition yes no => constBlockCalls c yes ++ constBlockCalls c no
  | .onOption value present absent => constBlockCalls c present ++ constBlockCalls c absent
  | .onTag value arms => constArmsCalls c arms
  | .onWhy reason arms => constReasonArmsCalls c arms
  | .ret value h => []
  | .call f args hp hr => [f]
  | .assignSlot .. => []
  | .assignThru .. => []
  | .assignGlob .. => []
  | .putBytes .. => []
  | .shift .. => []
  | .callInd .. => []
  | .locks .. => []
  | .breaking .. => []
  | .traverse .. => []
  | .retry .. => []
  | .forever .. => []
  | .axiomCall .. => []
  | .regWrite .. => []
  | .transition .. => []
  | .publish .. => []
  | .advances .. => []
  | .retires .. => []
  | .retWhy .. => []
  | .leave .. => []
  | .next .. => []
  | .assignSlotRef .. => []
def constBlockCalls (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {Λ Λout : List (Res c.D)} : Block c.D V l Γ Λ Λout → List c.D.Fn
  | .nil => []
  | .cons stmt rest => constStmtCalls c stmt ++ constBlockCalls c rest
  | .bind value rest => constBlockCalls c rest
  | .bindCall f args he hp hr rest => [f] ++ constBlockCalls c rest
  | .bindCallInd .. => []
  | .bindCallElse .. => []
  | .bindAxiom .. => []
  | .bindAxiomElse .. => []
  | .regRead .. => []
  | .regReadElse .. => []
  | .awaits .. => []
  | .exchange .. => []
  | .narrow .. => []
  | .check .. => []
  | .float .. => []
  | .floatLit .. => []
  | .floatOf .. => []
  | .floatNarrow .. => []
def constEndCalls (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {Λ : List (Res c.D)} : Endblock c.D V l Γ Λ → List c.D.Fn
  | .ret value h => []
  | .cons stmt rest => constStmtCalls c stmt ++ constEndCalls c rest
  | .bind value rest => constEndCalls c rest
  | .ite condition yes no => constEndCalls c yes ++ constEndCalls c no
  | .bindCall f args he hp hr rest => [f] ++ constEndCalls c rest
  | .retWhy .. => []
  | .leave .. => []
  | .next .. => []
  | .bindCallElse .. => []
  | .bindAxiom .. => []
  | .bindAxiomElse .. => []
  | .regRead .. => []
  | .regReadElse .. => []
  | .awaits .. => []
  | .bindCallInd .. => []
  | .narrow .. => []
  | .exchange .. => []
def constArmsCalls (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {Λ Λout : List (Res c.D)} {cs : List (Option (Int × Int))} : Arms c.D V l Γ Λ Λout cs → List c.D.Fn
  | .nil => []
  | .cons body rest => constBlockCalls c body ++ constArmsCalls c rest
def constReasonArmsCalls (c : ConstProgram) {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {Λ Λout : List (Res c.D)} {n : Nat} : GrundArms c.D V l Γ Λ Λout n → List c.D.Fn
  | .nil => []
  | .cons body rest => constBlockCalls c body ++ constReasonArmsCalls c rest
end

/-- Direct call graph of canonical const bodies. -/
def constCallees (c : ConstProgram) (f : c.D.Fn) : List c.D.Fn :=
  constEndCalls c (c.P.rumpf f)

/-- A rank bounded by n certifies at most n nested call edges.
    The bound may conservatively exceed the longest path. -/
def ConstTermination (c : ConstProgram) (n : Nat) : Prop :=
  ∃ rank : c.D.Fn → Nat, ∀ f,
    rank f ≤ n ∧ ∀ g ∈ constCallees c f, rank g < rank f

def constTerminationB (c : ConstProgram) (n : Nat) (rank : c.D.Fn → Nat) : Bool :=
  c.functions.all fun f => decide (rank f ≤ n) &&
    (constCallees c f).all (fun g => decide (rank g < rank f))

theorem constTerminationB_sound (c : ConstProgram) (n : Nat)
    (rank : c.D.Fn → Nat) (h : constTerminationB c n rank = true) :
    ConstTermination c n := by
  refine ⟨rank, ?_⟩
  simp only [constTerminationB, List.all_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  intro f
  exact h f (c.functions_complete f)

end Gabbro.Grammatik
