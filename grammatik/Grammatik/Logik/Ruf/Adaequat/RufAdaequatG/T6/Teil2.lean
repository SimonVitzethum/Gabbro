module

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T5
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T6.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

mutual

/-- The statement never hands the world to the oracle. -/
def Stmt.ohneOrakel {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => t.ohneOrakel && e.ohneOrakel
  | .onOption _ p a => p.ohneOrakel && a.ohneOrakel
  | .onTag _ arms => arms.ohneOrakel
  | .onWhy _ arms => arms.ohneOrakel
  | .locks _ _ body => body.ohneOrakel
  | .breaking _ body => body.ohneOrakel
  | .traverse _ _ body => body.ohneOrakel
  | .consumeTraverse _ _ _ _ _ _ body => body.ohneOrakel
  | .retry _ _ body u => body.ohneOrakel && u.ohneOrakel
  | .forever _ _ body => body.ohneOrakel
  | .axiomCall .. => false
  | _ => true

def Block.ohneOrakel {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => s.ohneOrakel && rest.ohneOrakel
  | .bind _ rest => rest.ohneOrakel
  | .bindCall _ _ _ _ _ rest => rest.ohneOrakel
  | .bindCallInd _ _ _ _ _ rest => rest.ohneOrakel
  | .bindCallElse _ _ _ _ _ err rest => err.ohneOrakel && rest.ohneOrakel
  | .bindAxiom .. => false
  | .bindAxiomElse .. => false
  | .regRead .. => false
  | .regReadElse .. => false
  | .awaits .. => false
  | .exchange _ _ _ _ rest => rest.ohneOrakel
  | .narrow _ _ _ sonst rest => sonst.ohneOrakel && rest.ohneOrakel
  | .narrowRequired _ _ _ rest => rest.ohneOrakel
  | .check _ sonst rest => sonst.ohneOrakel && rest.ohneOrakel
  | .float _ _ _ _ _ rest => rest.ohneOrakel
  | .floatLit _ _ _ rest => rest.ohneOrakel
  | .floatOf _ _ _ rest => rest.ohneOrakel
  | .floatNarrow _ _ _ sonst rest => sonst.ohneOrakel && rest.ohneOrakel

def Endblock.ohneOrakel {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retWhy .. => true
  | .retScoped .. => true
  | .retWhyScoped .. => true
  | .leave .. => true
  | .next .. => true
  | .cons s rest => s.ohneOrakel && rest.ohneOrakel
  | .bind _ rest => rest.ohneOrakel
  | .bindCall _ _ _ _ _ rest => rest.ohneOrakel
  | .bindCallElse _ _ _ _ _ err rest => err.ohneOrakel && rest.ohneOrakel
  | .bindAxiom .. => false
  | .bindAxiomElse .. => false
  | .regRead .. => false
  | .regReadElse .. => false
  | .awaits .. => false
  | .bindCallInd _ _ _ _ _ rest => rest.ohneOrakel
  | .narrow _ _ _ sonst rest => sonst.ohneOrakel && rest.ohneOrakel
  | .narrowRequired _ _ _ rest => rest.ohneOrakel
  | .exchange _ _ _ _ rest => rest.ohneOrakel
  | .ite _ t e => t.ohneOrakel && e.ohneOrakel

def Arms.ohneOrakel {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => b.ohneOrakel && rest.ohneOrakel

def GrundArms.ohneOrakel {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} : GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => b.ohneOrakel && rest.ohneOrakel

end
/-- `armWahlG` selects an oracle-free arm of oracle-free arms. -/
theorem armWahlG_ohneOrakel {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    arms.ohneOrakel = true → (armWahlG arms v).2.1.ohneOrakel = true
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨⟨0, _⟩, _⟩, h => by
      simp only [Arms.ohneOrakel, Bool.and_eq_true] at h
      exact h.1
  | _, .cons _ rest, ⟨⟨_ + 1, _⟩, _⟩, h => by
      simp only [Arms.ohneOrakel, Bool.and_eq_true] at h
      exact armWahlG_ohneOrakel rest _ h.2


end Gabbro.Grammatik
