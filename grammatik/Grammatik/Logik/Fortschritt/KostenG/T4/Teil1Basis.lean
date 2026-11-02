module

public import Grammatik.Logik.Fortschritt.KostenG.T3

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

mutual
/-- **The correspondence, per statement form**: the Lean bound is at most
    the checker's number plus the remainder `zusatz`. -/
theorem spiegel_stmt (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → spiegelS s = true →
      kostenStmt c pa s ≤ kostenKS c s + zusatzS s
  | .ite b t e, h => by
      simp only [spiegelS, Bool.and_eq_true] at h
      have h1 := spiegel_block c pa t h.1
      have h2 := spiegel_block c pa e h.2
      simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .onOption o p a, h => by
      simp only [spiegelS, Bool.and_eq_true] at h
      have h1 := spiegel_block c pa p h.1
      have h2 := spiegel_block c pa a h.2
      simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .onTag v arms, h => by
      have h1 := spiegel_arms c pa arms h
      simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .onWhy r arms, h => by
      have h1 := spiegel_garms c pa arms h
      simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .locks _ _ body, h => by
      have h1 := spiegel_block c pa body h
      simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .breaking _ body, h => by
      have h1 := spiegel_block c pa body h
      simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .traverse t inv body, h => by
      have h1 := spiegel_block c pa body h
      have h2 : (D.count t).toNat * (kostenBlock c pa body + kostenExpr inv + 2) ≤
          (D.count t).toNat * kostenKB c body +
            (D.count t).toNat * (zusatzB body + kostenExpr inv + 2) := by
        rw [← Nat.mul_add]
        exact Nat.mul_le_mul_left _ (by omega)
      simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .callInd .., h => by simp only [spiegelS, Bool.false_eq_true] at h
  | .consumeTraverse .., h => by simp only [spiegelS, Bool.false_eq_true] at h
  | .retry .., h => by simp only [spiegelS, Bool.false_eq_true] at h
  | .forever .., h => by simp only [spiegelS, Bool.false_eq_true] at h
  | .axiomCall .., h => by simp only [spiegelS, Bool.false_eq_true] at h
  | .transition .., h => by simp only [spiegelS, Bool.false_eq_true] at h
  | .advances .., h => by simp only [spiegelS, Bool.false_eq_true] at h
  | .retires .., h => by simp only [spiegelS, Bool.false_eq_true] at h
  | .assignSlot .., _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .assignThru .., _ | .assignSlotRef .., _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .assignGlob .., _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .putBytes .., _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .assignVar .., _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .shift .., _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .call .., _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .regWrite .., _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .publish .., _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .ret .., _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .retWhy .., _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .retScoped .., h => by simp only [spiegelS, Bool.false_eq_true] at h
  | .retWhyScoped .., h => by simp only [spiegelS, Bool.false_eq_true] at h
  | .leave _, _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega
  | .next _, _ => by simp only [kostenStmt, kostenKS, zusatzS]; omega

theorem spiegel_block (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → spiegelB b = true →
      kostenBlock c pa b ≤ kostenKB c b + zusatzB b
  | .nil, _ => by simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .cons s rest, h => by
      simp only [spiegelB, Bool.and_eq_true] at h
      have h1 := spiegel_stmt c pa s h.1
      have h2 := spiegel_block c pa rest h.2
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .bind _ rest, h => by
      have h1 := spiegel_block c pa rest h
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .bindCall _ _ _ _ _ rest, h => by
      have h1 := spiegel_block c pa rest h
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .bindCallInd .., h => by simp only [spiegelB, Bool.false_eq_true] at h
  | .bindCallElse _ _ _ _ _ err rest, h => by
      simp only [spiegelB, Bool.and_eq_true] at h
      have h1 := spiegel_sonst c pa err h.1
      have h2 := spiegel_block c pa rest h.2
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .bindAxiom .., h => by simp only [spiegelB, Bool.false_eq_true] at h
  | .bindAxiomElse .., h => by simp only [spiegelB, Bool.false_eq_true] at h
  | .regRead _ _ rest, h => by
      have h1 := spiegel_block c pa rest h
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .regReadElse _ _ _ sonst rest, h => by
      simp only [spiegelB, Bool.and_eq_true] at h
      have h1 := spiegel_sonst c pa sonst h.1
      have h2 := spiegel_block c pa rest h.2
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .awaits _ _ _ _ _ rest, h => by
      have h1 := spiegel_block c pa rest h
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .exchange _ _ _ _ rest, h => by
      have h1 := spiegel_block c pa rest h
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .narrow _ _ _ sonst rest, h => by
      simp only [spiegelB, Bool.and_eq_true] at h
      have h1 := spiegel_sonst c pa sonst h.1
      have h2 := spiegel_block c pa rest h.2
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .narrowRequired _ _ _ rest, h => by
      have h1 := spiegel_block c pa rest h
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .check _ sonst rest, h => by
      simp only [spiegelB, Bool.and_eq_true] at h
      have h1 := spiegel_sonst c pa sonst h.1
      have h2 := spiegel_block c pa rest h.2
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .float _ _ _ _ _ rest, h => by
      have h1 := spiegel_block c pa rest h
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .floatLit _ _ _ rest, h => by
      have h1 := spiegel_block c pa rest h
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .floatOf _ _ _ rest, h => by
      have h1 := spiegel_block c pa rest h
      simp only [kostenBlock, kostenKB, zusatzB]; omega
  | .floatNarrow _ _ _ sonst rest, h => by
      simp only [spiegelB, Bool.and_eq_true] at h
      have h1 := spiegel_sonst c pa sonst h.1
      have h2 := spiegel_block c pa rest h.2
      simp only [kostenBlock, kostenKB, zusatzB]; omega

theorem spiegel_arms (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} :
    (arms : Arms D V l Γ Λ Λ' cs) → spiegelArms arms = true →
      kostenArms c pa arms ≤ kostenKArms c arms + zusatzArms arms
  | .nil, _ => by simp only [kostenArms, kostenKArms, zusatzArms]; omega
  | .cons b rest, h => by
      simp only [spiegelArms, Bool.and_eq_true] at h
      have h1 := spiegel_block c pa b h.1
      have h2 := spiegel_arms c pa rest h.2
      simp only [kostenArms, kostenKArms, zusatzArms]; omega

theorem spiegel_garms (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} :
    (arms : GrundArms D V l Γ Λ Λ' n) → spiegelGArms arms = true →
      kostenGrundArms c pa arms ≤ kostenKGArms c arms + zusatzGArms arms
  | .nil, _ => by simp only [kostenGrundArms, kostenKGArms, zusatzGArms]; omega
  | .cons b rest, h => by
      simp only [spiegelGArms, Bool.and_eq_true] at h
      have h1 := spiegel_block c pa b h.1
      have h2 := spiegel_garms c pa rest h.2
      simp only [kostenGrundArms, kostenKGArms, zusatzGArms]; omega

theorem spiegel_end (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} :
    (e : Endblock D V l Γ Λ) → spiegelE e = true →
      kostenEnd c pa e ≤ kostenKE c e + zusatzE e
  | .ret .., _ => by simp only [kostenEnd, kostenKE, zusatzE]; omega
  | .retWhy .., _ => by simp only [kostenEnd, kostenKE, zusatzE]; omega
  | .leave _, _ => by simp only [kostenEnd, kostenKE, zusatzE]; omega
  | .next _, _ => by simp only [kostenEnd, kostenKE, zusatzE]; omega
  | .cons s rest, h => by
      simp only [spiegelE, Bool.and_eq_true] at h
      have h1 := spiegel_stmt c pa s h.1
      have h2 := spiegel_end c pa rest h.2
      simp only [kostenEnd, kostenKE, zusatzE]; omega
  | .bind _ rest, h => by
      have h1 := spiegel_end c pa rest h
      simp only [kostenEnd, kostenKE, zusatzE]; omega
  | .bindCall _ _ _ _ _ rest, h => by
      have h1 := spiegel_sonst c pa rest h
      simp only [kostenEnd, kostenKE, zusatzE]; omega
  | .bindCallElse _ _ _ _ _ err rest, h => by
      simp only [spiegelE, Bool.and_eq_true] at h
      have h1 := spiegel_sonst c pa err h.1
      have h2 := spiegel_sonst c pa rest h.2
      simp only [kostenEnd, kostenKE, zusatzE]; omega
  | .bindAxiom .., h => by simp only [spiegelE, Bool.false_eq_true] at h
  | .bindAxiomElse .., h => by simp only [spiegelE, Bool.false_eq_true] at h
  | .regRead _ _ rest, h => by
      have h1 := spiegel_sonst c pa rest h
      simp only [kostenEnd, kostenKE, zusatzE]; omega
  | .regReadElse _ _ _ sonst rest, h => by
      simp only [spiegelE, Bool.and_eq_true] at h
      have h1 := spiegel_sonst c pa sonst h.1
      have h2 := spiegel_sonst c pa rest h.2
      simp only [kostenEnd, kostenKE, zusatzE]; omega
  | .awaits _ _ _ _ _ rest, h => by
      have h1 := spiegel_sonst c pa rest h
      simp only [kostenEnd, kostenKE, zusatzE]; omega
  | .bindCallInd .., h => by simp only [spiegelE, Bool.false_eq_true] at h
  | .narrow .., h => by simp only [spiegelE, Bool.false_eq_true] at h
  | .narrowRequired .., h => by simp only [spiegelE, Bool.false_eq_true] at h
  | .retScoped .., h => by simp only [spiegelE, Bool.false_eq_true] at h
  | .retWhyScoped .., h => by simp only [spiegelE, Bool.false_eq_true] at h
  | .exchange .., h => by simp only [spiegelE, Bool.false_eq_true] at h
  | .ite .., h => by simp only [spiegelE, Bool.false_eq_true] at h

theorem spiegel_sonst (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} :
    (e : Endblock D V l Γ Λ) → spiegelE e = true →
      kostenSonst c pa e ≤ kostenKE c e + zusatzSonst e
  | .ret .., _ => by simp only [kostenSonst, kostenKE, zusatzSonst]; omega
  | .retWhy .., _ => by simp only [kostenSonst, kostenKE, zusatzSonst]; omega
  | .leave _, _ => by simp only [kostenSonst, kostenKE, zusatzSonst]; omega
  | .next _, _ => by simp only [kostenSonst, kostenKE, zusatzSonst]; omega
  | .cons s rest, h => by
      simp only [spiegelE, Bool.and_eq_true] at h
      have h1 := spiegel_stmt c pa s h.1
      have h2 := spiegel_sonst c pa rest h.2
      simp only [kostenSonst, kostenKE, zusatzSonst]; omega
  | .bind _ rest, h => by
      have h1 := spiegel_sonst c pa rest h
      simp only [kostenSonst, kostenKE, zusatzSonst]; omega
  | .bindCall _ _ _ _ _ rest, h => by
      have h1 := spiegel_sonst c pa rest h
      simp only [kostenSonst, kostenKE, zusatzSonst]; omega
  | .bindCallElse _ _ _ _ _ err rest, h => by
      simp only [spiegelE, Bool.and_eq_true] at h
      have h1 := spiegel_sonst c pa err h.1
      have h2 := spiegel_sonst c pa rest h.2
      simp only [kostenSonst, kostenKE, zusatzSonst]; omega
  | .bindAxiom .., h => by simp only [spiegelE, Bool.false_eq_true] at h
  | .bindAxiomElse .., h => by simp only [spiegelE, Bool.false_eq_true] at h
  | .regRead _ _ rest, h => by
      have h1 := spiegel_sonst c pa rest h
      simp only [kostenSonst, kostenKE, zusatzSonst]; omega
  | .regReadElse _ _ _ sonst rest, h => by
      simp only [spiegelE, Bool.and_eq_true] at h
      have h1 := spiegel_sonst c pa sonst h.1
      have h2 := spiegel_sonst c pa rest h.2
      simp only [kostenSonst, kostenKE, zusatzSonst]; omega
  | .awaits _ _ _ _ _ rest, h => by
      have h1 := spiegel_sonst c pa rest h
      simp only [kostenSonst, kostenKE, zusatzSonst]; omega
  | .bindCallInd .., h => by simp only [spiegelE, Bool.false_eq_true] at h
  | .narrow .., h => by simp only [spiegelE, Bool.false_eq_true] at h
  | .narrowRequired .., h => by simp only [spiegelE, Bool.false_eq_true] at h
  | .retScoped .., h => by simp only [spiegelE, Bool.false_eq_true] at h
  | .retWhyScoped .., h => by simp only [spiegelE, Bool.false_eq_true] at h
  | .exchange .., h => by simp only [spiegelE, Bool.false_eq_true] at h
  | .ite .., h => by simp only [spiegelE, Bool.false_eq_true] at h
end

end Gabbro.Grammatik
