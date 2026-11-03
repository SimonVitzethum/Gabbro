module
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheStatisch.T1.Teil1Basis

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuhe
public import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}
/-! ## 4. Read carriers of bodies -/

mutual

theorem ruS_orteP (P : Programm D) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ'),
    stmtOrteP P.mitRuhe (ruS s) = stmtOrteP P s
  | _, _, _, _, .assignSlot _ _ i e _ _ => kongr₂ (· ++ ·) (ruE_orte i) (ruE_orte e)
  | _, _, _, _, .assignThru p _ _ _ i e _ _ =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte p) (ruE_orte i)) (ruE_orte e)
  | _, _, _, _, .assignThruOwn p _ _ _ i e _ _ _ _ _ _ _ =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte p) (ruE_orte i)) (ruE_orte e)
  | _, _, _, _, .assignSlotRef r _ _ _ _ e _ _ => kongr₂ (· ++ ·) (ruE_orte r) (ruE_orte e)
  | _, _, _, _, .assignGlob _ e _ _ => ruE_orte e
  | _, _, _, _, .putBytes _ _ _ _ i _ _ e _ _ => kongr₂ (· ++ ·) (ruE_orte i) (ruE_orte e)
  | _, _, _, _, .assignVar _ e => ruE_orte e
  | _, _, _, _, .shift t _ _ i _ _ _ _ _ _ => congrArg (Sum.inl t :: ·) (ruE_orte i)
  | _, _, _, _, .ite c t e =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte c) (ruB_orteP P t)) (ruB_orteP P e)
  | _, _, _, _, .onOption o p a =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte o) (ruB_orteP P p)) (ruB_orteP P a)
  | _, _, _, _, .onTag v arms => kongr₂ (· ++ ·) (ruE_orte v) (ruArms_orteP P arms)
  | _, _, _, _, .onWhy r arms => kongr₂ (· ++ ·) (ruE_orte r) (ruGArms_orteP P arms)
  | _, _, _, _, .call g args _ _ =>
      (orteP_nachΛ _ _ _).trans (kongr₂ (· ++ ·) (ruA_orte args)
        (kongr₂ (· ++ ·) (requires_mitRuhe_orte P g) (ensures_mitRuhe_orte P g)))
  | _, _, _, _, .callInd p args _ _ =>
      (orteP_nachΛ _ _ _).trans (kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args)) (ptrPre_mitRuhe_orte P _)) (ptrPost_mitRuhe_orte P _))
  | _, _, _, _, .callIndElse p args _ _ _ err =>
      (orteP_nachΛ _ _ _).trans (kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args)) (ptrPre_mitRuhe_orte P _)) (ptrPost_mitRuhe_orte P _)) ((orteP_umΛ _ _ _).trans (ruEnd_orteP P err)))
  | _, _, _, _, .locks _ _ body => ruB_orteP P body
  | _, _, _, _, .breaking _ body => ruB_orteP P body
  | _, _, _, _, .traverse _ inv body => kongr₂ (· ++ ·) (ruE_orte inv) (ruB_orteP P body)
  | _, _, _, _, .consumeTraverse _ member edge inv _ mass body =>
      kongr₂ (· ++ ·)
        (kongr₂ (· ++ ·)
          (kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte member) (ruE_orte edge)) (ruE_orte inv))
          (ruE_orte mass))
        (ruB_orteP P body)
  | _, _, _, _, .retry _ bis body ueber =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte bis) (ruB_orteP P body)) (ruB_orteP P ueber)
  | _, _, _, _, .forever _ inv body => kongr₂ (· ++ ·) (ruE_orte inv) (ruB_orteP P body)
  | _, _, _, _, .axiomCall _ args _ _ _ _ _ => ruA_orte args
  | _, _, _, _, .axiomCallElse e _ args _ _ _ _ _ err => by
      have ih0 := ruEnd_orteP P err
      cases e with
      | none =>
          simp only [ruS, stmtOrteP]
          exact (orteP_nachΛ _ _ _).trans
            (kongr₂ (· ++ ·) (ruA_orte args) ((orteP_umΛ _ _ _).trans (ih0)))
      | some _ =>
          simp only [ruS, stmtOrteP]
          exact (orteP_nachΛ _ _ _).trans
            (kongr₂ (· ++ ·) (ruA_orte args) ((orteP_umΛ _ _ _).trans (ih0)))
  | _, _, _, _, .regWrite _ _ e => ruE_orte e
  | _, _, _, _, .transition .. => rfl
  | _, _, _, _, .publish _ e _ _ _ _ => ruE_orte e
  | _, _, _, _, .advances .. => orteP_nachΛ _ _ _
  | _, _, _, _, .retires .. => orteP_nachΛ _ _ _
  | _, _, _, _, .ret e _ => ruErg_orte e
  | _, _, _, _, .retWhy .. => rfl
  | _, _, _, _, .retScoped e _ => ruErg_orte e
  | _, _, _, _, .retWhyScoped .. => rfl
  | _, _, _, _, .leave _ => rfl
  | _, _, _, _, .next _ => rfl

theorem ruB_orteP (P : Programm D) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ'),
    blockOrteP P.mitRuhe (ruB b) = blockOrteP P b
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons s rest => kongr₂ (· ++ ·) (ruS_orteP P s) (ruB_orteP P rest)
  | _, _, _, _, .bind e rest => kongr₂ (· ++ ·) (ruE_orte e) (ruB_orteP P rest)
  | _, _, _, _, .bindCall g args _ _ _ rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruA_orte args)
        (kongr₂ (· ++ ·) (requires_mitRuhe_orte P g) (ensures_mitRuhe_orte P g)))
        ((orteP_vorΛ _ _ _).trans (ruB_orteP P rest))
  | _, _, _, _, .bindCallInd p args _ _ _ rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args)) (ptrPre_mitRuhe_orte P _)) (ptrPost_mitRuhe_orte P _))
        ((orteP_vorΛ _ _ _).trans (ruB_orteP P rest))
  | _, _, _, _, .bindCallIndElse p args _ _ _ err rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args)) (ptrPre_mitRuhe_orte P _)) (ptrPost_mitRuhe_orte P _)) ((orteP_umΛ _ _ _).trans (ruEnd_orteP P err)))
        ((orteP_vorΛ _ _ _).trans (ruB_orteP P rest))
  | _, _, _, _, .bindCallElse g args _ _ _ err rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruA_orte args)
        (kongr₂ (· ++ ·) (requires_mitRuhe_orte P g) (ensures_mitRuhe_orte P g)))
        ((orteP_umΛ _ _ _).trans (ruEnd_orteP P err)))
        ((orteP_vorΛ _ _ _).trans (ruB_orteP P rest))
  | _, _, _, _, .bindAxiom _ args _ _ _ _ _ rest =>
      kongr₂ (· ++ ·) (ruA_orte args) (ruB_orteP P rest)
  | _, _, _, _, .bindAxiomElse _ args _ _ _ _ _ _ err rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruA_orte args) (ruEnd_orteP P err)) (ruB_orteP P rest)
  | _, _, _, _, .bindAxiomOpt e _ args _ _ _ _ rest => by
      have ih0 := ruB_orteP P rest
      cases e with
      | none =>
          simp only [ruB, blockOrteP]
          exact kongr₂ (· ++ ·) (ruA_orte args)
            ((orteP_vorΛ _ _ _).trans (ih0))
      | some _ =>
          simp only [ruB, blockOrteP]
          exact kongr₂ (· ++ ·) (ruA_orte args)
            ((orteP_vorΛ _ _ _).trans (ih0))
  | _, _, _, _, .bindAxiomOptElse e _ args _ _ _ _ _ err rest => by
      have ih0 := ruEnd_orteP P err
      have ih1 := ruB_orteP P rest
      cases e with
      | none =>
          simp only [ruB, blockOrteP]
          exact kongr₂ (· ++ ·)
            (kongr₂ (· ++ ·) (ruA_orte args)
              ((orteP_umΛ _ _ _).trans (ih0)))
            ((orteP_vorΛ _ _ _).trans (ih1))
      | some _ =>
          simp only [ruB, blockOrteP]
          exact kongr₂ (· ++ ·)
            (kongr₂ (· ++ ·) (ruA_orte args)
              ((orteP_umΛ _ _ _).trans (ih0)))
            ((orteP_vorΛ _ _ _).trans (ih1))
  | _, _, _, _, .regRead _ _ rest => ruB_orteP P rest
  | _, _, _, _, .regReadElse _ _ zusage sonst rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte zusage) (ruEnd_orteP P sonst))
        (ruB_orteP P rest)
  | _, _, _, _, .awaits g _ _ _ _ rest => congrArg (Sum.inr g :: ·) (ruB_orteP P rest)
  | _, _, _, _, .exchange g neu _ _ rest =>
      kongr₂ (fun x y => (Sum.inr g :: x) ++ y) (ruE_orte neu) (ruB_orteP P rest)
  | _, _, _, _, .narrow e _ _ sonst rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte e) (ruEnd_orteP P sonst)) (ruB_orteP P rest)
  | _, _, _, _, .narrowRequired e _ _ rest =>
      kongr₂ (· ++ ·) (ruE_orte e) (ruB_orteP P rest)
  | _, _, _, _, .check c sonst rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte c) (ruEnd_orteP P sonst)) (ruB_orteP P rest)
  | _, _, _, _, .float _ a b _ _ rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)) (ruB_orteP P rest)
  | _, _, _, _, .floatLit _ _ _ rest => ruB_orteP P rest
  | _, _, _, _, .floatOf e _ _ rest => kongr₂ (· ++ ·) (ruE_orte e) (ruB_orteP P rest)
  | _, _, _, _, .floatNarrow e _ _ sonst rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte e) (ruEnd_orteP P sonst)) (ruB_orteP P rest)

theorem ruEnd_orteP (P : Programm D) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (e : Endblock D V l Γ Λ),
    endblockOrteP P.mitRuhe (ruEnd e) = endblockOrteP P e
  | _, _, _, .ret e _ => ruErg_orte e
  | _, _, _, .retWhy .. => rfl
  | _, _, _, .retScoped e _ => ruErg_orte e
  | _, _, _, .retWhyScoped .. => rfl
  | _, _, _, .leave _ => rfl
  | _, _, _, .next _ => rfl
  | _, _, _, .cons s rest => kongr₂ (· ++ ·) (ruS_orteP P s) (ruEnd_orteP P rest)
  | _, _, _, .bind e rest => kongr₂ (· ++ ·) (ruE_orte e) (ruEnd_orteP P rest)
  | _, _, _, .bindCall g args _ _ _ rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruA_orte args)
        (kongr₂ (· ++ ·) (requires_mitRuhe_orte P g) (ensures_mitRuhe_orte P g)))
        ((orteP_umΛ _ _ _).trans (ruEnd_orteP P rest))
  | _, _, _, .bindCallElse g args _ _ _ err rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruA_orte args)
        (kongr₂ (· ++ ·) (requires_mitRuhe_orte P g) (ensures_mitRuhe_orte P g)))
        ((orteP_umΛ _ _ _).trans (ruEnd_orteP P err)))
        ((orteP_umΛ _ _ _).trans (ruEnd_orteP P rest))
  | _, _, _, .bindAxiom _ args _ _ _ _ _ rest =>
      kongr₂ (· ++ ·) (ruA_orte args) (ruEnd_orteP P rest)
  | _, _, _, .bindAxiomElse _ args _ _ _ _ _ _ err rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruA_orte args) (ruEnd_orteP P err)) (ruEnd_orteP P rest)
  | _, _, _, .bindAxiomOpt e _ args _ _ _ _ rest => by
      have ih0 := ruEnd_orteP P rest
      cases e with
      | none =>
          simp only [ruEnd, endblockOrteP]
          exact kongr₂ (· ++ ·) (ruA_orte args)
            ((orteP_umΛ _ _ _).trans (ih0))
      | some _ =>
          simp only [ruEnd, endblockOrteP]
          exact kongr₂ (· ++ ·) (ruA_orte args)
            ((orteP_umΛ _ _ _).trans (ih0))
  | _, _, _, .bindAxiomOptElse e _ args _ _ _ _ _ err rest => by
      have ih0 := ruEnd_orteP P err
      have ih1 := ruEnd_orteP P rest
      cases e with
      | none =>
          simp only [ruEnd, endblockOrteP]
          exact kongr₂ (· ++ ·)
            (kongr₂ (· ++ ·) (ruA_orte args)
              ((orteP_umΛ _ _ _).trans (ih0)))
            ((orteP_umΛ _ _ _).trans (ih1))
      | some _ =>
          simp only [ruEnd, endblockOrteP]
          exact kongr₂ (· ++ ·)
            (kongr₂ (· ++ ·) (ruA_orte args)
              ((orteP_umΛ _ _ _).trans (ih0)))
            ((orteP_umΛ _ _ _).trans (ih1))
  | _, _, _, .regRead _ _ rest => ruEnd_orteP P rest
  | _, _, _, .regReadElse _ _ zusage sonst rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte zusage) (ruEnd_orteP P sonst))
        (ruEnd_orteP P rest)
  | _, _, _, .awaits g _ _ _ _ rest => congrArg (Sum.inr g :: ·) (ruEnd_orteP P rest)
  | _, _, _, .bindCallInd p args _ _ _ rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args)) (ptrPre_mitRuhe_orte P _)) (ptrPost_mitRuhe_orte P _))
        ((orteP_umΛ _ _ _).trans (ruEnd_orteP P rest))
  | _, _, _, .bindCallIndElse p args _ _ _ err rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args)) (ptrPre_mitRuhe_orte P _)) (ptrPost_mitRuhe_orte P _)) ((orteP_umΛ _ _ _).trans (ruEnd_orteP P err)))
        ((orteP_umΛ _ _ _).trans (ruEnd_orteP P rest))
  | _, _, _, .narrow e _ _ sonst rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte e) (ruEnd_orteP P sonst)) (ruEnd_orteP P rest)
  | _, _, _, .narrowRequired e _ _ rest =>
      kongr₂ (· ++ ·) (ruE_orte e) (ruEnd_orteP P rest)
  | _, _, _, .exchange g neu _ _ rest =>
      kongr₂ (fun x y => (Sum.inr g :: x) ++ y) (ruE_orte neu) (ruEnd_orteP P rest)
  | _, _, _, .ite c t e =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte c) (ruEnd_orteP P e)) (ruEnd_orteP P t)

theorem ruArms_orteP (P : Programm D) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs),
    armsOrteP P.mitRuhe (ruArms arms) = armsOrteP P arms
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons (c := none) b rest =>
      kongr₂ (· ++ ·) (ruB_orteP P b) (ruArms_orteP P rest)
  | _, _, _, _, _, .cons (c := some _) b rest =>
      kongr₂ (· ++ ·) (ruB_orteP P b) (ruArms_orteP P rest)

theorem ruGArms_orteP (P : Programm D) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n),
    grundArmsOrteP P.mitRuhe (ruGArms arms) = grundArmsOrteP P arms
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons b rest => kongr₂ (· ++ ·) (ruB_orteP P b) (ruGArms_orteP P rest)

end
/-! ## 5. Register reads -/

mutual

theorem ruS_regs {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ'), (ruS s).regs = s.regs
  | _, _, _, _, .assignSlot .. => rfl
  | _, _, _, _, .assignThru .. | _, _, _, _, .assignThruOwn .. | _, _, _, _, .assignSlotRef .. => rfl
  | _, _, _, _, .assignGlob .. => rfl
  | _, _, _, _, .putBytes .. => rfl
  | _, _, _, _, .assignVar .. => rfl
  | _, _, _, _, .shift .. => rfl
  | _, _, _, _, .ite _ t e => kongr₂ (· ++ ·) (ruB_regs t) (ruB_regs e)
  | _, _, _, _, .onOption _ p a => kongr₂ (· ++ ·) (ruB_regs p) (ruB_regs a)
  | _, _, _, _, .onTag _ arms => ruArms_regs arms
  | _, _, _, _, .onWhy _ arms => ruGArms_regs arms
  | _, _, _, _, .call .. => regs_nachΛ _ _
  | _, _, _, _, .callInd .. => regs_nachΛ _ _
  | _, _, _, _, .callIndElse _ _ _ _ _ err =>
      (regs_nachΛ _ _).trans ((regs_umΛ _ _).trans (ruEnd_regs err))
  | _, _, _, _, .locks _ _ body => ruB_regs body
  | _, _, _, _, .breaking _ body => ruB_regs body
  | _, _, _, _, .traverse _ _ body => ruB_regs body
  | _, _, _, _, .consumeTraverse _ _ _ _ _ _ body => ruB_regs body
  | _, _, _, _, .retry _ _ body ueber => kongr₂ (· ++ ·) (ruB_regs body) (ruB_regs ueber)
  | _, _, _, _, .forever _ _ body => ruB_regs body
  | _, _, _, _, .axiomCall .. => rfl
  | _, _, _, _, .axiomCallElse e _ _ _ _ _ _ _ err => by
      have ih := ruEnd_regs err
      cases e <;> exact (regs_nachΛ _ _).trans ((regs_umΛ _ _).trans ih)
  | _, _, _, _, .regWrite .. => rfl
  | _, _, _, _, .transition .. => rfl
  | _, _, _, _, .publish .. => rfl
  | _, _, _, _, .advances .. => regs_nachΛ _ _
  | _, _, _, _, .retires .. => regs_nachΛ _ _
  | _, _, _, _, .ret .. => rfl
  | _, _, _, _, .retWhy .. => rfl
  | _, _, _, _, .retScoped .. => rfl
  | _, _, _, _, .retWhyScoped .. => rfl
  | _, _, _, _, .leave _ => rfl
  | _, _, _, _, .next _ => rfl

theorem ruB_regs {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ'), (ruB b).regs = b.regs
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons s rest => kongr₂ (· ++ ·) (ruS_regs s) (ruB_regs rest)
  | _, _, _, _, .bind _ rest => ruB_regs rest
  | _, _, _, _, .bindCall _ _ _ _ _ rest => (regs_vorΛ _ _).trans (ruB_regs rest)
  | _, _, _, _, .bindCallInd _ _ _ _ _ rest => (regs_vorΛ _ _).trans (ruB_regs rest)
  | _, _, _, _, .bindCallIndElse _ _ _ _ _ err rest =>
      kongr₂ (· ++ ·) ((regs_umΛ _ _).trans (ruEnd_regs err))
        ((regs_vorΛ _ _).trans (ruB_regs rest))
  | _, _, _, _, .bindCallElse _ _ _ _ _ err rest =>
      kongr₂ (· ++ ·) ((regs_umΛ _ _).trans (ruEnd_regs err))
        ((regs_vorΛ _ _).trans (ruB_regs rest))
  | _, _, _, _, .bindAxiom _ _ _ _ _ _ _ rest => ruB_regs rest
  | _, _, _, _, .bindAxiomOpt e _ _ _ _ _ _ rest => by
      have ih := ruB_regs rest
      cases e <;> exact (regs_vorΛ _ _).trans ih
  | _, _, _, _, .bindAxiomOptElse e _ _ _ _ _ _ _ err rest => by
      have ih0 := ruEnd_regs err
      have ih1 := ruB_regs rest
      cases e <;> exact kongr₂ (· ++ ·) ((regs_umΛ _ _).trans ih0)
        ((regs_vorΛ _ _).trans ih1)
  | _, _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest => kongr₂ (· ++ ·) (ruEnd_regs err) (ruB_regs rest)
  | _, _, _, _, .regRead r _ rest => congrArg (r :: ·) (ruB_regs rest)
  | _, _, _, _, .regReadElse r _ _ sonst rest =>
      congrArg (r :: ·) (kongr₂ (· ++ ·) (ruEnd_regs sonst) (ruB_regs rest))
  | _, _, _, _, .awaits _ _ _ _ _ rest => ruB_regs rest
  | _, _, _, _, .exchange _ _ _ _ rest => ruB_regs rest
  | _, _, _, _, .narrow _ _ _ sonst rest => kongr₂ (· ++ ·) (ruEnd_regs sonst) (ruB_regs rest)
  | _, _, _, _, .narrowRequired _ _ _ rest => ruB_regs rest
  | _, _, _, _, .check _ sonst rest => kongr₂ (· ++ ·) (ruEnd_regs sonst) (ruB_regs rest)
  | _, _, _, _, .float _ _ _ _ _ rest => ruB_regs rest
  | _, _, _, _, .floatLit _ _ _ rest => ruB_regs rest
  | _, _, _, _, .floatOf _ _ _ rest => ruB_regs rest
  | _, _, _, _, .floatNarrow _ _ _ sonst rest =>
      kongr₂ (· ++ ·) (ruEnd_regs sonst) (ruB_regs rest)

theorem ruEnd_regs {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ), (ruEnd e).regs = e.regs
  | _, _, _, .ret .. => rfl
  | _, _, _, .retWhy .. => rfl
  | _, _, _, .retScoped .. => rfl
  | _, _, _, .retWhyScoped .. => rfl
  | _, _, _, .leave _ => rfl
  | _, _, _, .next _ => rfl
  | _, _, _, .cons s rest => kongr₂ (· ++ ·) (ruS_regs s) (ruEnd_regs rest)
  | _, _, _, .bind _ rest => ruEnd_regs rest
  | _, _, _, .bindCall _ _ _ _ _ rest => (regs_umΛ _ _).trans (ruEnd_regs rest)
  | _, _, _, .bindCallIndElse _ _ _ _ _ err rest =>
      kongr₂ (· ++ ·) ((regs_umΛ _ _).trans (ruEnd_regs err))
        ((regs_umΛ _ _).trans (ruEnd_regs rest))
  | _, _, _, .bindCallElse _ _ _ _ _ err rest =>
      kongr₂ (· ++ ·) ((regs_umΛ _ _).trans (ruEnd_regs err))
        ((regs_umΛ _ _).trans (ruEnd_regs rest))
  | _, _, _, .bindAxiom _ _ _ _ _ _ _ rest => ruEnd_regs rest
  | _, _, _, .bindAxiomOpt e _ _ _ _ _ _ rest => by
      have ih := ruEnd_regs rest
      cases e <;> exact (regs_umΛ _ _).trans ih
  | _, _, _, .bindAxiomOptElse e _ _ _ _ _ _ _ err rest => by
      have ih0 := ruEnd_regs err
      have ih1 := ruEnd_regs rest
      cases e <;> exact kongr₂ (· ++ ·) ((regs_umΛ _ _).trans ih0)
        ((regs_umΛ _ _).trans ih1)
  | _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest => kongr₂ (· ++ ·) (ruEnd_regs err) (ruEnd_regs rest)
  | _, _, _, .regRead r _ rest => congrArg (r :: ·) (ruEnd_regs rest)
  | _, _, _, .regReadElse r _ _ sonst rest =>
      congrArg (r :: ·) (kongr₂ (· ++ ·) (ruEnd_regs sonst) (ruEnd_regs rest))
  | _, _, _, .awaits _ _ _ _ _ rest => ruEnd_regs rest
  | _, _, _, .bindCallInd _ _ _ _ _ rest => (regs_umΛ _ _).trans (ruEnd_regs rest)
  | _, _, _, .narrow _ _ _ sonst rest => kongr₂ (· ++ ·) (ruEnd_regs sonst) (ruEnd_regs rest)
  | _, _, _, .narrowRequired _ _ _ rest => ruEnd_regs rest
  | _, _, _, .exchange _ _ _ _ rest => ruEnd_regs rest
  | _, _, _, .ite _ t e => kongr₂ (· ++ ·) (ruEnd_regs e) (ruEnd_regs t)

theorem ruArms_regs {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs),
    (ruArms arms).regs = arms.regs
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons (c := none) b rest => kongr₂ (· ++ ·) (ruB_regs b) (ruArms_regs rest)
  | _, _, _, _, _, .cons (c := some _) b rest =>
      kongr₂ (· ++ ·) (ruB_regs b) (ruArms_regs rest)

theorem ruGArms_regs {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n), (ruGArms arms).regs = arms.regs
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons b rest => kongr₂ (· ++ ·) (ruB_regs b) (ruGArms_regs rest)

end
/-! ## 6. The fragment test -/

/-- The fragment admissibility, shifted back: signature `n` of `D` is
    signature `n + 1` of `D.mitRuhe`. -/
def kZ (K : Nat → Bool) : Nat → Bool := fun n => K (n + 1)

end Gabbro.Grammatik
