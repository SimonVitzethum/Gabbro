/-
  File:      Grammatik/MitRuheStatisch.lean
  Subject:   STATIC TRANSFER to `P.mitRuhe` (MitRuhe.lean): every fold the
             checker computes over a body -- read carriers, register
             reads, the fragment test, the feature test `mE` -- gives on the
             translated body what it gave on the body.
-/
import Grammatik.MitRuhe
import Grammatik.Verklemmung

namespace Gabbro.Grammatik

variable {D : Deklaration}

theorem kongr₂ {α β γ : Sort _} (f : α → β → γ) {a a' : α} {b b' : β} (ha : a = a')
    (hb : b = b') : f a b = f a' b' := by
  subst ha; subst hb; rfl

/-! ## 1. Read carriers of expressions -/

mutual

theorem renE_orte : ∀ {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ),
    (renE e).orte = e.orte
  | _, _, _, .lit _ => rfl
  | _, _, _, .wahr => rfl
  | _, _, _, .falsch => rfl
  | _, _, _, .var _ => rfl
  | _, _, _, .glob _ _ => rfl
  | _, _, _, .slot t f i hL => congrArg (Sum.inl t :: ·) (renE_orte i)
  | _, _, _, .durch p t ht f i hL => kongr₂ (fun x y => x ++ Sum.inl t :: y) (renE_orte p) (renE_orte i)
  | _, _, _, .ptrOf .. => rfl
  | _, _, _, .fnref .. => rfl
  | _, _, _, .altGlob _ _ => rfl
  | _, _, _, .altSlot t f i hL => congrArg (Sum.inl t :: ·) (renE_orte i)
  | _, _, _, .weiter _ _ e => renE_orte e
  | _, _, _, .add a b => kongr₂ (· ++ ·) (renE_orte a) (renE_orte b)
  | _, _, _, .sub a b => kongr₂ (· ++ ·) (renE_orte a) (renE_orte b)
  | _, _, _, .neg a => renE_orte a
  | _, _, _, .mul a b => kongr₂ (· ++ ·) (renE_orte a) (renE_orte b)
  | _, _, _, .div _ _ a b => kongr₂ (· ++ ·) (renE_orte a) (renE_orte b)
  | _, _, _, .rem _ _ a b => kongr₂ (· ++ ·) (renE_orte a) (renE_orte b)
  | _, _, _, .sdiv _ a b => kongr₂ (· ++ ·) (renE_orte a) (renE_orte b)
  | _, _, _, .srem _ a b => kongr₂ (· ++ ·) (renE_orte a) (renE_orte b)
  | _, _, _, .leseBytes t _ _ _ i _ _ _ => congrArg (Sum.inl t :: ·) (renE_orte i)
  | _, _, _, .band _ _ a b => kongr₂ (· ++ ·) (renE_orte a) (renE_orte b)
  | _, _, _, .bor _ _ _ _ _ a b => kongr₂ (· ++ ·) (renE_orte a) (renE_orte b)
  | _, _, _, .bxor _ _ _ _ _ a b => kongr₂ (· ++ ·) (renE_orte a) (renE_orte b)
  | _, _, _, .shl _ _ _ _ _ a b => kongr₂ (· ++ ·) (renE_orte a) (renE_orte b)
  | _, _, _, .shr _ _ _ _ _ a b => kongr₂ (· ++ ·) (renE_orte a) (renE_orte b)
  | _, _, _, .lt a b => kongr₂ (· ++ ·) (renE_orte a) (renE_orte b)
  | _, _, _, .le a b => kongr₂ (· ++ ·) (renE_orte a) (renE_orte b)
  | _, _, _, .eq a b => kongr₂ (· ++ ·) (renE_orte a) (renE_orte b)
  | _, _, _, .fllt a b => kongr₂ (· ++ ·) (renE_orte a) (renE_orte b)
  | _, _, _, .flle a b => kongr₂ (· ++ ·) (renE_orte a) (renE_orte b)
  | _, _, _, .und a b => kongr₂ (· ++ ·) (renE_orte a) (renE_orte b)
  | _, _, _, .oder a b => kongr₂ (· ++ ·) (renE_orte a) (renE_orte b)
  | _, _, _, .nicht a => renE_orte a
  | _, _, _, .none _ => rfl
  | _, _, _, .some a => renE_orte a
  | _, _, _, .istSome a => renE_orte a
  | _, _, _, .fall _ _ nutz => renN_orte nutz
  | _, _, _, .grund _ _ => rfl
  | _, _, _, .forallSlots t body _ => congrArg (Sum.inl t :: ·) (renE_orte body)
  | _, _, _, .existsSlots t body _ => congrArg (Sum.inl t :: ·) (renE_orte body)
  | _, _, _, .reaches t _ _ a b _ => kongr₂ (fun x y => Sum.inl t :: x ++ y) (renE_orte a) (renE_orte b)

theorem renN_orte : ∀ {Γ : Ctx} {Λ : List (Res D)} {c : Option (Int × Int)}
    (n : NutzlastExpr D Γ Λ c), (renN n).orte = n.orte
  | _, _, _, .keine => rfl
  | _, _, _, .zahl e => renE_orte e

end

theorem renA_orte : ∀ {Γ : Ctx} {Λ : List (Res D)} {τs : List Ty} (a : Args D Γ Λ τs),
    (renA a).orte = a.orte
  | _, _, _, .nil => rfl
  | _, _, _, .cons e rest => kongr₂ (· ++ ·) (renE_orte e) (renA_orte rest)

theorem renErg_orte : ∀ {Γ : Ctx} {Λ : List (Res D)} {e : Option Ty} (a : ErgExpr D Γ Λ e),
    (renErg a).orte = a.orte
  | _, _, _, .keine => rfl
  | _, _, _, .wert e => renE_orte e

theorem umΛ_orte {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} (h : Λ = Λ') (e : Expr D Γ Λ τ) :
    (Expr.umΛ h e).orte = e.orte := by
  subst h; rfl

theorem umΓ_orte {Γ Γ' : Ctx} {Λ : List (Res D)} {τ : Ty} (h : Γ = Γ') (e : Expr D Γ Λ τ) :
    (Expr.umΓ h e).orte = e.orte := by
  subst h; rfl

/-! ## 2. The contracts of `P.mitRuhe` -/

theorem requires_mitRuhe_orte (P : Programm D) (f : D.Fn) :
    (P.mitRuhe.requires (some f)).orte = (P.requires f).orte :=
  (umΛ_orte _ _).trans (renE_orte _)

theorem ensures_mitRuhe_orte (P : Programm D) (f : D.Fn) :
    (P.mitRuhe.ensures (some f)).orte = (P.ensures f).orte :=
  ((umΓ_orte _ _).trans (umΛ_orte _ _)).trans (renE_orte _)

theorem invariante_mitRuhe_orte (P : Programm D) (i : D.Inv) :
    (P.mitRuhe.invariante i).orte = (P.invariante i).orte :=
  (umΛ_orte _ _).trans (renE_orte _)

/-! ## 3. Transports -/

section Um

variable {V : Vertrag D} {l : Bool} {Γ : Ctx}

theorem orteP_nachΛ (P : Programm D) {Λ Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂)
    (s : Stmt D V l Γ Λ Λ₁) : stmtOrteP P (Stmt.nachΛ h s) = stmtOrteP P s := by subst h; rfl
theorem orteP_vorΛ (P : Programm D) {Λ₁ Λ₂ Λ' : List (Res D)} (h : Λ₁ = Λ₂)
    (b : Block D V l Γ Λ₁ Λ') : blockOrteP P (Block.vorΛ h b) = blockOrteP P b := by subst h; rfl
theorem orteP_umΛ (P : Programm D) {Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂)
    (e : Endblock D V l Γ Λ₁) : endblockOrteP P (Endblock.umΛ h e) = endblockOrteP P e := by
  subst h; rfl
theorem regs_nachΛ {Λ Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂) (s : Stmt D V l Γ Λ Λ₁) :
    (Stmt.nachΛ h s).regs = s.regs := by subst h; rfl
theorem regs_vorΛ {Λ₁ Λ₂ Λ' : List (Res D)} (h : Λ₁ = Λ₂) (b : Block D V l Γ Λ₁ Λ') :
    (Block.vorΛ h b).regs = b.regs := by subst h; rfl
theorem regs_umΛ {Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂) (e : Endblock D V l Γ Λ₁) :
    (Endblock.umΛ h e).regs = e.regs := by subst h; rfl
theorem gOk_nachΛ (K : Nat → Bool) (Rg : D.Reg → Bool) {Λ Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂)
    (s : Stmt D V l Γ Λ Λ₁) : (Stmt.nachΛ h s).gOk K Rg = s.gOk K Rg := by subst h; rfl
theorem gOk_vorΛ (K : Nat → Bool) (Rg : D.Reg → Bool) {Λ₁ Λ₂ Λ' : List (Res D)} (h : Λ₁ = Λ₂)
    (b : Block D V l Γ Λ₁ Λ') : (Block.vorΛ h b).gOk K Rg = b.gOk K Rg := by subst h; rfl
theorem gOk_umΛ (K : Nat → Bool) (Rg : D.Reg → Bool) {Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂)
    (e : Endblock D V l Γ Λ₁) : (Endblock.umΛ h e).gOk K Rg = e.gOk K Rg := by subst h; rfl
theorem mS_nachΛ (A : Merkmal D) {Λ Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂)
    (s : Stmt D V l Γ Λ Λ₁) : mS A (Stmt.nachΛ h s) = mS A s := by subst h; rfl
theorem mB_vorΛ (A : Merkmal D) {Λ₁ Λ₂ Λ' : List (Res D)} (h : Λ₁ = Λ₂)
    (b : Block D V l Γ Λ₁ Λ') : mB A (Block.vorΛ h b) = mB A b := by subst h; rfl
theorem mE_umΛ (A : Merkmal D) {Λ₁ Λ₂ : List (Res D)} (h : Λ₁ = Λ₂)
    (e : Endblock D V l Γ Λ₁) : mE A (Endblock.umΛ h e) = mE A e := by subst h; rfl

end Um

/-! ## 4. Read carriers of bodies -/

mutual

theorem renS_orteP (P : Programm D) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ'),
    stmtOrteP P.mitRuhe (renS s) = stmtOrteP P s
  | _, _, _, _, .assignSlot _ _ i e _ _ => kongr₂ (· ++ ·) (renE_orte i) (renE_orte e)
  | _, _, _, _, .assignDurch p _ _ _ i e _ _ =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (renE_orte p) (renE_orte i)) (renE_orte e)
  | _, _, _, _, .assignGlob _ e _ _ => renE_orte e
  | _, _, _, _, .schreibBytes _ _ _ _ i _ _ e _ _ => kongr₂ (· ++ ·) (renE_orte i) (renE_orte e)
  | _, _, _, _, .assignVar _ e => renE_orte e
  | _, _, _, _, .uebergang t _ _ i _ _ _ _ _ _ => congrArg (Sum.inl t :: ·) (renE_orte i)
  | _, _, _, _, .ite c t e =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (renE_orte c) (renB_orteP P t)) (renB_orteP P e)
  | _, _, _, _, .onOption o p a =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (renE_orte o) (renB_orteP P p)) (renB_orteP P a)
  | _, _, _, _, .onTag v arms => kongr₂ (· ++ ·) (renE_orte v) (renArms_orteP P arms)
  | _, _, _, _, .onGrund r arms => kongr₂ (· ++ ·) (renE_orte r) (renGArms_orteP P arms)
  | _, _, _, _, .call g args _ _ =>
      (orteP_nachΛ _ _ _).trans (kongr₂ (· ++ ·) (renA_orte args)
        (kongr₂ (· ++ ·) (requires_mitRuhe_orte P g) (ensures_mitRuhe_orte P g)))
  | _, _, _, _, .callInd p args _ _ =>
      (orteP_nachΛ _ _ _).trans (kongr₂ (· ++ ·) (renE_orte p) (renA_orte args))
  | _, _, _, _, .locks _ _ body => renB_orteP P body
  | _, _, _, _, .breaking _ body => renB_orteP P body
  | _, _, _, _, .traverse _ inv body => kongr₂ (· ++ ·) (renE_orte inv) (renB_orteP P body)
  | _, _, _, _, .retry _ bis body ueber =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (renE_orte bis) (renB_orteP P body)) (renB_orteP P ueber)
  | _, _, _, _, .forever _ inv body => kongr₂ (· ++ ·) (renE_orte inv) (renB_orteP P body)
  | _, _, _, _, .axiomCall _ args _ _ _ _ _ => renA_orte args
  | _, _, _, _, .regSchreib _ _ e => renE_orte e
  | _, _, _, _, .transition .. => rfl
  | _, _, _, _, .publish _ e _ _ _ _ => renE_orte e
  | _, _, _, _, .advances .. => orteP_nachΛ _ _ _
  | _, _, _, _, .retires .. => orteP_nachΛ _ _ _
  | _, _, _, _, .ret e _ => renErg_orte e
  | _, _, _, _, .retGrund .. => rfl
  | _, _, _, _, .leave _ => rfl
  | _, _, _, _, .next _ => rfl

theorem renB_orteP (P : Programm D) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ'),
    blockOrteP P.mitRuhe (renB b) = blockOrteP P b
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons s rest => kongr₂ (· ++ ·) (renS_orteP P s) (renB_orteP P rest)
  | _, _, _, _, .bind e rest => kongr₂ (· ++ ·) (renE_orte e) (renB_orteP P rest)
  | _, _, _, _, .bindCall g args _ _ _ rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (renA_orte args)
        (kongr₂ (· ++ ·) (requires_mitRuhe_orte P g) (ensures_mitRuhe_orte P g)))
        ((orteP_vorΛ _ _ _).trans (renB_orteP P rest))
  | _, _, _, _, .bindCallInd p args _ _ _ rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (renE_orte p) (renA_orte args))
        ((orteP_vorΛ _ _ _).trans (renB_orteP P rest))
  | _, _, _, _, .bindCallElse g args _ _ _ err rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (renA_orte args)
        (kongr₂ (· ++ ·) (requires_mitRuhe_orte P g) (ensures_mitRuhe_orte P g)))
        ((orteP_umΛ _ _ _).trans (renEnd_orteP P err)))
        ((orteP_vorΛ _ _ _).trans (renB_orteP P rest))
  | _, _, _, _, .bindAxiom _ args _ _ _ _ _ rest =>
      kongr₂ (· ++ ·) (renA_orte args) (renB_orteP P rest)
  | _, _, _, _, .regLies _ _ rest => renB_orteP P rest
  | _, _, _, _, .regLiesElse _ _ zusage sonst rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (renE_orte zusage) (renEnd_orteP P sonst))
        (renB_orteP P rest)
  | _, _, _, _, .awaits g _ _ _ rest => congrArg (Sum.inr g :: ·) (renB_orteP P rest)
  | _, _, _, _, .exchange g neu _ _ rest =>
      kongr₂ (fun x y => (Sum.inr g :: x) ++ y) (renE_orte neu) (renB_orteP P rest)
  | _, _, _, _, .narrow e _ _ sonst rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (renE_orte e) (renEnd_orteP P sonst)) (renB_orteP P rest)
  | _, _, _, _, .pruefung c sonst rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (renE_orte c) (renEnd_orteP P sonst)) (renB_orteP P rest)
  | _, _, _, _, .gleit _ a b _ _ rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (renE_orte a) (renE_orte b)) (renB_orteP P rest)
  | _, _, _, _, .gleitLit _ _ _ rest => renB_orteP P rest
  | _, _, _, _, .gleitVon e _ _ rest => kongr₂ (· ++ ·) (renE_orte e) (renB_orteP P rest)
  | _, _, _, _, .gleitNarrow e _ _ sonst rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (renE_orte e) (renEnd_orteP P sonst)) (renB_orteP P rest)

theorem renEnd_orteP (P : Programm D) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (e : Endblock D V l Γ Λ),
    endblockOrteP P.mitRuhe (renEnd e) = endblockOrteP P e
  | _, _, _, .ret e _ => renErg_orte e
  | _, _, _, .retGrund .. => rfl
  | _, _, _, .leave _ => rfl
  | _, _, _, .next _ => rfl
  | _, _, _, .cons s rest => kongr₂ (· ++ ·) (renS_orteP P s) (renEnd_orteP P rest)
  | _, _, _, .bind e rest => kongr₂ (· ++ ·) (renE_orte e) (renEnd_orteP P rest)

theorem renArms_orteP (P : Programm D) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs),
    armsOrteP P.mitRuhe (renArms arms) = armsOrteP P arms
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons (c := none) b rest =>
      kongr₂ (· ++ ·) (renB_orteP P b) (renArms_orteP P rest)
  | _, _, _, _, _, .cons (c := some (_, _)) b rest =>
      kongr₂ (· ++ ·) (renB_orteP P b) (renArms_orteP P rest)

theorem renGArms_orteP (P : Programm D) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n),
    grundArmsOrteP P.mitRuhe (renGArms arms) = grundArmsOrteP P arms
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons b rest => kongr₂ (· ++ ·) (renB_orteP P b) (renGArms_orteP P rest)

end

/-! ## 5. Register reads -/

mutual

theorem renS_regs {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ'), (renS s).regs = s.regs
  | _, _, _, _, .assignSlot .. => rfl
  | _, _, _, _, .assignDurch .. => rfl
  | _, _, _, _, .assignGlob .. => rfl
  | _, _, _, _, .schreibBytes .. => rfl
  | _, _, _, _, .assignVar .. => rfl
  | _, _, _, _, .uebergang .. => rfl
  | _, _, _, _, .ite _ t e => kongr₂ (· ++ ·) (renB_regs t) (renB_regs e)
  | _, _, _, _, .onOption _ p a => kongr₂ (· ++ ·) (renB_regs p) (renB_regs a)
  | _, _, _, _, .onTag _ arms => renArms_regs arms
  | _, _, _, _, .onGrund _ arms => renGArms_regs arms
  | _, _, _, _, .call .. => regs_nachΛ _ _
  | _, _, _, _, .callInd .. => regs_nachΛ _ _
  | _, _, _, _, .locks _ _ body => renB_regs body
  | _, _, _, _, .breaking _ body => renB_regs body
  | _, _, _, _, .traverse _ _ body => renB_regs body
  | _, _, _, _, .retry _ _ body ueber => kongr₂ (· ++ ·) (renB_regs body) (renB_regs ueber)
  | _, _, _, _, .forever _ _ body => renB_regs body
  | _, _, _, _, .axiomCall .. => rfl
  | _, _, _, _, .regSchreib .. => rfl
  | _, _, _, _, .transition .. => rfl
  | _, _, _, _, .publish .. => rfl
  | _, _, _, _, .advances .. => regs_nachΛ _ _
  | _, _, _, _, .retires .. => regs_nachΛ _ _
  | _, _, _, _, .ret .. => rfl
  | _, _, _, _, .retGrund .. => rfl
  | _, _, _, _, .leave _ => rfl
  | _, _, _, _, .next _ => rfl

theorem renB_regs {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ'), (renB b).regs = b.regs
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons s rest => kongr₂ (· ++ ·) (renS_regs s) (renB_regs rest)
  | _, _, _, _, .bind _ rest => renB_regs rest
  | _, _, _, _, .bindCall _ _ _ _ _ rest => (regs_vorΛ _ _).trans (renB_regs rest)
  | _, _, _, _, .bindCallInd _ _ _ _ _ rest => (regs_vorΛ _ _).trans (renB_regs rest)
  | _, _, _, _, .bindCallElse _ _ _ _ _ err rest =>
      kongr₂ (· ++ ·) ((regs_umΛ _ _).trans (renEnd_regs err))
        ((regs_vorΛ _ _).trans (renB_regs rest))
  | _, _, _, _, .bindAxiom _ _ _ _ _ _ _ rest => renB_regs rest
  | _, _, _, _, .regLies r _ rest => congrArg (r :: ·) (renB_regs rest)
  | _, _, _, _, .regLiesElse r _ _ sonst rest =>
      congrArg (r :: ·) (kongr₂ (· ++ ·) (renEnd_regs sonst) (renB_regs rest))
  | _, _, _, _, .awaits _ _ _ _ rest => renB_regs rest
  | _, _, _, _, .exchange _ _ _ _ rest => renB_regs rest
  | _, _, _, _, .narrow _ _ _ sonst rest => kongr₂ (· ++ ·) (renEnd_regs sonst) (renB_regs rest)
  | _, _, _, _, .pruefung _ sonst rest => kongr₂ (· ++ ·) (renEnd_regs sonst) (renB_regs rest)
  | _, _, _, _, .gleit _ _ _ _ _ rest => renB_regs rest
  | _, _, _, _, .gleitLit _ _ _ rest => renB_regs rest
  | _, _, _, _, .gleitVon _ _ _ rest => renB_regs rest
  | _, _, _, _, .gleitNarrow _ _ _ sonst rest =>
      kongr₂ (· ++ ·) (renEnd_regs sonst) (renB_regs rest)

theorem renEnd_regs {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ), (renEnd e).regs = e.regs
  | _, _, _, .ret .. => rfl
  | _, _, _, .retGrund .. => rfl
  | _, _, _, .leave _ => rfl
  | _, _, _, .next _ => rfl
  | _, _, _, .cons s rest => kongr₂ (· ++ ·) (renS_regs s) (renEnd_regs rest)
  | _, _, _, .bind _ rest => renEnd_regs rest

theorem renArms_regs {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs),
    (renArms arms).regs = arms.regs
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons (c := none) b rest => kongr₂ (· ++ ·) (renB_regs b) (renArms_regs rest)
  | _, _, _, _, _, .cons (c := some (_, _)) b rest =>
      kongr₂ (· ++ ·) (renB_regs b) (renArms_regs rest)

theorem renGArms_regs {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D V l Γ Λ Λ' n), (renGArms arms).regs = arms.regs
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons b rest => kongr₂ (· ++ ·) (renB_regs b) (renGArms_regs rest)

end

/-! ## 6. The fragment test -/

/-- The fragment admissibility, shifted back: signature `n` of `D` is
    signature `n + 1` of `D.mitRuhe`. -/
def kZ (K : Nat → Bool) : Nat → Bool := fun n => K (n + 1)

mutual

theorem renS_gOk (K : Nat → Bool) (Rg : D.Reg → Bool) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ'), Stmt.gOk (D := D.mitRuhe) K Rg (renS s) = s.gOk (kZ K) Rg
  | _, _, _, _, .assignSlot .. => rfl
  | _, _, _, _, .assignDurch .. => rfl
  | _, _, _, _, .assignGlob .. => rfl
  | _, _, _, _, .schreibBytes .. => rfl
  | _, _, _, _, .assignVar .. => rfl
  | _, _, _, _, .uebergang .. => rfl
  | _, _, _, _, .ite _ t e => kongr₂ (· && ·) (renB_gOk K Rg t) (renB_gOk K Rg e)
  | _, _, _, _, .onOption _ p a => kongr₂ (· && ·) (renB_gOk K Rg p) (renB_gOk K Rg a)
  | _, _, _, _, .onTag _ arms => renArms_gOk K Rg arms
  | _, _, _, _, .onGrund _ arms => renGArms_gOk K Rg arms
  | _, _, _, _, .call .. => gOk_nachΛ _ _ _ _
  | _, _, _, _, .callInd .. => gOk_nachΛ _ _ _ _
  | _, _, _, _, .locks _ _ body => renB_gOk K Rg body
  | _, _, _, _, .breaking _ body => renB_gOk K Rg body
  | _, _, _, _, .traverse _ _ body => renB_gOk K Rg body
  | _, _, _, _, .retry _ _ body ueber =>
      kongr₂ (· && ·) (renB_gOk K Rg body) (renB_gOk K Rg ueber)
  | _, _, _, _, .forever _ _ body => renB_gOk K Rg body
  | _, _, _, _, .axiomCall .. => rfl
  | _, _, _, _, .regSchreib .. => rfl
  | _, _, _, _, .transition .. => rfl
  | _, _, _, _, .publish .. => rfl
  | _, _, _, _, .advances .. => gOk_nachΛ _ _ _ _
  | _, _, _, _, .retires .. => gOk_nachΛ _ _ _ _
  | _, _, _, _, .ret .. => rfl
  | _, _, _, _, .retGrund .. => rfl
  | _, _, _, _, .leave _ => rfl
  | _, _, _, _, .next _ => rfl

theorem renB_gOk (K : Nat → Bool) (Rg : D.Reg → Bool) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ'), Block.gOk (D := D.mitRuhe) K Rg (renB b) = b.gOk (kZ K) Rg
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons s rest => kongr₂ (· && ·) (renS_gOk K Rg s) (renB_gOk K Rg rest)
  | _, _, _, _, .bind _ rest => renB_gOk K Rg rest
  | _, _, _, _, .bindCall _ _ _ _ _ rest => (gOk_vorΛ _ _ _ _).trans (renB_gOk K Rg rest)
  | _, _, _, _, .bindCallInd (n := n) _ _ _ _ _ rest =>
      congrArg (K (n + 1) && ·) ((gOk_vorΛ _ _ _ _).trans (renB_gOk K Rg rest))
  | _, _, _, _, .bindCallElse _ _ _ _ _ err rest =>
      kongr₂ (· && ·) ((gOk_umΛ _ _ _ _).trans (renEnd_gOk K Rg err))
        ((gOk_vorΛ _ _ _ _).trans (renB_gOk K Rg rest))
  | _, _, _, _, .bindAxiom _ _ _ _ _ _ _ rest => renB_gOk K Rg rest
  | _, _, _, _, .regLies r _ rest => congrArg (Rg r && ·) (renB_gOk K Rg rest)
  | _, _, _, _, .regLiesElse r _ _ sonst rest =>
      congrArg (Rg r && ·) (kongr₂ (· && ·) (renEnd_gOk K Rg sonst) (renB_gOk K Rg rest))
  | _, _, _, _, .awaits _ _ _ _ rest => renB_gOk K Rg rest
  | _, _, _, _, .exchange _ _ _ _ rest => renB_gOk K Rg rest
  | _, _, _, _, .narrow _ _ _ sonst rest =>
      kongr₂ (· && ·) (renEnd_gOk K Rg sonst) (renB_gOk K Rg rest)
  | _, _, _, _, .pruefung _ sonst rest =>
      kongr₂ (· && ·) (renEnd_gOk K Rg sonst) (renB_gOk K Rg rest)
  | _, _, _, _, .gleit _ _ _ _ _ rest => renB_gOk K Rg rest
  | _, _, _, _, .gleitLit _ _ _ rest => renB_gOk K Rg rest
  | _, _, _, _, .gleitVon _ _ _ rest => renB_gOk K Rg rest
  | _, _, _, _, .gleitNarrow _ _ _ sonst rest =>
      kongr₂ (· && ·) (renEnd_gOk K Rg sonst) (renB_gOk K Rg rest)

theorem renEnd_gOk (K : Nat → Bool) (Rg : D.Reg → Bool) {V : Vertrag D} : ∀ {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ), Endblock.gOk (D := D.mitRuhe) K Rg (renEnd e) = e.gOk (kZ K) Rg
  | _, _, _, .ret .. => rfl
  | _, _, _, .retGrund .. => rfl
  | _, _, _, .leave _ => rfl
  | _, _, _, .next _ => rfl
  | _, _, _, .cons s rest => kongr₂ (· && ·) (renS_gOk K Rg s) (renEnd_gOk K Rg rest)
  | _, _, _, .bind _ rest => renEnd_gOk K Rg rest

theorem renArms_gOk (K : Nat → Bool) (Rg : D.Reg → Bool) {V : Vertrag D} : ∀ {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    (arms : Arms D V l Γ Λ Λ' cs), Arms.gOk (D := D.mitRuhe) K Rg (renArms arms) = arms.gOk (kZ K) Rg
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons (c := none) b rest =>
      kongr₂ (· && ·) (renB_gOk K Rg b) (renArms_gOk K Rg rest)
  | _, _, _, _, _, .cons (c := some (_, _)) b rest =>
      kongr₂ (· && ·) (renB_gOk K Rg b) (renArms_gOk K Rg rest)

theorem renGArms_gOk (K : Nat → Bool) (Rg : D.Reg → Bool) {V : Vertrag D} : ∀ {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n),
    GrundArms.gOk (D := D.mitRuhe) K Rg (renGArms arms) = arms.gOk (kZ K) Rg
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons b rest => kongr₂ (· && ·) (renB_gOk K Rg b) (renGArms_gOk K Rg rest)

end

/-! ## 7. The feature test -/

/-- A feature set of `D.mitRuhe`, read back on `D`: direct callee `f` is
    `some f`, signature `n` is `n + 1`. -/
def mZ (A : Merkmal D.mitRuhe) : Merkmal D :=
  ⟨fun f => A.ruf (some f), fun n => A.ind (n + 1), A.sperre⟩

mutual

theorem renS_mS (A : Merkmal D.mitRuhe) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ'), mS A (renS s) = mS (mZ A) s
  | _, _, _, _, .assignSlot .. => rfl
  | _, _, _, _, .assignDurch .. => rfl
  | _, _, _, _, .assignGlob .. => rfl
  | _, _, _, _, .schreibBytes .. => rfl
  | _, _, _, _, .assignVar .. => rfl
  | _, _, _, _, .uebergang .. => rfl
  | _, _, _, _, .ite _ t e => kongr₂ (· && ·) (renB_mB A t) (renB_mB A e)
  | _, _, _, _, .onOption _ p a => kongr₂ (· && ·) (renB_mB A p) (renB_mB A a)
  | _, _, _, _, .onTag _ arms => renArms_mArms A arms
  | _, _, _, _, .onGrund _ arms => renGArms_mGArms A arms
  | _, _, _, _, .call .. => mS_nachΛ _ _ _
  | _, _, _, _, .callInd .. => mS_nachΛ _ _ _
  | _, _, _, _, .locks L _ body => congrArg (A.sperre L && ·) (renB_mB A body)
  | _, _, _, _, .breaking _ body => renB_mB A body
  | _, _, _, _, .traverse _ _ body => renB_mB A body
  | _, _, _, _, .retry _ _ body ueber => kongr₂ (· && ·) (renB_mB A body) (renB_mB A ueber)
  | _, _, _, _, .forever _ _ body => renB_mB A body
  | _, _, _, _, .axiomCall .. => rfl
  | _, _, _, _, .regSchreib .. => rfl
  | _, _, _, _, .transition .. => rfl
  | _, _, _, _, .publish .. => rfl
  | _, _, _, _, .advances .. => mS_nachΛ _ _ _
  | _, _, _, _, .retires .. => mS_nachΛ _ _ _
  | _, _, _, _, .ret .. => rfl
  | _, _, _, _, .retGrund .. => rfl
  | _, _, _, _, .leave _ => rfl
  | _, _, _, _, .next _ => rfl

theorem renB_mB (A : Merkmal D.mitRuhe) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ'), mB A (renB b) = mB (mZ A) b
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons s rest => kongr₂ (· && ·) (renS_mS A s) (renB_mB A rest)
  | _, _, _, _, .bind _ rest => renB_mB A rest
  | _, _, _, _, .bindCall g _ _ _ _ rest =>
      congrArg (A.ruf (some g) && ·) ((mB_vorΛ _ _ _).trans (renB_mB A rest))
  | _, _, _, _, .bindCallInd (n := n) _ _ _ _ _ rest =>
      congrArg (A.ind (n + 1) && ·) ((mB_vorΛ _ _ _).trans (renB_mB A rest))
  | _, _, _, _, .bindCallElse g _ _ _ _ err rest =>
      kongr₂ (fun x y => A.ruf (some g) && x && y) ((mE_umΛ _ _ _).trans (renEnd_mE A err))
        ((mB_vorΛ _ _ _).trans (renB_mB A rest))
  | _, _, _, _, .bindAxiom _ _ _ _ _ _ _ rest => renB_mB A rest
  | _, _, _, _, .regLies _ _ rest => renB_mB A rest
  | _, _, _, _, .regLiesElse _ _ _ sonst rest =>
      kongr₂ (· && ·) (renEnd_mE A sonst) (renB_mB A rest)
  | _, _, _, _, .awaits _ _ _ _ rest => renB_mB A rest
  | _, _, _, _, .exchange _ _ _ _ rest => renB_mB A rest
  | _, _, _, _, .narrow _ _ _ sonst rest => kongr₂ (· && ·) (renEnd_mE A sonst) (renB_mB A rest)
  | _, _, _, _, .pruefung _ sonst rest => kongr₂ (· && ·) (renEnd_mE A sonst) (renB_mB A rest)
  | _, _, _, _, .gleit _ _ _ _ _ rest => renB_mB A rest
  | _, _, _, _, .gleitLit _ _ _ rest => renB_mB A rest
  | _, _, _, _, .gleitVon _ _ _ rest => renB_mB A rest
  | _, _, _, _, .gleitNarrow _ _ _ sonst rest =>
      kongr₂ (· && ·) (renEnd_mE A sonst) (renB_mB A rest)

theorem renEnd_mE (A : Merkmal D.mitRuhe) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (e : Endblock D V l Γ Λ), mE A (renEnd e) = mE (mZ A) e
  | _, _, _, .ret .. => rfl
  | _, _, _, .retGrund .. => rfl
  | _, _, _, .leave _ => rfl
  | _, _, _, .next _ => rfl
  | _, _, _, .cons s rest => kongr₂ (· && ·) (renS_mS A s) (renEnd_mE A rest)
  | _, _, _, .bind _ rest => renEnd_mE A rest

theorem renArms_mArms (A : Merkmal D.mitRuhe) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs),
    mArms A (renArms arms) = mArms (mZ A) arms
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons (c := none) b rest => kongr₂ (· && ·) (renB_mB A b) (renArms_mArms A rest)
  | _, _, _, _, _, .cons (c := some (_, _)) b rest =>
      kongr₂ (· && ·) (renB_mB A b) (renArms_mArms A rest)

theorem renGArms_mGArms (A : Merkmal D.mitRuhe) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n),
    mGArms A (renGArms arms) = mGArms (mZ A) arms
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons b rest => kongr₂ (· && ·) (renB_mB A b) (renGArms_mGArms A rest)

end


/-! ## 8. The feature test is monotone -/

/-- Feature set `A` admits no more than `A'`. -/
def MLe (A A' : Merkmal D) : Prop :=
  (∀ f, A.ruf f = true → A'.ruf f = true) ∧ (∀ n, A.ind n = true → A'.ind n = true) ∧
    (∀ L, A.sperre L = true → A'.sperre L = true)

section Mono

variable {A A' : Merkmal D}

mutual

theorem mS_mono (hle : MLe A A') {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ'), mS A s = true → mS A' s = true
  | _, _, _, _, .ite _ t e, h => by
      simp only [mS, Bool.and_eq_true] at h ⊢; exact ⟨mB_mono hle t h.1, mB_mono hle e h.2⟩
  | _, _, _, _, .onOption _ p a, h => by
      simp only [mS, Bool.and_eq_true] at h ⊢; exact ⟨mB_mono hle p h.1, mB_mono hle a h.2⟩
  | _, _, _, _, .onTag _ arms, h => mArms_mono hle arms h
  | _, _, _, _, .onGrund _ arms, h => mGArms_mono hle arms h
  | _, _, _, _, .call g .., h => hle.1 g h
  | _, _, _, _, .callInd (n := n) .., h => hle.2.1 n h
  | _, _, _, _, .locks L _ body, h => by
      simp only [mS, Bool.and_eq_true] at h ⊢; exact ⟨hle.2.2 L h.1, mB_mono hle body h.2⟩
  | _, _, _, _, .breaking _ body, h => mB_mono hle body h
  | _, _, _, _, .traverse _ _ body, h => mB_mono hle body h
  | _, _, _, _, .retry _ _ body ueber, h => by
      simp only [mS, Bool.and_eq_true] at h ⊢; exact ⟨mB_mono hle body h.1, mB_mono hle ueber h.2⟩
  | _, _, _, _, .forever _ _ body, h => mB_mono hle body h
  | _, _, _, _, .assignSlot .., _ => rfl
  | _, _, _, _, .assignDurch .., _ => rfl
  | _, _, _, _, .assignGlob .., _ => rfl
  | _, _, _, _, .schreibBytes .., _ => rfl
  | _, _, _, _, .assignVar .., _ => rfl
  | _, _, _, _, .uebergang .., _ => rfl
  | _, _, _, _, .axiomCall .., _ => rfl
  | _, _, _, _, .regSchreib .., _ => rfl
  | _, _, _, _, .transition .., _ => rfl
  | _, _, _, _, .publish .., _ => rfl
  | _, _, _, _, .advances .., _ => rfl
  | _, _, _, _, .retires .., _ => rfl
  | _, _, _, _, .ret .., _ => rfl
  | _, _, _, _, .retGrund .., _ => rfl
  | _, _, _, _, .leave _, _ => rfl
  | _, _, _, _, .next _, _ => rfl

theorem mB_mono (hle : MLe A A') {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ'), mB A b = true → mB A' b = true
  | _, _, _, _, .nil, _ => rfl
  | _, _, _, _, .cons s rest, h => by
      simp only [mB, Bool.and_eq_true] at h ⊢; exact ⟨mS_mono hle s h.1, mB_mono hle rest h.2⟩
  | _, _, _, _, .bind _ rest, h => mB_mono hle rest h
  | _, _, _, _, .bindCall g _ _ _ _ rest, h => by
      simp only [mB, Bool.and_eq_true] at h ⊢; exact ⟨hle.1 g h.1, mB_mono hle rest h.2⟩
  | _, _, _, _, .bindCallInd (n := n) _ _ _ _ _ rest, h => by
      simp only [mB, Bool.and_eq_true] at h ⊢; exact ⟨hle.2.1 n h.1, mB_mono hle rest h.2⟩
  | _, _, _, _, .bindCallElse g _ _ _ _ err rest, h => by
      simp only [mB, Bool.and_eq_true] at h ⊢
      exact ⟨⟨hle.1 g h.1.1, mE_mono hle err h.1.2⟩, mB_mono hle rest h.2⟩
  | _, _, _, _, .bindAxiom _ _ _ _ _ _ _ rest, h => mB_mono hle rest h
  | _, _, _, _, .regLies _ _ rest, h => mB_mono hle rest h
  | _, _, _, _, .regLiesElse _ _ _ sonst rest, h => by
      simp only [mB, Bool.and_eq_true] at h ⊢; exact ⟨mE_mono hle sonst h.1, mB_mono hle rest h.2⟩
  | _, _, _, _, .awaits _ _ _ _ rest, h => mB_mono hle rest h
  | _, _, _, _, .exchange _ _ _ _ rest, h => mB_mono hle rest h
  | _, _, _, _, .narrow _ _ _ sonst rest, h => by
      simp only [mB, Bool.and_eq_true] at h ⊢; exact ⟨mE_mono hle sonst h.1, mB_mono hle rest h.2⟩
  | _, _, _, _, .pruefung _ sonst rest, h => by
      simp only [mB, Bool.and_eq_true] at h ⊢; exact ⟨mE_mono hle sonst h.1, mB_mono hle rest h.2⟩
  | _, _, _, _, .gleit _ _ _ _ _ rest, h => mB_mono hle rest h
  | _, _, _, _, .gleitLit _ _ _ rest, h => mB_mono hle rest h
  | _, _, _, _, .gleitVon _ _ _ rest, h => mB_mono hle rest h
  | _, _, _, _, .gleitNarrow _ _ _ sonst rest, h => by
      simp only [mB, Bool.and_eq_true] at h ⊢; exact ⟨mE_mono hle sonst h.1, mB_mono hle rest h.2⟩

theorem mE_mono (hle : MLe A A') {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ), mE A e = true → mE A' e = true
  | _, _, _, .ret .., _ => rfl
  | _, _, _, .retGrund .., _ => rfl
  | _, _, _, .leave _, _ => rfl
  | _, _, _, .next _, _ => rfl
  | _, _, _, .cons s rest, h => by
      simp only [mE, Bool.and_eq_true] at h ⊢; exact ⟨mS_mono hle s h.1, mE_mono hle rest h.2⟩
  | _, _, _, .bind _ rest, h => mE_mono hle rest h

theorem mArms_mono (hle : MLe A A') {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs),
    mArms A arms = true → mArms A' arms = true
  | _, _, _, _, _, .nil, _ => rfl
  | _, _, _, _, _, .cons b rest, h => by
      simp only [mArms, Bool.and_eq_true] at h ⊢; exact ⟨mB_mono hle b h.1, mArms_mono hle rest h.2⟩

theorem mGArms_mono (hle : MLe A A') {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n),
    mGArms A arms = true → mGArms A' arms = true
  | _, _, _, _, _, .nil, _ => rfl
  | _, _, _, _, _, .cons b rest, h => by
      simp only [mGArms, Bool.and_eq_true] at h ⊢
      exact ⟨mB_mono hle b h.1, mGArms_mono hle rest h.2⟩

end

end Mono

/-! ## 9. The program `P.mitRuhe`: bodies, footprints -/

section Programm

variable (P : Programm D)

theorem rumpf_mitRuhe_orteP (f : D.Fn) :
    endblockOrteP P.mitRuhe (P.mitRuhe.rumpf (some f)) = endblockOrteP P (P.rumpf f) :=
  (orteP_umΛ _ _ _).trans (renEnd_orteP P _)

theorem rumpf_mitRuhe_regs (f : D.Fn) :
    (P.mitRuhe.rumpf (some f)).regs = (P.rumpf f).regs :=
  (regs_umΛ _ _).trans (renEnd_regs _)

theorem rumpf_mitRuhe_mE (A : Merkmal D.mitRuhe) (f : D.Fn) :
    mE A (P.mitRuhe.rumpf (some f)) = mE (mZ A) (P.rumpf f) :=
  (mE_umΛ _ _ _).trans (renEnd_mE A _)

theorem rumpf_mitRuhe_gOk (K : Nat → Bool) (Rg : D.Reg → Bool) (f : D.Fn) :
    Endblock.gOk (D := D.mitRuhe) K Rg (P.mitRuhe.rumpf (some f)) = (P.rumpf f).gOk (kZ K) Rg :=
  (gOk_umΛ _ _ _ _).trans (renEnd_gOk K Rg _)

theorem invOrteP_mitRuhe (f : D.Fn) : invOrteP P.mitRuhe (some f) = invOrteP P f :=
  congrArg (fun g => (D.invs.filter (schuldet f)).flatMap g)
    (funext fun i => invariante_mitRuhe_orte P i)

theorem invOrteP_mitRuhe_ruhe : invOrteP P.mitRuhe none = [] := by
  unfold invOrteP
  have : (D.mitRuhe).invs.filter (schuldet (D := D.mitRuhe) none) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro i _
    simp [schuldet, Deklaration.schreibt, Deklaration.signatur, Deklaration.mitRuhe, sigM,
      sigNrM, sigRuhe]
  rw [this]
  rfl

theorem fussOrte_mitRuhe (f : D.Fn) : fussOrte P.mitRuhe (some f) = fussOrte P f := by
  unfold fussOrte
  rw [requires_mitRuhe_orte, ensures_mitRuhe_orte, rumpf_mitRuhe_orteP, invOrteP_mitRuhe]
  rfl

theorem fussOrte_mitRuhe_ruhe : fussOrte P.mitRuhe none = [] := by
  unfold fussOrte
  rw [invOrteP_mitRuhe_ruhe]
  rfl

theorem fussOrteG_mitRuhe (f : D.Fn) : fussOrteG P.mitRuhe (some f) = fussOrteG P f := by
  unfold fussOrteG
  rw [fussOrte_mitRuhe, rumpf_mitRuhe_regs]
  rfl

theorem fussOrteG_mitRuhe_ruhe : fussOrteG P.mitRuhe none = [] := by
  unfold fussOrteG
  rw [fussOrte_mitRuhe_ruhe]
  rfl

end Programm

/-! ## 10. Call graphs of `P.mitRuhe` -/

theorem merkmal_ext {A B : Merkmal D} (h1 : A.ruf = B.ruf) (h2 : A.ind = B.ind)
    (h3 : A.sperre = B.sperre) : A = B := by
  cases A; cases B; simp_all

/-- The full feature set: every call, every signature, every lock. -/
def mVoll (D : Deklaration) : Merkmal D := ⟨fun _ => true, fun _ => true, fun _ => true⟩

theorem any_fsRuhe (fs : List D.Fn) (p : D.mitRuhe.Fn → Bool) :
    (fsRuhe fs).any p = (p none || fs.any fun f => p (some f)) := by
  show (p none || (fs.map some).any p) = _
  congr 1
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      show (p (some f) || (fs.map some).any p) = (p (some f) || fs.any _)
      rw [ih]

theorem all_fsRuhe (fs : List D.Fn) (p : D.mitRuhe.Fn → Bool) :
    (fsRuhe fs).all p = (p none && fs.all fun f => p (some f)) := by
  show (p none && (fs.map some).all p) = _
  congr 1
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      show (p (some f) && (fs.map some).all p) = (p (some f) && fs.all _)
      rw [ih]

section Graph

variable [DecidableEq D.Fn] (P : Programm D) {fs : List D.Fn}

theorem ruftB_mitRuhe (f g : D.Fn) : ruftB P.mitRuhe (some f) (some g) = ruftB P f g := by
  unfold ruftB
  rw [rumpf_mitRuhe_mE]
  apply congrArg (fun A => !(mE A (P.rumpf f)))
  apply merkmal_ext
  · funext h
    show (!decide (some h = some g)) = !decide (h = g)
    congr 1
    exact decide_eq_decide.mpr ⟨fun e => Option.some.inj e, fun e => e ▸ rfl⟩
  · funext n
    show (!decide (n + 1 = D.sig g + 1)) = !decide (n = D.sig g)
    congr 1
    exact decide_eq_decide.mpr ⟨fun e => Nat.succ.inj e, fun e => e ▸ rfl⟩
  · rfl

theorem ruftB_mitRuhe_ruhe_ziel (hT : ∀ f, mE (mVoll D) (P.rumpf f) = true) (f : D.Fn) :
    ruftB P.mitRuhe (some f) none = false := by
  unfold ruftB
  rw [rumpf_mitRuhe_mE]
  have e : ∀ A : Merkmal D, A = mVoll D → (!(mE A (P.rumpf f))) = false := by
    intro A hA; rw [hA, hT f]; rfl
  apply e
  apply merkmal_ext
  · funext h
    show (!decide ((some h : Option D.Fn) = none)) = true
    have : decide ((some h : Option D.Fn) = none) = false := decide_eq_false (by intro e; cases e)
    rw [this]; rfl
  · funext n
    show (!decide (n + 1 = 0)) = true
    have : decide (n + 1 = 0) = false := decide_eq_false (Nat.succ_ne_zero n)
    rw [this]; rfl
  · rfl

theorem ruftB_mitRuhe_ruhe (g : D.mitRuhe.Fn) : ruftB P.mitRuhe none g = false := rfl

/-- **Reach from `some w` is reach from `w`** in every round, and never the
    root. -/
theorem erreichB_mitRuhe (hT : ∀ f, mE (mVoll D) (P.rumpf f) = true) (w : D.Fn) :
    ∀ n, (∀ g, erreichB P.mitRuhe (fsRuhe fs) (some w) n (some g) = erreichB P fs w n g) ∧
      erreichB P.mitRuhe (fsRuhe fs) (some w) n none = false
  | 0 => ⟨fun g => by
        show decide ((some g : Option D.Fn) = some w) = decide (g = w)
        exact decide_eq_decide.mpr ⟨fun e => Option.some.inj e, fun e => e ▸ rfl⟩,
      by
        show decide ((none : Option D.Fn) = some w) = false
        exact decide_eq_false (by intro e; cases e)⟩
  | n + 1 => by
      obtain ⟨ih1, ih2⟩ := erreichB_mitRuhe hT w n
      refine ⟨fun g => ?_, ?_⟩
      · show erreichSchritt P.mitRuhe (fsRuhe fs) (erreichB P.mitRuhe (fsRuhe fs) (some w) n)
          (some g) = erreichSchritt P fs (erreichB P fs w n) g
        unfold erreichSchritt
        rw [any_fsRuhe, ih1, ih2]
        simp only [Bool.false_and, Bool.false_or, ih1, ruftB_mitRuhe]
      · show erreichSchritt P.mitRuhe (fsRuhe fs) (erreichB P.mitRuhe (fsRuhe fs) (some w) n)
          none = false
        unfold erreichSchritt
        rw [any_fsRuhe, ih2]
        simp only [Bool.false_and, Bool.false_or, ruftB_mitRuhe_ruhe_ziel P hT, Bool.and_false,
          List.any_eq_false]
        intro _ _ h
        cases h

/-- Reach from the root is the root alone. -/
theorem erreichB_mitRuhe_ruhe : ∀ n,
    erreichB P.mitRuhe (fsRuhe fs) none n none = true ∧
      ∀ g, erreichB P.mitRuhe (fsRuhe fs) none n (some g) = false
  | 0 => ⟨by
        show decide ((none : Option D.Fn) = none) = true
        exact decide_eq_true rfl,
      fun g => by
        show decide ((some g : Option D.Fn) = none) = false
        exact decide_eq_false (by intro e; cases e)⟩
  | n + 1 => by
      obtain ⟨ih1, ih2⟩ := erreichB_mitRuhe_ruhe n
      refine ⟨?_, fun g => ?_⟩
      · show erreichSchritt P.mitRuhe (fsRuhe fs) (erreichB P.mitRuhe (fsRuhe fs) none n) none =
          true
        unfold erreichSchritt
        rw [ih1]
        rfl
      · show erreichSchritt P.mitRuhe (fsRuhe fs) (erreichB P.mitRuhe (fsRuhe fs) none n)
          (some g) = false
        unfold erreichSchritt
        have h1 : ruftB P.mitRuhe none (some g) = false := rfl
        rw [any_fsRuhe]
        simp only [ih2, h1, Bool.and_false, Bool.false_or, Bool.false_and, List.any_eq_false]
        intro _ _ h
        cases h

theorem reachB_mitRuhe_ruhe_ruhe : reachB P.mitRuhe (fsRuhe fs) none none = true :=
  (erreichB_mitRuhe_ruhe P _).1

theorem reachB_mitRuhe_ruhe (g : D.Fn) : reachB P.mitRuhe (fsRuhe fs) none (some g) = false :=
  (erreichB_mitRuhe_ruhe P _).2 g

/-- A closed call graph is closed under `ruftB`. -/
theorem abgK_ruft (hvoll : ∀ g : D.Fn, g ∈ fs) {Z : D.Fn → Bool} (hA : AbgK P fs Z) {f g : D.Fn}
    (hf : Z f = true) (hr : ruftB P f g = true) : Z g = true := by
  cases hg : Z g
  · exfalso
    have hm := hA f hf
    have hle : MLe (rufM fs Z)
        ⟨fun h => !(decide (h = g)), fun n => !(decide (n = D.sig g)), fun _ => true⟩ := by
      refine ⟨fun h hh => ?_, fun n hn => ?_, fun _ _ => rfl⟩
      · show (!decide (h = g)) = true
        have hh' : Z h = true := hh
        have : h ≠ g := fun e => by subst e; rw [hh'] at hg; cases hg
        simp [this]
      · show (!decide (n = D.sig g)) = true
        have h1 := (List.all_eq_true.mp hn) g (hvoll g)
        by_cases e : n = D.sig g
        · subst e; simp [hg] at h1
        · simp [e]
    have := mE_mono hle _ hm
    unfold ruftB at hr
    rw [this] at hr
    cases hr
  · rfl

/-- A closed graph is a fixed point of one more round. -/
theorem erreichSchritt_abg (hvoll : ∀ g : D.Fn, g ∈ fs) {Z : D.Fn → Bool} (hA : AbgK P fs Z) :
    erreichSchritt P fs Z = Z := by
  funext g
  unfold erreichSchritt
  cases hg : Z g
  · simp only [Bool.false_or, List.any_eq_false, Bool.and_eq_true, not_and]
    intro f _ hf hr
    rw [abgK_ruft P hvoll hA hf hr] at hg
    cases hg
  · rfl

/-- Every function's body passes the full feature set (from its own closed
    call graph). -/
theorem mVoll_of_abg (hA : ∀ w, AbgK P fs (reachB P fs w)) (f : D.Fn) :
    mE (mVoll D) (P.rumpf f) = true :=
  mE_mono ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩ _ (hA f f (reachB_wurzel P fs f))

/-- **Reach in `P.mitRuhe` from `some w` IS reach in `P` from `w`**, given
    closed call graphs. -/
theorem reachB_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs) (hA : ∀ w, AbgK P fs (reachB P fs w))
    (w g : D.Fn) : reachB P.mitRuhe (fsRuhe fs) (some w) (some g) = reachB P fs w g := by
  have h := (erreichB_mitRuhe (fs := fs) P (mVoll_of_abg P hA) w (fs.length + 1)).1 g
  unfold reachB
  have hl : (fsRuhe fs).length = fs.length + 1 := congrArg (· + 1) (List.length_map (as := fs) some)
  rw [hl, h]
  show erreichSchritt P fs (reachB P fs w) g = reachB P fs w g
  rw [erreichSchritt_abg P hvoll (hA w)]

theorem reachB_mitRuhe_nicht_ruhe (hA : ∀ w, AbgK P fs (reachB P fs w)) (w : D.Fn) :
    reachB P.mitRuhe (fsRuhe fs) (some w) none = false :=
  (erreichB_mitRuhe (fs := fs) P (mVoll_of_abg P hA) w _).2

end Graph


end Gabbro.Grammatik
