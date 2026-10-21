/-
  File:      Grammatik/MitRuheStatisch.lean
  Subject:   STATIC TRANSFER to `P.mitRuhe` (MitRuhe.lean): every fold the
             checker computes over a body -- read carriers, register
             reads, the fragment test, the feature test `mE` -- gives on the
             translated body what it gave on the body.
-/
import Grammatik.Nebenlaeufigkeit.Sperren.MitRuhe
import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung

namespace Gabbro.Grammatik

variable {D : Deklaration}

theorem kongr₂ {α β γ : Sort _} (f : α → β → γ) {a a' : α} {b b' : β} (ha : a = a')
    (hb : b = b') : f a b = f a' b' := by
  subst ha; subst hb; rfl

/-! ## 1. Read carriers of expressions -/

mutual

theorem ruE_orte : ∀ {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ),
    (ruE e).orte = e.orte
  | _, _, _, .lit _ => rfl
  | _, _, _, .tru => rfl
  | _, _, _, .fls => rfl
  | _, _, _, .var _ => rfl
  | _, _, _, .glob _ _ => rfl
  | _, _, _, .slot t f i hL => congrArg (Sum.inl t :: ·) (ruE_orte i)
  | _, _, _, .thru p t ht f i hL => kongr₂ (fun x y => x ++ Sum.inl t :: y) (ruE_orte p) (ruE_orte i)
  | _, _, _, .ptrOf .. => rfl
  | _, _, _, .fnref .. => rfl
  | _, _, _, .oldG _ _ => rfl
  | _, _, _, .oldS t f i hL => congrArg (Sum.inl t :: ·) (ruE_orte i)
  | _, _, _, .widen _ _ e => ruE_orte e
  | _, _, _, .add a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .sub a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .neg a => ruE_orte a
  | _, _, _, .mul a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .div _ _ a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .rem _ _ a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .sdiv _ a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .srem _ a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .getBytes t _ _ _ i _ _ _ => congrArg (Sum.inl t :: ·) (ruE_orte i)
  | _, _, _, .band _ _ a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .bor _ _ _ _ _ a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .bxor _ _ _ _ _ a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .shl _ _ _ _ _ a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .shr _ _ _ _ _ a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .lt a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .le a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .eq a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .fllt a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .flle a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .and a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .or a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .not a => ruE_orte a
  | _, _, _, .none _ => rfl
  | _, _, _, .some a => ruE_orte a
  | _, _, _, .istSome a => ruE_orte a
  | _, _, _, .case _ _ nutz => ruN_orte nutz
  | _, _, _, .why _ _ => rfl
  | _, _, _, .forallSlots t body _ => congrArg (Sum.inl t :: ·) (ruE_orte body)
  | _, _, _, .existsSlots t body _ => congrArg (Sum.inl t :: ·) (ruE_orte body)
  | _, _, _, .reaches t _ _ a b _ => kongr₂ (fun x y => Sum.inl t :: x ++ y) (ruE_orte a) (ruE_orte b)

theorem ruN_orte : ∀ {Γ : Ctx} {Λ : List (Res D)} {c : Option (Int × Int)}
    (n : NutzlastExpr D Γ Λ c), (ruN n).orte = n.orte
  | _, _, _, .empty => rfl
  | _, _, _, .num e => ruE_orte e

end
theorem ruA_orte : ∀ {Γ : Ctx} {Λ : List (Res D)} {τs : List Ty} (a : Args D Γ Λ τs),
    (ruA a).orte = a.orte
  | _, _, _, .nil => rfl
  | _, _, _, .cons e rest => kongr₂ (· ++ ·) (ruE_orte e) (ruA_orte rest)

theorem ruErg_orte : ∀ {Γ : Ctx} {Λ : List (Res D)} {e : Option Ty} (a : ErgExpr D Γ Λ e),
    (ruErg a).orte = a.orte
  | _, _, _, .empty => rfl
  | _, _, _, .val e => ruE_orte e

theorem umΛ_orte {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} (h : Λ = Λ') (e : Expr D Γ Λ τ) :
    (Expr.umΛ h e).orte = e.orte := by
  subst h; rfl

theorem umΓ_orte {Γ Γ' : Ctx} {Λ : List (Res D)} {τ : Ty} (h : Γ = Γ') (e : Expr D Γ Λ τ) :
    (Expr.umΓ h e).orte = e.orte := by
  subst h; rfl

/-! ## 2. The contracts of `P.mitRuhe` -/

theorem requires_mitRuhe_orte (P : Programm D) (f : D.Fn) :
    (P.mitRuhe.requires (some f)).orte = (P.requires f).orte :=
  (umΛ_orte _ _).trans (ruE_orte _)

theorem ensures_mitRuhe_orte (P : Programm D) (f : D.Fn) :
    (P.mitRuhe.ensures (some f)).orte = (P.ensures f).orte :=
  ((umΓ_orte _ _).trans (umΛ_orte _ _)).trans (ruE_orte _)

theorem invariante_mitRuhe_orte (P : Programm D) (i : D.Inv) :
    (P.mitRuhe.invariante i).orte = (P.invariante i).orte :=
  (umΛ_orte _ _).trans (ruE_orte _)

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

theorem ruS_orteP (P : Programm D) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ'),
    stmtOrteP P.mitRuhe (ruS s) = stmtOrteP P s
  | _, _, _, _, .assignSlot _ _ i e _ _ => kongr₂ (· ++ ·) (ruE_orte i) (ruE_orte e)
  | _, _, _, _, .assignThru p _ _ _ i e _ _ =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte p) (ruE_orte i)) (ruE_orte e)
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
      (orteP_nachΛ _ _ _).trans (kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args))
  | _, _, _, _, .locks _ _ body => ruB_orteP P body
  | _, _, _, _, .breaking _ body => ruB_orteP P body
  | _, _, _, _, .traverse _ inv body => kongr₂ (· ++ ·) (ruE_orte inv) (ruB_orteP P body)
  | _, _, _, _, .retry _ bis body ueber =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte bis) (ruB_orteP P body)) (ruB_orteP P ueber)
  | _, _, _, _, .forever _ inv body => kongr₂ (· ++ ·) (ruE_orte inv) (ruB_orteP P body)
  | _, _, _, _, .axiomCall _ args _ _ _ _ _ => ruA_orte args
  | _, _, _, _, .regWrite _ _ e => ruE_orte e
  | _, _, _, _, .transition .. => rfl
  | _, _, _, _, .publish _ e _ _ _ _ => ruE_orte e
  | _, _, _, _, .advances .. => orteP_nachΛ _ _ _
  | _, _, _, _, .retires .. => orteP_nachΛ _ _ _
  | _, _, _, _, .ret e _ => ruErg_orte e
  | _, _, _, _, .retWhy .. => rfl
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
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args))
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
  | _, _, _, _, .regRead _ _ rest => ruB_orteP P rest
  | _, _, _, _, .regReadElse _ _ zusage sonst rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte zusage) (ruEnd_orteP P sonst))
        (ruB_orteP P rest)
  | _, _, _, _, .awaits g _ _ _ _ rest => congrArg (Sum.inr g :: ·) (ruB_orteP P rest)
  | _, _, _, _, .exchange g neu _ _ rest =>
      kongr₂ (fun x y => (Sum.inr g :: x) ++ y) (ruE_orte neu) (ruB_orteP P rest)
  | _, _, _, _, .narrow e _ _ sonst rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte e) (ruEnd_orteP P sonst)) (ruB_orteP P rest)
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
  | _, _, _, .regRead _ _ rest => ruEnd_orteP P rest
  | _, _, _, .regReadElse _ _ zusage sonst rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte zusage) (ruEnd_orteP P sonst))
        (ruEnd_orteP P rest)
  | _, _, _, .awaits g _ _ _ _ rest => congrArg (Sum.inr g :: ·) (ruEnd_orteP P rest)
  | _, _, _, .bindCallInd p args _ _ _ rest =>
      kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte p) (ruA_orte args))
        ((orteP_umΛ _ _ _).trans (ruEnd_orteP P rest))

theorem ruArms_orteP (P : Programm D) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs),
    armsOrteP P.mitRuhe (ruArms arms) = armsOrteP P arms
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons (c := none) b rest =>
      kongr₂ (· ++ ·) (ruB_orteP P b) (ruArms_orteP P rest)
  | _, _, _, _, _, .cons (c := some (_, _)) b rest =>
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
  | _, _, _, _, .assignThru .. => rfl
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
  | _, _, _, _, .locks _ _ body => ruB_regs body
  | _, _, _, _, .breaking _ body => ruB_regs body
  | _, _, _, _, .traverse _ _ body => ruB_regs body
  | _, _, _, _, .retry _ _ body ueber => kongr₂ (· ++ ·) (ruB_regs body) (ruB_regs ueber)
  | _, _, _, _, .forever _ _ body => ruB_regs body
  | _, _, _, _, .axiomCall .. => rfl
  | _, _, _, _, .regWrite .. => rfl
  | _, _, _, _, .transition .. => rfl
  | _, _, _, _, .publish .. => rfl
  | _, _, _, _, .advances .. => regs_nachΛ _ _
  | _, _, _, _, .retires .. => regs_nachΛ _ _
  | _, _, _, _, .ret .. => rfl
  | _, _, _, _, .retWhy .. => rfl
  | _, _, _, _, .leave _ => rfl
  | _, _, _, _, .next _ => rfl

theorem ruB_regs {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ'), (ruB b).regs = b.regs
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons s rest => kongr₂ (· ++ ·) (ruS_regs s) (ruB_regs rest)
  | _, _, _, _, .bind _ rest => ruB_regs rest
  | _, _, _, _, .bindCall _ _ _ _ _ rest => (regs_vorΛ _ _).trans (ruB_regs rest)
  | _, _, _, _, .bindCallInd _ _ _ _ _ rest => (regs_vorΛ _ _).trans (ruB_regs rest)
  | _, _, _, _, .bindCallElse _ _ _ _ _ err rest =>
      kongr₂ (· ++ ·) ((regs_umΛ _ _).trans (ruEnd_regs err))
        ((regs_vorΛ _ _).trans (ruB_regs rest))
  | _, _, _, _, .bindAxiom _ _ _ _ _ _ _ rest => ruB_regs rest
  | _, _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest => kongr₂ (· ++ ·) (ruEnd_regs err) (ruB_regs rest)
  | _, _, _, _, .regRead r _ rest => congrArg (r :: ·) (ruB_regs rest)
  | _, _, _, _, .regReadElse r _ _ sonst rest =>
      congrArg (r :: ·) (kongr₂ (· ++ ·) (ruEnd_regs sonst) (ruB_regs rest))
  | _, _, _, _, .awaits _ _ _ _ _ rest => ruB_regs rest
  | _, _, _, _, .exchange _ _ _ _ rest => ruB_regs rest
  | _, _, _, _, .narrow _ _ _ sonst rest => kongr₂ (· ++ ·) (ruEnd_regs sonst) (ruB_regs rest)
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
  | _, _, _, .leave _ => rfl
  | _, _, _, .next _ => rfl
  | _, _, _, .cons s rest => kongr₂ (· ++ ·) (ruS_regs s) (ruEnd_regs rest)
  | _, _, _, .bind _ rest => ruEnd_regs rest
  | _, _, _, .bindCall _ _ _ _ _ rest => (regs_umΛ _ _).trans (ruEnd_regs rest)
  | _, _, _, .bindCallElse _ _ _ _ _ err rest =>
      kongr₂ (· ++ ·) ((regs_umΛ _ _).trans (ruEnd_regs err))
        ((regs_umΛ _ _).trans (ruEnd_regs rest))
  | _, _, _, .bindAxiom _ _ _ _ _ _ _ rest => ruEnd_regs rest
  | _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest => kongr₂ (· ++ ·) (ruEnd_regs err) (ruEnd_regs rest)
  | _, _, _, .regRead r _ rest => congrArg (r :: ·) (ruEnd_regs rest)
  | _, _, _, .regReadElse r _ _ sonst rest =>
      congrArg (r :: ·) (kongr₂ (· ++ ·) (ruEnd_regs sonst) (ruEnd_regs rest))
  | _, _, _, .awaits _ _ _ _ _ rest => ruEnd_regs rest
  | _, _, _, .bindCallInd _ _ _ _ _ rest => (regs_umΛ _ _).trans (ruEnd_regs rest)

theorem ruArms_regs {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs),
    (ruArms arms).regs = arms.regs
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons (c := none) b rest => kongr₂ (· ++ ·) (ruB_regs b) (ruArms_regs rest)
  | _, _, _, _, _, .cons (c := some (_, _)) b rest =>
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

mutual

theorem ruS_gOk (K : Nat → Bool) (Rg : D.Reg → Bool) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ'), Stmt.gOk (D := D.mitRuhe) K Rg (ruS s) = s.gOk (kZ K) Rg
  | _, _, _, _, .assignSlot .. => rfl
  | _, _, _, _, .assignThru .. => rfl
  | _, _, _, _, .assignGlob .. => rfl
  | _, _, _, _, .putBytes .. => rfl
  | _, _, _, _, .assignVar .. => rfl
  | _, _, _, _, .shift .. => rfl
  | _, _, _, _, .ite _ t e => kongr₂ (· && ·) (ruB_gOk K Rg t) (ruB_gOk K Rg e)
  | _, _, _, _, .onOption _ p a => kongr₂ (· && ·) (ruB_gOk K Rg p) (ruB_gOk K Rg a)
  | _, _, _, _, .onTag _ arms => ruArms_gOk K Rg arms
  | _, _, _, _, .onWhy _ arms => ruGArms_gOk K Rg arms
  | _, _, _, _, .call .. => gOk_nachΛ _ _ _ _
  | _, _, _, _, .callInd .. => gOk_nachΛ _ _ _ _
  | _, _, _, _, .locks _ _ body => ruB_gOk K Rg body
  | _, _, _, _, .breaking _ body => ruB_gOk K Rg body
  | _, _, _, _, .traverse _ _ body => ruB_gOk K Rg body
  | _, _, _, _, .retry _ _ body ueber =>
      kongr₂ (· && ·) (ruB_gOk K Rg body) (ruB_gOk K Rg ueber)
  | _, _, _, _, .forever _ _ body => ruB_gOk K Rg body
  | _, _, _, _, .axiomCall .. => rfl
  | _, _, _, _, .regWrite .. => rfl
  | _, _, _, _, .transition .. => rfl
  | _, _, _, _, .publish .. => rfl
  | _, _, _, _, .advances .. => gOk_nachΛ _ _ _ _
  | _, _, _, _, .retires .. => gOk_nachΛ _ _ _ _
  | _, _, _, _, .ret .. => rfl
  | _, _, _, _, .retWhy .. => rfl
  | _, _, _, _, .leave _ => rfl
  | _, _, _, _, .next _ => rfl

theorem ruB_gOk (K : Nat → Bool) (Rg : D.Reg → Bool) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ'), Block.gOk (D := D.mitRuhe) K Rg (ruB b) = b.gOk (kZ K) Rg
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons s rest => kongr₂ (· && ·) (ruS_gOk K Rg s) (ruB_gOk K Rg rest)
  | _, _, _, _, .bind _ rest => ruB_gOk K Rg rest
  | _, _, _, _, .bindCall _ _ _ _ _ rest => (gOk_vorΛ _ _ _ _).trans (ruB_gOk K Rg rest)
  | _, _, _, _, .bindCallInd (n := n) _ _ _ _ _ rest =>
      congrArg (K (n + 1) && ·) ((gOk_vorΛ _ _ _ _).trans (ruB_gOk K Rg rest))
  | _, _, _, _, .bindCallElse _ _ _ _ _ err rest =>
      kongr₂ (· && ·) ((gOk_umΛ _ _ _ _).trans (ruEnd_gOk K Rg err))
        ((gOk_vorΛ _ _ _ _).trans (ruB_gOk K Rg rest))
  | _, _, _, _, .bindAxiom _ _ _ _ _ _ _ rest => ruB_gOk K Rg rest
  | _, _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest =>
      kongr₂ (· && ·) (ruEnd_gOk K Rg err) (ruB_gOk K Rg rest)
  | _, _, _, _, .regRead r _ rest => congrArg (Rg r && ·) (ruB_gOk K Rg rest)
  | _, _, _, _, .regReadElse r _ _ sonst rest =>
      congrArg (Rg r && ·) (kongr₂ (· && ·) (ruEnd_gOk K Rg sonst) (ruB_gOk K Rg rest))
  | _, _, _, _, .awaits _ _ _ _ _ rest => ruB_gOk K Rg rest
  | _, _, _, _, .exchange _ _ _ _ rest => ruB_gOk K Rg rest
  | _, _, _, _, .narrow _ _ _ sonst rest =>
      kongr₂ (· && ·) (ruEnd_gOk K Rg sonst) (ruB_gOk K Rg rest)
  | _, _, _, _, .check _ sonst rest =>
      kongr₂ (· && ·) (ruEnd_gOk K Rg sonst) (ruB_gOk K Rg rest)
  | _, _, _, _, .float _ _ _ _ _ rest => ruB_gOk K Rg rest
  | _, _, _, _, .floatLit _ _ _ rest => ruB_gOk K Rg rest
  | _, _, _, _, .floatOf _ _ _ rest => ruB_gOk K Rg rest
  | _, _, _, _, .floatNarrow _ _ _ sonst rest =>
      kongr₂ (· && ·) (ruEnd_gOk K Rg sonst) (ruB_gOk K Rg rest)

theorem ruEnd_gOk (K : Nat → Bool) (Rg : D.Reg → Bool) {V : Vertrag D} : ∀ {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ), Endblock.gOk (D := D.mitRuhe) K Rg (ruEnd e) = e.gOk (kZ K) Rg
  | _, _, _, .ret .. => rfl
  | _, _, _, .retWhy .. => rfl
  | _, _, _, .leave _ => rfl
  | _, _, _, .next _ => rfl
  | _, _, _, .cons s rest => kongr₂ (· && ·) (ruS_gOk K Rg s) (ruEnd_gOk K Rg rest)
  | _, _, _, .bind _ rest => ruEnd_gOk K Rg rest
  | _, _, _, .bindCall _ _ _ _ _ rest => (gOk_umΛ _ _ _ _).trans (ruEnd_gOk K Rg rest)
  | _, _, _, .bindCallElse _ _ _ _ _ err rest =>
      kongr₂ (· && ·) ((gOk_umΛ _ _ _ _).trans (ruEnd_gOk K Rg err))
        ((gOk_umΛ _ _ _ _).trans (ruEnd_gOk K Rg rest))
  | _, _, _, .bindAxiom _ _ _ _ _ _ _ rest => ruEnd_gOk K Rg rest
  | _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest =>
      kongr₂ (· && ·) (ruEnd_gOk K Rg err) (ruEnd_gOk K Rg rest)
  | _, _, _, .regRead r _ rest => congrArg (Rg r && ·) (ruEnd_gOk K Rg rest)
  | _, _, _, .regReadElse r _ _ sonst rest =>
      congrArg (Rg r && ·) (kongr₂ (· && ·) (ruEnd_gOk K Rg sonst) (ruEnd_gOk K Rg rest))
  | _, _, _, .awaits _ _ _ _ _ rest => ruEnd_gOk K Rg rest
  | _, _, _, .bindCallInd (n := n) _ _ _ _ _ rest =>
      congrArg (K (n + 1) && ·) ((gOk_umΛ _ _ _ _).trans (ruEnd_gOk K Rg rest))

theorem ruArms_gOk (K : Nat → Bool) (Rg : D.Reg → Bool) {V : Vertrag D} : ∀ {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))}
    (arms : Arms D V l Γ Λ Λ' cs), Arms.gOk (D := D.mitRuhe) K Rg (ruArms arms) = arms.gOk (kZ K) Rg
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons (c := none) b rest =>
      kongr₂ (· && ·) (ruB_gOk K Rg b) (ruArms_gOk K Rg rest)
  | _, _, _, _, _, .cons (c := some (_, _)) b rest =>
      kongr₂ (· && ·) (ruB_gOk K Rg b) (ruArms_gOk K Rg rest)

theorem ruGArms_gOk (K : Nat → Bool) (Rg : D.Reg → Bool) {V : Vertrag D} : ∀ {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n),
    GrundArms.gOk (D := D.mitRuhe) K Rg (ruGArms arms) = arms.gOk (kZ K) Rg
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons b rest => kongr₂ (· && ·) (ruB_gOk K Rg b) (ruGArms_gOk K Rg rest)

end
/-! ## 7. The feature test -/

/-- A feature set of `D.mitRuhe`, read back on `D`: direct callee `f` is
    `some f`, signature `n` is `n + 1`. -/
def mZ (A : Merkmal D.mitRuhe) : Merkmal D :=
  ⟨fun f => A.ruf (some f), fun n => A.ind (n + 1), A.sperre⟩


end Gabbro.Grammatik
