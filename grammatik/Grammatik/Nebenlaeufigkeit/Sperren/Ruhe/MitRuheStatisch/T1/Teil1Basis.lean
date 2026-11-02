module

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuhe
public import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung

@[expose] public section



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
  | _, _, _, .refEq a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .slotRef r t ht ho f hL => congrArg (Sum.inl t :: ·) (ruE_orte r)
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
  | _, _, _, .arrNil => rfl
  | _, _, _, .strLit _ _ => rfl
  | _, _, _, .arrCons a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .arrGet a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .strCat a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .arrSet a i v => kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte i)) (ruE_orte v)
  | _, _, _, .strLen e => ruE_orte e
  | _, _, _, .strGet a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .strEq a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .strLt a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .strWeit _ e => ruE_orte e
  | _, _, _, .wenn c a b => kongr₂ (· ++ ·) (kongr₂ (· ++ ·) (ruE_orte c) (ruE_orte a)) (ruE_orte b)
  | _, _, _, .eng e _ _ s => kongr₂ (· ++ ·) (ruE_orte e) (ruE_orte s)
  | _, _, _, .intBuiltin1 _ a => ruE_orte a
  | _, _, _, .intBuiltin2 _ a b => kongr₂ (· ++ ·) (ruE_orte a) (ruE_orte b)
  | _, _, _, .count _ body => ruE_orte body

theorem ruN_orte : ∀ {Γ : Ctx} {Λ : List (Res D)} {c : Option Ty}
    (n : NutzlastExpr D Γ Λ c), (ruN n).orte = n.orte
  | _, _, _, .empty => rfl
  | _, _, _, .val e => ruE_orte e

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

theorem ptrPre_mitRuhe_orte (P : Programm D) (n : Nat) :
    (P.mitRuhe.ptrVertrag (n + 1)).pre.orte = (P.ptrVertrag n).pre.orte :=
  (umΛ_orte _ _).trans (ruE_orte _)

theorem ptrPost_mitRuhe_orte (P : Programm D) (n : Nat) :
    (P.mitRuhe.ptrVertrag (n + 1)).post.orte = (P.ptrVertrag n).post.orte :=
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

end Gabbro.Grammatik
