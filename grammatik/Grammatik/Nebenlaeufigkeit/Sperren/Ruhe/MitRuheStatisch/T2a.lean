/- Part 2 of 3 of `MitRuheStatisch` (split by instrumente/teile/lean-teilen.py; the umbrella `MitRuheStatisch.lean` imports all parts). -/
module
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheStatisch.T1
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

mutual

theorem ruS_mS (A : Merkmal D.mitRuhe) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ'), mS A (ruS s) = mS (mZ A) s
  | _, _, _, _, .assignSlot .. => rfl
  | _, _, _, _, .assignThru .. | _, _, _, _, .assignSlotRef .. => rfl
  | _, _, _, _, .assignGlob .. => rfl
  | _, _, _, _, .putBytes .. => rfl
  | _, _, _, _, .assignVar .. => rfl
  | _, _, _, _, .shift .. => rfl
  | _, _, _, _, .ite _ t e => kongr₂ (· && ·) (ruB_mB A t) (ruB_mB A e)
  | _, _, _, _, .onOption _ p a => kongr₂ (· && ·) (ruB_mB A p) (ruB_mB A a)
  | _, _, _, _, .onTag _ arms => ruArms_mArms A arms
  | _, _, _, _, .onWhy _ arms => ruGArms_mGArms A arms
  | _, _, _, _, .call .. => mS_nachΛ _ _ _
  | _, _, _, _, .callInd .. => mS_nachΛ _ _ _
  | _, _, _, _, .callIndElse (n := n) _ _ _ _ _ err =>
      (mS_nachΛ _ _ _).trans (kongr₂ (· && ·) rfl ((mE_umΛ _ _ _).trans (ruEnd_mE A err)))
  | _, _, _, _, .locks L _ body => congrArg (A.sperre L && ·) (ruB_mB A body)
  | _, _, _, _, .breaking _ body => ruB_mB A body
  | _, _, _, _, .traverse _ _ body => ruB_mB A body
  | _, _, _, _, .consumeTraverse _ _ _ _ _ _ body => ruB_mB A body
  | _, _, _, _, .retry _ _ body ueber => kongr₂ (· && ·) (ruB_mB A body) (ruB_mB A ueber)
  | _, _, _, _, .forever _ _ body => ruB_mB A body
  | _, _, _, _, .axiomCall .. => rfl
  | _, _, _, _, .regWrite .. => rfl
  | _, _, _, _, .transition .. => rfl
  | _, _, _, _, .publish .. => rfl
  | _, _, _, _, .advances .. => mS_nachΛ _ _ _
  | _, _, _, _, .retires .. => mS_nachΛ _ _ _
  | _, _, _, _, .ret .. => rfl
  | _, _, _, _, .retWhy .. => rfl
  | _, _, _, _, .retScoped .. => rfl
  | _, _, _, _, .retWhyScoped .. => rfl
  | _, _, _, _, .leave _ => rfl
  | _, _, _, _, .next _ => rfl

theorem ruB_mB (A : Merkmal D.mitRuhe) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ'), mB A (ruB b) = mB (mZ A) b
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons s rest => kongr₂ (· && ·) (ruS_mS A s) (ruB_mB A rest)
  | _, _, _, _, .bind _ rest => ruB_mB A rest
  | _, _, _, _, .bindCall g _ _ _ _ rest =>
      congrArg (A.ruf (some g) && ·) ((mB_vorΛ _ _ _).trans (ruB_mB A rest))
  | _, _, _, _, .bindCallInd (n := n) _ _ _ _ _ rest =>
      congrArg (A.ind (n + 1) && ·) ((mB_vorΛ _ _ _).trans (ruB_mB A rest))
  | _, _, _, _, .bindCallIndElse (n := n) _ _ _ _ _ err rest =>
      kongr₂ (fun x y => A.ind (n + 1) && x && y) ((mE_umΛ _ _ _).trans (ruEnd_mE A err))
        ((mB_vorΛ _ _ _).trans (ruB_mB A rest))
  | _, _, _, _, .bindCallElse g _ _ _ _ err rest =>
      kongr₂ (fun x y => A.ruf (some g) && x && y) ((mE_umΛ _ _ _).trans (ruEnd_mE A err))
        ((mB_vorΛ _ _ _).trans (ruB_mB A rest))
  | _, _, _, _, .bindAxiom _ _ _ _ _ _ _ rest => ruB_mB A rest
  | _, _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest =>
      kongr₂ (· && ·) (ruEnd_mE A err) (ruB_mB A rest)
  | _, _, _, _, .regRead _ _ rest => ruB_mB A rest
  | _, _, _, _, .regReadElse _ _ _ sonst rest =>
      kongr₂ (· && ·) (ruEnd_mE A sonst) (ruB_mB A rest)
  | _, _, _, _, .awaits _ _ _ _ _ rest => ruB_mB A rest
  | _, _, _, _, .exchange _ _ _ _ rest => ruB_mB A rest
  | _, _, _, _, .narrow _ _ _ sonst rest => kongr₂ (· && ·) (ruEnd_mE A sonst) (ruB_mB A rest)
  | _, _, _, _, .narrowRequired _ _ _ rest => ruB_mB A rest
  | _, _, _, _, .check _ sonst rest => kongr₂ (· && ·) (ruEnd_mE A sonst) (ruB_mB A rest)
  | _, _, _, _, .float _ _ _ _ _ rest => ruB_mB A rest
  | _, _, _, _, .floatLit _ _ _ rest => ruB_mB A rest
  | _, _, _, _, .floatOf _ _ _ rest => ruB_mB A rest
  | _, _, _, _, .floatNarrow _ _ _ sonst rest =>
      kongr₂ (· && ·) (ruEnd_mE A sonst) (ruB_mB A rest)

theorem ruEnd_mE (A : Merkmal D.mitRuhe) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (e : Endblock D V l Γ Λ), mE A (ruEnd e) = mE (mZ A) e
  | _, _, _, .ret .. => rfl
  | _, _, _, .retWhy .. => rfl
  | _, _, _, .retScoped .. => rfl
  | _, _, _, .retWhyScoped .. => rfl
  | _, _, _, .leave _ => rfl
  | _, _, _, .next _ => rfl
  | _, _, _, .cons s rest => kongr₂ (· && ·) (ruS_mS A s) (ruEnd_mE A rest)
  | _, _, _, .bind _ rest => ruEnd_mE A rest
  | _, _, _, .bindCall g _ _ _ _ rest =>
      congrArg (A.ruf (some g) && ·) ((mE_umΛ _ _ _).trans (ruEnd_mE A rest))
  | _, _, _, .bindCallElse g _ _ _ _ err rest =>
      kongr₂ (fun x y => A.ruf (some g) && x && y) ((mE_umΛ _ _ _).trans (ruEnd_mE A err))
        ((mE_umΛ _ _ _).trans (ruEnd_mE A rest))
  | _, _, _, .bindAxiom _ _ _ _ _ _ _ rest => ruEnd_mE A rest
  | _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest =>
      kongr₂ (· && ·) (ruEnd_mE A err) (ruEnd_mE A rest)
  | _, _, _, .regRead _ _ rest => ruEnd_mE A rest
  | _, _, _, .regReadElse _ _ _ sonst rest =>
      kongr₂ (· && ·) (ruEnd_mE A sonst) (ruEnd_mE A rest)
  | _, _, _, .awaits _ _ _ _ _ rest => ruEnd_mE A rest
  | _, _, _, .bindCallInd (n := n) _ _ _ _ _ rest =>
      congrArg (A.ind (n + 1) && ·) ((mE_umΛ _ _ _).trans (ruEnd_mE A rest))
  | _, _, _, .bindCallIndElse (n := n) _ _ _ _ _ err rest =>
      kongr₂ (fun x y => A.ind (n + 1) && x && y) ((mE_umΛ _ _ _).trans (ruEnd_mE A err))
        ((mE_umΛ _ _ _).trans (ruEnd_mE A rest))
  | _, _, _, .narrow _ _ _ sonst rest => kongr₂ (· && ·) (ruEnd_mE A sonst) (ruEnd_mE A rest)
  | _, _, _, .narrowRequired _ _ _ rest => ruEnd_mE A rest
  | _, _, _, .exchange _ _ _ _ rest => ruEnd_mE A rest
  | _, _, _, .ite _ t e => kongr₂ (· && ·) (ruEnd_mE A t) (ruEnd_mE A e)

theorem ruArms_mArms (A : Merkmal D.mitRuhe) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs),
    mArms A (ruArms arms) = mArms (mZ A) arms
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons (c := none) b rest => kongr₂ (· && ·) (ruB_mB A b) (ruArms_mArms A rest)
  | _, _, _, _, _, .cons (c := some _) b rest =>
      kongr₂ (· && ·) (ruB_mB A b) (ruArms_mArms A rest)

theorem ruGArms_mGArms (A : Merkmal D.mitRuhe) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n),
    mGArms A (ruGArms arms) = mGArms (mZ A) arms
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons b rest => kongr₂ (· && ·) (ruB_mB A b) (ruGArms_mGArms A rest)

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
  | _, _, _, _, .onWhy _ arms, h => mGArms_mono hle arms h
  | _, _, _, _, .call g .., h => hle.1 g h
  | _, _, _, _, .callInd (n := n) .., h => hle.2.1 n h
  | _, _, _, _, .callIndElse (n := n) _ _ _ _ _ err, h => by
      simp only [mS, Bool.and_eq_true] at h ⊢
      exact ⟨hle.2.1 n h.1, mE_mono hle err h.2⟩
  | _, _, _, _, .locks L _ body, h => by
      simp only [mS, Bool.and_eq_true] at h ⊢; exact ⟨hle.2.2 L h.1, mB_mono hle body h.2⟩
  | _, _, _, _, .breaking _ body, h => mB_mono hle body h
  | _, _, _, _, .traverse _ _ body, h => mB_mono hle body h
  | _, _, _, _, .consumeTraverse _ _ _ _ _ _ body, h => mB_mono hle body h
  | _, _, _, _, .retry _ _ body ueber, h => by
      simp only [mS, Bool.and_eq_true] at h ⊢; exact ⟨mB_mono hle body h.1, mB_mono hle ueber h.2⟩
  | _, _, _, _, .forever _ _ body, h => mB_mono hle body h
  | _, _, _, _, .assignSlot .., _ => rfl
  | _, _, _, _, .assignThru .., _ | _, _, _, _, .assignSlotRef .., _ => rfl
  | _, _, _, _, .assignGlob .., _ => rfl
  | _, _, _, _, .putBytes .., _ => rfl
  | _, _, _, _, .assignVar .., _ => rfl
  | _, _, _, _, .shift .., _ => rfl
  | _, _, _, _, .axiomCall .., _ => rfl
  | _, _, _, _, .regWrite .., _ => rfl
  | _, _, _, _, .transition .., _ => rfl
  | _, _, _, _, .publish .., _ => rfl
  | _, _, _, _, .advances .., _ => rfl
  | _, _, _, _, .retires .., _ => rfl
  | _, _, _, _, .ret .., _ => rfl
  | _, _, _, _, .retWhy .., _ => rfl
  | _, _, _, _, .retScoped .., _ => rfl
  | _, _, _, _, .retWhyScoped .., _ => rfl
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
  | _, _, _, _, .bindCallIndElse (n := n) _ _ _ _ _ err rest, h => by
      simp only [mB, Bool.and_eq_true] at h ⊢
      exact ⟨⟨hle.2.1 n h.1.1, mE_mono hle err h.1.2⟩, mB_mono hle rest h.2⟩
  | _, _, _, _, .bindCallElse g _ _ _ _ err rest, h => by
      simp only [mB, Bool.and_eq_true] at h ⊢
      exact ⟨⟨hle.1 g h.1.1, mE_mono hle err h.1.2⟩, mB_mono hle rest h.2⟩
  | _, _, _, _, .bindAxiom _ _ _ _ _ _ _ rest, h => mB_mono hle rest h
  | _, _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest, h => by
      simp only [mB, Bool.and_eq_true] at h ⊢
      exact ⟨mE_mono hle err h.1, mB_mono hle rest h.2⟩
  | _, _, _, _, .regRead _ _ rest, h => mB_mono hle rest h
  | _, _, _, _, .regReadElse _ _ _ sonst rest, h => by
      simp only [mB, Bool.and_eq_true] at h ⊢; exact ⟨mE_mono hle sonst h.1, mB_mono hle rest h.2⟩
  | _, _, _, _, .awaits _ _ _ _ _ rest, h => mB_mono hle rest h
  | _, _, _, _, .exchange _ _ _ _ rest, h => mB_mono hle rest h
  | _, _, _, _, .narrow _ _ _ sonst rest, h => by
      simp only [mB, Bool.and_eq_true] at h ⊢; exact ⟨mE_mono hle sonst h.1, mB_mono hle rest h.2⟩
  | _, _, _, _, .narrowRequired _ _ _ rest, h => by
      simp only [mB] at h ⊢; exact mB_mono hle rest h
  | _, _, _, _, .check _ sonst rest, h => by
      simp only [mB, Bool.and_eq_true] at h ⊢; exact ⟨mE_mono hle sonst h.1, mB_mono hle rest h.2⟩
  | _, _, _, _, .float _ _ _ _ _ rest, h => mB_mono hle rest h
  | _, _, _, _, .floatLit _ _ _ rest, h => mB_mono hle rest h
  | _, _, _, _, .floatOf _ _ _ rest, h => mB_mono hle rest h
  | _, _, _, _, .floatNarrow _ _ _ sonst rest, h => by
      simp only [mB, Bool.and_eq_true] at h ⊢; exact ⟨mE_mono hle sonst h.1, mB_mono hle rest h.2⟩

theorem mE_mono (hle : MLe A A') {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ), mE A e = true → mE A' e = true
  | _, _, _, .ret .., _ => rfl
  | _, _, _, .retWhy .., _ => rfl
  | _, _, _, .retScoped .., _ => rfl
  | _, _, _, .retWhyScoped .., _ => rfl
  | _, _, _, .leave _, _ => rfl
  | _, _, _, .next _, _ => rfl
  | _, _, _, .cons s rest, h => by
      simp only [mE, Bool.and_eq_true] at h ⊢; exact ⟨mS_mono hle s h.1, mE_mono hle rest h.2⟩
  | _, _, _, .bind _ rest, h => mE_mono hle rest h
  | _, _, _, .bindCall g _ _ _ _ rest, h => by
      simp only [mE, Bool.and_eq_true] at h ⊢; exact ⟨hle.1 g h.1, mE_mono hle rest h.2⟩
  | _, _, _, .bindCallElse g _ _ _ _ err rest, h => by
      simp only [mE, Bool.and_eq_true] at h ⊢
      exact ⟨⟨hle.1 g h.1.1, mE_mono hle err h.1.2⟩, mE_mono hle rest h.2⟩
  | _, _, _, .bindAxiom _ _ _ _ _ _ _ rest, h => mE_mono hle rest h
  | _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest, h => by
      simp only [mE, Bool.and_eq_true] at h ⊢
      exact ⟨mE_mono hle err h.1, mE_mono hle rest h.2⟩
  | _, _, _, .regRead _ _ rest, h => mE_mono hle rest h
  | _, _, _, .regReadElse _ _ _ sonst rest, h => by
      simp only [mE, Bool.and_eq_true] at h ⊢; exact ⟨mE_mono hle sonst h.1, mE_mono hle rest h.2⟩
  | _, _, _, .awaits _ _ _ _ _ rest, h => mE_mono hle rest h
  | _, _, _, .bindCallInd (n := n) _ _ _ _ _ rest, h => by
      simp only [mE, Bool.and_eq_true] at h ⊢; exact ⟨hle.2.1 n h.1, mE_mono hle rest h.2⟩
  | _, _, _, .bindCallIndElse (n := n) _ _ _ _ _ err rest, h => by
      simp only [mE, Bool.and_eq_true] at h ⊢
      exact ⟨⟨hle.2.1 n h.1.1, mE_mono hle err h.1.2⟩, mE_mono hle rest h.2⟩
  | _, _, _, .narrow _ _ _ sonst rest, h => by
      simp only [mE, Bool.and_eq_true] at h ⊢; exact ⟨mE_mono hle sonst h.1, mE_mono hle rest h.2⟩
  | _, _, _, .narrowRequired _ _ _ rest, h => by
      simp only [mE] at h ⊢; exact mE_mono hle rest h
  | _, _, _, .exchange _ _ _ _ rest, h => mE_mono hle rest h
  | _, _, _, .ite _ t e, h => by
      simp only [mE, Bool.and_eq_true] at h ⊢; exact ⟨mE_mono hle t h.1, mE_mono hle e h.2⟩

theorem mArms_mono (hle : MLe A A') {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs),
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

end Gabbro.Grammatik
