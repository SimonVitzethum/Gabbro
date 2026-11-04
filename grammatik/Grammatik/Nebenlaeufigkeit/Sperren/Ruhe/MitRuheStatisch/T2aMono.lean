module
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheStatisch.T2a
@[expose] public section
namespace Gabbro.Grammatik
variable {D : Deklaration}
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
  | _, _, _, _, .axiomCallElse _ _ _ _ _ _ _ _ err, h => mE_mono hle err h
  | _, _, _, _, .assignSlot .., _ => rfl
  | _, _, _, _, .assignThru .., _ | _, _, _, _, .assignThruOwn .., _ | _, _, _, _, .assignSlotRef .., _ => rfl
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
  | _, _, _, _, .bindAxiomOpt _ _ _ _ _ _ _ rest, h => mB_mono hle rest h
  | _, _, _, _, .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest, h => by
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
  | _, _, _, .bindAxiomOpt _ _ _ _ _ _ _ rest, h => mE_mono hle rest h
  | _, _, _, .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest, h => by
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

  | _, _, _, .float _ _ _ _ _ rest, h => mE_mono hle rest h
  | _, _, _, .floatLit _ _ _ rest, h => mE_mono hle rest h
  | _, _, _, .floatOf _ _ _ rest, h => mE_mono hle rest h
  | _, _, _, .floatNarrow _ _ _ sonst rest, h => by
      simp only [mE, Bool.and_eq_true] at h ⊢; exact ⟨mE_mono hle sonst h.1, mE_mono hle rest h.2⟩
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
