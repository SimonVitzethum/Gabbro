module
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheStatisch.T2aMono
@[expose] public section
namespace Gabbro.Grammatik
variable {D : Deklaration}
/-! ## 8b. Two feature tests at once (Opus agent H, 2026-09-26) -/

/-- The feature set admitting what BOTH `A` and `B` admit. -/
def mUnd (A B : Merkmal D) : Merkmal D :=
  ⟨fun f => A.ruf f && B.ruf f, fun n => A.ind n && B.ind n, fun L => A.sperre L && B.sperre L⟩

section Und

variable {A B : Merkmal D}

mutual

theorem mS_und {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ'), mS A s = true → mS B s = true → mS (mUnd A B) s = true
  | _, _, _, _, .ite _ t e, h, h' => by
      simp only [mS, Bool.and_eq_true] at h h' ⊢
      exact ⟨mB_und t h.1 h'.1, mB_und e h.2 h'.2⟩
  | _, _, _, _, .onOption _ p a, h, h' => by
      simp only [mS, Bool.and_eq_true] at h h' ⊢
      exact ⟨mB_und p h.1 h'.1, mB_und a h.2 h'.2⟩
  | _, _, _, _, .onTag _ arms, h, h' => mArms_und arms h h'
  | _, _, _, _, .onWhy _ arms, h, h' => mGArms_und arms h h'
  | _, _, _, _, .call g .., h, h' => by
      simp only [mS, mUnd, Bool.and_eq_true] at h h' ⊢; exact ⟨h, h'⟩
  | _, _, _, _, .callInd (n := n) .., h, h' => by
      simp only [mS, mUnd, Bool.and_eq_true] at h h' ⊢; exact ⟨h, h'⟩
  | _, _, _, _, .locks L _ body, h, h' => by
      simp only [mS, mUnd, Bool.and_eq_true] at h h' ⊢
      exact ⟨⟨h.1, h'.1⟩, mB_und body h.2 h'.2⟩
  | _, _, _, _, .breaking _ body, h, h' => mB_und body h h'
  | _, _, _, _, .traverse _ _ body, h, h' => mB_und body h h'
  | _, _, _, _, .retry _ _ body ueber, h, h' => by
      simp only [mS, Bool.and_eq_true] at h h' ⊢
      exact ⟨mB_und body h.1 h'.1, mB_und ueber h.2 h'.2⟩
  | _, _, _, _, .forever _ _ body, h, h' => mB_und body h h'
  | _, _, _, _, .assignSlot .., _, _ => rfl
  | _, _, _, _, .assignThru .., _, _ | _, _, _, _, .assignSlotRef .., _, _ => rfl
  | _, _, _, _, .assignGlob .., _, _ => rfl
  | _, _, _, _, .putBytes .., _, _ => rfl
  | _, _, _, _, .assignVar .., _, _ => rfl
  | _, _, _, _, .shift .., _, _ => rfl
  | _, _, _, _, .axiomCall .., _, _ => rfl
  | _, _, _, _, .axiomCallElse _ _ _ _ _ _ _ _ err, h, h' => by
      simp only [mS] at h h' ⊢
      exact mE_und err h h'
  | _, _, _, _, .regWrite .., _, _ => rfl
  | _, _, _, _, .transition .., _, _ => rfl
  | _, _, _, _, .publish .., _, _ => rfl
  | _, _, _, _, .advances .., _, _ => rfl
  | _, _, _, _, .retires .., _, _ => rfl
  | _, _, _, _, .ret .., _, _ => rfl
  | _, _, _, _, .retWhy .., _, _ => rfl
  | _, _, _, _, .leave _, _, _ => rfl
  | _, _, _, _, .next _, _, _ => rfl

theorem mB_und {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ'), mB A b = true → mB B b = true → mB (mUnd A B) b = true
  | _, _, _, _, .nil, _, _ => rfl
  | _, _, _, _, .cons s rest, h, h' => by
      simp only [mB, Bool.and_eq_true] at h h' ⊢
      exact ⟨mS_und s h.1 h'.1, mB_und rest h.2 h'.2⟩
  | _, _, _, _, .bind _ rest, h, h' => mB_und rest h h'
  | _, _, _, _, .bindCall g _ _ _ _ rest, h, h' => by
      simp only [mB, mUnd, Bool.and_eq_true] at h h' ⊢
      exact ⟨⟨h.1, h'.1⟩, mB_und rest h.2 h'.2⟩
  | _, _, _, _, .bindCallInd (n := n) _ _ _ _ _ rest, h, h' => by
      simp only [mB, mUnd, Bool.and_eq_true] at h h' ⊢
      exact ⟨⟨h.1, h'.1⟩, mB_und rest h.2 h'.2⟩
  | _, _, _, _, .bindCallElse g _ _ _ _ err rest, h, h' => by
      simp only [mB, mUnd, Bool.and_eq_true] at h h' ⊢
      exact ⟨⟨⟨h.1.1, h'.1.1⟩, mE_und err h.1.2 h'.1.2⟩, mB_und rest h.2 h'.2⟩
  | _, _, _, _, .bindAxiom _ _ _ _ _ _ _ rest, h, h' => mB_und rest h h'
  | _, _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest, h, h' => by
      simp only [mB, mUnd, Bool.and_eq_true] at h h' ⊢
      exact ⟨mE_und err h.1 h'.1, mB_und rest h.2 h'.2⟩
  | _, _, _, _, .bindAxiomOpt _ _ _ _ _ _ _ rest, h, h' => mB_und rest h h'
  | _, _, _, _, .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest, h, h' => by
      simp only [mB, mUnd, Bool.and_eq_true] at h h' ⊢
      exact ⟨mE_und err h.1 h'.1, mB_und rest h.2 h'.2⟩
  | _, _, _, _, .regRead _ _ rest, h, h' => mB_und rest h h'
  | _, _, _, _, .regReadElse _ _ _ sonst rest, h, h' => by
      simp only [mB, Bool.and_eq_true] at h h' ⊢
      exact ⟨mE_und sonst h.1 h'.1, mB_und rest h.2 h'.2⟩
  | _, _, _, _, .awaits _ _ _ _ _ rest, h, h' => mB_und rest h h'
  | _, _, _, _, .exchange _ _ _ _ rest, h, h' => mB_und rest h h'
  | _, _, _, _, .narrow _ _ _ sonst rest, h, h' => by
      simp only [mB, Bool.and_eq_true] at h h' ⊢
      exact ⟨mE_und sonst h.1 h'.1, mB_und rest h.2 h'.2⟩
  | _, _, _, _, .check _ sonst rest, h, h' => by
      simp only [mB, Bool.and_eq_true] at h h' ⊢
      exact ⟨mE_und sonst h.1 h'.1, mB_und rest h.2 h'.2⟩
  | _, _, _, _, .float _ _ _ _ _ rest, h, h' => mB_und rest h h'
  | _, _, _, _, .floatLit _ _ _ rest, h, h' => mB_und rest h h'
  | _, _, _, _, .floatOf _ _ _ rest, h, h' => mB_und rest h h'
  | _, _, _, _, .floatNarrow _ _ _ sonst rest, h, h' => by
      simp only [mB, Bool.and_eq_true] at h h' ⊢
      exact ⟨mE_und sonst h.1 h'.1, mB_und rest h.2 h'.2⟩

theorem mE_und {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ), mE A e = true → mE B e = true → mE (mUnd A B) e = true
  | _, _, _, .ret .., _, _ => rfl
  | _, _, _, .retWhy .., _, _ => rfl
  | _, _, _, .leave _, _, _ => rfl
  | _, _, _, .next _, _, _ => rfl
  | _, _, _, .cons s rest, h, h' => by
      simp only [mE, Bool.and_eq_true] at h h' ⊢
      exact ⟨mS_und s h.1 h'.1, mE_und rest h.2 h'.2⟩
  | _, _, _, .bind _ rest, h, h' => mE_und rest h h'
  | _, _, _, .bindCall g _ _ _ _ rest, h, h' => by
      simp only [mE, mUnd, Bool.and_eq_true] at h h' ⊢
      exact ⟨⟨h.1, h'.1⟩, mE_und rest h.2 h'.2⟩
  | _, _, _, .bindCallElse g _ _ _ _ err rest, h, h' => by
      simp only [mE, mUnd, Bool.and_eq_true] at h h' ⊢
      exact ⟨⟨⟨h.1.1, h'.1.1⟩, mE_und err h.1.2 h'.1.2⟩, mE_und rest h.2 h'.2⟩
  | _, _, _, .bindAxiom _ _ _ _ _ _ _ rest, h, h' => mE_und rest h h'
  | _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest, h, h' => by
      simp only [mE, mUnd, Bool.and_eq_true] at h h' ⊢
      exact ⟨mE_und err h.1 h'.1, mE_und rest h.2 h'.2⟩
  | _, _, _, .bindAxiomOpt _ _ _ _ _ _ _ rest, h, h' => mE_und rest h h'
  | _, _, _, .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest, h, h' => by
      simp only [mE, mUnd, Bool.and_eq_true] at h h' ⊢
      exact ⟨mE_und err h.1 h'.1, mE_und rest h.2 h'.2⟩
  | _, _, _, .regRead _ _ rest, h, h' => mE_und rest h h'
  | _, _, _, .regReadElse _ _ _ sonst rest, h, h' => by
      simp only [mE, Bool.and_eq_true] at h h' ⊢
      exact ⟨mE_und sonst h.1 h'.1, mE_und rest h.2 h'.2⟩
  | _, _, _, .awaits _ _ _ _ _ rest, h, h' => mE_und rest h h'
  | _, _, _, .bindCallInd (n := n) _ _ _ _ _ rest, h, h' => by
      simp only [mE, mUnd, Bool.and_eq_true] at h h' ⊢
      exact ⟨⟨h.1, h'.1⟩, mE_und rest h.2 h'.2⟩
  | _, _, _, .narrow _ _ _ sonst rest, h, h' => by
      simp only [mE, Bool.and_eq_true] at h h' ⊢
      exact ⟨mE_und sonst h.1 h'.1, mE_und rest h.2 h'.2⟩
  | _, _, _, .exchange _ _ _ _ rest, h, h' => mE_und rest h h'
  | _, _, _, .ite _ t e, h, h' => by
      simp only [mE, Bool.and_eq_true] at h h' ⊢
      exact ⟨mE_und t h.1 h'.1, mE_und e h.2 h'.2⟩

theorem mArms_und {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs),
    mArms A arms = true → mArms B arms = true → mArms (mUnd A B) arms = true
  | _, _, _, _, _, .nil, _, _ => rfl
  | _, _, _, _, _, .cons b rest, h, h' => by
      simp only [mArms, Bool.and_eq_true] at h h' ⊢
      exact ⟨mB_und b h.1 h'.1, mArms_und rest h.2 h'.2⟩

theorem mGArms_und {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n),
    mGArms A arms = true → mGArms B arms = true → mGArms (mUnd A B) arms = true
  | _, _, _, _, _, .nil, _, _ => rfl
  | _, _, _, _, _, .cons b rest, h, h' => by
      simp only [mGArms, Bool.and_eq_true] at h h' ⊢
      exact ⟨mB_und b h.1 h'.1, mGArms_und rest h.2 h'.2⟩

end

end Und
/-! ## 9. The program `P.mitRuhe`: bodies, footprints -/

section Programm

variable (P : Programm D)

theorem rumpf_mitRuhe_orteP (f : D.Fn) :
    endblockOrteP P.mitRuhe (P.mitRuhe.rumpf (some f)) = endblockOrteP P (P.rumpf f) :=
  (orteP_umΛ _ _ _).trans (ruEnd_orteP P _)

theorem rumpf_mitRuhe_regs (f : D.Fn) :
    (P.mitRuhe.rumpf (some f)).regs = (P.rumpf f).regs :=
  (regs_umΛ _ _).trans (ruEnd_regs _)

theorem rumpf_mitRuhe_mE (A : Merkmal D.mitRuhe) (f : D.Fn) :
    mE A (P.mitRuhe.rumpf (some f)) = mE (mZ A) (P.rumpf f) :=
  (mE_umΛ _ _ _).trans (ruEnd_mE A _)

theorem rumpf_mitRuhe_gOk (K : Nat → Bool) (Rg : D.Reg → Bool) (f : D.Fn) :
    Endblock.gOk (D := D.mitRuhe) K Rg (P.mitRuhe.rumpf (some f)) = (P.rumpf f).gOk (kZ K) Rg :=
  (gOk_umΛ _ _ _ _).trans (ruEnd_gOk K Rg _)

theorem invOrteP_mitRuhe (f : D.Fn) : invOrteP P.mitRuhe (some f) = invOrteP P f :=
  congrArg (fun g => (D.invs.filter (schuldet f)).flatMap g)
    (funext fun i => invariante_mitRuhe_orte P i)

theorem invOrteP_mitRuhe_ruhe : invOrteP P.mitRuhe none = [] := by
  unfold invOrteP
  have : (D.mitRuhe).invs.filter (schuldet (D := D.mitRuhe) none) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro i _
    simp only [schuldet, Deklaration.mitRuhe, Deklaration.schreibt, Deklaration.signatur, sigNrM, sigM, sigRuheM,
  List.any_eq_true, Bool.false_eq_true, and_false, exists_false, not_false_eq_true]
  rw [this]
  rfl

theorem fussOrte_mitRuhe (f : D.Fn) : fussOrte P.mitRuhe (some f) = fussOrte P f := by
  unfold fussOrte
  rw [requires_mitRuhe_orte, ensures_mitRuhe_orte, rumpf_mitRuhe_orteP, invOrteP_mitRuhe] <;> rfl

theorem fussOrte_mitRuhe_ruhe : fussOrte P.mitRuhe none = [] := by
  unfold fussOrte
  rw [invOrteP_mitRuhe_ruhe]
  rfl

theorem fussOrteG_mitRuhe (f : D.Fn) : fussOrteG P.mitRuhe (some f) = fussOrteG P f := by
  unfold fussOrteG
  rw [fussOrte_mitRuhe, rumpf_mitRuhe_regs] <;> rfl

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

end Gabbro.Grammatik
