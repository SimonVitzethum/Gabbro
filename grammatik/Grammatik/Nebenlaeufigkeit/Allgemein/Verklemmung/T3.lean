/- Part 3 of 3 of `Verklemmung` (split by instrumente/teile/lean-teilen.py; the umbrella `Verklemmung.lean` imports all parts). -/
import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung.T2

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Stufen

variable (A : Merkmal D) (hr : ∀ g, A.ruf g = true) (hi : ∀ n, A.ind n = true)
  (b : Option Int) (hs : ∀ L, UeberB b L → A.sperre L = true)

include hr hi hs in
mutual

theorem mS_boden {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → Stmt.BodenOk b s → mS A s = true
  | .ite _ t e, h => by
      simp only [mS, Bool.and_eq_true]
      exact ⟨mB_boden t fun c hc => by have := h c hc; simp_all [Stmt.ueberBoden],
        mB_boden e fun c hc => by have := h c hc; simp_all [Stmt.ueberBoden]⟩
  | .onOption _ p a, h => by
      simp only [mS, Bool.and_eq_true]
      exact ⟨mB_boden p fun c hc => by have := h c hc; simp_all [Stmt.ueberBoden],
        mB_boden a fun c hc => by have := h c hc; simp_all [Stmt.ueberBoden]⟩
  | .onTag _ arms, h => by
      simp only [mS]
      exact mArms_boden arms fun c hc => by have := h c hc; simp_all [Stmt.ueberBoden]
  | .onWhy _ arms, h => by
      simp only [mS]
      exact mGArms_boden arms fun c hc => by have := h c hc; simp_all [Stmt.ueberBoden]
  | .call g _ _ _, _ => by simp only [mS]; exact hr g
  | .callInd (n := n) _ _ _ _, _ => by simp only [mS]; exact hi n
  | .locks L _ body, h => by
      simp only [mS, Bool.and_eq_true]
      refine ⟨hs L fun c hc => ?_, mB_boden body fun c hc => ?_⟩
      · have := h c hc; simp only [Stmt.ueberBoden, Bool.and_eq_true, decide_eq_true_eq] at this
        exact this.1
      · have := h c hc; simp only [Stmt.ueberBoden, Bool.and_eq_true] at this
        exact this.2
  | .breaking _ body, h => by
      simp only [mS]
      exact mB_boden body fun c hc => by have := h c hc; simp_all [Stmt.ueberBoden]
  | .traverse _ _ body, h => by
      simp only [mS]
      exact mB_boden body fun c hc => by have := h c hc; simp_all [Stmt.ueberBoden]
  | .retry _ _ body ueber, h => by
      simp only [mS, Bool.and_eq_true]
      exact ⟨mB_boden body fun c hc => by have := h c hc; simp_all [Stmt.ueberBoden],
        mB_boden ueber fun c hc => by have := h c hc; simp_all [Stmt.ueberBoden]⟩
  | .forever _ _ body, h => by
      simp only [mS]
      exact mB_boden body fun c hc => by have := h c hc; simp_all [Stmt.ueberBoden]
  | .assignSlot .., _ => rfl
  | .assignThru .., _ => rfl
  | .assignGlob .., _ => rfl
  | .putBytes .., _ => rfl
  | .assignVar .., _ => rfl
  | .shift .., _ => rfl
  | .axiomCall .., _ => rfl
  | .regWrite .., _ => rfl
  | .transition .., _ => rfl
  | .publish .., _ => rfl
  | .advances .., _ => rfl
  | .retires .., _ => rfl
  | .ret .., _ => rfl
  | .retWhy .., _ => rfl
  | .leave _, _ => rfl
  | .next _, _ => rfl

theorem mB_boden {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (bl : Block D V l Γ Λ Λ') → Block.BodenOk b bl → mB A bl = true
  | .nil, _ => rfl
  | .cons s rest, h => by
      simp only [mB, Bool.and_eq_true]
      exact ⟨mS_boden s fun c hc => by have := h c hc; simp_all [Block.ueberBoden],
        mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]⟩
  | .bind _ rest, h => by
      simp only [mB]
      exact mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]
  | .bindCall g _ _ _ _ rest, h => by
      simp only [mB, Bool.and_eq_true]
      exact ⟨hr g, mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]⟩
  | .bindCallInd (n := n) _ _ _ _ _ rest, h => by
      simp only [mB, Bool.and_eq_true]
      exact ⟨hi n, mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]⟩
  | .bindCallElse g _ _ _ _ err rest, h => by
      simp only [mB, Bool.and_eq_true]
      exact ⟨⟨hr g, mE_boden err fun c hc => by have := h c hc; simp_all [Block.ueberBoden]⟩,
        mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]⟩
  | .bindAxiom _ _ _ _ _ _ _ rest, h => by
      simp only [mB]
      exact mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest, h => by
      simp only [mB, Bool.and_eq_true]
      exact ⟨mE_boden err fun c hc => by have := h c hc; simp_all [Block.ueberBoden],
        mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]⟩
  | .regRead _ _ rest, h => by
      simp only [mB]
      exact mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]
  | .regReadElse _ _ _ sonst rest, h => by
      simp only [mB, Bool.and_eq_true]
      exact ⟨mE_boden sonst fun c hc => by have := h c hc; simp_all [Block.ueberBoden],
        mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]⟩
  | .awaits _ _ _ _ rest, h => by
      simp only [mB]
      exact mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]
  | .exchange _ _ _ _ rest, h => by
      simp only [mB]
      exact mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]
  | .narrow _ _ _ sonst rest, h => by
      simp only [mB, Bool.and_eq_true]
      exact ⟨mE_boden sonst fun c hc => by have := h c hc; simp_all [Block.ueberBoden],
        mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]⟩
  | .check _ sonst rest, h => by
      simp only [mB, Bool.and_eq_true]
      exact ⟨mE_boden sonst fun c hc => by have := h c hc; simp_all [Block.ueberBoden],
        mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]⟩
  | .float _ _ _ _ _ rest, h => by
      simp only [mB]
      exact mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]
  | .floatLit _ _ _ rest, h => by
      simp only [mB]
      exact mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]
  | .floatOf _ _ _ rest, h => by
      simp only [mB]
      exact mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]
  | .floatNarrow _ _ _ sonst rest, h => by
      simp only [mB, Bool.and_eq_true]
      exact ⟨mE_boden sonst fun c hc => by have := h c hc; simp_all [Block.ueberBoden],
        mB_boden rest fun c hc => by have := h c hc; simp_all [Block.ueberBoden]⟩

theorem mArms_boden {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    (a : Arms D V l Γ Λ Λ' cs) → Arms.BodenOk b a → mArms A a = true
  | .nil, _ => rfl
  | .cons bl rest, h => by
      simp only [mArms, Bool.and_eq_true]
      exact ⟨mB_boden bl fun c hc => by have := h c hc; simp_all [Arms.ueberBoden],
        mArms_boden rest fun c hc => by have := h c hc; simp_all [Arms.ueberBoden]⟩

theorem mGArms_boden {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    (a : GrundArms D V l Γ Λ Λ' n) → GrundArms.BodenOk b a → mGArms A a = true
  | .nil, _ => rfl
  | .cons bl rest, h => by
      simp only [mGArms, Bool.and_eq_true]
      exact ⟨mB_boden bl fun c hc => by have := h c hc; simp_all [GrundArms.ueberBoden],
        mGArms_boden rest fun c hc => by have := h c hc; simp_all [GrundArms.ueberBoden]⟩

theorem mE_boden {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (e : Endblock D V l Γ Λ) → Endblock.BodenOk b e → mE A e = true
  | .ret .., _ => rfl
  | .retWhy .., _ => rfl
  | .leave _, _ => rfl
  | .next _, _ => rfl
  | .cons s rest, h => by
      simp only [mE, Bool.and_eq_true]
      exact ⟨mS_boden s fun c hc => by have := h c hc; simp_all [Endblock.ueberBoden],
        mE_boden rest fun c hc => by have := h c hc; simp_all [Endblock.ueberBoden]⟩
  | .bind _ rest, h => by
      simp only [mE]
      exact mE_boden rest fun c hc => by have := h c hc; simp_all [Endblock.ueberBoden]
  | .bindCall g _ _ _ _ rest, h => by
      simp only [mE, Bool.and_eq_true]
      exact ⟨hr g, mE_boden rest fun c hc => by have := h c hc; simp_all [Endblock.ueberBoden]⟩
  | .bindCallElse g _ _ _ _ err rest, h => by
      simp only [mE, Bool.and_eq_true]
      exact ⟨⟨hr g, mE_boden err fun c hc => by have := h c hc; simp_all [Endblock.ueberBoden]⟩,
        mE_boden rest fun c hc => by have := h c hc; simp_all [Endblock.ueberBoden]⟩
  | .bindAxiom _ _ _ _ _ _ _ rest, h => by
      simp only [mE]
      exact mE_boden rest fun c hc => by have := h c hc; simp_all [Endblock.ueberBoden]
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest, h => by
      simp only [mE, Bool.and_eq_true]
      exact ⟨mE_boden err fun c hc => by have := h c hc; simp_all [Endblock.ueberBoden],
        mE_boden rest fun c hc => by have := h c hc; simp_all [Endblock.ueberBoden]⟩

end

end Stufen
/-- **The model's floor discipline `StufenOk` gives the residue form**: the
    floors on the bodies. -/
theorem stufenM_of_ok {P : Programm D} (h : StufenOk P) : StufenM P := by
  intro f
  refine mE_boden (bodenM f) (fun _ => rfl) (fun _ => rfl) (bodenF f) (fun L hL => ?_) _
    (fun c hc => h f c hc)
  unfold bodenM
  cases hb : bodenF f with
  | none => rfl
  | some c => exact decide_eq_true (hL c hb)

#print axioms Gabbro.Grammatik.stufenM_of_ok
#print axioms Gabbro.Grammatik.rangInvG_erreichbar
#print axioms Gabbro.Grammatik.sperre_rang
#print axioms Gabbro.Grammatik.schritt_an_sperre
#print axioms Gabbro.Grammatik.keine_verklemmungG
#print axioms Gabbro.Grammatik.keine_verklemmungG'


end Gabbro.Grammatik
