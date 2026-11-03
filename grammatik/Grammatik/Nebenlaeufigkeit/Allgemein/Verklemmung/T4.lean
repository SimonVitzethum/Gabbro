/- Part 4 of 4 of `Verklemmung` (C11 split; pure move of the floor converse):
   the residue form gives back the model form (`StufenOk`). -/
module
public import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung.T2
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

section StufenUmkehr

variable (f : D.Fn)

mutual

/-- Every `locks` admitted by the floor feature respects the floor. -/
theorem mS_boden_inv {V : vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → mS (bodenM f) s = true → s.BodenOk (bodenF f)
  | .ite _ t e, h => by
      simp only [mS, Bool.and_eq_true] at h
      intro c hc
      simp only [Stmt.ueberBoden, Bool.and_eq_true]
      exact ⟨mB_boden_inv t h.1 c hc, mB_boden_inv e h.2 c hc⟩
  | .onOption _ p a, h => by
      simp only [mS, Bool.and_eq_true] at h
      intro c hc
      simp only [Stmt.ueberBoden, Bool.and_eq_true]
      exact ⟨mB_boden_inv p h.1 c hc, mB_boden_inv a h.2 c hc⟩
  | .onTag _ arms, h => by
      simp only [mS] at h
      intro c hc
      simp only [Stmt.ueberBoden]
      exact mArms_boden_inv arms h c hc
  | .onWhy _ arms, h => by
      simp only [mS] at h
      intro c hc
      simp only [Stmt.ueberBoden]
      exact mGArms_boden_inv arms h c hc
  | .call g _ _ _, _ => fun _ _ => rfl
  | .callInd (n := n) _ _ _ _, _ => fun _ _ => rfl
  | .callIndElse (n := n) _ _ _ _ _ err, h => by
      simp only [mS, Bool.and_eq_true] at h
      intro c hc
      simp only [Stmt.ueberBoden]
      exact mE_boden_inv err h.2 c hc
  | .locks L _ body, h => by
      simp only [mS, Bool.and_eq_true] at h
      obtain ⟨hL, hb⟩ := h
      intro c hc
      simp only [Stmt.ueberBoden, Bool.and_eq_true]
      exact ⟨decide_eq_true (bodenM_ueber hL c hc), mB_boden_inv body hb c hc⟩
  | .breaking _ body, h => by
      simp only [mS] at h
      intro c hc
      simp only [Stmt.ueberBoden]
      exact mB_boden_inv body h c hc
  | .traverse _ _ body, h => by
      simp only [mS] at h
      intro c hc
      simp only [Stmt.ueberBoden]
      exact mB_boden_inv body h c hc
  | .consumeTraverse _ _ _ _ _ _ body, h => by
      simp only [mS] at h
      intro c hc
      simp only [Stmt.ueberBoden]
      exact mB_boden_inv body h c hc
  | .retry _ _ body ueber, h => by
      simp only [mS, Bool.and_eq_true] at h
      intro c hc
      simp only [Stmt.ueberBoden, Bool.and_eq_true]
      exact ⟨mB_boden_inv body h.1 c hc, mB_boden_inv ueber h.2 c hc⟩
  | .forever _ _ body, h => by
      simp only [mS] at h
      intro c hc
      simp only [Stmt.ueberBoden]
      exact mB_boden_inv body h c hc
  | .assignSlot .., _ => fun _ _ => rfl
  | .assignThru .., _ | .assignSlotRef .., _ => fun _ _ => rfl
  | .assignGlob .., _ => fun _ _ => rfl
  | .putBytes .., _ => fun _ _ => rfl
  | .assignVar .., _ => fun _ _ => rfl
  | .shift .., _ => fun _ _ => rfl
  | .axiomCall .., _ => fun _ _ => rfl
  | .axiomCallElse _ _ _ _ _ _ _ _ err, h => by
      simp only [mS] at h
      intro c hc
      simp only [Stmt.ueberBoden]
      exact mE_boden_inv err h c hc
  | .regWrite .., _ => fun _ _ => rfl
  | .transition .., _ => fun _ _ => rfl
  | .publish .., _ => fun _ _ => rfl
  | .advances .., _ => fun _ _ => rfl
  | .retires .., _ => fun _ _ => rfl
  | .ret .., _ => fun _ _ => rfl
  | .retWhy .., _ => fun _ _ => rfl
  | .retScoped .., _ => fun _ _ => rfl
  | .retWhyScoped .., _ => fun _ _ => rfl
  | .leave _, _ => fun _ _ => rfl
  | .next _, _ => fun _ _ => rfl

theorem mB_boden_inv {V : vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (bl : Block D V l Γ Λ Λ') → mB (bodenM f) bl = true → bl.BodenOk (bodenF f)
  | .nil, _ => fun _ _ => rfl
  | .cons s rest, h => by
      simp only [mB, Bool.and_eq_true] at h
      intro c hc
      simp only [Block.ueberBoden, Bool.and_eq_true]
      exact ⟨mS_boden_inv s h.1 c hc, mB_boden_inv rest h.2 c hc⟩
  | .bind _ rest, h => by
      simp only [mB] at h
      intro c hc
      simp only [Block.ueberBoden]
      exact mB_boden_inv rest h c hc
  | .bindCall g _ _ _ _ rest, h => by
      simp only [mB, Bool.and_eq_true] at h
      intro c hc
      simp only [Block.ueberBoden]
      exact mB_boden_inv rest h.2 c hc
  | .bindCallInd (n := n) _ _ _ _ _ rest, h => by
      simp only [mB, Bool.and_eq_true] at h
      intro c hc
      simp only [Block.ueberBoden]
      exact mB_boden_inv rest h.2 c hc
  | .bindCallIndElse (n := n) _ _ _ _ _ err rest, h => by
      simp only [mB, Bool.and_eq_true] at h
      intro c hc
      simp only [Block.ueberBoden, Bool.and_eq_true]
      refine ⟨mE_boden_inv err h.1.2 c hc, mB_boden_inv rest h.2 c hc⟩
  | .bindCallElse g _ _ _ _ err rest, h => by
      simp only [mB, Bool.and_eq_true] at h
      intro c hc
      simp only [Block.ueberBoden, Bool.and_eq_true]
      exact ⟨mE_boden_inv err h.1.2 c hc, mB_boden_inv rest h.2 c hc⟩
  | .bindAxiom _ _ _ _ _ _ _ rest, h => by
      simp only [mB] at h
      intro c hc
      simp only [Block.ueberBoden]
      exact mB_boden_inv rest h c hc
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest, h => by
      simp only [mB, Bool.and_eq_true] at h
      intro c hc
      simp only [Block.ueberBoden, Bool.and_eq_true]
      exact ⟨mE_boden_inv err h.1 c hc, mB_boden_inv rest h.2 c hc⟩
  | .bindAxiomOpt _ _ _ _ _ _ _ rest, h => by
      simp only [mB] at h
      intro c hc
      simp only [Block.ueberBoden]
      exact mB_boden_inv rest h c hc
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest, h => by
      simp only [mB, Bool.and_eq_true] at h
      intro c hc
      simp only [Block.ueberBoden, Bool.and_eq_true]
      exact ⟨mE_boden_inv err h.1 c hc, mB_boden_inv rest h.2 c hc⟩
  | .regRead _ _ rest, h => by
      simp only [mB] at h
      intro c hc
      simp only [Block.ueberBoden]
      exact mB_boden_inv rest h c hc
  | .regReadElse _ _ _ sonst rest, h => by
      simp only [mB, Bool.and_eq_true] at h
      intro c hc
      simp only [Block.ueberBoden, Bool.and_eq_true]
      exact ⟨mE_boden_inv sonst h.1 c hc, mB_boden_inv rest h.2 c hc⟩
  | .awaits _ _ _ _ _ rest, h => by
      simp only [mB] at h
      intro c hc
      simp only [Block.ueberBoden]
      exact mB_boden_inv rest h c hc
  | .exchange _ _ _ _ rest, h => by
      simp only [mB] at h
      intro c hc
      simp only [Block.ueberBoden]
      exact mB_boden_inv rest h c hc
  | .narrow _ _ _ sonst rest, h => by
      simp only [mB, Bool.and_eq_true] at h
      intro c hc
      simp only [Block.ueberBoden, Bool.and_eq_true]
      exact ⟨mE_boden_inv sonst h.1 c hc, mB_boden_inv rest h.2 c hc⟩
  | .narrowRequired _ _ _ rest, h => by
      simp only [mB] at h
      intro c hc
      simp only [Block.ueberBoden]
      exact mB_boden_inv rest h c hc
  | .check _ sonst rest, h => by
      simp only [mB, Bool.and_eq_true] at h
      intro c hc
      simp only [Block.ueberBoden, Bool.and_eq_true]
      exact ⟨mE_boden_inv sonst h.1 c hc, mB_boden_inv rest h.2 c hc⟩
  | .float _ _ _ _ _ rest, h => by
      simp only [mB] at h
      intro c hc
      simp only [Block.ueberBoden]
      exact mB_boden_inv rest h c hc
  | .floatLit _ _ _ rest, h => by
      simp only [mB] at h
      intro c hc
      simp only [Block.ueberBoden]
      exact mB_boden_inv rest h c hc
  | .floatOf _ _ _ rest, h => by
      simp only [mB] at h
      intro c hc
      simp only [Block.ueberBoden]
      exact mB_boden_inv rest h c hc
  | .floatNarrow _ _ _ sonst rest, h => by
      simp only [mB, Bool.and_eq_true] at h
      intro c hc
      simp only [Block.ueberBoden, Bool.and_eq_true]
      exact ⟨mE_boden_inv sonst h.1 c hc, mB_boden_inv rest h.2 c hc⟩

theorem mArms_boden_inv {V : vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} :
    (a : Arms D V l Γ Λ Λ' cs) → mArms (bodenM f) a = true → a.BodenOk (bodenF f)
  | .nil, _ => fun _ _ => rfl
  | .cons bl rest, h => by
      simp only [mArms, Bool.and_eq_true] at h
      intro c hc
      simp only [Arms.ueberBoden, Bool.and_eq_true]
      exact ⟨mB_boden_inv bl h.1 c hc, mArms_boden_inv rest h.2 c hc⟩

theorem mGArms_boden_inv {V : vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} :
    (a : GrundArms D V l Γ Λ Λ' n) → mGArms (bodenM f) a = true → a.BodenOk (bodenF f)
  | .nil, _ => fun _ _ => rfl
  | .cons bl rest, h => by
      simp only [mGArms, Bool.and_eq_true] at h
      intro c hc
      simp only [GrundArms.ueberBoden, Bool.and_eq_true]
      exact ⟨mB_boden_inv bl h.1 c hc, mGArms_boden_inv rest h.2 c hc⟩

theorem mE_boden_inv {V : vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (e : Endblock D V l Γ Λ) → mE (bodenM f) e = true → e.BodenOk (bodenF f)
  | .ret .., _ => fun _ _ => rfl
  | .retWhy .., _ => fun _ _ => rfl
  | .retScoped .., _ => fun _ _ => rfl
  | .retWhyScoped .., _ => fun _ _ => rfl
  | .leave _, _ => fun _ _ => rfl
  | .next _, _ => fun _ _ => rfl
  | .cons s rest, h => by
      simp only [mE, Bool.and_eq_true] at h
      intro c hc
      simp only [Endblock.ueberBoden, Bool.and_eq_true]
      exact ⟨mS_boden_inv s h.1 c hc, mE_boden_inv rest h.2 c hc⟩
  | .bind _ rest, h => by
      simp only [mE] at h
      intro c hc
      simp only [Endblock.ueberBoden]
      exact mE_boden_inv rest h c hc
  | .bindCall g _ _ _ _ rest, h => by
      simp only [mE, Bool.and_eq_true] at h
      intro c hc
      simp only [Endblock.ueberBoden]
      exact mE_boden_inv rest h.2 c hc
  | .bindCallElse g _ _ _ _ err rest, h => by
      simp only [mE, Bool.and_eq_true] at h
      intro c hc
      simp only [Endblock.ueberBoden, Bool.and_eq_true]
      exact ⟨mE_boden_inv err h.1.2 c hc, mE_boden_inv rest h.2 c hc⟩
  | .bindAxiom _ _ _ _ _ _ _ rest, h => by
      simp only [mE] at h
      intro c hc
      simp only [Endblock.ueberBoden]
      exact mE_boden_inv rest h c hc
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest, h => by
      simp only [mE, Bool.and_eq_true] at h
      intro c hc
      simp only [Endblock.ueberBoden, Bool.and_eq_true]
      exact ⟨mE_boden_inv err h.1 c hc, mE_boden_inv rest h.2 c hc⟩
  | .bindAxiomOpt _ _ _ _ _ _ _ rest, h => by
      simp only [mE] at h
      intro c hc
      simp only [Endblock.ueberBoden]
      exact mE_boden_inv rest h c hc
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest, h => by
      simp only [mE, Bool.and_eq_true] at h
      intro c hc
      simp only [Endblock.ueberBoden, Bool.and_eq_true]
      exact ⟨mE_boden_inv err h.1 c hc, mE_boden_inv rest h.2 c hc⟩
  | .regRead _ _ rest, h => by
      simp only [mE] at h
      intro c hc
      simp only [Endblock.ueberBoden]
      exact mE_boden_inv rest h c hc
  | .regReadElse _ _ _ sonst rest, h => by
      simp only [mE, Bool.and_eq_true] at h
      intro c hc
      simp only [Endblock.ueberBoden, Bool.and_eq_true]
      exact ⟨mE_boden_inv sonst h.1 c hc, mE_boden_inv rest h.2 c hc⟩
  | .awaits _ _ _ _ _ rest, h => by
      simp only [mE] at h
      intro c hc
      simp only [Endblock.ueberBoden]
      exact mE_boden_inv rest h c hc
  | .bindCallInd (n := n) _ _ _ _ _ rest, h => by
      simp only [mE, Bool.and_eq_true] at h
      intro c hc
      simp only [Endblock.ueberBoden]
      exact mE_boden_inv rest h.2 c hc
  | .bindCallIndElse (n := n) _ _ _ _ _ err rest, h => by
      simp only [mE, Bool.and_eq_true] at h
      intro c hc
      simp only [Endblock.ueberBoden, Bool.and_eq_true]
      exact ⟨mE_boden_inv err h.1.2 c hc, mE_boden_inv rest h.2 c hc⟩
  | .narrow _ _ _ sonst rest, h => by
      simp only [mE, Bool.and_eq_true] at h
      intro c hc
      simp only [Endblock.ueberBoden, Bool.and_eq_true]
      exact ⟨mE_boden_inv sonst h.1 c hc, mE_boden_inv rest h.2 c hc⟩
  | .narrowRequired _ _ _ rest, h => by
      simp only [mE] at h
      intro c hc
      simp only [Endblock.ueberBoden]
      exact mE_boden_inv rest h c hc
  | .exchange _ _ _ _ rest, h => by
      simp only [mE] at h
      intro c hc
      simp only [Endblock.ueberBoden]
      exact mE_boden_inv rest h c hc
  | .ite _ t e, h => by
      simp only [mE, Bool.and_eq_true] at h
      intro c hc
      simp only [Endblock.ueberBoden, Bool.and_eq_true]
      exact ⟨mE_boden_inv t h.1 c hc, mE_boden_inv e h.2 c hc⟩

end

end StufenUmkehr

/-- **The residue form gives back the model form**: a body whose floor feature
    holds respects its function's floor. -/
theorem stufenOk_of_stufenM {P : Programm D} (h : StufenM P) : StufenOk P :=
  fun f c hc => mE_boden_inv f (P.rumpf f) (h f) c hc

#print axioms Gabbro.Grammatik.stufenOk_of_stufenM


end Gabbro.Grammatik
