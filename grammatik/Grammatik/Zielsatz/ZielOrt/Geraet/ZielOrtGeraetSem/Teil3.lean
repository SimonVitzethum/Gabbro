module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetSem.Teil2
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetSem.Teil2a

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section AusV

variable {K : Nat → Bool} {Rg : D.Reg → Bool}

mutual

theorem Stmt.gOk_of_vOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → s.vOk K = true → s.gOk K Rg = true ∧ s.regs = []
  | .ite _ t e, h => by
      simp only [Stmt.vOk, Bool.and_eq_true] at h
      have ht : t.gOk K Rg = true ∧ t.regs = [] := Block.gOk_of_vOk t h.1
      have he : e.gOk K Rg = true ∧ e.regs = [] := Block.gOk_of_vOk e h.2
      simp only [Stmt.gOk, Stmt.regs, ht.1, he.1, ht.2, he.2, Bool.and_self, List.append_nil,
        and_self]
  | .onOption _ p a, h => by
      simp only [Stmt.vOk, Bool.and_eq_true] at h
      have hp : p.gOk K Rg = true ∧ p.regs = [] := Block.gOk_of_vOk p h.1
      have ha : a.gOk K Rg = true ∧ a.regs = [] := Block.gOk_of_vOk a h.2
      simp only [Stmt.gOk, Stmt.regs, hp.1, ha.1, hp.2, ha.2, Bool.and_self, List.append_nil,
        and_self]
  | .onTag _ arms, h => by
      simp only [Stmt.vOk] at h
      exact Arms.gOk_of_vOk arms h
  | .onWhy _ arms, h => by
      simp only [Stmt.vOk] at h
      exact GrundArms.gOk_of_vOk arms h
  | .locks _ _ body, h => by
      simp only [Stmt.vOk] at h
      exact Block.gOk_of_vOk body h
  | .breaking _ body, h => by
      simp only [Stmt.vOk] at h
      exact Block.gOk_of_vOk body h
  | .traverse _ _ body, h => by
      simp only [Stmt.vOk] at h
      exact Block.gOk_of_vOk body h
  | .consumeTraverse _ _ _ _ _ _ body, h => by
      simp only [Stmt.vOk] at h
      exact Block.gOk_of_vOk body h
  | .retry _ _ body ueber, h => by
      simp only [Stmt.vOk, Bool.and_eq_true] at h
      have hb : body.gOk K Rg = true ∧ body.regs = [] := Block.gOk_of_vOk body h.1
      have hu : ueber.gOk K Rg = true ∧ ueber.regs = [] := Block.gOk_of_vOk ueber h.2
      simp only [Stmt.gOk, Stmt.regs, hb.1, hu.1, hb.2, hu.2, Bool.and_self, List.append_nil,
        and_self]
  | .forever _ _ body, h => by
      simp only [Stmt.vOk] at h
      exact Block.gOk_of_vOk body h
  | .callInd .., h => by
      simp only [Stmt.vOk] at h
      exact ⟨h, rfl⟩
  | .callIndElse _ _ _ _ _ err, h => by
      simp only [Stmt.vOk, Bool.and_eq_true] at h
      have he : err.gOk K Rg = true ∧ err.regs = [] := Endblock.gOk_of_vOk err h.2
      simp only [Stmt.gOk, Stmt.regs, h.1, he.1, he.2, Bool.and_self, and_self]
  | .axiomCallElse (err := err) .., h => by
      simp only [Stmt.vOk] at h
      have he : err.gOk K Rg = true ∧ err.regs = [] := Endblock.gOk_of_vOk err h
      simp only [Stmt.gOk, Stmt.regs, he.1, he.2, and_self]
  | .assignSlot .., _ => ⟨rfl, rfl⟩
  | .assignThru .., _ | .assignThruOwn .., _ | .assignSlotRef .., _ => ⟨rfl, rfl⟩
  | .assignGlob .., _ => ⟨rfl, rfl⟩
  | .putBytes .., _ => ⟨rfl, rfl⟩
  | .assignVar .., _ => ⟨rfl, rfl⟩
  | .shift .., _ => ⟨rfl, rfl⟩
  | .call .., _ => ⟨rfl, rfl⟩
  | .axiomCall .., _ => ⟨rfl, rfl⟩
  | .regWrite .., _ => ⟨rfl, rfl⟩
  | .transition .., _ => ⟨rfl, rfl⟩
  | .publish .., _ => ⟨rfl, rfl⟩
  | .advances .., _ => ⟨rfl, rfl⟩
  | .retires .., _ => ⟨rfl, rfl⟩
  | .ret .., _ => ⟨rfl, rfl⟩
  | .retWhy .., _ => ⟨rfl, rfl⟩
  | .retScoped .., _ => ⟨rfl, rfl⟩
  | .retWhyScoped .., _ => ⟨rfl, rfl⟩
  | .leave .., _ => ⟨rfl, rfl⟩
  | .next .., _ => ⟨rfl, rfl⟩

theorem Block.gOk_of_vOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → b.vOk K = true → b.gOk K Rg = true ∧ b.regs = []
  | .nil, _ => ⟨rfl, rfl⟩
  | .cons s rest, h => by
      simp only [Block.vOk, Bool.and_eq_true] at h
      have hs : s.gOk K Rg = true ∧ s.regs = [] := Stmt.gOk_of_vOk s h.1
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := Block.gOk_of_vOk rest h.2
      simp only [Block.gOk, Block.regs, hs.1, hr.1, hs.2, hr.2, Bool.and_self, List.append_nil,
        and_self]
  | .bind _ rest, h => by
      simp only [Block.vOk] at h
      exact Block.gOk_of_vOk rest h
  | .bindCall _ _ _ _ _ rest, h => by
      simp only [Block.vOk] at h
      exact Block.gOk_of_vOk rest h
  | .bindCallInd _ _ _ _ _ rest, h => by
      simp only [Block.vOk, Bool.and_eq_true] at h
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := Block.gOk_of_vOk rest h.2
      simp only [Block.gOk, Block.regs, h.1, hr.1, hr.2, Bool.and_self, and_self]
  | .bindCallIndElse _ _ _ _ _ err rest, h => by
      simp only [Block.vOk, Bool.and_eq_true] at h
      have he : err.gOk K Rg = true ∧ err.regs = [] := Endblock.gOk_of_vOk err h.1.2
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := Block.gOk_of_vOk rest h.2
      simp only [Block.gOk, Block.regs, h.1.1, he.1, hr.1, he.2, hr.2, Bool.and_self, List.append_nil,
        and_self]
  | .bindCallElse _ _ _ _ _ err rest, h => by
      simp only [Block.vOk, Bool.and_eq_true] at h
      have he : err.gOk K Rg = true ∧ err.regs = [] := Endblock.gOk_of_vOk err h.1
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := Block.gOk_of_vOk rest h.2
      simp only [Block.gOk, Block.regs, he.1, hr.1, he.2, hr.2, Bool.and_self, List.append_nil,
        and_self]
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest, h => by
      simp only [Block.vOk, Bool.and_eq_true] at h
      have he : err.gOk K Rg = true ∧ err.regs = [] := Endblock.gOk_of_vOk err h.1
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := Block.gOk_of_vOk rest h.2
      simp only [Block.gOk, Block.regs, he.1, hr.1, he.2, hr.2, Bool.and_self, List.append_nil,
        and_self]
  | .bindAxiomOpt (rest := rest) .., h => by
      simp only [Block.vOk] at h
      exact Block.gOk_of_vOk rest h
  | .bindAxiomOptElse (err := err) (rest := rest) .., h => by
      simp only [Block.vOk, Bool.and_eq_true] at h
      have he : err.gOk K Rg = true ∧ err.regs = [] := Endblock.gOk_of_vOk err h.1
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := Block.gOk_of_vOk rest h.2
      simp only [Block.gOk, Block.regs, he.1, hr.1, he.2, hr.2, Bool.and_self, List.append_nil,
        and_self]
  | .bindAxiom _ _ _ _ _ _ _ rest, h => by
      simp only [Block.vOk] at h
      exact Block.gOk_of_vOk rest h
  | .regRead .., h => by simp only [Block.vOk, Bool.false_eq_true] at h
  | .regReadElse .., h => by simp only [Block.vOk, Bool.false_eq_true] at h
  | .awaits .., h => by simp only [Block.vOk, Bool.false_eq_true] at h
  | .exchange _ _ _ _ rest, h => by
      simp only [Block.vOk] at h
      exact Block.gOk_of_vOk rest h
  | .narrow _ _ _ sonst rest, h => by
      simp only [Block.vOk, Bool.and_eq_true] at h
      have hs : sonst.gOk K Rg = true ∧ sonst.regs = [] := Endblock.gOk_of_vOk sonst h.1
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := Block.gOk_of_vOk rest h.2
      simp only [Block.gOk, Block.regs, hs.1, hr.1, hs.2, hr.2, Bool.and_self, List.append_nil,
        and_self]
  | .narrowRequired _ _ _ rest, h => by
      simp only [Block.vOk] at h
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := Block.gOk_of_vOk rest h
      simp only [Block.gOk, Block.regs, hr.1, hr.2, Bool.and_self, List.append_nil, and_self]
  | .check _ sonst rest, h => by
      simp only [Block.vOk, Bool.and_eq_true] at h
      have hs : sonst.gOk K Rg = true ∧ sonst.regs = [] := Endblock.gOk_of_vOk sonst h.1
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := Block.gOk_of_vOk rest h.2
      simp only [Block.gOk, Block.regs, hs.1, hr.1, hs.2, hr.2, Bool.and_self, List.append_nil,
        and_self]
  | .float _ _ _ _ _ rest, h => by
      simp only [Block.vOk] at h
      exact Block.gOk_of_vOk rest h
  | .floatLit _ _ _ rest, h => by
      simp only [Block.vOk] at h
      exact Block.gOk_of_vOk rest h
  | .floatOf _ _ _ rest, h => by
      simp only [Block.vOk] at h
      exact Block.gOk_of_vOk rest h
  | .floatNarrow _ _ _ sonst rest, h => by
      simp only [Block.vOk, Bool.and_eq_true] at h
      have hs : sonst.gOk K Rg = true ∧ sonst.regs = [] := Endblock.gOk_of_vOk sonst h.1
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := Block.gOk_of_vOk rest h.2
      simp only [Block.gOk, Block.regs, hs.1, hr.1, hs.2, hr.2, Bool.and_self, List.append_nil,
        and_self]

theorem Endblock.gOk_of_vOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (e : Endblock D V l Γ Λ) → e.vOk K = true → e.gOk K Rg = true ∧ e.regs = []
  | .ret .., _ => ⟨rfl, rfl⟩
  | .retWhy .., _ => ⟨rfl, rfl⟩
  | .retScoped .., _ => ⟨rfl, rfl⟩
  | .retWhyScoped .., _ => ⟨rfl, rfl⟩
  | .leave .., _ => ⟨rfl, rfl⟩
  | .next .., _ => ⟨rfl, rfl⟩
  | .cons s rest, h => by
      simp only [Endblock.vOk, Bool.and_eq_true] at h
      have hs : s.gOk K Rg = true ∧ s.regs = [] := Stmt.gOk_of_vOk s h.1
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := Endblock.gOk_of_vOk rest h.2
      simp only [Endblock.gOk, Endblock.regs, hs.1, hr.1, hs.2, hr.2, Bool.and_self,
        List.append_nil, and_self]
  | .bind _ rest, h => by
      simp only [Endblock.vOk] at h
      exact Endblock.gOk_of_vOk rest h
  | .bindCall _ _ _ _ _ rest, h => by
      simp only [Endblock.vOk] at h
      exact Endblock.gOk_of_vOk rest h
  | .bindCallElse _ _ _ _ _ err rest, h => by
      simp only [Endblock.vOk, Bool.and_eq_true] at h
      have he : err.gOk K Rg = true ∧ err.regs = [] := Endblock.gOk_of_vOk err h.1
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := Endblock.gOk_of_vOk rest h.2
      simp only [Endblock.gOk, Endblock.regs, he.1, hr.1, he.2, hr.2, Bool.and_self, List.append_nil,
        and_self]
  | .bindAxiom _ _ _ _ _ _ _ rest, h => by
      simp only [Endblock.vOk] at h
      exact Endblock.gOk_of_vOk rest h
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest, h => by
      simp only [Endblock.vOk, Bool.and_eq_true] at h
      have he : err.gOk K Rg = true ∧ err.regs = [] := Endblock.gOk_of_vOk err h.1
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := Endblock.gOk_of_vOk rest h.2
      simp only [Endblock.gOk, Endblock.regs, he.1, hr.1, he.2, hr.2, Bool.and_self, List.append_nil,
        and_self]
  | .bindAxiomOpt (rest := rest) .., h => by
      simp only [Endblock.vOk] at h
      exact Endblock.gOk_of_vOk rest h
  | .bindAxiomOptElse (err := err) (rest := rest) .., h => by
      simp only [Endblock.vOk, Bool.and_eq_true] at h
      have he : err.gOk K Rg = true ∧ err.regs = [] := Endblock.gOk_of_vOk err h.1
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := Endblock.gOk_of_vOk rest h.2
      simp only [Endblock.gOk, Endblock.regs, he.1, hr.1, he.2, hr.2, Bool.and_self, List.append_nil,
        and_self]
  | .regRead .., h => by simp only [Endblock.vOk, Bool.false_eq_true] at h
  | .regReadElse .., h => by simp only [Endblock.vOk, Bool.false_eq_true] at h
  | .awaits .., h => by simp only [Endblock.vOk, Bool.false_eq_true] at h
  | .bindCallInd _ _ _ _ _ rest, h => by
      simp only [Endblock.vOk, Bool.and_eq_true] at h
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := Endblock.gOk_of_vOk rest h.2
      simp only [Endblock.gOk, Endblock.regs, h.1, hr.1, hr.2, Bool.and_self, and_self]
  | .bindCallIndElse _ _ _ _ _ err rest, h => by
      simp only [Endblock.vOk, Bool.and_eq_true] at h
      have he : err.gOk K Rg = true ∧ err.regs = [] := Endblock.gOk_of_vOk err h.1.2
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := Endblock.gOk_of_vOk rest h.2
      simp only [Endblock.gOk, Endblock.regs, h.1.1, he.1, hr.1, he.2, hr.2, Bool.and_self,
        List.append_nil, and_self]
  | .narrow _ _ _ sonst rest, h => by
      simp only [Endblock.vOk, Bool.and_eq_true] at h
      have hs : sonst.gOk K Rg = true ∧ sonst.regs = [] := Endblock.gOk_of_vOk sonst h.1
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := Endblock.gOk_of_vOk rest h.2
      simp only [Endblock.gOk, Endblock.regs, hs.1, hr.1, hs.2, hr.2, Bool.and_self, List.append_nil,
        and_self]
  | .narrowRequired _ _ _ rest, h => by
      simp only [Endblock.vOk] at h
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := Endblock.gOk_of_vOk rest h
      simp only [Endblock.gOk, Endblock.regs, hr.1, hr.2, Bool.and_self, List.append_nil, and_self]
  | .exchange _ _ _ _ rest, h => by
      simp only [Endblock.vOk] at h
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := Endblock.gOk_of_vOk rest h
      simp only [Endblock.gOk, Endblock.regs, hr.1, hr.2, and_self]
  | .ite _ t e, h => by
      simp only [Endblock.vOk, Bool.and_eq_true] at h
      have he : e.gOk K Rg = true ∧ e.regs = [] := Endblock.gOk_of_vOk e h.1
      have ht : t.gOk K Rg = true ∧ t.regs = [] := Endblock.gOk_of_vOk t h.2
      simp only [Endblock.gOk, Endblock.regs, he.1, ht.1, he.2, ht.2, Bool.and_self, List.append_nil,
        and_self]

theorem Arms.gOk_of_vOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} :
    (a : Arms D V l Γ Λ Λ' cs) → a.vOk K = true → a.gOk K Rg = true ∧ a.regs = []
  | .nil, _ => ⟨rfl, rfl⟩
  | .cons b rest, h => by
      simp only [Arms.vOk, Bool.and_eq_true] at h
      have hb : b.gOk K Rg = true ∧ b.regs = [] := Block.gOk_of_vOk b h.1
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := Arms.gOk_of_vOk rest h.2
      simp only [Arms.gOk, Arms.regs, hb.1, hr.1, hb.2, hr.2, Bool.and_self, List.append_nil,
        and_self]

theorem GrundArms.gOk_of_vOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} : (a : GrundArms D V l Γ Λ Λ' n) → a.vOk K = true →
      a.gOk K Rg = true ∧ a.regs = []
  | .nil, _ => ⟨rfl, rfl⟩
  | .cons b rest, h => by
      simp only [GrundArms.vOk, Bool.and_eq_true] at h
      have hb : b.gOk K Rg = true ∧ b.regs = [] := Block.gOk_of_vOk b h.1
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := GrundArms.gOk_of_vOk rest h.2
      simp only [GrundArms.gOk, GrundArms.regs, hb.1, hr.1, hb.2, hr.2, Bool.and_self,
        List.append_nil, and_self]

end

end AusV

/-- A body of the fragment of `ziel_ort_voll` reads no register: its
    widened footprint is its footprint. -/
theorem fussOrteG_of_vOk (P : Programm D) (fs : List D.Fn) (f : D.Fn)
    (h : (P.rumpf f).vOk (kandB P fs (fussOrte P f)) = true) : fussOrteG P f = fussOrte P f := by
  unfold fussOrteG
  rw [(Endblock.gOk_of_vOk (Rg := fun _ => true) _ h).2]
  simp only [List.flatMap_nil, List.append_nil]

/-- **The fragment of `ziel_ort_voll` is inside the widened fragment.** -/
theorem programmImFragmentG_of_V (P : Programm D) (fs : List D.Fn)
    (h : programmImFragmentV P fs = true) : programmImFragmentG P fs = true :=
  List.all_eq_true.mpr fun f hf => by
    have hv := (List.all_eq_true.mp h) f hf
    rw [fussOrteG_of_vOk P fs f hv]
    exact (Endblock.gOk_of_vOk _ hv).1

/-- **On the fragment of `ziel_ort_voll` the widened footprint check is the
    old one.** -/
theorem fussOrtGB_of_V (P : Programm D) (fs : List D.Fn) (h : programmImFragmentV P fs = true)
    (hF : fussOrtB P fs = true) : fussOrtGB P fs = true :=
  List.all_eq_true.mpr fun f hf => by
    rw [fussOrteG_of_vOk P fs f ((List.all_eq_true.mp h) f hf)]
    exact (List.all_eq_true.mp hF) f hf

/-! ## CUTS:

  What is proved: the hardware class `RegLokal` and its closure under the
  record oracle (`regLokal_orakelAus`); the transfer of a register or
  visibility answer from the sequential world to the machine world
  (`regLies_gleich`, `sichtbar_gleich`); the user obligation `KoerperGutG`
  (weaker than `KoerperGutV`); the widened fragment `gOk` with its
  monotonicity; the widened footprint `fussOrteG` (device carriers of the
  registers read) with its check `fussOrtGB` and soundness; the decided
  fragment `programmImFragmentG` with soundness; the residue predicate
  `GRest.okG`; the frame semantics of the three device forms; the fragment
  and footprint check of `ziel_ort_voll` inside the widened ones
  (`programmImFragmentG_of_V`, `fussOrtGB_of_V`).

  What is NOT here: the replay and the theorem (`ZielOrtGeraetBeweis.lean`,
  `ZielOrtGeraet.lean`).
-/

#print axioms Gabbro.Grammatik.regLies_gleich
#print axioms Gabbro.Grammatik.programmImFragmentG_ok
#print axioms Gabbro.Grammatik.fussOrtGB_ok
#print axioms Gabbro.Grammatik.semV_regLiesElseFalsch

end Gabbro.Grammatik
