import Grammatik.Bausteine.Arena.Ownership.Machine.Block

/-! **What a judged block says about its first form**, whatever weakening
of its end context the derivation went through. One clause per block
former that binds a value in front of the rest; the statement and the
narrowing forms have their own inversions (`ob_cons_inv`, `ob_narrow_inv`). -/

namespace Gabbro.Grammatik.ArenaOwnership.Machine

open Source Body

variable {D : Deklaration}

/-- The end context of a block that binds nothing: `c1`, possibly weakened. -/
def EqW (cout c1 : Context) : Prop := cout = c1 ∨ Weaker cout c1

theorem EqW.weaken {c2 cout c1 : Context} (h : EqW cout c1) (hw : Weaker c2 cout) : EqW c2 c1 := by
  rcases h with rfl | h
  · exact Or.inr hw
  · exact Or.inr (hw.trans h)

variable {A : FreiForm D} {I : Interfaces A} {V : Vertrag D} {out : Flow.Output A V.erg}

/-- **The first form of a judged block.** -/
def BTop (A : FreiForm D) (I : Interfaces A) {V : Vertrag D} (out : Flow.Output A V.erg) (k c cout : Context) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Block D V l Γ Λ Λ' → Prop
  | _, _, _, _, .nil => EqW cout c
  | _, _, _, _, .bind e rest =>
      checkExpression A c e = true ∧ ∃ c1, OB A I out k (c.bind (origin c e)) rest c1 ∧ DropW cout c1
  | _, _, _, _, .bindCall f args _ _ _ rest =>
      checkArguments A c args = true ∧ planFits c (modeList (I f).parameters) (originList c args) = true ∧
      ∃ c1, OB A I out k
        (resultContext (c.afterCall (modeList (I f).parameters) (originList c args)) (I f).output) rest c1 ∧
        DropW cout c1
  | _, _, _, _, .bindCallInd (n := n) p args _ _ _ rest =>
      ∃ (J : Modes (D.sigNr n).params) (owner : Bool), SigCompatible I n J owner ∧
        checkExpression A c p = true ∧ checkArguments A c args = true ∧
        planFits c (modeList J) (originList c args) = true ∧
        ∃ c1, OB A I out k (resultContextB (c.afterCall (modeList J) (originList c args)) owner) rest c1 ∧
          DropW cout c1
  | _, _, _, _, .bindCallElse f args _ _ _ err rest =>
      checkArguments A c args = true ∧ planFits c (modeList (I f).parameters) (originList c args) = true ∧
      OE A I out k ((c.afterCall (modeList (I f).parameters) (originList c args)).bind none) err ∧
      ∃ c1, OB A I out k
        (resultContext (c.afterCall (modeList (I f).parameters) (originList c args)) (I f).output) rest c1 ∧
        DropW cout c1
  | _, _, _, _, .bindAxiom a args _ _ _ _ _ rest =>
      AxiomFree A a ∧ checkArguments A c args = true ∧
      ∃ c1, OB A I out k (c.bind none) rest c1 ∧ DropW cout c1
  | _, _, _, _, .bindAxiomElse a args _ _ _ _ _ _ err rest =>
      AxiomFree A a ∧ checkArguments A c args = true ∧ OE A I out k (c.bind none) err ∧
      ∃ c1, OB A I out k (c.bind none) rest c1 ∧ DropW cout c1
  | _, _, _, _, .regRead _ _ rest => ∃ c1, OB A I out k (c.bind none) rest c1 ∧ DropW cout c1
  | _, _, _, _, .regReadElse _ _ z sonst rest =>
      checkExpression A (c.bind none) z = true ∧ OE A I out k c sonst ∧
      ∃ c1, OB A I out k (c.bind none) rest c1 ∧ DropW cout c1
  | _, _, _, _, .awaits _ _ _ _ _ rest => ∃ c1, OB A I out k (c.bind none) rest c1 ∧ DropW cout c1
  | _, _, _, _, .exchange g neu _ _ rest =>
      NotMetaGlob A g ∧ checkExpression A (c.bind none) neu = true ∧
      ∃ c1, OB A I out k (c.bind none) rest c1 ∧ DropW cout c1
  | _, _, _, _, .check cond sonst rest =>
      checkExpression A c cond = true ∧ OE A I out k c sonst ∧ ∃ c1, OB A I out k c rest c1 ∧ EqW cout c1
  | _, _, _, _, .float _ a b _ _ rest =>
      checkExpression A c a = true ∧ checkExpression A c b = true ∧
      ∃ c1, OB A I out k (c.bind none) rest c1 ∧ DropW cout c1
  | _, _, _, _, .floatLit _ _ _ rest => ∃ c1, OB A I out k (c.bind none) rest c1 ∧ DropW cout c1
  | _, _, _, _, .floatOf e _ _ rest =>
      checkExpression A c e = true ∧ ∃ c1, OB A I out k (c.bind none) rest c1 ∧ DropW cout c1
  | _, _, _, _, .floatNarrow e _ _ sonst rest =>
      checkExpression A c e = true ∧ OE A I out k c sonst ∧
      ∃ c1, OB A I out k (c.bind none) rest c1 ∧ DropW cout c1
  | _, _, _, _, .cons _ _ => True
  | _, _, _, _, .narrow .. => True

theorem BTop.weaken {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {k c cout c2 : Context}
    {b : Block D V l Γ Λ Λ'} (h : BTop A I out k c cout b) (hw : Weaker c2 cout) : BTop A I out k c c2 b := by
  cases b with
  | nil => exact EqW.weaken h hw
  | cons => trivial
  | narrow => trivial
  | bind => exact ⟨h.1, h.2.elim fun c1 h => ⟨c1, h.1, h.2.weaken hw⟩⟩
  | bindCall => exact ⟨h.1, h.2.1, h.2.2.elim fun c1 h => ⟨c1, h.1, h.2.weaken hw⟩⟩
  | bindCallInd =>
    obtain ⟨J, o, h1, h2, h3, h4, c1, h5, h6⟩ := h
    exact ⟨J, o, h1, h2, h3, h4, c1, h5, h6.weaken hw⟩
  | bindCallElse => exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.elim fun c1 h => ⟨c1, h.1, h.2.weaken hw⟩⟩
  | bindAxiom => exact ⟨h.1, h.2.1, h.2.2.elim fun c1 h => ⟨c1, h.1, h.2.weaken hw⟩⟩
  | bindAxiomElse => exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.elim fun c1 h => ⟨c1, h.1, h.2.weaken hw⟩⟩
  | regRead => exact h.elim fun c1 h => ⟨c1, h.1, h.2.weaken hw⟩
  | regReadElse => exact ⟨h.1, h.2.1, h.2.2.elim fun c1 h => ⟨c1, h.1, h.2.weaken hw⟩⟩
  | awaits => exact h.elim fun c1 h => ⟨c1, h.1, h.2.weaken hw⟩
  | exchange => exact ⟨h.1, h.2.1, h.2.2.elim fun c1 h => ⟨c1, h.1, h.2.weaken hw⟩⟩
  | check => exact ⟨h.1, h.2.1, h.2.2.elim fun c1 h => ⟨c1, h.1, h.2.weaken hw⟩⟩
  | float => exact ⟨h.1, h.2.1, h.2.2.elim fun c1 h => ⟨c1, h.1, h.2.weaken hw⟩⟩
  | floatLit => exact h.elim fun c1 h => ⟨c1, h.1, h.2.weaken hw⟩
  | floatOf => exact ⟨h.1, h.2.elim fun c1 h => ⟨c1, h.1, h.2.weaken hw⟩⟩
  | floatNarrow => exact ⟨h.1, h.2.1, h.2.2.elim fun c1 h => ⟨c1, h.1, h.2.weaken hw⟩⟩

/-- **Every judged block says what its first form needs.** -/
theorem ob_top : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {k c cout : Context} {b : Block D V l Γ Λ Λ'},
    OB A I out k c b cout → BTop A I out k c cout b
  | _, _, _, _, _, _, _, _, .nil => Or.inl rfl
  | _, _, _, _, _, _, _, _, .cons .. => trivial
  | _, _, _, _, _, _, _, _, .dead .. => trivial
  | _, _, _, _, _, _, _, _, .release .. => trivial
  | _, _, _, _, _, _, _, _, .narrow .. => trivial
  | _, _, _, _, _, _, _, _, .allocList .. => trivial
  | _, _, _, _, _, _, _, _, .allocCounter .. => trivial
  | _, _, _, _, _, _, _, _, .weaken _ hb hw => (ob_top hb).weaken hw
  | _, _, _, _, _, _, _, _, .bind _ _ he hr => ⟨he, _, hr, Or.inl rfl⟩
  | _, _, _, _, _, _, _, _, .bindCall _ _ _ _ _ _ ha hplan hrest => ⟨ha, hplan, _, hrest, Or.inl rfl⟩
  | _, _, _, _, _, _, _, _, .bindCallInd _ _ _ _ _ _ J owner hJ hpc ha hplan hrest =>
    ⟨J, owner, hJ, hpc, ha, hplan, _, hrest, Or.inl rfl⟩
  | _, _, _, _, _, _, _, _, .bindCallElse _ _ _ _ _ _ _ ha hplan herr hrest =>
    ⟨ha, hplan, herr, _, hrest, Or.inl rfl⟩
  | _, _, _, _, _, _, _, _, .bindAxiom _ _ _ _ _ _ _ _ hfree ha hrest => ⟨hfree, ha, _, hrest, Or.inl rfl⟩
  | _, _, _, _, _, _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ _ _ hfree ha herr hrest =>
    ⟨hfree, ha, herr, _, hrest, Or.inl rfl⟩
  | _, _, _, _, _, _, _, _, .regRead _ _ _ hrest => ⟨_, hrest, Or.inl rfl⟩
  | _, _, _, _, _, _, _, _, .regReadElse _ _ _ _ _ hz hs hrest => ⟨hz, hs, _, hrest, Or.inl rfl⟩
  | _, _, _, _, _, _, _, _, .awaits _ _ _ _ _ _ hrest => ⟨_, hrest, Or.inl rfl⟩
  | _, _, _, _, _, _, _, _, .exchange _ _ _ _ _ hg hn hrest => ⟨hg, hn, _, hrest, Or.inl rfl⟩
  | _, _, _, _, _, _, _, _, .check _ _ _ hc hs hrest => ⟨hc, hs, _, hrest, Or.inl rfl⟩
  | _, _, _, _, _, _, _, _, .float _ _ _ _ _ _ ha hb hrest => ⟨ha, hb, _, hrest, Or.inl rfl⟩
  | _, _, _, _, _, _, _, _, .floatLit _ _ _ _ hrest => ⟨_, hrest, Or.inl rfl⟩
  | _, _, _, _, _, _, _, _, .floatOf _ _ _ _ he hrest => ⟨he, _, hrest, Or.inl rfl⟩
  | _, _, _, _, _, _, _, _, .floatNarrow _ _ _ _ _ he hs hrest => ⟨he, hs, _, hrest, Or.inl rfl⟩

end Gabbro.Grammatik.ArenaOwnership.Machine
