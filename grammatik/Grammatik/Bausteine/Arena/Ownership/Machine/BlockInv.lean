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

/-! ## A judged statement -/

/-- **What a judged statement says**, by its form. -/
def STop (A : FreiForm D) (I : Interfaces A) {V : Vertrag D} (out : Flow.Output A V.erg) (k c c2 : Context) :
    {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Stmt D V l Γ Λ Λ' → Prop
  | _, _, _, _, .ite cond t e =>
      checkExpression A c cond = true ∧ OB A I out k c t c2 ∧ OB A I out k c e c2
  | _, _, _, _, .onOption o p a =>
      checkExpression A c o = true ∧ (∃ c1, OB A I out k (c.bind none) p c1 ∧ Weaker c2 c1.drop) ∧
        OB A I out k c a c2
  | _, _, _, _, .onTag v arms => checkExpression A c v = true ∧ OArms A I out k c arms c2
  | _, _, _, _, .onWhy r arms => checkExpression A c r = true ∧ OGrund A I out k c arms c2
  | _, _, _, _, .call f args _ _ =>
      checkArguments A c args = true ∧ planFits c (modeList (I f).parameters) (originList c args) = true ∧
        c2 = dropContext (c.afterCall (modeList (I f).parameters) (originList c args)) (I f).output
  | _, _, _, _, .callInd (n := n) p args _ _ =>
      ∃ (J : Modes (D.sigNr n).params) (owner : Bool), SigCompatible I n J owner ∧
        checkExpression A c p = true ∧ checkArguments A c args = true ∧
        planFits c (modeList J) (originList c args) = true ∧
        c2 = dropContextB (c.afterCall (modeList J) (originList c args)) owner
  | _, _, _, _, .locks _ _ body => OB A I out k c body c2
  | _, _, _, _, .breaking _ body => OB A I out k c body c2
  | _, _, _, _, .traverse _ inv body =>
      Weaker c2 c ∧ checkExpression A c2 inv = true ∧
        ∃ c1, OB A I out c2 (c2.bind none) body c1 ∧ Weaker c2 c1.drop
  | _, _, _, _, .retry _ bis body ueber =>
      Weaker c2 c ∧ checkExpression A c2 bis = true ∧ (∃ c1, OB A I out c2 c2 body c1 ∧ Weaker c2 c1) ∧
        OB A I out k c2 ueber c2
  | _, _, _, _, .forever _ inv body =>
      Weaker c2 c ∧ checkExpression A c2 inv = true ∧ ∃ c1, OB A I out c2 c2 body c1 ∧ Weaker c2 c1
  | _, _, _, _, .ret e _ => out.check A c e = true
  | _, _, _, _, .retWhy _ _ => finish c none = true
  | _, _, _, _, .leave _ => ExitsTo k c
  | _, _, _, _, .next _ => ExitsTo k c
  | _, _, _, _, .axiomCall a args _ _ _ _ _ => AxiomFree A a ∧ checkArguments A c args = true
  | _, _, _, _, _ => True

/-- **Every judged statement says what its form needs.** -/
theorem os_top : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {k c c2 : Context} {st : Stmt D V l Γ Λ Λ'},
    OS A I out k c st c2 → STop A I out k c c2 st
  | _, _, _, _, _, _, _, _, .assignSlot .. => trivial
  | _, _, _, _, _, _, _, _, .assignThru .. => trivial
  | _, _, _, _, _, _, _, _, .assignGlob .. => trivial
  | _, _, _, _, _, _, _, _, .putBytes .. => trivial
  | _, _, _, _, _, _, _, _, .assignVar .. => trivial
  | _, _, _, _, _, _, _, _, .shift .. => trivial
  | _, _, _, _, _, _, _, _, .ite _ _ _ hc ht he => ⟨hc, ht, he⟩
  | _, _, _, _, _, _, _, _, .onOption _ _ _ ho hp hw ha => ⟨ho, ⟨_, hp, hw⟩, ha⟩
  | _, _, _, _, _, _, _, _, .onTag _ _ hv ha => ⟨hv, ha⟩
  | _, _, _, _, _, _, _, _, .onWhy _ _ hr ha => ⟨hr, ha⟩
  | _, _, _, _, _, _, _, _, .call _ _ _ _ ha hplan => ⟨ha, hplan, rfl⟩
  | _, _, _, _, _, _, _, _, .callInd _ _ _ _ J owner hJ hpc ha hplan => ⟨J, owner, hJ, hpc, ha, hplan, rfl⟩
  | _, _, _, _, _, _, _, _, .locks _ _ _ hb => hb
  | _, _, _, _, _, _, _, _, .breaking _ _ hb => hb
  | _, _, _, _, _, _, _, _, .traverse _ _ _ hentry hinv hb hback => ⟨hentry, hinv, _, hb, hback⟩
  | _, _, _, _, _, _, _, _, .retry _ _ _ _ hentry hbis hb hback hu => ⟨hentry, hbis, ⟨_, hb, hback⟩, hu⟩
  | _, _, _, _, _, _, _, _, .forever _ _ _ hentry hinv hb hback => ⟨hentry, hinv, _, hb, hback⟩
  | _, _, _, _, _, _, _, _, .axiomCall _ _ _ _ _ _ _ hfree ha => ⟨hfree, ha⟩
  | _, _, _, _, _, _, _, _, .regWrite .. => trivial
  | _, _, _, _, _, _, _, _, .transition .. => trivial
  | _, _, _, _, _, _, _, _, .publish .. => trivial
  | _, _, _, _, _, _, _, _, .advances .. => trivial
  | _, _, _, _, _, _, _, _, .retires .. => trivial
  | _, _, _, _, _, _, _, _, .ret _ _ he => he
  | _, _, _, _, _, _, _, _, .retWhy _ _ hf => hf
  | _, _, _, _, _, _, _, _, .leave _ hx => hx
  | _, _, _, _, _, _, _, _, .next _ hx => hx

/-! ## The traverse shim -/

/-- What a residue says when it is the traverse shim (whose index context `cases` cannot take apart). -/
def RShim (A : FreiForm D) (I : Interfaces A) {V : Vertrag D} (out : Flow.Output A V.erg) (k c : Context) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Prop
  | _, _, _, .travRest t inv body ks r => Weaker k c.drop ∧ OX A I out k (.travRest t inv body ks r)
  | _, _, _, _ => True

def XShim (A : FreiForm D) (I : Interfaces A) {V : Vertrag D} (out : Flow.Output A V.erg) (k : Context) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Prop
  | _, _, _, .travRest (Γ := Γ) _ inv body _ r => ∃ k0 c1, checkExpression A k inv = true ∧
      OB A I out k (k.bind none) body c1 ∧ Weaker k c1.drop ∧ k.references.length = Γ.length ∧
      k0.references.length ≤ Γ.length ∧ OR A I out k0 k r
  | _, _, _, _ => True

theorem or_shim : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {k c : Context} {r : GRest D V l Γ Λ},
    OR A I out k c r → RShim A I out k c r
  | _, _, _, _, _, _, .travRest _ _ _ _ _ hentry hx => ⟨hentry, hx⟩
  | _, _, _, _, _, _, .ende .. => trivial
  | _, _, _, _, _, _, .dann .. => trivial
  | _, _, _, _, _, _, .dannDead .. => trivial
  | _, _, _, _, _, _, .schrumpf .. => trivial
  | _, _, _, _, _, _, .frei .. => trivial
  | _, _, _, _, _, _, .abbruch .. => trivial
  | _, _, _, _, _, _, .leer => trivial
  | _, _, _, _, _, _, .trav .. => trivial
  | _, _, _, _, _, _, .wieder .. => trivial
  | _, _, _, _, _, _, .wiederRest .. => trivial
  | _, _, _, _, _, _, .ewig .. => trivial
  | _, _, _, _, _, _, .ewigRest .. => trivial

theorem ox_shim : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {k : Context} {r : GRest D V l Γ Λ},
    OX A I out k r → XShim A I out k r
  | _, _, _, _, _, .travRest _ _ _ _ _ hinv hb hback hlen hk hr => ⟨_, _, hinv, hb, hback, hlen, hk, hr⟩
  | _, _, _, _, _, .dann .. => trivial
  | _, _, _, _, _, .schrumpf .. => trivial
  | _, _, _, _, _, .frei .. => trivial
  | _, _, _, _, _, .abbruch .. => trivial
  | _, _, _, _, _, .wiederRest .. => trivial
  | _, _, _, _, _, .ewigRest .. => trivial
  | _, _, _, _, _, .ende .. => trivial
  | _, _, _, _, _, .leer => trivial
  | _, _, _, _, _, .trav .. => trivial
  | _, _, _, _, _, .wieder .. => trivial
  | _, _, _, _, _, .ewig .. => trivial
  | _, _, _, _, _, .wartet .. => trivial
  | _, _, _, _, _, .wartetSonst .. => trivial

end Gabbro.Grammatik.ArenaOwnership.Machine
