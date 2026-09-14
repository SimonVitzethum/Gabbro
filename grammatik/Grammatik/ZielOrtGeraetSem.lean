/-
  File:      Grammatik/ZielOrtGeraetSem.lean
  Subject:   THE DEVICE FORMS FOR `ziel_ort_geraet` -- the hardware class of
             register locality (`RegLokal`), the widened fragment (`gOk`:
             register reads, `let … else` register reads and `awaits`
             admitted), the footprint widened by the device carriers of every
             register a body reads (`fussOrteG`), its check (`fussOrtGB`), the
             user obligation against local oracles (`KoerperGutG`), and the
             frame semantics of the three device forms.

  `ZielOrtRegister.lean` shows that register reads cannot join the fragment
  of `ziel_ort_voll` as it stands: a register answer is `O.regLies r σ`, a
  function of the WHOLE world, and on G another thread changes the world
  between two reads outside the reader's footprint. The repair has two
  halves.

  * HARDWARE (`RegLokal`): the declaration attributes to every register the
    carriers that hold its device's state (`D.rtraeger r`, a declaration
    field, default none); the answer of a read depends on those carriers
    only. The same for the visibility answer of `awaits g`: it depends on the
    awaited global `g` only. Two reads MAY answer differently exactly when
    those carriers changed in between; a device whose state changes by
    itself writes those carriers, through a declared write (an axiom whose
    frame names them), and that write is recorded like every axiom write
    (`fadenV_ax`/`fadenG_ax`).
  * PROGRAM FACT (`fussOrteG`, `fussOrtGB`): the footprint of a function
    contains the device carriers of every register its body reads, and the
    footprint check covers them (guarded by a lock the function holds by
    signature, or written by no function).

  Together: the reader's sequential world agrees with the machine world on
  the footprint, hence on the device carriers, hence the sequential answer
  of a local oracle is the machine's answer.
-/
import Grammatik.ZielOrtVollBeweis

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The hardware class: register locality -/

/-- **Register locality** (hardware). A register read answers from the
    state of its device: two worlds that agree on the device carriers the
    declaration attributes to `r` (`D.rtraeger r`) get the same answer. The
    visibility answer of `awaits g` (A10) depends on the awaited global only.
    Consecutive reads may differ only where those carriers changed. -/
def RegLokal (O : Orakel D) : Prop :=
  (∀ (r : D.Reg) (σ σ' : World D), GleichAuf (D.rtraeger r) σ σ' →
    O.regLies r σ = O.regLies r σ') ∧
  (∀ (g : D.Glob) (σ σ' : World D), GleichAuf [Sum.inr g] σ σ' →
    O.sichtbar g σ = O.sichtbar g σ')

/-- The sequential oracle `O'` gives the register and visibility answers of
    the machine's oracle `O`. -/
def GleichRS (O O' : Orakel D) : Prop :=
  O'.regLies = O.regLies ∧ O'.sichtbar = O.sichtbar

theorem gleichRS_orakelAus (O : Orakel D) (HA : List (AxEintrag D)) :
    GleichRS O (orakelAus O HA) := ⟨rfl, rfl⟩

/-- The oracle of a record answers registers and visibility like the
    machine's oracle, so it is local when the machine's oracle is. -/
theorem regLokal_orakelAus {O : Orakel D} (h : RegLokal O) (HA : List (AxEintrag D)) :
    RegLokal (orakelAus O HA) := h

/-- A sequential oracle with the machine's register answers, read at a world
    that agrees with the machine world on the device carriers, answers what
    the machine read. -/
theorem regLies_gleich {O O' : Orakel D} (hRL : RegLokal O) (hQ : GleichRS O O') (r : D.Reg)
    {S : List (D.Tab ⊕ D.Glob)} (hS : ∀ o ∈ D.rtraeger r, o ∈ S) {σ W : World D}
    (hg : GleichAuf S σ W) : O'.regLies r σ = O.regLies r W := by
  rw [hQ.1]
  exact hRL.1 r σ W (GleichAuf.mono hS hg)

theorem sichtbar_gleich {O O' : Orakel D} (hRL : RegLokal O) (hQ : GleichRS O O') (g : D.Glob)
    {S : List (D.Tab ⊕ D.Glob)} (hS : Sum.inr g ∈ S) {σ W : World D}
    (hg : GleichAuf S σ W) : O'.sichtbar g σ = O.sichtbar g W := by
  rw [hQ.2]
  exact hRL.2 g σ W (GleichAuf.mono (fun o ho => by
    rw [List.mem_singleton] at ho
    subst ho
    exact hS) hg)

/-! ## 2. The user obligation against local oracles -/

/-- **The user obligation of one function, with device forms.** The body
    triple and the caller duty of `KoerperGut`, for EVERY oracle that
    respects the declared axiom frames AND is register-local: what a
    register answers is hardware, but the triple may use that it answers
    from its device's carriers. Weaker than `KoerperGutV`
    (`koerperGutG_of_V`). -/
def KoerperGutG (P : Programm D) (passes : Nat) (f : D.Fn) : Prop :=
  ∀ O' : Orakel D, RahmenO O' → RegLokal O' → KoerperGut P O' passes f

theorem koerperGutG_of_V {P : Programm D} {passes : Nat} {f : D.Fn}
    (h : KoerperGutV P passes f) : KoerperGutG P passes f :=
  fun O' hr _ => h O' hr

/-! ## 3. The widened fragment -/

mutual

/-- The statement is in the widened fragment: every form, an indirect call
    through a pointer of signature `n` where `K n` holds. -/
def Stmt.gOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (K : Nat → Bool)
    (Rg : D.Reg → Bool) : Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => t.gOk K Rg && e.gOk K Rg
  | .onOption _ p a => p.gOk K Rg && a.gOk K Rg
  | .onTag _ arms => arms.gOk K Rg
  | .onGrund _ arms => arms.gOk K Rg
  | .locks _ _ body => body.gOk K Rg
  | .breaking _ body => body.gOk K Rg
  | .traverse _ _ body => body.gOk K Rg
  | .retry _ _ body ueber => body.gOk K Rg && ueber.gOk K Rg
  | .forever _ _ body => body.gOk K Rg
  | .callInd (n := n) .. => K n
  | _ => true

/-- The block is in the widened fragment: a register read of `r` where
    `Rg r` holds (its device carriers in the footprint), `awaits` always. -/
def Block.gOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (K : Nat → Bool)
    (Rg : D.Reg → Bool) : Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => s.gOk K Rg && rest.gOk K Rg
  | .bind _ rest => rest.gOk K Rg
  | .bindCall _ _ _ _ _ rest => rest.gOk K Rg
  | .bindCallInd (n := n) _ _ _ _ _ rest => K n && rest.gOk K Rg
  | .bindCallElse _ _ _ _ _ err rest => err.gOk K Rg && rest.gOk K Rg
  | .bindAxiom _ _ _ _ _ _ _ rest => rest.gOk K Rg
  | .regLies r _ rest => Rg r && rest.gOk K Rg
  | .regLiesElse r _ _ sonst rest => Rg r && (sonst.gOk K Rg && rest.gOk K Rg)
  | .awaits _ _ _ _ rest => rest.gOk K Rg
  | .exchange _ _ _ _ rest => rest.gOk K Rg
  | .narrow _ _ _ sonst rest => sonst.gOk K Rg && rest.gOk K Rg
  | .pruefung _ sonst rest => sonst.gOk K Rg && rest.gOk K Rg
  | .gleit _ _ _ _ _ rest => rest.gOk K Rg
  | .gleitLit _ _ _ rest => rest.gOk K Rg
  | .gleitVon _ _ _ rest => rest.gOk K Rg
  | .gleitNarrow _ _ _ sonst rest => sonst.gOk K Rg && rest.gOk K Rg

def Endblock.gOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (K : Nat → Bool)
    (Rg : D.Reg → Bool) : Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retGrund .. => true
  | .leave .. => true
  | .next .. => true
  | .cons s rest => s.gOk K Rg && rest.gOk K Rg
  | .bind _ rest => rest.gOk K Rg

def Arms.gOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (K : Nat → Bool) (Rg : D.Reg → Bool) :
    Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => b.gOk K Rg && rest.gOk K Rg

def GrundArms.gOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} (K : Nat → Bool) (Rg : D.Reg → Bool) : GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => b.gOk K Rg && rest.gOk K Rg

end

theorem Endblock.gOk_alsBlock {V : Vertrag D} {l : Bool} (K : Nat → Bool) (Rg : D.Reg → Bool) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ), e.alsBlock.2.gOk K Rg = e.gOk K Rg
  | _, _, .ret _ _ => rfl
  | _, _, .retGrund _ _ => rfl
  | _, _, .leave _ => rfl
  | _, _, .next _ => rfl
  | _, _, .cons s rest => by
      simp only [Endblock.alsBlock, Block.gOk, Endblock.gOk, Endblock.gOk_alsBlock K Rg rest]
  | _, _, .bind _ rest => by
      simp only [Endblock.alsBlock, Block.gOk, Endblock.gOk, Endblock.gOk_alsBlock K Rg rest]

/-! ### The registers a body reads -/

mutual

def Stmt.regs {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → List D.Reg
  | .ite _ t e => t.regs ++ e.regs
  | .onOption _ p a => p.regs ++ a.regs
  | .onTag _ arms => arms.regs
  | .onGrund _ arms => arms.regs
  | .locks _ _ body => body.regs
  | .breaking _ body => body.regs
  | .traverse _ _ body => body.regs
  | .retry _ _ body ueber => body.regs ++ ueber.regs
  | .forever _ _ body => body.regs
  | _ => []

/-- The registers a block reads (`let x = R`, `let x = R else …`). -/
def Block.regs {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → List D.Reg
  | .nil => []
  | .cons s rest => s.regs ++ rest.regs
  | .bind _ rest => rest.regs
  | .bindCall _ _ _ _ _ rest => rest.regs
  | .bindCallInd _ _ _ _ _ rest => rest.regs
  | .bindCallElse _ _ _ _ _ err rest => err.regs ++ rest.regs
  | .bindAxiom _ _ _ _ _ _ _ rest => rest.regs
  | .regLies r _ rest => r :: rest.regs
  | .regLiesElse r _ _ sonst rest => r :: (sonst.regs ++ rest.regs)
  | .awaits _ _ _ _ rest => rest.regs
  | .exchange _ _ _ _ rest => rest.regs
  | .narrow _ _ _ sonst rest => sonst.regs ++ rest.regs
  | .pruefung _ sonst rest => sonst.regs ++ rest.regs
  | .gleit _ _ _ _ _ rest => rest.regs
  | .gleitLit _ _ _ rest => rest.regs
  | .gleitVon _ _ _ rest => rest.regs
  | .gleitNarrow _ _ _ sonst rest => sonst.regs ++ rest.regs

def Endblock.regs {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → List D.Reg
  | .ret .. => []
  | .retGrund .. => []
  | .leave .. => []
  | .next .. => []
  | .cons s rest => s.regs ++ rest.regs
  | .bind _ rest => rest.regs

def Arms.regs {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} : Arms D V l Γ Λ Λ' cs → List D.Reg
  | .nil => []
  | .cons b rest => b.regs ++ rest.regs

def GrundArms.regs {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} : GrundArms D V l Γ Λ Λ' n → List D.Reg
  | .nil => []
  | .cons b rest => b.regs ++ rest.regs

end

/-! ### Monotonicity: the admissibility grows, the register test holds on
    the registers read -/

section Mono

variable {K K' : Nat → Bool} {Rg Rg' : D.Reg → Bool} (hKK : ∀ n, K n = true → K' n = true)
include hKK

mutual

theorem Stmt.gOk_mono {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → s.gOk K Rg = true → (∀ r ∈ s.regs, Rg' r = true) →
      s.gOk K' Rg' = true
  | .ite _ t e, h, hr => by
      simp only [Stmt.gOk, Stmt.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Block.gOk_mono t h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono e h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .onOption _ p a, h, hr => by
      simp only [Stmt.gOk, Stmt.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Block.gOk_mono p h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono a h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .onTag _ arms, h, hr => by
      simp only [Stmt.gOk, Stmt.regs] at h hr ⊢
      exact Arms.gOk_mono arms h hr
  | .onGrund _ arms, h, hr => by
      simp only [Stmt.gOk, Stmt.regs] at h hr ⊢
      exact GrundArms.gOk_mono arms h hr
  | .locks _ _ body, h, hr => by
      simp only [Stmt.gOk, Stmt.regs] at h hr ⊢
      exact Block.gOk_mono body h hr
  | .breaking _ body, h, hr => by
      simp only [Stmt.gOk, Stmt.regs] at h hr ⊢
      exact Block.gOk_mono body h hr
  | .traverse _ _ body, h, hr => by
      simp only [Stmt.gOk, Stmt.regs] at h hr ⊢
      exact Block.gOk_mono body h hr
  | .retry _ _ body ueber, h, hr => by
      simp only [Stmt.gOk, Stmt.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Block.gOk_mono body h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono ueber h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .forever _ _ body, h, hr => by
      simp only [Stmt.gOk, Stmt.regs] at h hr ⊢
      exact Block.gOk_mono body h hr
  | .callInd .., h, _ => by
      simp only [Stmt.gOk] at h ⊢
      exact hKK _ h
  | .assignSlot .., _, _ => rfl
  | .assignDurch .., _, _ => rfl
  | .assignGlob .., _, _ => rfl
  | .schreibBytes .., _, _ => rfl
  | .assignVar .., _, _ => rfl
  | .uebergang .., _, _ => rfl
  | .call .., _, _ => rfl
  | .axiomCall .., _, _ => rfl
  | .regSchreib .., _, _ => rfl
  | .transition .., _, _ => rfl
  | .publish .., _, _ => rfl
  | .advances .., _, _ => rfl
  | .retires .., _, _ => rfl
  | .ret .., _, _ => rfl
  | .retGrund .., _, _ => rfl
  | .leave .., _, _ => rfl
  | .next .., _, _ => rfl

theorem Block.gOk_mono {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → b.gOk K Rg = true → (∀ r ∈ b.regs, Rg' r = true) →
      b.gOk K' Rg' = true
  | .nil, _, _ => rfl
  | .cons s rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Stmt.gOk_mono s h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .bind _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .bindCall _ _ _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .bindCallInd _ _ _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true] at h hr ⊢
      exact ⟨hKK _ h.1, Block.gOk_mono rest h.2 hr⟩
  | .bindCallElse _ _ _ _ _ err rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Endblock.gOk_mono err h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .bindAxiom _ _ _ _ _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .regLies r _ rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true, List.mem_cons] at h hr ⊢
      exact ⟨hr r (Or.inl rfl), Block.gOk_mono rest h.2 (fun r' h' => hr r' (Or.inr h'))⟩
  | .regLiesElse r _ _ sonst rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true, List.mem_cons, List.mem_append]
        at h hr ⊢
      exact ⟨hr r (Or.inl rfl),
        Endblock.gOk_mono sonst h.2.1 (fun r' h' => hr r' (Or.inr (Or.inl h'))),
        Block.gOk_mono rest h.2.2 (fun r' h' => hr r' (Or.inr (Or.inr h')))⟩
  | .awaits _ _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .exchange _ _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .narrow _ _ _ sonst rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Endblock.gOk_mono sonst h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .pruefung _ sonst rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Endblock.gOk_mono sonst h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .gleit _ _ _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .gleitLit _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .gleitVon _ _ _ rest, h, hr => by
      simp only [Block.gOk, Block.regs] at h hr ⊢
      exact Block.gOk_mono rest h hr
  | .gleitNarrow _ _ _ sonst rest, h, hr => by
      simp only [Block.gOk, Block.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Endblock.gOk_mono sonst h.1 (fun r h' => hr r (Or.inl h')),
        Block.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩

theorem Endblock.gOk_mono {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (e : Endblock D V l Γ Λ) → e.gOk K Rg = true → (∀ r ∈ e.regs, Rg' r = true) →
      e.gOk K' Rg' = true
  | .ret .., _, _ => rfl
  | .retGrund .., _, _ => rfl
  | .leave .., _, _ => rfl
  | .next .., _, _ => rfl
  | .cons s rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Stmt.gOk_mono s h.1 (fun r h' => hr r (Or.inl h')),
        Endblock.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩
  | .bind _ rest, h, hr => by
      simp only [Endblock.gOk, Endblock.regs] at h hr ⊢
      exact Endblock.gOk_mono rest h hr

theorem Arms.gOk_mono {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    (a : Arms D V l Γ Λ Λ' cs) → a.gOk K Rg = true → (∀ r ∈ a.regs, Rg' r = true) →
      a.gOk K' Rg' = true
  | .nil, _, _ => rfl
  | .cons b rest, h, hr => by
      simp only [Arms.gOk, Arms.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Block.gOk_mono b h.1 (fun r h' => hr r (Or.inl h')),
        Arms.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩

theorem GrundArms.gOk_mono {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} : (a : GrundArms D V l Γ Λ Λ' n) → a.gOk K Rg = true →
      (∀ r ∈ a.regs, Rg' r = true) → a.gOk K' Rg' = true
  | .nil, _, _ => rfl
  | .cons b rest, h, hr => by
      simp only [GrundArms.gOk, GrundArms.regs, Bool.and_eq_true, List.mem_append] at h hr ⊢
      exact ⟨Block.gOk_mono b h.1 (fun r h' => hr r (Or.inl h')),
        GrundArms.gOk_mono rest h.2 (fun r h' => hr r (Or.inr h'))⟩

end

end Mono

theorem armWahlG_gOk {V : Vertrag D} {K : Nat → Bool} {Rg : D.Reg → Bool} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    arms.gOk K Rg = true → (armWahlG arms v).2.1.gOk K Rg = true
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨⟨0, _⟩, _⟩, h => by
      simp only [Arms.gOk, Bool.and_eq_true] at h
      exact h.1
  | _, .cons _ rest, ⟨⟨_ + 1, _⟩, _⟩, h => by
      simp only [Arms.gOk, Bool.and_eq_true] at h
      exact armWahlG_gOk rest _ h.2

theorem armWahlG_gOk' {V : Vertrag D} {K : Nat → Bool} {Rg : D.Reg → Bool} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs)
    (v : Wert D (.sum cs)) {c : Option (Int × Int)} {b : Block D V l (ArmCtx Γ c) Λ Λ'}
    {nutz : Nutzlast c} (hw : armWahlG arms v = ⟨c, b, nutz⟩) (h : arms.gOk K Rg = true) :
    b.gOk K Rg = true := by
  have h0 := armWahlG_gOk arms v h
  rw [hw] at h0
  exact h0

theorem grundWahlG_gOk {V : Vertrag D} {K : Nat → Bool} {Rg : D.Reg → Bool} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
    arms.gOk K Rg = true → (grundWahlG arms r).gOk K Rg = true
  | _, .nil, ⟨k, hk⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨0, _⟩, h => by
      simp only [GrundArms.gOk, Bool.and_eq_true] at h
      exact h.1
  | _, .cons _ rest, ⟨_ + 1, _⟩, h => by
      simp only [GrundArms.gOk, Bool.and_eq_true] at h
      exact grundWahlG_gOk rest _ h.2

/-! ## 4. The footprint with the device carriers, and its check -/

/-- The register test: every device carrier of `r` is in `S`. -/
def regP (S : List (D.Tab ⊕ D.Glob)) (r : D.Reg) : Bool :=
  (D.rtraeger r).all fun o => S.any fun o' => decide (o' = o)

theorem regP_ok {S : List (D.Tab ⊕ D.Glob)} {r : D.Reg} (h : regP S r = true) :
    ∀ o ∈ D.rtraeger r, o ∈ S := by
  intro o ho
  obtain ⟨o', ho', he⟩ := List.any_eq_true.mp ((List.all_eq_true.mp h) o ho)
  rw [← of_decide_eq_true he]
  exact ho'

theorem regP_of {S : List (D.Tab ⊕ D.Glob)} {r : D.Reg} (h : ∀ o ∈ D.rtraeger r, o ∈ S) :
    regP S r = true :=
  List.all_eq_true.mpr fun o ho => List.any_eq_true.mpr ⟨o, h o ho, decide_eq_true rfl⟩

/-- **The footprint of `f` with its devices**: the footprint of `ziel_ort`
    (`fussOrte`: contract carriers, body reads, contract carriers of direct
    callees) and the device carriers of every register the body reads. -/
def fussOrteG (P : Programm D) (f : D.Fn) : List (D.Tab ⊕ D.Glob) :=
  fussOrte P f ++ (P.rumpf f).regs.flatMap D.rtraeger

theorem fuss_teilG (P : Programm D) (f : D.Fn) : fussOrte P f ⊆ fussOrteG P f :=
  fun _ h => List.mem_append_left _ h

theorem fuss_rumpfG (P : Programm D) (f : D.Fn) : endblockOrteP P (P.rumpf f) ⊆ fussOrteG P f :=
  fun _ h => fuss_teilG P f (fuss_rumpf P f h)

theorem fuss_ensG (P : Programm D) (f : D.Fn) : (P.ensures f).orte ⊆ fussOrteG P f :=
  fun _ h => fuss_teilG P f (fuss_ens P f h)

theorem fuss_regG (P : Programm D) (f : D.Fn) (r : D.Reg) (hr : r ∈ (P.rumpf f).regs) :
    ∀ o ∈ D.rtraeger r, o ∈ fussOrteG P f :=
  fun _ ho => List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, hr, ho⟩)

/-- **The footprint check with the devices.** Every carrier of the widened
    footprint of `f` -- the device carriers of the registers it reads
    included -- is guarded by a lock that `f` holds BY SIGNATURE, or no
    function writes it. -/
def fussOrtGB (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun f => (fussOrteG P f).all fun o =>
    (waechterVon o).any (fun L => decide (L ∈ D.haelt f)) ||
    fs.all (fun g => !(TraegerSchreibt g o))

/-- The property that `fussOrtGB` decides. -/
def FussOrtGOk (P : Programm D) (f : D.Fn) : Prop :=
  ∀ o ∈ fussOrteG P f,
    (∃ L : D.Lock, Bewacht o L ∧ L ∈ D.haelt f) ∨ (∀ g : D.Fn, TraegerSchreibt g o = false)

theorem fussOrtGB_ok (P : Programm D) (fs : List D.Fn) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (h : fussOrtGB P fs = true) (f : D.Fn) : FussOrtGOk P f := by
  intro o ho
  have h1 := (List.all_eq_true.mp h) f (hvoll f)
  have h2 := (List.all_eq_true.mp h1) o ho
  simp only [Bool.or_eq_true] at h2
  rcases h2 with hg | hfrei
  · obtain ⟨L, hL, hLh⟩ := List.any_eq_true.mp hg
    exact Or.inl ⟨L, waechterVon_mem.mp hL, of_decide_eq_true hLh⟩
  · refine Or.inr fun g => ?_
    have := (List.all_eq_true.mp hfrei) g (hvoll g)
    simpa using this

/-- The widened check covers the old one. -/
theorem fussOrtB_of_G (P : Programm D) (fs : List D.Fn) (h : fussOrtGB P fs = true) :
    fussOrtB P fs = true :=
  List.all_eq_true.mpr fun f hf => List.all_eq_true.mpr fun o ho =>
    (List.all_eq_true.mp ((List.all_eq_true.mp h) f hf)) o (fuss_teilG P f ho)

/-- **The widened fragment, as a decidable program fact**: every body is in
    `gOk` (every form; an indirect call admitted where every function of its
    signature has its contract carriers in the caller's widened footprint). -/
def programmImFragmentG (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun f => (P.rumpf f).gOk (kandB P fs (fussOrteG P f)) (fun _ => true)

/-- The decided fragment gives the fragment the replay reads: every body is
    in `gOk` with the admissibility `KandOk` of its widened footprint, and
    every register it reads has its device carriers there. -/
theorem programmImFragmentG_ok (P : Programm D) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (h : programmImFragmentG P fs = true) (f : D.Fn) :
    (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) = true :=
  Endblock.gOk_mono (kandB_kandP P hvoll _) _ ((List.all_eq_true.mp h) f (hvoll f))
    (fun r hr => regP_of (fuss_regG P f r hr))

/-! ## 5. The residues the replay follows -/

/-- A residue in the widened fragment whose blocks, loop heads and calls
    read only inside the footprint `S`, and whose register reads have their
    device carriers in `S`. -/
def GRest.okG (P : Programm D) (S : List (D.Tab ⊕ D.Glob)) {V : Vertrag D} :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Prop
  | _, _, _, .ende e => e.gOk (kandP P S) (regP S) = true ∧ endblockOrteP P e ⊆ S
  | _, _, _, .dann b k => b.gOk (kandP P S) (regP S) = true ∧ blockOrteP P b ⊆ S ∧ k.okG P S
  | _, _, _, .schrumpf k => k.okG P S
  | _, _, _, .frei _ k => k.okG P S
  | _, _, _, .trav _ inv body _ k =>
      inv.orte ⊆ S ∧ body.gOk (kandP P S) (regP S) = true ∧ blockOrteP P body ⊆ S ∧ k.okG P S
  | _, _, _, .travRest _ inv body _ k =>
      inv.orte ⊆ S ∧ body.gOk (kandP P S) (regP S) = true ∧ blockOrteP P body ⊆ S ∧ k.okG P S
  | _, _, _, .wieder _ bis body ueber k =>
      bis.orte ⊆ S ∧ body.gOk (kandP P S) (regP S) = true ∧ blockOrteP P body ⊆ S ∧
        ueber.gOk (kandP P S) (regP S) = true ∧
        blockOrteP P ueber ⊆ S ∧ k.okG P S
  | _, _, _, .wiederRest _ bis body ueber k =>
      bis.orte ⊆ S ∧ body.gOk (kandP P S) (regP S) = true ∧ blockOrteP P body ⊆ S ∧
        ueber.gOk (kandP P S) (regP S) = true ∧
        blockOrteP P ueber ⊆ S ∧ k.okG P S
  | _, _, _, .ewig _ _ inv body k =>
      inv.orte ⊆ S ∧ body.gOk (kandP P S) (regP S) = true ∧ blockOrteP P body ⊆ S ∧ k.okG P S
  | _, _, _, .ewigRest _ _ inv body k =>
      inv.orte ⊆ S ∧ body.gOk (kandP P S) (regP S) = true ∧ blockOrteP P body ⊆ S ∧ k.okG P S
  | _, _, _, .wartet b k => b.gOk (kandP P S) (regP S) = true ∧ blockOrteP P b ⊆ S ∧ k.okG P S
  | _, _, _, .wartetSonst _ err b k =>
      err.gOk (kandP P S) (regP S) = true ∧ endblockOrteP P err ⊆ S ∧
        b.gOk (kandP P S) (regP S) = true ∧ blockOrteP P b ⊆ S ∧ k.okG P S
  | _, _, Λ, @GRest.abbruch _ _ _ _ _ Λk k =>
      (∀ L, Res.held L ∈ Λk ↔ Res.held L ∈ Λ) ∧ k.okG P S

section OkG

variable {P : Programm D} {S : List (D.Tab ⊕ D.Glob)} {V : Vertrag D} {l : Bool} {Γ : Ctx}

theorem okG_dann_cons {Λ Λ' Λ'' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Block D V l Γ Λ' Λ''} {k : GRest D V l Γ Λ''}
    (h : (GRest.dann (.cons s rest) k).okG P S) :
    s.gOk (kandP P S) (regP S) = true ∧ stmtOrteP P s ⊆ S ∧ (GRest.dann rest k).okG P S := by
  obtain ⟨hk, hs, hk'⟩ := h
  simp only [Block.gOk, Bool.and_eq_true] at hk
  simp only [blockOrteP] at hs
  exact ⟨hk.1, (teil_append hs).1, hk.2, (teil_append hs).2, hk'⟩

theorem okG_ende_cons {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Endblock D V l Γ Λ'} (h : (GRest.ende (.cons s rest)).okG P S) :
    s.gOk (kandP P S) (regP S) = true ∧ stmtOrteP P s ⊆ S ∧ (GRest.ende rest).okG P S := by
  obtain ⟨hk, hs⟩ := h
  simp only [Endblock.gOk, Bool.and_eq_true] at hk
  simp only [endblockOrteP] at hs
  exact ⟨hk.1, (teil_append hs).1, hk.2, (teil_append hs).2⟩

/-- **The residue of an `else` branch is in the fragment** (as
    `okV_alsBlock`). -/
theorem okG_alsBlock {Λ Λk : List (Res D)} (e : Endblock D V l Γ Λ) (k : GRest D V l Γ Λk)
    (hΛ : ∀ L, Res.held L ∈ Λk ↔ Res.held L ∈ Λ) (he : e.gOk (kandP P S) (regP S) = true)
    (heS : endblockOrteP P e ⊆ S) (hk : k.okG P S) :
    (GRest.dann e.alsBlock.2 (.abbruch k)).okG P S :=
  ⟨by rw [Endblock.gOk_alsBlock]; exact he, by rw [blockOrteP_alsBlock]; exact heS,
    fun L => (hΛ L).trans (e.alsBlock.2.held_iff L).symm, hk⟩

end OkG

/-! ## 6. The frame semantics of the device forms -/

section Geraet

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  {l : Bool} {Γ : Ctx}

theorem semV_regLies {Λ Λ' : List (Res D)} (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
    (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (D.rtyp r)) (hv : einpassen (D.rtyp r) (O.regLies r σ) = some v)
    (hz : D.rzusage r v = true) :
    semV O passes R (.dann (.regLies r hk rest) k) σ ρ =
      semV O passes R (.dann rest (.schrumpf k)) σ (.cons v ρ) := by
  rw [semV_dann]
  simp only [execBlock, hv, hz, if_true]
  rfl

theorem semV_regLiesElseWahr {Λ Λ' : List (Res D)} (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
    (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (D.rtyp r)) (hv : einpassen (D.rtyp r) (O.regLies r σ) = some v)
    (hw : wahr? (eval (σ.lese Λ zusage.orte) zusage (σ.lese Λ zusage.orte) (.cons v ρ)) = true) :
    semV O passes R (.dann (.regLiesElse r hk zusage sonst rest) k) σ ρ =
      semV O passes R (.dann rest (.schrumpf k)) (σ.lese Λ zusage.orte) (.cons v ρ) := by
  rw [semV_dann]
  simp only [execBlock, hv, hw, if_true]
  rfl

theorem semV_regLiesElseFalsch {Λ Λ' : List (Res D)} (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
    (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (D.rtyp r)) (hv : einpassen (D.rtyp r) (O.regLies r σ) = some v)
    (hw : wahr? (eval (σ.lese Λ zusage.orte) zusage (σ.lese Λ zusage.orte) (.cons v ρ)) = false) :
    (semV O passes R (.dann (.regLiesElse r hk zusage sonst rest) k) σ ρ).folgt
      (semV O passes R (.dann sonst.alsBlock.2 (.abbruch k)) (σ.lese Λ zusage.orte) ρ) := by
  rw [semV_dann]
  simp only [execBlock, hv, hw, Bool.false_eq_true, if_false]
  rw [semV_alsBlock]
  exact ZErg.folgt_refl _

theorem semV_awaits {Λ Λ' : List (Res D)} (g : D.Glob) (payload : List D.Glob)
    (hp : payload = D.nutzlast g) (hL : gdarf D g Λ) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) (hvis : O.sichtbar g σ = true) :
    semV O passes R (.dann (.awaits g payload hp hL rest) k) σ ρ =
      semV O passes R (.dann rest (.schrumpf k)) (σ.lese Λ [.inr g])
        (.cons ((σ.lese Λ [.inr g]).globs g) ρ) := by
  rw [semV_dann]
  simp only [execBlock, hvis, if_true]
  rfl

end Geraet

/-! ## 7. The fragment of `ziel_ort_voll` is inside the widened one -/

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
  | .onGrund _ arms, h => by
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
  | .assignSlot .., _ => ⟨rfl, rfl⟩
  | .assignDurch .., _ => ⟨rfl, rfl⟩
  | .assignGlob .., _ => ⟨rfl, rfl⟩
  | .schreibBytes .., _ => ⟨rfl, rfl⟩
  | .assignVar .., _ => ⟨rfl, rfl⟩
  | .uebergang .., _ => ⟨rfl, rfl⟩
  | .call .., _ => ⟨rfl, rfl⟩
  | .axiomCall .., _ => ⟨rfl, rfl⟩
  | .regSchreib .., _ => ⟨rfl, rfl⟩
  | .transition .., _ => ⟨rfl, rfl⟩
  | .publish .., _ => ⟨rfl, rfl⟩
  | .advances .., _ => ⟨rfl, rfl⟩
  | .retires .., _ => ⟨rfl, rfl⟩
  | .ret .., _ => ⟨rfl, rfl⟩
  | .retGrund .., _ => ⟨rfl, rfl⟩
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
  | .bindCallElse _ _ _ _ _ err rest, h => by
      simp only [Block.vOk, Bool.and_eq_true] at h
      have he : err.gOk K Rg = true ∧ err.regs = [] := Endblock.gOk_of_vOk err h.1
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := Block.gOk_of_vOk rest h.2
      simp only [Block.gOk, Block.regs, he.1, hr.1, he.2, hr.2, Bool.and_self, List.append_nil,
        and_self]
  | .bindAxiom _ _ _ _ _ _ _ rest, h => by
      simp only [Block.vOk] at h
      exact Block.gOk_of_vOk rest h
  | .regLies .., h => by simp [Block.vOk] at h
  | .regLiesElse .., h => by simp [Block.vOk] at h
  | .awaits .., h => by simp [Block.vOk] at h
  | .exchange _ _ _ _ rest, h => by
      simp only [Block.vOk] at h
      exact Block.gOk_of_vOk rest h
  | .narrow _ _ _ sonst rest, h => by
      simp only [Block.vOk, Bool.and_eq_true] at h
      have hs : sonst.gOk K Rg = true ∧ sonst.regs = [] := Endblock.gOk_of_vOk sonst h.1
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := Block.gOk_of_vOk rest h.2
      simp only [Block.gOk, Block.regs, hs.1, hr.1, hs.2, hr.2, Bool.and_self, List.append_nil,
        and_self]
  | .pruefung _ sonst rest, h => by
      simp only [Block.vOk, Bool.and_eq_true] at h
      have hs : sonst.gOk K Rg = true ∧ sonst.regs = [] := Endblock.gOk_of_vOk sonst h.1
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := Block.gOk_of_vOk rest h.2
      simp only [Block.gOk, Block.regs, hs.1, hr.1, hs.2, hr.2, Bool.and_self, List.append_nil,
        and_self]
  | .gleit _ _ _ _ _ rest, h => by
      simp only [Block.vOk] at h
      exact Block.gOk_of_vOk rest h
  | .gleitLit _ _ _ rest, h => by
      simp only [Block.vOk] at h
      exact Block.gOk_of_vOk rest h
  | .gleitVon _ _ _ rest, h => by
      simp only [Block.vOk] at h
      exact Block.gOk_of_vOk rest h
  | .gleitNarrow _ _ _ sonst rest, h => by
      simp only [Block.vOk, Bool.and_eq_true] at h
      have hs : sonst.gOk K Rg = true ∧ sonst.regs = [] := Endblock.gOk_of_vOk sonst h.1
      have hr : rest.gOk K Rg = true ∧ rest.regs = [] := Block.gOk_of_vOk rest h.2
      simp only [Block.gOk, Block.regs, hs.1, hr.1, hs.2, hr.2, Bool.and_self, List.append_nil,
        and_self]

theorem Endblock.gOk_of_vOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (e : Endblock D V l Γ Λ) → e.vOk K = true → e.gOk K Rg = true ∧ e.regs = []
  | .ret .., _ => ⟨rfl, rfl⟩
  | .retGrund .., _ => ⟨rfl, rfl⟩
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

theorem Arms.gOk_of_vOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
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
  simp

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
