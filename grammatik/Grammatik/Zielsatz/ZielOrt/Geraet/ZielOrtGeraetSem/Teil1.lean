module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The hardware class: register locality -/

/-- **Register locality** (hardware). A register read answers from the
    state of its device: two worlds that agree on the device carriers the
    declaration attributes to `r` (`D.rtraeger r`) get the same answer. The
    visibility answer of `awaits g` (A10) depends on the awaited global only.
    Consecutive reads may differ only where those carriers changed. (The trace records every read as
    `Ereignis.fremd` since 2026-10-25; lifting this assumption to answers that depend on that history needs the
    local replay to record register answers as it records foreign answers -- open.) -/
def RegLokal (O : Orakel D) : Prop :=
  (∀ (r : D.Reg) (σ σ' : World D), GleichAuf (D.rtraeger r) σ σ' →
    O.regLies r σ = O.regLies r σ') ∧
  (∀ (g : D.Glob) (σ σ' : World D), GleichAuf [Sum.inr g] σ σ' →
    O.sichtbar g σ = O.sichtbar g σ')

/-- The sequential oracle `O'` gives the register and visibility answers of
    the machine's oracle `O`. -/
def GleichRS (O O' : Orakel D) : Prop :=
  O'.regLies = O.regLies ∧ O'.sichtbar = O.sichtbar ∧ ZeigerGleich O O'

theorem gleichRS_orakelAus (O : Orakel D) (HA : List (AxEintrag D)) :
    GleichRS O (orakelAus O HA) := ⟨rfl, rfl, rfl⟩

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
  rw [hQ.2.1]
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
  | .onWhy _ arms => arms.gOk K Rg
  | .locks _ _ body => body.gOk K Rg
  | .breaking _ body => body.gOk K Rg
  | .traverse _ _ body => body.gOk K Rg
  | .consumeTraverse _ _ _ _ _ _ body => body.gOk K Rg
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
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => err.gOk K Rg && rest.gOk K Rg
  | .bindAxiom _ _ _ _ _ _ _ rest => rest.gOk K Rg
  | .regRead r _ rest => Rg r && rest.gOk K Rg
  | .regReadElse r _ _ sonst rest => Rg r && (sonst.gOk K Rg && rest.gOk K Rg)
  | .awaits _ _ _ _ _ rest => rest.gOk K Rg
  | .exchange _ _ _ _ rest => rest.gOk K Rg
  | .narrow _ _ _ sonst rest => sonst.gOk K Rg && rest.gOk K Rg
  | .narrowRequired _ _ _ rest => rest.gOk K Rg
  | .check _ sonst rest => sonst.gOk K Rg && rest.gOk K Rg
  | .float _ _ _ _ _ rest => rest.gOk K Rg
  | .floatLit _ _ _ rest => rest.gOk K Rg
  | .floatOf _ _ _ rest => rest.gOk K Rg
  | .floatNarrow _ _ _ sonst rest => sonst.gOk K Rg && rest.gOk K Rg

def Endblock.gOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (K : Nat → Bool)
    (Rg : D.Reg → Bool) : Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retWhy .. => true
  | .retScoped .. => true
  | .retWhyScoped .. => true
  | .leave .. => true
  | .next .. => true
  | .cons s rest => s.gOk K Rg && rest.gOk K Rg
  | .bind _ rest => rest.gOk K Rg
  | .bindCall _ _ _ _ _ rest => rest.gOk K Rg
  | .bindCallElse _ _ _ _ _ err rest => err.gOk K Rg && rest.gOk K Rg
  | .bindAxiom _ _ _ _ _ _ _ rest => rest.gOk K Rg
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => err.gOk K Rg && rest.gOk K Rg
  | .regRead r _ rest => Rg r && rest.gOk K Rg
  | .regReadElse r _ _ sonst rest => Rg r && (sonst.gOk K Rg && rest.gOk K Rg)
  | .awaits _ _ _ _ _ rest => rest.gOk K Rg
  | .bindCallInd (n := n) _ _ _ _ _ rest => K n && rest.gOk K Rg
  | .narrow _ _ _ sonst rest => sonst.gOk K Rg && rest.gOk K Rg
  | .narrowRequired _ _ _ rest => rest.gOk K Rg
  | .exchange _ _ _ _ rest => rest.gOk K Rg
  | .ite _ t e => e.gOk K Rg && t.gOk K Rg

def Arms.gOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} (K : Nat → Bool) (Rg : D.Reg → Bool) :
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
  | _, _, .retWhy _ _ => rfl
  | _, _, .leave _ => rfl
  | _, _, .next _ => rfl
  | _, _, .cons s rest => by
      simp only [Endblock.alsBlock, Block.gOk, Endblock.gOk, Endblock.gOk_alsBlock K Rg rest]
  | _, _, .bind _ rest => by
      simp only [Endblock.alsBlock, Block.gOk, Endblock.gOk, Endblock.gOk_alsBlock K Rg rest]
  | _, _, .bindCall _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.gOk, Endblock.gOk, Endblock.gOk_alsBlock K Rg rest]
  | _, _, .bindAxiom _ _ _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.gOk, Endblock.gOk, Endblock.gOk_alsBlock K Rg rest]
  | _, _, .bindCallElse _ _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, Block.gOk, Endblock.gOk, Endblock.gOk_alsBlock K Rg rest]
  | _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, Block.gOk, Endblock.gOk, Endblock.gOk_alsBlock K Rg rest]
  | _, _, .regRead r hk rest => by
      simp only [Endblock.alsBlock, Block.gOk, Endblock.gOk, Endblock.gOk_alsBlock K Rg rest]
  | _, _, .regReadElse r hk z sonst rest => by
      simp only [Endblock.alsBlock, Block.gOk, Endblock.gOk, Endblock.gOk_alsBlock K Rg rest]
  | _, _, .awaits g pl hp hL hat rest => by
      simp only [Endblock.alsBlock, Block.gOk, Endblock.gOk, Endblock.gOk_alsBlock K Rg rest]
  | _, _, .bindCallInd p args he hp hr rest => by
      simp only [Endblock.alsBlock, Block.gOk, Endblock.gOk, Endblock.gOk_alsBlock K Rg rest]
  | _, _, .narrow _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.gOk, Endblock.gOk, Endblock.gOk_alsBlock K Rg rest]
  | _, _, .exchange _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.gOk, Endblock.gOk, Endblock.gOk_alsBlock K Rg rest]
  | _, _, .ite _ t _ => by
      simp only [Endblock.alsBlock, Block.gOk, Endblock.gOk, Endblock.gOk_alsBlock K Rg t]

/-! ### The registers a body reads -/

mutual

def Stmt.regs {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → List D.Reg
  | .ite _ t e => t.regs ++ e.regs
  | .onOption _ p a => p.regs ++ a.regs
  | .onTag _ arms => arms.regs
  | .onWhy _ arms => arms.regs
  | .locks _ _ body => body.regs
  | .breaking _ body => body.regs
  | .traverse _ _ body => body.regs
  | .consumeTraverse _ _ _ _ _ _ body => body.regs
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
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => err.regs ++ rest.regs
  | .bindAxiom _ _ _ _ _ _ _ rest => rest.regs
  | .regRead r _ rest => r :: rest.regs
  | .regReadElse r _ _ sonst rest => r :: (sonst.regs ++ rest.regs)
  | .awaits _ _ _ _ _ rest => rest.regs
  | .exchange _ _ _ _ rest => rest.regs
  | .narrow _ _ _ sonst rest => sonst.regs ++ rest.regs
  | .narrowRequired _ _ _ rest => rest.regs
  | .check _ sonst rest => sonst.regs ++ rest.regs
  | .float _ _ _ _ _ rest => rest.regs
  | .floatLit _ _ _ rest => rest.regs
  | .floatOf _ _ _ rest => rest.regs
  | .floatNarrow _ _ _ sonst rest => sonst.regs ++ rest.regs

def Endblock.regs {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → List D.Reg
  | .ret .. => []
  | .retWhy .. => []
  | .retScoped .. => []
  | .retWhyScoped .. => []
  | .leave .. => []
  | .next .. => []
  | .cons s rest => s.regs ++ rest.regs
  | .bind _ rest => rest.regs
  | .bindCall _ _ _ _ _ rest => rest.regs
  | .bindCallElse _ _ _ _ _ err rest => err.regs ++ rest.regs
  | .bindAxiom _ _ _ _ _ _ _ rest => rest.regs
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => err.regs ++ rest.regs
  | .regRead r _ rest => r :: rest.regs
  | .regReadElse r _ _ sonst rest => r :: (sonst.regs ++ rest.regs)
  | .awaits _ _ _ _ _ rest => rest.regs
  | .bindCallInd _ _ _ _ _ rest => rest.regs
  | .narrow _ _ _ sonst rest => sonst.regs ++ rest.regs
  | .narrowRequired _ _ _ rest => rest.regs
  | .exchange _ _ _ _ rest => rest.regs
  | .ite _ t e => e.regs ++ t.regs

def Arms.regs {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} : Arms D V l Γ Λ Λ' cs → List D.Reg
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

end Mono
end Gabbro.Grammatik
