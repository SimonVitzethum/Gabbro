module

public import Grammatik.Zielsatz.Kern.Spec
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Shapes -/

section Formen

variable {V : Vertrag D}

/-- A statement that never ends normally: a return, a reason, `leave`, `next`. -/
def Stmt.istAbschluss {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Bool
  | .ret .. => true
  | .retWhy .. => true
  | .retScoped .. => true
  | .retWhyScoped .. => true
  | .leave .. => true
  | .next .. => true
  | _ => false

/-- The block never ends normally: a statement on its spine is a return, a
    reason, `leave` or `next`. -/
def Block.terminal {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Bool
  | .nil => false
  | .cons s rest => s.istAbschluss || rest.terminal
  | .bind _ rest => rest.terminal
  | .bindCall _ _ _ _ _ rest => rest.terminal
  | .bindCallInd _ _ _ _ _ rest => rest.terminal
  | .bindCallElse _ _ _ _ _ _ rest => rest.terminal
  | .bindCallIndElse _ _ _ _ _ _ rest => rest.terminal
  | .bindAxiom _ _ _ _ _ _ _ rest => rest.terminal
  | .bindAxiomElse _ _ _ _ _ _ _ _ _ rest => rest.terminal
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => rest.terminal
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ _ rest => rest.terminal
  | .regRead _ _ rest => rest.terminal
  | .regReadElse _ _ _ _ rest => rest.terminal
  | .awaits _ _ _ _ _ rest => rest.terminal
  | .exchange _ _ _ _ rest => rest.terminal
  | .narrow _ _ _ _ rest => rest.terminal
  | .narrowRequired _ _ _ rest => rest.terminal
  | .check _ _ rest => rest.terminal
  | .float _ _ _ _ _ rest => rest.terminal
  | .floatLit _ _ _ rest => rest.terminal
  | .floatOf _ _ _ rest => rest.terminal
  | .floatNarrow _ _ _ _ rest => rest.terminal

/-- An end block run as a block never ends normally. -/
theorem Endblock.alsBlock_terminal {l : Bool} :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ), e.alsBlock.2.terminal = true
  | _, _, .ret _ _ => rfl
  | _, _, .retWhy _ _ => rfl
  | _, _, .retScoped _ _ => rfl
  | _, _, .retWhyScoped _ _ => rfl
  | _, _, .leave _ => rfl
  | _, _, .next _ => rfl
  | _, _, .cons _ rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest, Bool.or_true]
  | _, _, .bind _ rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .bindCall _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .bindAxiom _ _ _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .bindCallElse _ _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .bindAxiomElse _ _ _ _ _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .bindAxiomOpt _ _ _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .bindAxiomOptElse _ _ _ _ _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .regRead r hk rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .regReadElse r hk z sonst rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .awaits g pl hp hL hat rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .bindCallInd p args he hp hr rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .bindCallIndElse p args he hp hr err rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .narrow _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .narrowRequired _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .exchange _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .ite _ t _ => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal t]

/-- The residue takes an abrupt exit (`leave`/`next`): a loop shim behind
    `dann`/`schrumpf`/`frei`/`abbruch` layers. -/
def GRest.absorb {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : GRest D V l Γ Λ → Bool
  | .travRest .. => true
  | .wiederRest .. => true
  | .ewigRest .. => true
  | .verbrauchRest .. => true
  | .dann _ k => k.absorb
  | .schrumpf k => k.absorb
  | .frei _ k => k.absorb
  | .abbruch k => k.absorb
  | _ => false

/-- The residue is an `else` continuation (`abbruch`, under bindings). -/
def GRest.blockiert {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : GRest D V l Γ Λ → Bool
  | .abbruch _ => true
  | .leer => true
  | .schrumpf k => k.blockiert
  | _ => false

/-- A loop-flagged continuation takes abrupt exits. -/
def GRest.nimmtAb {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (k : GRest D V l Γ Λ) : Bool :=
  !l || k.absorb

/-- **The residue shape invariant**: no `ende` node inside a loop; every
    loop-flagged continuation absorbs abrupt exits; the block in front of
    an `else` continuation never ends normally; a loop, a release marker
    and a loop shim never continue into an `else` continuation. -/
def GRest.fOk : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Bool
  | l, _, _, .ende _ => !l
  | _, _, _, .dann b k => k.fOk && k.nimmtAb && (!k.blockiert || b.terminal)
  | _, _, _, .schrumpf k => k.fOk
  | _, _, _, .frei _ k => k.fOk && k.nimmtAb && !k.blockiert
  | _, _, _, .trav _ _ _ _ k => k.fOk && k.nimmtAb && !k.blockiert
  | _, _, _, .travRest _ _ _ _ k => k.fOk && k.nimmtAb && !k.blockiert
  | _, _, _, .verbrauch _ _ _ _ _ _ _ _ k => k.fOk && k.nimmtAb && !k.blockiert
  | _, _, _, .verbrauchRest _ _ _ _ _ _ _ _ _ k => k.fOk && k.nimmtAb && !k.blockiert
  | _, _, _, .wieder _ _ _ _ k => k.fOk && k.nimmtAb && !k.blockiert
  | _, _, _, .wiederRest _ _ _ _ k => k.fOk && k.nimmtAb && !k.blockiert
  | _, _, _, .ewig _ _ _ _ k => k.fOk && k.nimmtAb && !k.blockiert
  | _, _, _, .ewigRest _ _ _ _ k => k.fOk && k.nimmtAb && !k.blockiert
  | _, _, _, .wartet rest k => k.fOk && k.nimmtAb && (!k.blockiert || rest.terminal)
  | _, _, _, .wartetSonst _ _ rest k => k.fOk && k.nimmtAb && (!k.blockiert || rest.terminal)
  | _, _, _, .abbruch k => k.fOk
  | _, _, _, .leer => true

end Formen
/-! ## 2. The caller's shape -/

/-- **The frame `c` suspended by a call of `g` can receive `g`'s answer**:
    it does not wait and `g` has no reasons; or it waits for a value of
    `g`'s result type and `g` has no reasons; or it waits in `let … else`
    with `g`'s result type and `g`'s reason count. -/
def FormG (c : RufRahmenG D) (g : D.Fn) : Prop :=
  (c.wartend = false ∧ D.gruende g = 0) ∨
  (∃ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
      (restb : Block D (vertragVon D c.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D c.f) l Γ Λ') (ρc : Env D Γ),
    c.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ ∧ D.erg g = some τ ∧ D.gruende g = 0) ∨
  (∃ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty) (n : Nat)
      (err : Endblock D (vertragVon D c.f) l (.why n :: Γ) Λ)
      (restb : Block D (vertragVon D c.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D c.f) l Γ Λ') (ρc : Env D Γ),
    c.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩ ∧ D.erg g = some τ ∧ D.gruende g = n)

/-- Every suspended frame has the shape of the call that suspended it: the
    frame right below the frame of `g` can receive `g`'s answer, and so on
    down the stack. -/
def FormKette : D.Fn → List (RufRahmenG D) → Prop
  | _, [] => True
  | g, c :: rest => FormG c g ∧ FormKette c.f rest

/-- **The thread invariant of progress**: the head residue and every
    suspended residue are in shape and no `else` continuation; the stack
    has the shape of its calls. -/
def FortInvG (z : RufFadenG D) : Prop :=
  z.kopf.rest.2.2.2.2.fOk = true ∧ z.kopf.rest.2.2.2.2.blockiert = false ∧
  (∀ c ∈ z.stapel, c.rest.2.2.2.2.fOk = true ∧ c.rest.2.2.2.2.blockiert = false) ∧
  FormKette z.kopf.f z.stapel

/-! ## 3. The invariant along every rule -/

/-- A statement that ends normally is no return, reason or abrupt exit. -/
theorem Stmt.istAbschluss_ok {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (s : Stmt D V l Γ Λ Λ') (σ σ' : World D) (ρ ρ' : Env D Γ)
    (h : execStmt O passes R s σ ρ = .ok σ' ρ') : s.istAbschluss = false := by
  cases s <;> first | rfl | (simp only [execStmt, reduceCtorEq] at h)

end Gabbro.Grammatik
