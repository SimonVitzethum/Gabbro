module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtSem

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The covered fragment

    `vOk K`: every form but the register and visibility forms; an indirect
    call through a pointer of signature `n` is admitted where `K n` holds.
    The replay takes `K n` to be "every function of signature `n` has its
    contract carriers in the caller's footprint" (`KandOk`); the decidable
    program fact computes it over the complete member list (`kandB`). -/

mutual

/-- The statement is in the covered fragment. -/
def Stmt.vOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (K : Nat → Bool) :
    Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => t.vOk K && e.vOk K
  | .onOption _ p a => p.vOk K && a.vOk K
  | .onTag _ arms => arms.vOk K
  | .onWhy _ arms => arms.vOk K
  | .locks _ _ body => body.vOk K
  | .breaking _ body => body.vOk K
  | .traverse _ _ body => body.vOk K
  | .consumeTraverse _ _ _ _ _ _ body => body.vOk K
  | .retry _ _ body ueber => body.vOk K && ueber.vOk K
  | .forever _ _ body => body.vOk K
  | .callInd (n := n) .. => K n
  | _ => true

/-- The block is in the covered fragment: no register read, no `awaits`. -/
def Block.vOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (K : Nat → Bool) :
    Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => s.vOk K && rest.vOk K
  | .bind _ rest => rest.vOk K
  | .bindCall _ _ _ _ _ rest => rest.vOk K
  | .bindCallInd (n := n) _ _ _ _ _ rest => K n && rest.vOk K
  | .bindCallElse _ _ _ _ _ err rest => err.vOk K && rest.vOk K
  | .bindAxiom _ _ _ _ _ _ _ rest => rest.vOk K
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => err.vOk K && rest.vOk K
  | .regRead .. => false
  | .regReadElse .. => false
  | .awaits .. => false
  | .exchange _ _ _ _ rest => rest.vOk K
  | .narrow _ _ _ sonst rest => sonst.vOk K && rest.vOk K
  | .narrowRequired _ _ _ rest => rest.vOk K
  | .check _ sonst rest => sonst.vOk K && rest.vOk K
  | .float _ _ _ _ _ rest => rest.vOk K
  | .floatLit _ _ _ rest => rest.vOk K
  | .floatOf _ _ _ rest => rest.vOk K
  | .floatNarrow _ _ _ sonst rest => sonst.vOk K && rest.vOk K

def Endblock.vOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (K : Nat → Bool) :
    Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retWhy .. => true
  | .leave .. => true
  | .next .. => true
  | .cons s rest => s.vOk K && rest.vOk K
  | .bind _ rest => rest.vOk K
  | .bindCall _ _ _ _ _ rest => rest.vOk K
  | .bindCallElse _ _ _ _ _ err rest => err.vOk K && rest.vOk K
  | .bindAxiom _ _ _ _ _ _ _ rest => rest.vOk K
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => err.vOk K && rest.vOk K
  | .regRead .. => false
  | .regReadElse .. => false
  | .awaits .. => false
  | .bindCallInd (n := n) _ _ _ _ _ rest => K n && rest.vOk K
  | .narrow _ _ _ sonst rest => sonst.vOk K && rest.vOk K
  | .narrowRequired _ _ _ rest => rest.vOk K
  | .exchange _ _ _ _ rest => rest.vOk K
  | .ite _ t e => e.vOk K && t.vOk K

def Arms.vOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (K : Nat → Bool) : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => b.vOk K && rest.vOk K

def GrundArms.vOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} (K : Nat → Bool) : GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => b.vOk K && rest.vOk K

end
theorem Endblock.vOk_alsBlock {V : Vertrag D} {l : Bool} (K : Nat → Bool) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ), e.alsBlock.2.vOk K = e.vOk K
  | _, _, .ret _ _ => rfl
  | _, _, .retWhy _ _ => rfl
  | _, _, .leave _ => rfl
  | _, _, .next _ => rfl
  | _, _, .cons s rest => by
      simp only [Endblock.alsBlock, Block.vOk, Endblock.vOk, Endblock.vOk_alsBlock K rest]
  | _, _, .bind _ rest => by
      simp only [Endblock.alsBlock, Block.vOk, Endblock.vOk, Endblock.vOk_alsBlock K rest]
  | _, _, .bindCall _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.vOk, Endblock.vOk, Endblock.vOk_alsBlock K rest]
  | _, _, .bindAxiom _ _ _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.vOk, Endblock.vOk, Endblock.vOk_alsBlock K rest]
  | _, _, .bindCallElse _ _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, Block.vOk, Endblock.vOk, Endblock.vOk_alsBlock K rest]
  | _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, Block.vOk, Endblock.vOk, Endblock.vOk_alsBlock K rest]
  | _, _, .regRead r hk rest => by
      simp only [Endblock.alsBlock, Block.vOk, Endblock.vOk, Endblock.vOk_alsBlock K rest]
  | _, _, .regReadElse r hk z sonst rest => by
      simp only [Endblock.alsBlock, Block.vOk, Endblock.vOk, Endblock.vOk_alsBlock K rest]
  | _, _, .awaits g pl hp hL hat rest => by
      simp only [Endblock.alsBlock, Block.vOk, Endblock.vOk, Endblock.vOk_alsBlock K rest]
  | _, _, .bindCallInd p args he hp hr rest => by
      simp only [Endblock.alsBlock, Block.vOk, Endblock.vOk, Endblock.vOk_alsBlock K rest]
  | _, _, .narrow _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.vOk, Endblock.vOk, Endblock.vOk_alsBlock K rest]
  | _, _, .exchange _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.vOk, Endblock.vOk, Endblock.vOk_alsBlock K rest]
  | _, _, .ite _ t _ => by
      simp only [Endblock.alsBlock, Block.vOk, Endblock.vOk, Endblock.vOk_alsBlock K t]

/-- The candidates of an indirect call through a pointer of signature `n`
    -- every function that conforms to it -- have their contract carriers in
    the footprint `S`. -/
def KandOk (P : Programm D) (S : List (D.Tab ⊕ D.Glob)) (n : Nat) : Prop :=
  ∀ g : D.Fn, D.passt g n = true → (P.requires g).orte ++ (P.ensures g).orte ⊆ S

/-- `KandOk` as the admissibility predicate of the fragment (for the replay). -/
noncomputable def kandP (P : Programm D) (S : List (D.Tab ⊕ D.Glob)) (n : Nat) : Bool :=
  @decide (KandOk P S n) (Classical.propDecidable _)

theorem kandP_ok {P : Programm D} {S : List (D.Tab ⊕ D.Glob)} {n : Nat}
    (h : kandP P S n = true) : KandOk P S n := by
  unfold kandP at h
  exact @of_decide_eq_true _ (Classical.propDecidable _) h

/-- `KandOk`, decided over a member list of the functions. -/
def kandB (P : Programm D) (fs : List D.Fn) (S : List (D.Tab ⊕ D.Glob)) (n : Nat) : Bool :=
  fs.all fun g => !(D.passt g n) ||
    ((P.requires g).orte ++ (P.ensures g).orte).all fun o => S.any fun o' => decide (o' = o)

/-- Soundness of `kandB` over a complete member list. -/
theorem kandB_kandP (P : Programm D) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (S : List (D.Tab ⊕ D.Glob)) (n : Nat) (h : kandB P fs S n = true) : kandP P S n = true := by
  unfold kandP
  refine @decide_eq_true _ (Classical.propDecidable _) fun g hg o ho => ?_
  have h1 := (List.all_eq_true.mp h) g (hvoll g)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h1
  rcases h1 with h1 | h1
  · exact absurd hg (by rw [h1]; decide)
  · obtain ⟨o', ho', he⟩ := List.any_eq_true.mp ((List.all_eq_true.mp h1) o ho)
    rw [← of_decide_eq_true he]
    exact ho'

/-- **The covered fragment, as a decidable program fact**: every body is in
    `vOk` (loops, exits, the error channel, axiom calls admitted; an
    indirect call admitted where every function of its signature has its
    contract carriers in the caller's footprint; register reads and
    `awaits` not). -/
def programmImFragmentV (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun f => (P.rumpf f).vOk (kandB P fs (fussOrte P f))

theorem armWahlG_vOk {V : Vertrag D} {K : Nat → Bool} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    arms.vOk K = true → (armWahlG arms v).2.1.vOk K = true
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨⟨0, _⟩, _⟩, h => by
      simp only [Arms.vOk, Bool.and_eq_true] at h
      exact h.1
  | _, .cons _ rest, ⟨⟨_ + 1, _⟩, _⟩, h => by
      simp only [Arms.vOk, Bool.and_eq_true] at h
      exact armWahlG_vOk rest _ h.2

theorem armWahlG_vOk' {V : Vertrag D} {K : Nat → Bool} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs)
    (v : Wert D (.sum cs)) {c : Option (Int × Int)} {b : Block D V l (ArmCtx Γ c) Λ Λ'}
    {nutz : Nutzlast c} (hw : armWahlG arms v = ⟨c, b, nutz⟩) (h : arms.vOk K = true) :
    b.vOk K = true := by
  have h0 := armWahlG_vOk arms v h
  rw [hw] at h0
  exact h0

theorem grundWahlG_vOk {V : Vertrag D} {K : Nat → Bool} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
    arms.vOk K = true → (grundWahlG arms r).vOk K = true
  | _, .nil, ⟨k, hk⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨0, _⟩, h => by
      simp only [GrundArms.vOk, Bool.and_eq_true] at h
      exact h.1
  | _, .cons _ rest, ⟨_ + 1, _⟩, h => by
      simp only [GrundArms.vOk, Bool.and_eq_true] at h
      exact grundWahlG_vOk rest _ h.2

/-! ### The admissibility predicate is monotone -/

section Mono

variable {K K' : Nat → Bool} (hKK : ∀ n, K n = true → K' n = true)
include hKK

mutual

theorem Stmt.vOk_mono {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → s.vOk K = true → s.vOk K' = true
  | .ite _ t e, h => by
      simp only [Stmt.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Block.vOk_mono t h.1, Block.vOk_mono e h.2⟩
  | .onOption _ p a, h => by
      simp only [Stmt.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Block.vOk_mono p h.1, Block.vOk_mono a h.2⟩
  | .onTag _ arms, h => by
      simp only [Stmt.vOk] at h ⊢
      exact Arms.vOk_mono arms h
  | .onWhy _ arms, h => by
      simp only [Stmt.vOk] at h ⊢
      exact GrundArms.vOk_mono arms h
  | .locks _ _ body, h => by
      simp only [Stmt.vOk] at h ⊢
      exact Block.vOk_mono body h
  | .breaking _ body, h => by
      simp only [Stmt.vOk] at h ⊢
      exact Block.vOk_mono body h
  | .traverse _ _ body, h => by
      simp only [Stmt.vOk] at h ⊢
      exact Block.vOk_mono body h
  | .consumeTraverse _ _ _ _ _ _ body, h => by
      simp only [Stmt.vOk] at h ⊢
      exact Block.vOk_mono body h
  | .retry _ _ body ueber, h => by
      simp only [Stmt.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Block.vOk_mono body h.1, Block.vOk_mono ueber h.2⟩
  | .forever _ _ body, h => by
      simp only [Stmt.vOk] at h ⊢
      exact Block.vOk_mono body h
  | .callInd .., h => by
      simp only [Stmt.vOk] at h ⊢
      exact hKK _ h
  | .assignSlot .., _ => rfl
  | .assignThru .., _ | .assignSlotRef .., _ => rfl
  | .assignGlob .., _ => rfl
  | .putBytes .., _ => rfl
  | .assignVar .., _ => rfl
  | .shift .., _ => rfl
  | .call .., _ => rfl
  | .axiomCall .., _ => rfl
  | .regWrite .., _ => rfl
  | .transition .., _ => rfl
  | .publish .., _ => rfl
  | .advances .., _ => rfl
  | .retires .., _ => rfl
  | .ret .., _ => rfl
  | .retWhy .., _ => rfl
  | .retScoped .., _ => rfl
  | .retWhyScoped .., _ => rfl
  | .leave .., _ => rfl
  | .next .., _ => rfl

theorem Block.vOk_mono {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → b.vOk K = true → b.vOk K' = true
  | .nil, _ => rfl
  | .cons s rest, h => by
      simp only [Block.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Stmt.vOk_mono s h.1, Block.vOk_mono rest h.2⟩
  | .bind _ rest, h => by
      simp only [Block.vOk] at h ⊢
      exact Block.vOk_mono rest h
  | .bindCall _ _ _ _ _ rest, h => by
      simp only [Block.vOk] at h ⊢
      exact Block.vOk_mono rest h
  | .bindCallInd _ _ _ _ _ rest, h => by
      simp only [Block.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨hKK _ h.1, Block.vOk_mono rest h.2⟩
  | .bindCallElse _ _ _ _ _ err rest, h => by
      simp only [Block.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_mono err h.1, Block.vOk_mono rest h.2⟩
  | .bindAxiom _ _ _ _ _ _ _ rest, h => by
      simp only [Block.vOk] at h ⊢
      exact Block.vOk_mono rest h
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest, h => by
      simp only [Block.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_mono err h.1, Block.vOk_mono rest h.2⟩
  | .regRead .., h => by simp only [Block.vOk, Bool.false_eq_true] at h
  | .regReadElse .., h => by simp only [Block.vOk, Bool.false_eq_true] at h
  | .awaits .., h => by simp only [Block.vOk, Bool.false_eq_true] at h
  | .exchange _ _ _ _ rest, h => by
      simp only [Block.vOk] at h ⊢
      exact Block.vOk_mono rest h
  | .narrow _ _ _ sonst rest, h => by
      simp only [Block.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_mono sonst h.1, Block.vOk_mono rest h.2⟩
  | .narrowRequired _ _ _ rest, h => by
      simp only [Block.vOk] at h ⊢
      exact Block.vOk_mono rest h
  | .check _ sonst rest, h => by
      simp only [Block.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_mono sonst h.1, Block.vOk_mono rest h.2⟩
  | .float _ _ _ _ _ rest, h => by
      simp only [Block.vOk] at h ⊢
      exact Block.vOk_mono rest h
  | .floatLit _ _ _ rest, h => by
      simp only [Block.vOk] at h ⊢
      exact Block.vOk_mono rest h
  | .floatOf _ _ _ rest, h => by
      simp only [Block.vOk] at h ⊢
      exact Block.vOk_mono rest h
  | .floatNarrow _ _ _ sonst rest, h => by
      simp only [Block.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_mono sonst h.1, Block.vOk_mono rest h.2⟩

theorem Endblock.vOk_mono {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (e : Endblock D V l Γ Λ) → e.vOk K = true → e.vOk K' = true
  | .ret .., _ => rfl
  | .retWhy .., _ => rfl
  | .retScoped .., _ => rfl
  | .retWhyScoped .., _ => rfl
  | .leave .., _ => rfl
  | .next .., _ => rfl
  | .cons s rest, h => by
      simp only [Endblock.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Stmt.vOk_mono s h.1, Endblock.vOk_mono rest h.2⟩
  | .bind _ rest, h => by
      simp only [Endblock.vOk] at h ⊢
      exact Endblock.vOk_mono rest h
  | .bindCall _ _ _ _ _ rest, h => by
      simp only [Endblock.vOk] at h ⊢
      exact Endblock.vOk_mono rest h
  | .bindCallElse _ _ _ _ _ err rest, h => by
      simp only [Endblock.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_mono err h.1, Endblock.vOk_mono rest h.2⟩
  | .bindAxiom _ _ _ _ _ _ _ rest, h => by
      simp only [Endblock.vOk] at h ⊢
      exact Endblock.vOk_mono rest h
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest, h => by
      simp only [Endblock.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_mono err h.1, Endblock.vOk_mono rest h.2⟩
  | .regRead .., h => by simp only [Endblock.vOk, Bool.false_eq_true] at h
  | .regReadElse .., h => by simp only [Endblock.vOk, Bool.false_eq_true] at h
  | .awaits .., h => by simp only [Endblock.vOk, Bool.false_eq_true] at h
  | .bindCallInd _ _ _ _ _ rest, h => by
      simp only [Endblock.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨hKK _ h.1, Endblock.vOk_mono rest h.2⟩
  | .narrow _ _ _ sonst rest, h => by
      simp only [Endblock.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_mono sonst h.1, Endblock.vOk_mono rest h.2⟩
  | .narrowRequired _ _ _ rest, h => by
      simp only [Endblock.vOk] at h ⊢
      exact Endblock.vOk_mono rest h
  | .exchange _ _ _ _ rest, h => by
      simp only [Endblock.vOk] at h ⊢
      exact Endblock.vOk_mono rest h
  | .ite _ t e, h => by
      simp only [Endblock.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_mono e h.1, Endblock.vOk_mono t h.2⟩

theorem Arms.vOk_mono {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    (a : Arms D V l Γ Λ Λ' cs) → a.vOk K = true → a.vOk K' = true
  | .nil, _ => rfl
  | .cons b rest, h => by
      simp only [Arms.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Block.vOk_mono b h.1, Arms.vOk_mono rest h.2⟩

theorem GrundArms.vOk_mono {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} : (a : GrundArms D V l Γ Λ Λ' n) → a.vOk K = true → a.vOk K' = true
  | .nil, _ => rfl
  | .cons b rest, h => by
      simp only [GrundArms.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Block.vOk_mono b h.1, GrundArms.vOk_mono rest h.2⟩

end

end Mono
/-- The decided fragment gives the fragment the replay reads: every body is
    in `vOk` with the admissibility `KandOk` of its own footprint. -/
theorem programmImFragmentV_ok (P : Programm D) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (h : programmImFragmentV P fs = true) (f : D.Fn) :
    (P.rumpf f).vOk (kandP P (fussOrte P f)) = true :=
  Endblock.vOk_mono (kandB_kandP P hvoll _) _ ((List.all_eq_true.mp h) f (hvoll f))

/-! ### The old fragment is inside the new one -/

section AusAlt

variable {K : Nat → Bool}

end AusAlt
end Gabbro.Grammatik
