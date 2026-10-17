/-
  File:      Grammatik/ZielOrtVollSem.lean
  Subject:   THE SEQUENTIAL SIDE OF `ziel_ort_voll` -- the frame semantics of
             EVERY residue of G (loops, their shims, the exits `leave`/`next`,
             the waiting residues), the covered fragment `vOk`, and the
             one-sided comparison of frame results.

  `ziel_ort` (`ZielOrtBeweis.lean`) replays each frame of G by the
  sequential semantics of its body, for bodies in the fragment `kOk` (no
  loops, no exits, no error channel, no oracle form). Here the frame
  semantics is extended to the whole residue type `GRest`:

  * `weiterZ r o` -- how the residue `r` continues from the outcome `o` of
    the code before it. A plain `ok` outcome runs `r`; `zurueck`, `grund`,
    `logik`, `hardware` pass through every residue; `leave`/`next` pass
    through `dann`/`schrumpf`/`frei` (they skip the rest of a loop body)
    and are consumed by the loop shims `travRest`/`wiederRest`/`ewigRest`
    exactly as `traverseLauf`/`retryLauf`/`foreverLauf` consume them. The
    loop residues `trav`/`wieder`/`ewig` run the remaining loop by the
    sequential loop functions themselves, with the remaining indices, tries
    or `forever` budget. `semZ' r σ ρ := weiterZ r (.ok σ ρ)`.
  * The waiting residues (`wartet`, `wartetSonst`) never run as a head
    (`rufG_nie_wartend`); they give `sonst` on `ok` and pass every other
    outcome through.
  * `ZErg.folgt a b`: the frame result `a` of the body is predicted by `b`
    -- `b` is `sonst` (no prediction) or `a` agrees with `b`. Some steps of
    G replace a residue by an end block (`narrow`/`pruefung`/float `else`
    blocks, the `else` block of `let … else` on a reason): if that end
    block ends in `leave`/`next` inside a loop, G is stuck there, and the
    new residue predicts nothing (`sonst`). A preorder with `sonst` on top.
  * `vOk K`: the covered fragment -- every form but the register and
    visibility forms (`regLies`, `regLiesElse`, `awaits`); an indirect call
    through a pointer of signature `n` where `K n` holds (every function of
    that signature has its contract carriers in the footprint, `KandOk`;
    decided over the complete member list, `kandB`); and `GRest.okV`,
    residues in it that read inside a footprint.
-/
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtSem

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
  | .bindAxiom _ _ _ _ _ _ _ rest => rest.vOk K
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => err.vOk K && rest.vOk K

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
  | _, _, .bindAxiom _ _ _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.vOk, Endblock.vOk, Endblock.vOk_alsBlock K rest]
  | _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, Block.vOk, Endblock.vOk, Endblock.vOk_alsBlock K rest]

/-- The candidates of an indirect call through a pointer of signature `n`
    -- every function of that signature -- have their contract carriers in
    the footprint `S`. -/
def KandOk (P : Programm D) (S : List (D.Tab ⊕ D.Glob)) (n : Nat) : Prop :=
  ∀ g : D.Fn, D.sig g = n → (P.requires g).orte ++ (P.ensures g).orte ⊆ S

/-- `KandOk` as the admissibility predicate of the fragment (for the replay). -/
noncomputable def kandP (P : Programm D) (S : List (D.Tab ⊕ D.Glob)) (n : Nat) : Bool :=
  @decide (KandOk P S n) (Classical.propDecidable _)

theorem kandP_ok {P : Programm D} {S : List (D.Tab ⊕ D.Glob)} {n : Nat}
    (h : kandP P S n = true) : KandOk P S n := by
  unfold kandP at h
  exact @of_decide_eq_true _ (Classical.propDecidable _) h

/-- `KandOk`, decided over a member list of the functions. -/
def kandB (P : Programm D) (fs : List D.Fn) (S : List (D.Tab ⊕ D.Glob)) (n : Nat) : Bool :=
  fs.all fun g => !(decide (D.sig g = n)) ||
    ((P.requires g).orte ++ (P.ensures g).orte).all fun o => S.any fun o' => decide (o' = o)

/-- Soundness of `kandB` over a complete member list. -/
theorem kandB_kandP (P : Programm D) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (S : List (D.Tab ⊕ D.Glob)) (n : Nat) (h : kandB P fs S n = true) : kandP P S n = true := by
  unfold kandP
  refine @decide_eq_true _ (Classical.propDecidable _) fun g hg o ho => ?_
  have h1 := (List.all_eq_true.mp h) g (hvoll g)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h1
  rcases h1 with h1 | h1
  · exact absurd hg h1
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
  | .assignThru .., _ => rfl
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
  | .regRead .., h => by simp [Block.vOk] at h
  | .regReadElse .., h => by simp [Block.vOk] at h
  | .awaits .., h => by simp [Block.vOk] at h
  | .exchange _ _ _ _ rest, h => by
      simp only [Block.vOk] at h ⊢
      exact Block.vOk_mono rest h
  | .narrow _ _ _ sonst rest, h => by
      simp only [Block.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_mono sonst h.1, Block.vOk_mono rest h.2⟩
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
  | .leave .., _ => rfl
  | .next .., _ => rfl
  | .cons s rest, h => by
      simp only [Endblock.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Stmt.vOk_mono s h.1, Endblock.vOk_mono rest h.2⟩
  | .bind _ rest, h => by
      simp only [Endblock.vOk] at h ⊢
      exact Endblock.vOk_mono rest h
  | .bindAxiom _ _ _ _ _ _ _ rest, h => by
      simp only [Endblock.vOk] at h ⊢
      exact Endblock.vOk_mono rest h
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest, h => by
      simp only [Endblock.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_mono err h.1, Endblock.vOk_mono rest h.2⟩

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

mutual

theorem Stmt.vOk_of_kOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → s.kOk = true → s.vOk K = true
  | .ite _ t e, h => by
      simp only [Stmt.kOk, Stmt.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Block.vOk_of_kOk t h.1, Block.vOk_of_kOk e h.2⟩
  | .onOption _ p a, h => by
      simp only [Stmt.kOk, Stmt.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Block.vOk_of_kOk p h.1, Block.vOk_of_kOk a h.2⟩
  | .onTag _ arms, h => by
      simp only [Stmt.kOk, Stmt.vOk] at h ⊢
      exact Arms.vOk_of_kOk arms h
  | .onWhy _ arms, h => by
      simp only [Stmt.kOk, Stmt.vOk] at h ⊢
      exact GrundArms.vOk_of_kOk arms h
  | .locks _ _ body, h => by
      simp only [Stmt.kOk, Stmt.vOk] at h ⊢
      exact Block.vOk_of_kOk body h
  | .breaking _ body, h => by
      simp only [Stmt.kOk, Stmt.vOk] at h ⊢
      exact Block.vOk_of_kOk body h
  | .traverse .., h => by simp [Stmt.kOk] at h
  | .retry .., h => by simp [Stmt.kOk] at h
  | .forever .., h => by simp [Stmt.kOk] at h
  | .callInd .., h => by simp [Stmt.kOk] at h
  | .assignSlot .., _ => rfl
  | .assignThru .., _ => rfl
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
  | .leave .., _ => rfl
  | .next .., _ => rfl

theorem Block.vOk_of_kOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → b.kOk = true → b.vOk K = true
  | .nil, _ => rfl
  | .cons s rest, h => by
      simp only [Block.kOk, Block.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Stmt.vOk_of_kOk s h.1, Block.vOk_of_kOk rest h.2⟩
  | .bind _ rest, h => by
      simp only [Block.kOk, Block.vOk] at h ⊢
      exact Block.vOk_of_kOk rest h
  | .bindCall _ _ _ _ _ rest, h => by
      simp only [Block.kOk, Block.vOk] at h ⊢
      exact Block.vOk_of_kOk rest h
  | .bindCallInd .., h => by simp [Block.kOk] at h
  | .bindCallElse .., h => by simp [Block.kOk] at h
  | .bindAxiom .., h => by simp [Block.kOk] at h
  | .bindAxiomElse .., h => by simp [Block.kOk] at h
  | .regRead .., h => by simp [Block.kOk] at h
  | .regReadElse .., h => by simp [Block.kOk] at h
  | .awaits .., h => by simp [Block.kOk] at h
  | .exchange _ _ _ _ rest, h => by
      simp only [Block.kOk, Block.vOk] at h ⊢
      exact Block.vOk_of_kOk rest h
  | .narrow _ _ _ sonst rest, h => by
      simp only [Block.kOk, Block.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_of_kOk sonst h.1, Block.vOk_of_kOk rest h.2⟩
  | .check _ sonst rest, h => by
      simp only [Block.kOk, Block.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_of_kOk sonst h.1, Block.vOk_of_kOk rest h.2⟩
  | .float _ _ _ _ _ rest, h => by
      simp only [Block.kOk, Block.vOk] at h ⊢
      exact Block.vOk_of_kOk rest h
  | .floatLit _ _ _ rest, h => by
      simp only [Block.kOk, Block.vOk] at h ⊢
      exact Block.vOk_of_kOk rest h
  | .floatOf _ _ _ rest, h => by
      simp only [Block.kOk, Block.vOk] at h ⊢
      exact Block.vOk_of_kOk rest h
  | .floatNarrow _ _ _ sonst rest, h => by
      simp only [Block.kOk, Block.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_of_kOk sonst h.1, Block.vOk_of_kOk rest h.2⟩

theorem Endblock.vOk_of_kOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (e : Endblock D V l Γ Λ) → e.kOk = true → e.vOk K = true
  | .ret .., _ => rfl
  | .retWhy .., _ => rfl
  | .leave .., _ => rfl
  | .next .., _ => rfl
  | .cons s rest, h => by
      simp only [Endblock.kOk, Endblock.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Stmt.vOk_of_kOk s h.1, Endblock.vOk_of_kOk rest h.2⟩
  | .bind _ rest, h => by
      simp only [Endblock.kOk, Endblock.vOk] at h ⊢
      exact Endblock.vOk_of_kOk rest h
  | .bindAxiom .., h => by simp [Endblock.kOk] at h
  | .bindAxiomElse .., h => by simp [Endblock.kOk] at h

theorem Arms.vOk_of_kOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    (a : Arms D V l Γ Λ Λ' cs) → a.kOk = true → a.vOk K = true
  | .nil, _ => rfl
  | .cons b rest, h => by
      simp only [Arms.kOk, Arms.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Block.vOk_of_kOk b h.1, Arms.vOk_of_kOk rest h.2⟩

theorem GrundArms.vOk_of_kOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} : (a : GrundArms D V l Γ Λ Λ' n) → a.kOk = true → a.vOk K = true
  | .nil, _ => rfl
  | .cons b rest, h => by
      simp only [GrundArms.kOk, GrundArms.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Block.vOk_of_kOk b h.1, GrundArms.vOk_of_kOk rest h.2⟩

end

end AusAlt
/-- The old fragment check implies the new one. -/
theorem programmImFragmentV_of (P : Programm D) (fs : List D.Fn)
    (h : programmImFragment P fs = true) : programmImFragmentV P fs = true :=
  List.all_eq_true.mpr fun f hf =>
    Endblock.vOk_of_kOk _ ((List.all_eq_true.mp h) f hf)

/-! ## 2. The one-sided comparison of frame results -/

/-- `a.folgt b`: the result `a` is predicted by `b` -- `b` predicts nothing
    (`sonst`), or `a` agrees with `b` up to the trace. -/
def ZErg.folgt {V : Vertrag D} (a b : ZErg V) : Prop := b = .sonst ∨ a.gleich b

namespace ZErg

variable {V : Vertrag D}

theorem folgt_refl (a : ZErg V) : a.folgt a := Or.inr (ZErg.gleich_refl a)

theorem folgt_of_gleich {a b : ZErg V} (h : a.gleich b) : a.folgt b := Or.inr h

theorem folgt_of_eq {a b : ZErg V} (h : a = b) : a.folgt b := by subst h; exact folgt_refl a

theorem folgt_sonst (a : ZErg V) : a.folgt .sonst := Or.inl rfl

theorem gleich_sonst_links {b : ZErg V} (h : ZErg.gleich .sonst b) : b = .sonst := by
  cases b <;> simp_all [ZErg.gleich]

theorem folgt_trans {a b c : ZErg V} (h1 : a.folgt b) (h2 : b.folgt c) : a.folgt c := by
  rcases h2 with h2 | h2
  · exact Or.inl h2
  · rcases h1 with h1 | h1
    · subst h1
      exact Or.inl (gleich_sonst_links h2)
    · exact Or.inr (ZErg.gleich_trans h1 h2)

theorem folgt_zurueck {a : ZErg V} {σ : World D} {v : ErgVal D V.erg}
    (h : a.folgt (.zurueck σ v)) : a.gleich (.zurueck σ v) := by
  rcases h with h | h
  · cases h
  · exact h

theorem folgt_logik {a : ZErg V} {e : Logik D} (h : a.folgt (.logik e)) :
    a.gleich (.logik e) := by
  rcases h with h | h
  · cases h
  · exact h

end ZErg
/-! ## 3. The frame semantics of every residue -/


end Gabbro.Grammatik
