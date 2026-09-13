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
import Grammatik.ZielOrtSem

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
  | .onGrund _ arms => arms.vOk K
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
  | .regLies .. => false
  | .regLiesElse .. => false
  | .awaits .. => false
  | .exchange _ _ _ _ rest => rest.vOk K
  | .narrow _ _ _ sonst rest => sonst.vOk K && rest.vOk K
  | .pruefung _ sonst rest => sonst.vOk K && rest.vOk K
  | .gleit _ _ _ _ _ rest => rest.vOk K
  | .gleitLit _ _ _ rest => rest.vOk K
  | .gleitVon _ _ _ rest => rest.vOk K
  | .gleitNarrow _ _ _ sonst rest => sonst.vOk K && rest.vOk K

def Endblock.vOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (K : Nat → Bool) :
    Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retGrund .. => true
  | .leave .. => true
  | .next .. => true
  | .cons s rest => s.vOk K && rest.vOk K
  | .bind _ rest => rest.vOk K

def Arms.vOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (K : Nat → Bool) : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => b.vOk K && rest.vOk K

def GrundArms.vOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} (K : Nat → Bool) : GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => b.vOk K && rest.vOk K

end

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
  | .onGrund _ arms, h => by
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
  | .assignDurch .., _ => rfl
  | .assignGlob .., _ => rfl
  | .schreibBytes .., _ => rfl
  | .assignVar .., _ => rfl
  | .uebergang .., _ => rfl
  | .call .., _ => rfl
  | .axiomCall .., _ => rfl
  | .regSchreib .., _ => rfl
  | .transition .., _ => rfl
  | .publish .., _ => rfl
  | .advances .., _ => rfl
  | .retires .., _ => rfl
  | .ret .., _ => rfl
  | .retGrund .., _ => rfl
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
  | .regLies .., h => by simp [Block.vOk] at h
  | .regLiesElse .., h => by simp [Block.vOk] at h
  | .awaits .., h => by simp [Block.vOk] at h
  | .exchange _ _ _ _ rest, h => by
      simp only [Block.vOk] at h ⊢
      exact Block.vOk_mono rest h
  | .narrow _ _ _ sonst rest, h => by
      simp only [Block.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_mono sonst h.1, Block.vOk_mono rest h.2⟩
  | .pruefung _ sonst rest, h => by
      simp only [Block.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_mono sonst h.1, Block.vOk_mono rest h.2⟩
  | .gleit _ _ _ _ _ rest, h => by
      simp only [Block.vOk] at h ⊢
      exact Block.vOk_mono rest h
  | .gleitLit _ _ _ rest, h => by
      simp only [Block.vOk] at h ⊢
      exact Block.vOk_mono rest h
  | .gleitVon _ _ _ rest, h => by
      simp only [Block.vOk] at h ⊢
      exact Block.vOk_mono rest h
  | .gleitNarrow _ _ _ sonst rest, h => by
      simp only [Block.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_mono sonst h.1, Block.vOk_mono rest h.2⟩

theorem Endblock.vOk_mono {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (e : Endblock D V l Γ Λ) → e.vOk K = true → e.vOk K' = true
  | .ret .., _ => rfl
  | .retGrund .., _ => rfl
  | .leave .., _ => rfl
  | .next .., _ => rfl
  | .cons s rest, h => by
      simp only [Endblock.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Stmt.vOk_mono s h.1, Endblock.vOk_mono rest h.2⟩
  | .bind _ rest, h => by
      simp only [Endblock.vOk] at h ⊢
      exact Endblock.vOk_mono rest h

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
  | .onGrund _ arms, h => by
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
  | .assignDurch .., _ => rfl
  | .assignGlob .., _ => rfl
  | .schreibBytes .., _ => rfl
  | .assignVar .., _ => rfl
  | .uebergang .., _ => rfl
  | .call .., _ => rfl
  | .axiomCall .., _ => rfl
  | .regSchreib .., _ => rfl
  | .transition .., _ => rfl
  | .publish .., _ => rfl
  | .advances .., _ => rfl
  | .retires .., _ => rfl
  | .ret .., _ => rfl
  | .retGrund .., _ => rfl
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
  | .regLies .., h => by simp [Block.kOk] at h
  | .regLiesElse .., h => by simp [Block.kOk] at h
  | .awaits .., h => by simp [Block.kOk] at h
  | .exchange _ _ _ _ rest, h => by
      simp only [Block.kOk, Block.vOk] at h ⊢
      exact Block.vOk_of_kOk rest h
  | .narrow _ _ _ sonst rest, h => by
      simp only [Block.kOk, Block.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_of_kOk sonst h.1, Block.vOk_of_kOk rest h.2⟩
  | .pruefung _ sonst rest, h => by
      simp only [Block.kOk, Block.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_of_kOk sonst h.1, Block.vOk_of_kOk rest h.2⟩
  | .gleit _ _ _ _ _ rest, h => by
      simp only [Block.kOk, Block.vOk] at h ⊢
      exact Block.vOk_of_kOk rest h
  | .gleitLit _ _ _ rest, h => by
      simp only [Block.kOk, Block.vOk] at h ⊢
      exact Block.vOk_of_kOk rest h
  | .gleitVon _ _ _ rest, h => by
      simp only [Block.kOk, Block.vOk] at h ⊢
      exact Block.vOk_of_kOk rest h
  | .gleitNarrow _ _ _ sonst rest, h => by
      simp only [Block.kOk, Block.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Endblock.vOk_of_kOk sonst h.1, Block.vOk_of_kOk rest h.2⟩

theorem Endblock.vOk_of_kOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (e : Endblock D V l Γ Λ) → e.kOk = true → e.vOk K = true
  | .ret .., _ => rfl
  | .retGrund .., _ => rfl
  | .leave .., _ => rfl
  | .next .., _ => rfl
  | .cons s rest, h => by
      simp only [Endblock.kOk, Endblock.vOk, Bool.and_eq_true] at h ⊢
      exact ⟨Stmt.vOk_of_kOk s h.1, Endblock.vOk_of_kOk rest h.2⟩
  | .bind _ rest, h => by
      simp only [Endblock.kOk, Endblock.vOk] at h ⊢
      exact Endblock.vOk_of_kOk rest h

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

section Weiter

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}

/-- Run `f` on an `ok` outcome, pass every other outcome through. -/
def laufA {l : Bool} {Γ : Ctx} (f : World D → Env D Γ → Ausgang V l Γ) :
    Ausgang V l Γ → Ausgang V l Γ
  | .ok σ ρ => f σ ρ
  | o => o

/-- The invariant/bound read of a loop head, exactly as `execStmt` reads it. -/
def leseB {Γ : Ctx} {Λ : List (Res D)} (c : Expr D Γ Λ .bool) :
    World D → Env D Γ → World D × Bool :=
  fun σ ρ => let σ := σ.lese Λ c.orte; (σ, wahr? (eval σ c σ ρ))

/-- **How a residue continues from an outcome** (see the file header). -/
def weiterZ : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ →
    Ausgang V l Γ → ZErg V
  | _, _, _, .ende e, o =>
      match o with
      | .ok σ ρ => zErg (execEnd O passes R e σ ρ)
      | .zurueck σ v => .zurueck σ v
      | .logik e => .logik e
      | _ => .sonst
  | _, _, _, .dann b k, o => weiterZ k (laufA (fun σ ρ => execBlock O passes R b σ ρ) o)
  | _, _, _, .schrumpf k, o => weiterZ k o.schrumpf
  | _, _, _, .frei L k, o => weiterZ k (o.mapWelt (·.gibt L))
  | _, _, _, .trav _ inv body ks k, o =>
      weiterZ k (laufA (traverseLauf (fun σ ρ => execBlock O passes R body σ ρ) (leseB inv) ks) o)
  | _, _, _, .travRest _ inv body ks k, o =>
      match o with
      | .ok σ ρ =>
          weiterZ k (traverseLauf (fun σ ρ => execBlock O passes R body σ ρ) (leseB inv) ks σ ρ.tail)
      | .next _ σ ρ =>
          weiterZ k (traverseLauf (fun σ ρ => execBlock O passes R body σ ρ) (leseB inv) ks σ ρ.tail)
      | .leave _ σ ρ =>
          weiterZ k (if (leseB inv σ ρ.tail).2 = true then .ok (leseB inv σ ρ.tail).1 ρ.tail
            else .logik .schleife)
      | .zurueck σ v => weiterZ k (.zurueck σ v)
      | .grund σ r => weiterZ k (.grund σ r)
      | .logik e => weiterZ k (.logik e)
      | .hardware e => weiterZ k (.hardware e)
  | _, _, _, .wieder n bis body ueber k, o =>
      weiterZ k (laufA (retryLauf (fun σ ρ => execBlock O passes R body σ ρ) (leseB bis)
        (fun σ ρ => execBlock O passes R ueber σ ρ) n) o)
  | _, _, _, .wiederRest n bis body ueber k, o =>
      match o with
      | .ok σ ρ => weiterZ k (retryLauf (fun σ ρ => execBlock O passes R body σ ρ) (leseB bis)
          (fun σ ρ => execBlock O passes R ueber σ ρ) n σ ρ)
      | .next _ σ ρ => weiterZ k (retryLauf (fun σ ρ => execBlock O passes R body σ ρ) (leseB bis)
          (fun σ ρ => execBlock O passes R ueber σ ρ) n σ ρ)
      | .leave _ σ ρ => weiterZ k (.ok σ ρ)
      | .zurueck σ v => weiterZ k (.zurueck σ v)
      | .grund σ r => weiterZ k (.grund σ r)
      | .logik e => weiterZ k (.logik e)
      | .hardware e => weiterZ k (.hardware e)
  | _, _, _, .ewig a n inv body k, o =>
      weiterZ k (laufA (foreverLauf a (fun σ ρ => execBlock O passes R body σ ρ) (leseB inv) n) o)
  | _, _, _, .ewigRest a n inv body k, o =>
      match o with
      | .ok σ ρ => weiterZ k (foreverLauf a (fun σ ρ => execBlock O passes R body σ ρ)
          (leseB inv) n σ ρ)
      | .next _ σ ρ => weiterZ k (foreverLauf a (fun σ ρ => execBlock O passes R body σ ρ)
          (leseB inv) n σ ρ)
      | .leave _ σ ρ => weiterZ k (.ok σ ρ)
      | .zurueck σ v => weiterZ k (.zurueck σ v)
      | .grund σ r => weiterZ k (.grund σ r)
      | .logik e => weiterZ k (.logik e)
      | .hardware e => weiterZ k (.hardware e)
  | _, _, _, .wartet _ k, o =>
      match o with
      | .ok _ _ => .sonst
      | o => weiterZ k o
  | _, _, _, .wartetSonst _ _ _ k, o =>
      match o with
      | .ok _ _ => .sonst
      | o => weiterZ k o

/-- The frame semantics of a residue: run it from `σ`, `ρ`. -/
def semV {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ) (σ : World D)
    (ρ : Env D Γ) : ZErg V :=
  weiterZ O passes R r (.ok σ ρ)

variable {l : Bool} {Γ : Ctx}

theorem laufA_ok (f : World D → Env D Γ → Ausgang V l Γ) (σ : World D) (ρ : Env D Γ) :
    laufA f (.ok σ ρ) = f σ ρ := rfl

/-- A block with a head statement: the head, then the rest on `ok`. -/
theorem execBlock_cons_laufA {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (σ : World D) (ρ : Env D Γ) :
    execBlock O passes R (.cons s rest) σ ρ =
      laufA (fun σ ρ => execBlock O passes R rest σ ρ) (execStmt O passes R s σ ρ) := by
  simp only [execBlock]
  cases execStmt O passes R s σ ρ <;> rfl

theorem semV_dann {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.dann b k) σ ρ = weiterZ O passes R k (execBlock O passes R b σ ρ) := rfl

theorem semV_dann_cons {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.dann (.cons s rest) k) σ ρ =
      weiterZ O passes R (.dann rest k) (execStmt O passes R s σ ρ) := by
  rw [semV_dann, execBlock_cons_laufA]
  rfl

/-! ### Outcomes that pass through every residue -/

theorem weiterZ_logik : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (k : GRest D V l Γ Λ)
    (e : Logik D), weiterZ O passes R k (.logik e) = .logik e
  | _, _, _, .ende _, _ => rfl
  | _, _, _, .dann _ k, e => weiterZ_logik k e
  | _, _, _, .schrumpf k, e => weiterZ_logik k e
  | _, _, _, .frei _ k, e => weiterZ_logik k e
  | _, _, _, .trav _ _ _ _ k, e => weiterZ_logik k e
  | _, _, _, .travRest _ _ _ _ k, e => weiterZ_logik k e
  | _, _, _, .wieder _ _ _ _ k, e => weiterZ_logik k e
  | _, _, _, .wiederRest _ _ _ _ k, e => weiterZ_logik k e
  | _, _, _, .ewig _ _ _ _ k, e => weiterZ_logik k e
  | _, _, _, .ewigRest _ _ _ _ k, e => weiterZ_logik k e
  | _, _, _, .wartet _ k, e => weiterZ_logik k e
  | _, _, _, .wartetSonst _ _ _ k, e => weiterZ_logik k e

theorem weiterZ_grund : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (k : GRest D V l Γ Λ)
    (σ : World D) (r : Fin V.gruende), weiterZ O passes R k (.grund σ r) = .sonst
  | _, _, _, .ende _, _, _ => rfl
  | _, _, _, .dann _ k, σ, r => weiterZ_grund k σ r
  | _, _, _, .schrumpf k, σ, r => weiterZ_grund k σ r
  | _, _, _, .frei L k, σ, r => weiterZ_grund k (σ.gibt L) r
  | _, _, _, .trav _ _ _ _ k, σ, r => weiterZ_grund k σ r
  | _, _, _, .travRest _ _ _ _ k, σ, r => weiterZ_grund k σ r
  | _, _, _, .wieder _ _ _ _ k, σ, r => weiterZ_grund k σ r
  | _, _, _, .wiederRest _ _ _ _ k, σ, r => weiterZ_grund k σ r
  | _, _, _, .ewig _ _ _ _ k, σ, r => weiterZ_grund k σ r
  | _, _, _, .ewigRest _ _ _ _ k, σ, r => weiterZ_grund k σ r
  | _, _, _, .wartet _ k, σ, r => weiterZ_grund k σ r
  | _, _, _, .wartetSonst _ _ _ k, σ, r => weiterZ_grund k σ r

theorem weiterZ_hardware : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (k : GRest D V l Γ Λ)
    (e : Hardware D), weiterZ O passes R k (.hardware e) = .sonst
  | _, _, _, .ende _, _ => rfl
  | _, _, _, .dann _ k, e => weiterZ_hardware k e
  | _, _, _, .schrumpf k, e => weiterZ_hardware k e
  | _, _, _, .frei _ k, e => weiterZ_hardware k e
  | _, _, _, .trav _ _ _ _ k, e => weiterZ_hardware k e
  | _, _, _, .travRest _ _ _ _ k, e => weiterZ_hardware k e
  | _, _, _, .wieder _ _ _ _ k, e => weiterZ_hardware k e
  | _, _, _, .wiederRest _ _ _ _ k, e => weiterZ_hardware k e
  | _, _, _, .ewig _ _ _ _ k, e => weiterZ_hardware k e
  | _, _, _, .ewigRest _ _ _ _ k, e => weiterZ_hardware k e
  | _, _, _, .wartet _ k, e => weiterZ_hardware k e
  | _, _, _, .wartetSonst _ _ _ k, e => weiterZ_hardware k e

theorem sg_gibt (σ : World D) (L : D.Lock) : SG (σ.gibt L) σ := ⟨rfl, rfl⟩

theorem weiterZ_zurueck : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (k : GRest D V l Γ Λ)
    (σ : World D) (v : ErgVal D V.erg),
    (weiterZ O passes R k (.zurueck σ v)).gleich (.zurueck σ v)
  | _, _, _, .ende _, _, _ => ZErg.gleich_refl _
  | _, _, _, .dann _ k, σ, v => weiterZ_zurueck k σ v
  | _, _, _, .schrumpf k, σ, v => weiterZ_zurueck k σ v
  | _, _, _, .frei L k, σ, v =>
      ZErg.gleich_trans (weiterZ_zurueck k (σ.gibt L) v) ⟨sg_gibt σ L, rfl⟩
  | _, _, _, .trav _ _ _ _ k, σ, v => weiterZ_zurueck k σ v
  | _, _, _, .travRest _ _ _ _ k, σ, v => weiterZ_zurueck k σ v
  | _, _, _, .wieder _ _ _ _ k, σ, v => weiterZ_zurueck k σ v
  | _, _, _, .wiederRest _ _ _ _ k, σ, v => weiterZ_zurueck k σ v
  | _, _, _, .ewig _ _ _ _ k, σ, v => weiterZ_zurueck k σ v
  | _, _, _, .ewigRest _ _ _ _ k, σ, v => weiterZ_zurueck k σ v
  | _, _, _, .wartet _ k, σ, v => weiterZ_zurueck k σ v
  | _, _, _, .wartetSonst _ _ _ k, σ, v => weiterZ_zurueck k σ v

/-- **An end block replacing a residue.** Where G replaces the whole residue
    by an end block (the `else` block of `narrow`/`pruefung`/float
    narrowing, the `else` block of `let … else` on a reason), the old
    residue's prediction is refined by the end block's own result: a return
    and a logic failure pass through every continuation; everything else
    the end block predicts nothing. -/
theorem weiterZ_ende_folgt {Λ : List (Res D)} (k : GRest D V l Γ Λ) (eo : EndAusgang V l Γ) :
    (weiterZ O passes R k eo.zuAusgang).folgt (zErg eo) := by
  cases eo with
  | zurueck σ v => exact ZErg.folgt_of_gleich (weiterZ_zurueck O passes R k σ v)
  | logik e => exact ZErg.folgt_of_eq (weiterZ_logik O passes R k e)
  | _ => exact ZErg.folgt_sonst _

end Weiter

/-! ## 4. The residues the replay follows -/

/-- A residue in the covered fragment whose blocks, loop heads and calls
    read only inside the footprint `S`. -/
def GRest.okV (P : Programm D) (S : List (D.Tab ⊕ D.Glob)) {V : Vertrag D} :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Prop
  | _, _, _, .ende e => e.vOk (kandP P S) = true ∧ endblockOrteP P e ⊆ S
  | _, _, _, .dann b k => b.vOk (kandP P S) = true ∧ blockOrteP P b ⊆ S ∧ k.okV P S
  | _, _, _, .schrumpf k => k.okV P S
  | _, _, _, .frei _ k => k.okV P S
  | _, _, _, .trav _ inv body _ k =>
      inv.orte ⊆ S ∧ body.vOk (kandP P S) = true ∧ blockOrteP P body ⊆ S ∧ k.okV P S
  | _, _, _, .travRest _ inv body _ k =>
      inv.orte ⊆ S ∧ body.vOk (kandP P S) = true ∧ blockOrteP P body ⊆ S ∧ k.okV P S
  | _, _, _, .wieder _ bis body ueber k =>
      bis.orte ⊆ S ∧ body.vOk (kandP P S) = true ∧ blockOrteP P body ⊆ S ∧
        ueber.vOk (kandP P S) = true ∧
        blockOrteP P ueber ⊆ S ∧ k.okV P S
  | _, _, _, .wiederRest _ bis body ueber k =>
      bis.orte ⊆ S ∧ body.vOk (kandP P S) = true ∧ blockOrteP P body ⊆ S ∧
        ueber.vOk (kandP P S) = true ∧
        blockOrteP P ueber ⊆ S ∧ k.okV P S
  | _, _, _, .ewig _ _ inv body k =>
      inv.orte ⊆ S ∧ body.vOk (kandP P S) = true ∧ blockOrteP P body ⊆ S ∧ k.okV P S
  | _, _, _, .ewigRest _ _ inv body k =>
      inv.orte ⊆ S ∧ body.vOk (kandP P S) = true ∧ blockOrteP P body ⊆ S ∧ k.okV P S
  | _, _, _, .wartet b k => b.vOk (kandP P S) = true ∧ blockOrteP P b ⊆ S ∧ k.okV P S
  | _, _, _, .wartetSonst _ err b k =>
      err.vOk (kandP P S) = true ∧ endblockOrteP P err ⊆ S ∧ b.vOk (kandP P S) = true ∧
        blockOrteP P b ⊆ S ∧ k.okV P S

section OkV

variable {P : Programm D} {S : List (D.Tab ⊕ D.Glob)} {V : Vertrag D} {l : Bool} {Γ : Ctx}

theorem okV_dann_cons {Λ Λ' Λ'' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Block D V l Γ Λ' Λ''} {k : GRest D V l Γ Λ''}
    (h : (GRest.dann (.cons s rest) k).okV P S) :
    s.vOk (kandP P S) = true ∧ stmtOrteP P s ⊆ S ∧ (GRest.dann rest k).okV P S := by
  obtain ⟨hk, hs, hk'⟩ := h
  simp only [Block.vOk, Bool.and_eq_true] at hk
  simp only [blockOrteP] at hs
  exact ⟨hk.1, (teil_append hs).1, hk.2, (teil_append hs).2, hk'⟩

theorem okV_ende_cons {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'}
    {rest : Endblock D V l Γ Λ'} (h : (GRest.ende (.cons s rest)).okV P S) :
    s.vOk (kandP P S) = true ∧ stmtOrteP P s ⊆ S ∧ (GRest.ende rest).okV P S := by
  obtain ⟨hk, hs⟩ := h
  simp only [Endblock.vOk, Bool.and_eq_true] at hk
  simp only [endblockOrteP] at hs
  exact ⟨hk.1, (teil_append hs).1, hk.2, (teil_append hs).2⟩

end OkV

/-! ## 5. The residue step lemmas, one per rule of G -/

section Stufen

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  {l : Bool} {Γ : Ctx}

theorem semV_ende_cons {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Endblock D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.ende (.cons s rest)) σ ρ =
      weiterZ O passes R (.ende rest) (execStmt O passes R s σ ρ) := by
  show zErg (execEnd O passes R (.cons s rest) σ ρ) = _
  simp only [execEnd]
  cases execStmt O passes R s σ ρ <;> rfl

theorem laufA_nil {Λ : List (Res D)} (o : Ausgang V l Γ) :
    laufA (fun σ ρ => execBlock O passes R (.nil : Block D V l Γ Λ Λ) σ ρ) o = o := by
  cases o <;> rfl

theorem semV_endeEntf {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Endblock D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.ende (.cons s rest)) σ ρ =
      semV O passes R (.dann (.cons s .nil) (.ende rest)) σ ρ := by
  rw [semV_ende_cons, semV_dann_cons]
  show _ = weiterZ O passes R (.ende rest) (laufA _ _)
  rw [laufA_nil]

theorem semV_blatt {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (rest : Endblock D V l Γ Λ')
    (σ σ' : World D) (ρ ρ' : Env D Γ) (h : execStmt O passes R s σ ρ = .ok σ' ρ') :
    semV O passes R (.ende (.cons s rest)) σ ρ = semV O passes R (.ende rest) σ' ρ' := by
  rw [semV_ende_cons, h]
  rfl

theorem semV_dannBlatt {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ σ' : World D) (ρ ρ' : Env D Γ)
    (h : execStmt O passes R s σ ρ = .ok σ' ρ') :
    semV O passes R (.dann (.cons s rest) k) σ ρ = semV O passes R (.dann rest k) σ' ρ' := by
  rw [semV_dann_cons, h]
  rfl

theorem semV_dannLeer {Λ : List (Res D)} (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.dann .nil k) σ ρ = semV O passes R k σ ρ := rfl

theorem semV_ite {Λ Λ' Λ'' : List (Res D)} (c : Expr D Γ Λ .bool)
    (t e : Block D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) (b : Bool)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = b) :
    semV O passes R (.dann (.cons (.ite c t e) rest) k) σ ρ =
      semV O passes R (.dann (if b then t else e) (.dann rest k)) (σ.lese Λ c.orte) ρ := by
  rw [semV_dann_cons]
  cases b <;> simp only [execStmt, hw] <;> rfl

theorem semV_optSome {Λ Λ' Λ'' : List (Res D)} {n : Int} (o : Expr D Γ Λ (.opt n))
    (p : Block D V l (.index n :: Γ) Λ Λ') (a : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (.index n))
    (hv : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.some v) :
    semV O passes R (.dann (.cons (.onOption o p a) rest) k) σ ρ =
      semV O passes R (.dann p (.schrumpf (.dann rest k))) (σ.lese Λ o.orte) (.cons v ρ) := by
  rw [semV_dann_cons]
  simp only [execStmt, hv]
  rfl

theorem semV_optNone {Λ Λ' Λ'' : List (Res D)} {n : Int} (o : Expr D Γ Λ (.opt n))
    (p : Block D V l (.index n :: Γ) Λ Λ') (a : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (hv : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.none) :
    semV O passes R (.dann (.cons (.onOption o p a) rest) k) σ ρ =
      semV O passes R (.dann a (.dann rest k)) (σ.lese Λ o.orte) ρ := by
  rw [semV_dann_cons]
  simp only [execStmt, hv]
  rfl

theorem semV_tagSome {Λ Λ' Λ'' : List (Res D)} {cs : List (Option (Int × Int))}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (lo hi : Int) (b : Block D V l (.int lo hi :: Γ) Λ Λ') (nutz : Nutzlast (some (lo, hi)))
    (hw : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) =
      ⟨some (lo, hi), b, nutz⟩) :
    semV O passes R (.dann (.cons (.onTag v arms) rest) k) σ ρ =
      semV O passes R (.dann b (.schrumpf (.dann rest k))) (σ.lese Λ v.orte) (armEnv nutz ρ) := by
  rw [semV_dann_cons]
  simp only [execStmt]
  rw [execArms_wahl, hw]
  rfl

theorem semV_tagNone {Λ Λ' Λ'' : List (Res D)} {cs : List (Option (Int × Int))}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (b : Block D V l Γ Λ Λ') (nutz : Nutzlast none)
    (hw : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) = ⟨none, b, nutz⟩) :
    semV O passes R (.dann (.cons (.onTag v arms) rest) k) σ ρ =
      semV O passes R (.dann b (.dann rest k)) (σ.lese Λ v.orte) (armEnv nutz ρ) := by
  rw [semV_dann_cons]
  simp only [execStmt]
  rw [execArms_wahl, hw]
  rfl

theorem semV_grund {Λ Λ' Λ'' : List (Res D)} {n : Nat} (r : Expr D Γ Λ (.grund n))
    (arms : GrundArms D V l Γ Λ Λ' n) (rest : Block D V l Γ Λ' Λ'')
    (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.dann (.cons (.onGrund r arms) rest) k) σ ρ =
      semV O passes R (.dann (grundWahlG arms (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρ))
        (.dann rest k)) (σ.lese Λ r.orte) ρ := by
  rw [semV_dann_cons]
  simp only [execStmt]
  rw [execGrund_wahlW O passes R arms]
  rfl

theorem semV_breaking {Λ Λ' Λ'' : List (Res D)} (i : D.Inv) (body : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.dann (.cons (.breaking i body) rest) k) σ ρ =
      semV O passes R (.dann body (.dann rest k)) σ ρ := by
  rw [semV_dann_cons]
  rfl

theorem semV_locks {Λ Λ'' : List (Res D)} (L : D.Lock)
    (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (Res.held L :: Λ) (Res.held L :: Λ))
    (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.dann (.cons (.locks L hr body) rest) k) σ ρ =
      semV O passes R (.dann body (.frei L (.dann rest k))) (σ.nimmt L) ρ := by
  rw [semV_dann_cons]
  rfl

theorem semV_frei {Λ : List (Res D)} (L : D.Lock) (k : GRest D V l Γ Λ) (σ : World D)
    (ρ : Env D Γ) : semV O passes R (.frei L k) σ ρ = semV O passes R k (σ.gibt L) ρ := rfl

theorem semV_schrumpf {Λ : List (Res D)} {τ : Ty} (k : GRest D V l Γ Λ) (σ : World D)
    (v : Wert D τ) (ρ : Env D Γ) :
    semV O passes R (.schrumpf k) σ (.cons v ρ) = semV O passes R k σ ρ := rfl

theorem semV_endeBind {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (rest : Endblock D V l (τ :: Γ) Λ) (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.ende (.bind e rest)) σ ρ =
      semV O passes R (.ende rest) (σ.lese Λ e.orte)
        (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) := by
  show zErg (execEnd O passes R (.bind e rest) σ ρ) = zErg (execEnd O passes R rest _ _)
  simp only [execEnd]
  rw [zErg_schrumpf]

theorem semV_dannBind {Λ Λ' : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (rest : Block D V l (τ :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.dann (.bind e rest) k) σ ρ =
      semV O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte)
        (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) := rfl

theorem semV_narrowOk {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (h : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi') :
    semV O passes R (.dann (.narrow e lo' hi' sonst rest) k) σ ρ =
      semV O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte)
        (Env.cons (τ := .int lo' hi')
          ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, h.1, h.2⟩ ρ) := by
  rw [semV_dann, execBlock_narrowK]
  unfold narrowWeiterK
  rw [dif_pos h]
  rfl

theorem semV_narrowElse {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (h : ¬ (lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi')) :
    (semV O passes R (.dann (.narrow e lo' hi' sonst rest) k) σ ρ).folgt
      (semV O passes R (.ende sonst) (σ.lese Λ e.orte) ρ) := by
  rw [semV_dann, execBlock_narrowK]
  unfold narrowWeiterK
  rw [dif_neg h]
  exact weiterZ_ende_folgt O passes R k _

theorem semV_pruefWahr {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true) :
    semV O passes R (.dann (.pruefung c sonst rest) k) σ ρ =
      semV O passes R (.dann rest k) (σ.lese Λ c.orte) ρ := by
  rw [semV_dann]
  simp only [execBlock, hw, if_true]
  rfl

theorem semV_pruefFalsch {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false) :
    (semV O passes R (.dann (.pruefung c sonst rest) k) σ ρ).folgt
      (semV O passes R (.ende sonst) (σ.lese Λ c.orte) ρ) := by
  rw [semV_dann]
  simp only [execBlock, hw, Bool.false_eq_true, if_false]
  exact weiterZ_ende_folgt O passes R k _

theorem semV_exchange {Λ Λ' : List (Res D)} (g : D.Glob)
    (neuE : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)) (hw : V.gschreibt g = true)
    (hL : gdarf D g Λ) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.dann (.exchange g neuE hw hL rest) k) σ ρ =
      semV O passes R (.dann rest (.schrumpf k))
        ((σ.lese Λ (.inr g :: neuE.orte)).schreibGlob g Λ
          (eval (σ.lese Λ (.inr g :: neuE.orte)) neuE (σ.lese Λ (.inr g :: neuE.orte))
            (.cons ((σ.lese Λ (.inr g :: neuE.orte)).globs g) ρ)))
        (.cons ((σ.lese Λ (.inr g :: neuE.orte)).globs g) ρ) := rfl

theorem semV_gleit {Λ Λ' : List (Res D)} {l₁ h₁ l₂ h₂ : Int × Int} (op : GleitOp)
    (a : Expr D Γ Λ (.fl l₁ h₁)) (b : Expr D Γ Λ (.fl l₂ h₂)) (lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitRechne op
      (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
      (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = some v) :
    semV O passes R (.dann (.gleit op a b lo hi rest) k) σ ρ =
      semV O passes R (.dann rest (.schrumpf k)) (σ.lese Λ (a.orte ++ b.orte)) (.cons v ρ) := by
  rw [semV_dann]
  simp only [execBlock, hv]
  rfl

theorem semV_gleitLit {Λ Λ' : List (Res D)} (q lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi)) (hv : gleitPasst lo hi (bruch q) = some v) :
    semV O passes R (.dann (.gleitLit q lo hi rest) k) σ ρ =
      semV O passes R (.dann rest (.schrumpf k)) σ (.cons v ρ) := by
  rw [semV_dann]
  simp only [execBlock, hv]
  rfl

theorem semV_gleitVon {Λ Λ' : List (Res D)} {l₁ h₁ : Int} (e : Expr D Γ Λ (.int l₁ h₁))
    (lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (Float.ofInt (eval (σ.lese Λ e.orte) e
      (σ.lese Λ e.orte) ρ).n) = some v) :
    semV O passes R (.dann (.gleitVon e lo hi rest) k) σ ρ =
      semV O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) (.cons v ρ) := by
  rw [semV_dann]
  simp only [execBlock, hv]
  rfl

theorem semV_gleitNarrowOk {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = some v) :
    semV O passes R (.dann (.gleitNarrow e lo hi sonst rest) k) σ ρ =
      semV O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) (.cons v ρ) := by
  rw [semV_dann]
  simp only [execBlock, hv]
  rfl

theorem semV_gleitNarrowElse {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ)
    (hn : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = none) :
    (semV O passes R (.dann (.gleitNarrow e lo hi sonst rest) k) σ ρ).folgt
      (semV O passes R (.ende sonst) (σ.lese Λ e.orte) ρ) := by
  rw [semV_dann]
  simp only [execBlock, hn]
  exact weiterZ_ende_folgt O passes R k _

/-! ### Loops -/

theorem semV_dannTrav {Λ Λ'' : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.dann (.cons (.traverse t inv body) rest) k) σ ρ =
      semV O passes R (.trav t inv body (alleIndizes (D.count t)) (.dann rest k)) σ ρ := by
  rw [semV_dann_cons]
  rfl

theorem semV_travNext {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (i : Wert D (.index (D.count t))) (is : List (Wert D (.index (D.count t))))
    (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true) :
    semV O passes R (.trav t inv body (i :: is) k) σ ρ =
      semV O passes R (.dann body (.travRest t inv body is k)) (σ.lese Λ inv.orte) (.cons i ρ) := by
  have hl : (leseB inv σ ρ).2 = true := hw
  show weiterZ O passes R k (traverseLauf _ _ (i :: is) σ ρ) =
    weiterZ O passes R (.travRest t inv body is k)
      (execBlock O passes R body (leseB inv σ ρ).1 (.cons i ρ))
  simp only [traverseLauf, hl, Bool.true_eq_false, if_false]
  cases execBlock O passes R body (leseB inv σ ρ).1 (.cons i ρ) <;> rfl

theorem semV_travFort {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.travRest t inv body is k) σ (.cons i ρ) =
      semV O passes R (.trav t inv body is k) σ ρ := rfl

theorem semV_travDone {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true) :
    semV O passes R (.trav t inv body [] k) σ ρ = semV O passes R k (σ.lese Λ inv.orte) ρ := by
  have hl : (leseB inv σ ρ).2 = true := hw
  show weiterZ O passes R k (traverseLauf (fun σ ρ => execBlock O passes R body σ ρ)
    (leseB inv) [] σ ρ) = weiterZ O passes R k (.ok _ ρ)
  simp only [traverseLauf, hl, if_true]
  rfl

theorem semV_dannRetry {Λ Λ'' : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ)
    (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.dann (.cons (.retry n bis body ueber) rest) k) σ ρ =
      semV O passes R (.wieder n bis body ueber (.dann rest k)) σ ρ := by
  rw [semV_dann_cons]
  rfl

theorem semV_wiederUeber {Λ : List (Res D)} (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.wieder 0 bis body ueber k) σ ρ = semV O passes R (.dann ueber k) σ ρ := rfl

theorem semV_wiederWeiter {Λ : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = true) :
    semV O passes R (.wieder (n + 1) bis body ueber k) σ ρ =
      semV O passes R k (σ.lese Λ bis.orte) ρ := by
  have hl : (leseB bis σ ρ).2 = true := hw
  show weiterZ O passes R k (retryLauf _ _ _ (n + 1) σ ρ) = weiterZ O passes R k (.ok _ ρ)
  simp only [retryLauf, hl, if_true]
  rfl

theorem semV_wiederSchritt {Λ : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = false) :
    semV O passes R (.wieder (n + 1) bis body ueber k) σ ρ =
      semV O passes R (.dann body (.wiederRest n bis body ueber k)) (σ.lese Λ bis.orte) ρ := by
  have hl : (leseB bis σ ρ).2 = false := hw
  show weiterZ O passes R k (retryLauf _ _ _ (n + 1) σ ρ) =
    weiterZ O passes R (.wiederRest n bis body ueber k)
      (execBlock O passes R body (leseB bis σ ρ).1 ρ)
  simp only [retryLauf, hl, Bool.false_eq_true, if_false]
  cases execBlock O passes R body (leseB bis σ ρ).1 ρ <;> rfl

theorem semV_wiederFort {Λ : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.wiederRest n bis body ueber k) σ ρ =
      semV O passes R (.wieder n bis body ueber k) σ ρ := rfl

theorem semV_dannForever {Λ Λ'' : List (Res D)} (a : D.Annahme) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.dann (.cons (.forever a inv body) rest) k) σ ρ =
      semV O passes R (.ewig a passes inv body (.dann rest k)) σ ρ := by
  rw [semV_dann_cons]
  rfl

theorem semV_ewigWeiter {Λ : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true) :
    semV O passes R (.ewig a (n + 1) inv body k) σ ρ =
      semV O passes R (.dann body (.ewigRest a n inv body k)) (σ.lese Λ inv.orte) ρ := by
  have hl : (leseB inv σ ρ).2 = true := hw
  show weiterZ O passes R k (foreverLauf a _ _ (n + 1) σ ρ) =
    weiterZ O passes R (.ewigRest a n inv body k)
      (execBlock O passes R body (leseB inv σ ρ).1 ρ)
  simp only [foreverLauf, hl, Bool.true_eq_false, if_false]
  cases execBlock O passes R body (leseB inv σ ρ).1 ρ <;> rfl

theorem semV_ewigFort {Λ : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    semV O passes R (.ewigRest a n inv body k) σ ρ =
      semV O passes R (.ewig a n inv body k) σ ρ := rfl

/-! ### The exits `leave` and `next` -/

theorem semV_leaveTrav {Λ Λx : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ)
    (rest : Block D V true (.index (D.count t) :: Γ) Λx Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ) (h : true = true)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true) :
    semV O passes R (.dann (.cons (.leave h) rest) (.travRest t inv body is k)) σ (.cons i ρ) =
      semV O passes R k (σ.lese Λ inv.orte) ρ := by
  have hl : (leseB inv σ ρ).2 = true := hw
  rw [semV_dann_cons]
  show weiterZ O passes R k (if (leseB inv σ ρ).2 = true then _ else _) = _
  rw [if_pos hl]
  rfl

theorem semV_nextTrav {Λ Λx : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ)
    (rest : Block D V true (.index (D.count t) :: Γ) Λx Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semV O passes R (.dann (.cons (.next h) rest) (.travRest t inv body is k)) σ (.cons i ρ) =
      semV O passes R (.trav t inv body is k) σ ρ := by
  rw [semV_dann_cons]
  rfl

theorem semV_leaveWieder {Λ Λx : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (rest : Block D V true Γ Λx Λ) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semV O passes R (.dann (.cons (.leave h) rest) (.wiederRest n bis body ueber k)) σ ρ =
      semV O passes R k σ ρ := by
  rw [semV_dann_cons]
  rfl

theorem semV_nextWieder {Λ Λx : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (rest : Block D V true Γ Λx Λ) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semV O passes R (.dann (.cons (.next h) rest) (.wiederRest n bis body ueber k)) σ ρ =
      semV O passes R (.wieder n bis body ueber k) σ ρ := by
  rw [semV_dann_cons]
  rfl

theorem semV_leaveEwig {Λ Λx : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ)
    (rest : Block D V true Γ Λx Λ) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semV O passes R (.dann (.cons (.leave h) rest) (.ewigRest a n inv body k)) σ ρ =
      semV O passes R k σ ρ := by
  rw [semV_dann_cons]
  rfl

theorem semV_nextEwig {Λ Λx : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ)
    (rest : Block D V true Γ Λx Λ) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semV O passes R (.dann (.cons (.next h) rest) (.ewigRest a n inv body k)) σ ρ =
      semV O passes R (.ewig a n inv body k) σ ρ := by
  rw [semV_dann_cons]
  rfl

theorem semV_peelDann {Γ : Ctx} {Λ Λ1 Λ2 : List (Res D)}
    (rest : Block D V true Γ Λ Λ1) (b : Block D V true Γ Λ1 Λ2) (k : GRest D V true Γ Λ2)
    (σ : World D) (ρ : Env D Γ) (h : true = true) (x : Bool) :
    semV O passes R (.dann (.cons (if x then .leave h else .next h) rest) (.dann b k)) σ ρ =
      semV O passes R (.dann (.cons (if x then .leave h else .next h) .nil) k) σ ρ := by
  rw [semV_dann_cons, semV_dann_cons]
  cases x <;> rfl

theorem semV_peelSchrumpf {Γ : Ctx} {Λ Λ1 : List (Res D)} {τ : Ty}
    (rest : Block D V true (τ :: Γ) Λ Λ1) (k : GRest D V true Γ Λ1)
    (σ : World D) (ρ : Env D (τ :: Γ)) (h : true = true) (x : Bool) :
    semV O passes R (.dann (.cons (if x then .leave h else .next h) rest) (.schrumpf k)) σ ρ =
      semV O passes R (.dann (.cons (if x then .leave h else .next h) .nil) k) σ ρ.tail := by
  rw [semV_dann_cons, semV_dann_cons]
  cases x <;> rfl

theorem semV_peelFrei {Γ : Ctx} {Λ Λ1 : List (Res D)} (L : D.Lock)
    (rest : Block D V true Γ Λ (Res.held L :: Λ1)) (k : GRest D V true Γ Λ1)
    (σ : World D) (ρ : Env D Γ) (h : true = true) (x : Bool) :
    semV O passes R (.dann (.cons (if x then .leave h else .next h) rest) (.frei L k)) σ ρ =
      semV O passes R (.dann (.cons (if x then .leave h else .next h) .nil) k) (σ.gibt L) ρ := by
  rw [semV_dann_cons, semV_dann_cons]
  cases x <;> rfl

/-! ### Returns -/

theorem semV_rueck {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (σ : World D) (ρ : Env D Γ) :
    (semV O passes R (.ende (.ret (l := l) e hperm)) σ ρ).gleich
      (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)) :=
  ZErg.gleich_refl _

theorem semV_rueckCons {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (rest : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    (semV O passes R (.ende (.cons (.ret e hperm) rest)) σ ρ).gleich
      (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)) := by
  rw [semV_ende_cons]
  exact ZErg.gleich_refl _

theorem semV_dannRet {Λ Λ'' : List (Res D)} (e : ErgExpr D Γ Λ V.erg)
    (hperm : Λ.Perm V.ende) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) :
    (semV O passes R (.dann (.cons (.ret e hperm) rest) k) σ ρ).gleich
      (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)) := by
  rw [semV_dann_cons]
  exact weiterZ_zurueck O passes R (.dann rest k) _ _

end Stufen

/-! ## CUTS:

  What is proved: the covered fragment `vOk K` (every form but `regLies`,
  `regLiesElse`, `awaits`; indirect calls where `K` admits the pointer's
  signature), its decided form `programmImFragmentV` with soundness
  (`kandB_kandP`, `programmImFragmentV_ok`) and monotonicity (`vOk_mono`),
  the inclusion of the old fragment (`programmImFragmentV_of`); the frame
  semantics
  `weiterZ`/`semV` of EVERY residue of G, with the pass-through lemmas
  (`weiterZ_logik`, `weiterZ_zurueck`, `weiterZ_grund`,
  `weiterZ_hardware`) and the end-block refinement (`weiterZ_ende_folgt`);
  the preorder `ZErg.folgt`; the residue predicate `GRest.okV`.

  What is NOT here: the replay itself (`ZielOrtVollBeweis.lean`).
-/

#print axioms Gabbro.Grammatik.programmImFragmentV_of
#print axioms Gabbro.Grammatik.programmImFragmentV_ok
#print axioms Gabbro.Grammatik.weiterZ_zurueck
#print axioms Gabbro.Grammatik.weiterZ_ende_folgt
#print axioms Gabbro.Grammatik.ZErg.folgt_trans

end Gabbro.Grammatik
