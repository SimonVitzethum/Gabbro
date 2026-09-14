/-
  File:      Grammatik/Durchgaenge.lean
  Subject:   THE `forever` BUDGET IS NOT DATA (probe D of
             `messung/URTEIL-OPUS-2026-09-14.md` §5).

  Every semantics of the model -- `execStmt`, `execStmtH`, `rufAt`, and
  machine G -- takes a number `passes`: how many passes the environment
  gives a `forever` loop before the run stops at the loop's named
  assumption (`foreverLauf 0 = hardware (fortschritt a)`; G has no rule at
  `ewig 0`). G re-arms the budget at EVERY entry of a loop (`dannForever`
  pushes `ewig a passes`), so a run in which every loop entry makes at most
  `n` passes is a run of G at every budget `≥ n`; the union over all
  budgets is every finite run.

  Until 2026-09-14 the goal theorems took `passes` as free DATA and every
  witness fixed `passes = 0`. At `0` a `forever` loop stops before its first
  pass, the obligation says nothing about the loop, and probe D (every
  `ensures false`, every body `forever … invariant false { leave }`) met
  every premise -- while the emitted C runs the loop once. The repair (in
  `ZielOrtStart.lean`) quantifies the goal theorem over EVERY budget: the
  obligation is demanded at every `passes`, and the conclusion holds on the
  machines of every `passes`.

  **Why every budget and not "every budget from the machine's on".** A
  floor `B` would give the same set of runs (every run is a run at some
  budget `≥ B` as well), and it would cost the user nothing less: the
  sequential proof of a `forever` body has to cover an arbitrary finite
  number of passes either way. No choice of a budget can empty the
  obligation, because no budget is chosen.

  This file: the bodies without a `forever` loop (`ohneEwig`), and the fact
  that such a body MEANS THE SAME at every budget -- in the semantics with
  lock invariants (`Endblock.execH_passes`), in the plain one
  (`Endblock.exec_passes`), in the call semantics (`rufAt_passes`) -- so for
  a program without `forever` the per-budget obligation at `0` IS the
  obligation at every budget (`koerperGutS_passes`, `invGutS_passes`,
  `koerperGutS_alle`, `invGutS_alle`). This is how every earlier witness
  carries over to the quantified goal theorem at no cost.
-/
import Grammatik.ZielOrtInv

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Bodies without a `forever` loop -/

section Ohne

variable {V : Vertrag D}

mutual

/-- The statement contains no `forever` loop. -/
def Stmt.ohneEwig {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => t.ohneEwig && e.ohneEwig
  | .onOption _ p a => p.ohneEwig && a.ohneEwig
  | .onTag _ arms => arms.ohneEwig
  | .onGrund _ arms => arms.ohneEwig
  | .locks _ _ body => body.ohneEwig
  | .breaking _ body => body.ohneEwig
  | .traverse _ _ body => body.ohneEwig
  | .retry _ _ body ueber => body.ohneEwig && ueber.ohneEwig
  | .forever .. => false
  | _ => true

def Block.ohneEwig {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => s.ohneEwig && rest.ohneEwig
  | .bind _ rest => rest.ohneEwig
  | .bindCall _ _ _ _ _ rest => rest.ohneEwig
  | .bindCallInd _ _ _ _ _ rest => rest.ohneEwig
  | .bindCallElse _ _ _ _ _ err rest => err.ohneEwig && rest.ohneEwig
  | .bindAxiom _ _ _ _ _ _ _ rest => rest.ohneEwig
  | .regLies _ _ rest => rest.ohneEwig
  | .regLiesElse _ _ _ sonst rest => sonst.ohneEwig && rest.ohneEwig
  | .awaits _ _ _ _ rest => rest.ohneEwig
  | .exchange _ _ _ _ rest => rest.ohneEwig
  | .narrow _ _ _ sonst rest => sonst.ohneEwig && rest.ohneEwig
  | .pruefung _ sonst rest => sonst.ohneEwig && rest.ohneEwig
  | .gleit _ _ _ _ _ rest => rest.ohneEwig
  | .gleitLit _ _ _ rest => rest.ohneEwig
  | .gleitVon _ _ _ rest => rest.ohneEwig
  | .gleitNarrow _ _ _ sonst rest => sonst.ohneEwig && rest.ohneEwig

def Endblock.ohneEwig {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : Endblock D V l Γ Λ → Bool
  | .cons s rest => s.ohneEwig && rest.ohneEwig
  | .bind _ rest => rest.ohneEwig
  | _ => true

def Arms.ohneEwig {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} :
    Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => b.ohneEwig && rest.ohneEwig

def GrundArms.ohneEwig {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => b.ohneEwig && rest.ohneEwig

end

/-! ## 2. Such a body means the same at every budget -/

variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (n m : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

mutual

theorem Stmt.execH_passes {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → s.ohneEwig = true → ∀ (σ : World D) (ρ : Env D Γ),
      execStmtH S O U n R s σ ρ = execStmtH S O U m R s σ ρ
  | .ite c t e, h, σ, ρ => by
      simp only [Stmt.ohneEwig, Bool.and_eq_true] at h
      simp only [execStmtH, Block.execH_passes t h.1, Block.execH_passes e h.2]
  | .onOption o p a, h, σ, ρ => by
      simp only [Stmt.ohneEwig, Bool.and_eq_true] at h
      simp only [execStmtH, Block.execH_passes p h.1, Block.execH_passes a h.2]
  | .onTag v arms, h, σ, ρ => by
      simp only [Stmt.ohneEwig] at h
      simp only [execStmtH]
      exact Arms.execH_passes arms h _ _ _
  | .onGrund r arms, h, σ, ρ => by
      simp only [Stmt.ohneEwig] at h
      simp only [execStmtH]
      exact GrundArms.execH_passes arms h _ _ _
  | .locks L hr body, h, σ, ρ => by
      simp only [Stmt.ohneEwig] at h
      simp only [execStmtH, Block.execH_passes body h]
  | .breaking i body, h, σ, ρ => by
      simp only [Stmt.ohneEwig] at h
      simp only [execStmtH, Block.execH_passes body h]
  | .traverse t inv body, h, σ, ρ => by
      simp only [Stmt.ohneEwig] at h
      simp only [execStmtH]
      rw [show (fun σ ρ => execBlockH S O U n R body σ ρ) =
        (fun σ ρ => execBlockH S O U m R body σ ρ) from
          funext fun σ => funext fun ρ => Block.execH_passes body h σ ρ]
  | .retry k bis body ueber, h, σ, ρ => by
      simp only [Stmt.ohneEwig, Bool.and_eq_true] at h
      simp only [execStmtH]
      rw [show (fun σ ρ => execBlockH S O U n R body σ ρ) =
          (fun σ ρ => execBlockH S O U m R body σ ρ) from
            funext fun σ => funext fun ρ => Block.execH_passes body h.1 σ ρ,
        show (fun σ ρ => execBlockH S O U n R ueber σ ρ) =
          (fun σ ρ => execBlockH S O U m R ueber σ ρ) from
            funext fun σ => funext fun ρ => Block.execH_passes ueber h.2 σ ρ]
  | .forever .., h, _, _ => by simp [Stmt.ohneEwig] at h
  | .assignSlot .., _, _, _ => rfl
  | .assignDurch .., _, _, _ => rfl
  | .assignGlob .., _, _, _ => rfl
  | .schreibBytes .., _, _, _ => rfl
  | .assignVar .., _, _, _ => rfl
  | .uebergang .., _, _, _ => rfl
  | .call .., _, _, _ => rfl
  | .callInd .., _, _, _ => rfl
  | .axiomCall .., _, _, _ => rfl
  | .regSchreib .., _, _, _ => rfl
  | .transition .., _, _, _ => rfl
  | .publish .., _, _, _ => rfl
  | .advances .., _, _, _ => rfl
  | .retires .., _, _, _ => rfl
  | .ret .., _, _, _ => rfl
  | .retGrund .., _, _, _ => rfl
  | .leave .., _, _, _ => rfl
  | .next .., _, _, _ => rfl

theorem Block.execH_passes {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → b.ohneEwig = true → ∀ (σ : World D) (ρ : Env D Γ),
      execBlockH S O U n R b σ ρ = execBlockH S O U m R b σ ρ
  | .nil, _, _, _ => rfl
  | .cons s rest, h, σ, ρ => by
      simp only [Block.ohneEwig, Bool.and_eq_true] at h
      simp only [execBlockH, Stmt.execH_passes s h.1, Block.execH_passes rest h.2]
  | .bind e rest, h, σ, ρ => by
      simp only [Block.ohneEwig] at h
      simp only [execBlockH, Block.execH_passes rest h]
  | .bindCall f args he hp hr rest, h, σ, ρ => by
      simp only [Block.ohneEwig] at h
      simp only [execBlockH, Block.execH_passes rest h]
  | .bindCallInd p args he hp hr rest, h, σ, ρ => by
      simp only [Block.ohneEwig] at h
      simp only [execBlockH, Block.execH_passes rest h]
  | .bindCallElse f args he hp hr err rest, h, σ, ρ => by
      simp only [Block.ohneEwig, Bool.and_eq_true] at h
      simp only [execBlockH, Block.execH_passes rest h.2, Endblock.execH_passes err h.1]
  | .bindAxiom a args he hw hg hd hgd rest, h, σ, ρ => by
      simp only [Block.ohneEwig] at h
      simp only [execBlockH, Block.execH_passes rest h]
  | .regLies r hk rest, h, σ, ρ => by
      simp only [Block.ohneEwig] at h
      simp only [execBlockH, Block.execH_passes rest h]
  | .regLiesElse r hk zusage sonst rest, h, σ, ρ => by
      simp only [Block.ohneEwig, Bool.and_eq_true] at h
      simp only [execBlockH, Block.execH_passes rest h.2, Endblock.execH_passes sonst h.1]
  | .awaits g payload hp hL rest, h, σ, ρ => by
      simp only [Block.ohneEwig] at h
      simp only [execBlockH, Block.execH_passes rest h]
  | .exchange g neu hw hL rest, h, σ, ρ => by
      simp only [Block.ohneEwig] at h
      simp only [execBlockH, Block.execH_passes rest h]
  | .narrow e lo' hi' sonst rest, h, σ, ρ => by
      simp only [Block.ohneEwig, Bool.and_eq_true] at h
      simp only [execBlockH, Block.execH_passes rest h.2, Endblock.execH_passes sonst h.1]
  | .pruefung c sonst rest, h, σ, ρ => by
      simp only [Block.ohneEwig, Bool.and_eq_true] at h
      simp only [execBlockH, Block.execH_passes rest h.2, Endblock.execH_passes sonst h.1]
  | .gleit op a b lo hi rest, h, σ, ρ => by
      simp only [Block.ohneEwig] at h
      simp only [execBlockH, Block.execH_passes rest h]
  | .gleitLit q lo hi rest, h, σ, ρ => by
      simp only [Block.ohneEwig] at h
      simp only [execBlockH, Block.execH_passes rest h]
  | .gleitVon e lo hi rest, h, σ, ρ => by
      simp only [Block.ohneEwig] at h
      simp only [execBlockH, Block.execH_passes rest h]
  | .gleitNarrow e lo hi sonst rest, h, σ, ρ => by
      simp only [Block.ohneEwig, Bool.and_eq_true] at h
      simp only [execBlockH, Block.execH_passes rest h.2, Endblock.execH_passes sonst h.1]

theorem Endblock.execH_passes {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (b : Endblock D V l Γ Λ) → b.ohneEwig = true → ∀ (σ : World D) (ρ : Env D Γ),
      execEndH S O U n R b σ ρ = execEndH S O U m R b σ ρ
  | .ret .., _, _, _ => rfl
  | .retGrund .., _, _, _ => rfl
  | .leave .., _, _, _ => rfl
  | .next .., _, _, _ => rfl
  | .cons s rest, h, σ, ρ => by
      simp only [Endblock.ohneEwig, Bool.and_eq_true] at h
      simp only [execEndH, Stmt.execH_passes s h.1, Endblock.execH_passes rest h.2]
  | .bind e rest, h, σ, ρ => by
      simp only [Endblock.ohneEwig] at h
      simp only [execEndH, Endblock.execH_passes rest h]

theorem Arms.execH_passes {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    (a : Arms D V l Γ Λ Λ' cs) → a.ohneEwig = true →
      ∀ (v : Wert D (.sum cs)) (σ : World D) (ρ : Env D Γ),
      execArmsH S O U n R a v σ ρ = execArmsH S O U m R a v σ ρ
  | .nil, _, ⟨⟨k, hk⟩, _⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | .cons b _, h, ⟨⟨0, _⟩, nutz⟩, σ, ρ => by
      simp only [Arms.ohneEwig, Bool.and_eq_true] at h
      simp only [execArmsH, Block.execH_passes b h.1]
  | .cons _ rest, h, ⟨⟨i + 1, hi⟩, nutz⟩, σ, ρ => by
      simp only [Arms.ohneEwig, Bool.and_eq_true] at h
      simp only [execArmsH]
      exact Arms.execH_passes rest h.2 _ σ ρ

theorem GrundArms.execH_passes {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {k : Nat} :
    (a : GrundArms D V l Γ Λ Λ' k) → a.ohneEwig = true → ∀ (r : Fin k) (σ : World D) (ρ : Env D Γ),
      execGrundH S O U n R a r σ ρ = execGrundH S O U m R a r σ ρ
  | .nil, _, ⟨j, hj⟩, _, _ => (Nat.not_lt_zero j hj).elim
  | .cons b _, h, ⟨0, _⟩, σ, ρ => by
      simp only [GrundArms.ohneEwig, Bool.and_eq_true] at h
      simp only [execGrundH, Block.execH_passes b h.1]
  | .cons _ rest, h, ⟨i + 1, hi⟩, σ, ρ => by
      simp only [GrundArms.ohneEwig, Bool.and_eq_true] at h
      simp only [execGrundH]
      exact GrundArms.execH_passes rest h.2 _ σ ρ

end

/-- **The plain semantics**, the same: it is the semantics with the empty
    family under the identity move (`Endblock.execH_leer`). -/
theorem Endblock.exec_passes {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (b : Endblock D V l Γ Λ) (h : b.ohneEwig = true) (σ : World D) (ρ : Env D Γ) :
    execEnd O n R b σ ρ = execEnd O m R b σ ρ := by
  rw [← Endblock.execH_leer O (fun _ σ => σ) n R (fun _ _ => rfl) b σ ρ,
    ← Endblock.execH_leer O (fun _ σ => σ) m R (fun _ _ => rfl) b σ ρ]
  exact Endblock.execH_passes _ O _ n m R b h σ ρ

end Ohne

/-! ## 3. The obligations of a `forever`-free body do not depend on the budget -/

/-- No body of the listed functions contains a `forever` loop (decidable). -/
def ohneEwigB (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun f => (P.rumpf f).ohneEwig

theorem ohneEwigB_ok {P : Programm D} {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (h : ohneEwigB P fs = true) (f : D.Fn) : (P.rumpf f).ohneEwig = true :=
  List.all_eq_true.mp h f (hvoll f)

/-- **`KoerperGutS` of a `forever`-free body at one budget is
    `KoerperGutS` at every budget.** -/
theorem koerperGutS_passes {P : Programm D} {n : Nat} {Q : AxEns D} {S : SperrInv D} {f : D.Fn}
    (hE : (P.rumpf f).ohneEwig = true) (h : KoerperGutS P n Q S f) (m : Nat) :
    KoerperGutS P m Q S f := by
  refine ⟨fun O' hr hl hq U hU R hR hOV σ ρ hreq => ?_,
    fun O' hr hl hq U hU R hR hOL σ ρ hreq e => ?_⟩
  · rw [← Endblock.execH_passes S O' U n m R _ hE σ ρ,
      ← Endblock.execH_passes S O' U n m (torRuf P R) _ hE σ ρ]
    exact h.1 O' hr hl hq U hU R hR hOV σ ρ hreq
  · rw [← Endblock.execH_passes S O' U n m R _ hE σ ρ]
    exact h.2 O' hr hl hq U hU R hR hOL σ ρ hreq e

/-- **`InvGutS` of a `forever`-free body at one budget is `InvGutS` at
    every budget.** -/
theorem invGutS_passes {P : Programm D} {n : Nat} {Q : AxEns D} {S : SperrInv D} {f : D.Fn}
    (hE : (P.rumpf f).ohneEwig = true) (h : InvGutS P n Q S f) (m : Nat) :
    InvGutS P m Q S f := by
  intro O' hr hl hq U hU R hR hOV σ ρ hreq σ' v hrun
  rw [← Endblock.execH_passes S O' U n m R _ hE σ ρ] at hrun
  exact h O' hr hl hq U hU R hR hOV σ ρ hreq σ' v hrun

/-- **A program without `forever`: the obligation at budget `0` is the
    obligation at every budget.** -/
theorem koerperGutS_alle {P : Programm D} {Q : AxEns D} {S : SperrInv D} {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hE : ohneEwigB P fs = true)
    (h : ∀ f, KoerperGutS P 0 Q S f) : ∀ passes f, KoerperGutS P passes Q S f :=
  fun passes f => koerperGutS_passes (ohneEwigB_ok hvoll hE f) (h f) passes

theorem invGutS_alle {P : Programm D} {Q : AxEns D} {S : SperrInv D} {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hE : ohneEwigB P fs = true)
    (h : ∀ f, InvGutS P 0 Q S f) : ∀ passes f, InvGutS P passes Q S f :=
  fun passes f => invGutS_passes (ohneEwigB_ok hvoll hE f) (h f) passes

/-- **The call semantics of a `forever`-free program does not depend on the
    budget**, at every depth. -/
theorem rufAt_passes {P : Programm D} (O : Orakel D) (hE : ∀ f, (P.rumpf f).ohneEwig = true)
    (n m : Nat) : ∀ (k : Nat) (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)),
      rufAt P O n k f σ ρ = rufAt P O m k f σ ρ
  | 0, _, _, _ => rfl
  | k + 1, f, σ, ρ => by
      have ih : rufAt P O n k = rufAt P O m k :=
        funext fun g => funext fun σ => funext fun ρ => rufAt_passes O hE n m k g σ ρ
      simp only [rufAt, ih, Endblock.exec_passes O n m (rufAt P O m k) (P.rumpf f) (hE f)]

#print axioms Gabbro.Grammatik.Endblock.execH_passes
#print axioms Gabbro.Grammatik.Endblock.exec_passes
#print axioms Gabbro.Grammatik.koerperGutS_alle
#print axioms Gabbro.Grammatik.invGutS_alle
#print axioms Gabbro.Grammatik.rufAt_passes

end Gabbro.Grammatik
