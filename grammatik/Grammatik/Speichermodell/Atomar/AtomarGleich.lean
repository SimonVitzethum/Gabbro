/-
  File:      Grammatik/Speichermodell/Atomar/AtomarGleich.lean
  Subject:   **Two atomic environments that answer alike on what a body reads run it alike**
             (`Stmt/Block/Endblock/Arms/GrundArms.execHA_gleich`), and the consequence for a
             library proved against a smaller rely: only bodies that read a carrier of the grown
             rely need a new proof (`koerperGutSA_wachs`).

  The proofs follow `execHA_frei` (AtomarSem.lean) read for read: where that one rewrites a read
  outside `T` into a read without havoc, this one rewrites it into the other environment's read.
-/
import Grammatik.Speichermodell.Atomar.AtomarRec

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Gleich

set_option linter.unusedSectionVars false

variable (P : Programm D) (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (A : AUmwelt D)
  (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  {T : D.Tab ⊕ D.Glob → Prop} (A' : AUmwelt D)
  (hG : ∀ X : List (D.Tab ⊕ D.Glob), (∀ c ∈ X, ¬ T c) → ∀ (σ : World D) (Λ : List (Res D)),
    leseA A σ Λ X = leseA A' σ Λ X)
include hG

mutual

theorem Stmt.execHA_gleich {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → (∀ c ∈ stmtOrteP P s, ¬ T c) → ∀ (σ : World D) (ρ : Env D Γ),
      execStmtHA S O U A passes R s σ ρ = execStmtHA S O U A' passes R s σ ρ
  | .assignSlot t f i e _ _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, hG _ hT] <;> (try rfl)
  | .assignThru p t _ f i e _ _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, hG _ hT] <;> (try rfl)
  | .assignSlotRef r t _ _ f e _ _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, hG _ hT] <;> (try rfl)
  | .assignGlob g e _ _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, hG _ hT] <;> (try rfl)
  | .putBytes t f hf n i _ _ e _ _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, hG _ hT] <;> (try rfl)
  | .assignVar x e, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, hG _ hT] <;> (try rfl)
  | .shift t f hτ i von nach hn _ _ _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, hG _ hT] <;> (try rfl)
  | .ite c t e, hT, σ, ρ => by
      have h1 : ∀ x ∈ c.orte, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P t, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      have h3 : ∀ x ∈ blockOrteP P e, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      simp only [execStmtHA, hG _ h1, Block.execHA_gleich t h2,
        Block.execHA_gleich e h3] <;> (try rfl)
  | .onOption o p a, hT, σ, ρ => by
      have h1 : ∀ x ∈ o.orte, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P p, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      have h3 : ∀ x ∈ blockOrteP P a, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      simp only [execStmtHA, hG _ h1, Block.execHA_gleich p h2,
        Block.execHA_gleich a h3] <;> (try rfl)
  | .onTag v arms, hT, σ, ρ => by
      have h1 : ∀ x ∈ v.orte, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      have h2 : ∀ x ∈ armsOrteP P arms, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      simp only [execStmtHA, hG _ h1, Arms.execHA_gleich arms h2] <;> (try rfl)
  | .onWhy r arms, hT, σ, ρ => by
      have h1 : ∀ x ∈ r.orte, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      have h2 : ∀ x ∈ grundArmsOrteP P arms, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      simp only [execStmtHA, hG _ h1]
      exact GrundArms.execHA_gleich arms h2 _ _ _
  | .call f args _ hr, hT, σ, ρ => by
      have h1 : ∀ x ∈ args.orte, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      simp only [execStmtHA, hG _ h1] <;> (try rfl)
  | .callInd p args _ hr, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, hG _ hT] <;> (try rfl)
  | .locks L _ body, hT, σ, ρ => by
      simp only [execStmtHA, Block.execHA_gleich body hT] <;> (try rfl)
  | .breaking _ body, hT, σ, ρ => by
      simp only [execStmtHA, Block.execHA_gleich body hT] <;> (try rfl)
  | .traverse t inv body, hT, σ, ρ => by
      have h1 : ∀ x ∈ inv.orte, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P body, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      simp only [execStmtHA, hG _ h1]
      rw [show (fun σ ρ => execBlockHA S O U A passes R body σ ρ) =
        (fun σ ρ => execBlockHA S O U A' passes R body σ ρ) from
          funext fun σ => funext fun ρ => Block.execHA_gleich body h2 σ ρ]
  | .retry n bis body ueber, hT, σ, ρ => by
      have h1 : ∀ x ∈ bis.orte, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P body, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      have h3 : ∀ x ∈ blockOrteP P ueber, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      simp only [execStmtHA, hG _ h1]
      rw [show (fun σ ρ => execBlockHA S O U A passes R body σ ρ) =
          (fun σ ρ => execBlockHA S O U A' passes R body σ ρ) from
            funext fun σ => funext fun ρ => Block.execHA_gleich body h2 σ ρ,
        show (fun σ ρ => execBlockHA S O U A passes R ueber σ ρ) =
          (fun σ ρ => execBlockHA S O U A' passes R ueber σ ρ) from
            funext fun σ => funext fun ρ => Block.execHA_gleich ueber h3 σ ρ]
  | .forever a inv body, hT, σ, ρ => by
      have h1 : ∀ x ∈ inv.orte, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P body, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      simp only [execStmtHA, hG _ h1]
      rw [show (fun σ ρ => execBlockHA S O U A passes R body σ ρ) =
        (fun σ ρ => execBlockHA S O U A' passes R body σ ρ) from
          funext fun σ => funext fun ρ => Block.execHA_gleich body h2 σ ρ]
  | .axiomCall a args _ _ _ _ _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, hG _ hT] <;> (try rfl)
  | .regWrite r _ e, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, hG _ hT] <;> (try rfl)
  | .transition .., _, _, _ => rfl
  | .publish g e _ _ _ _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, hG _ hT] <;> (try rfl)
  | .advances .., _, _, _ => rfl
  | .retires .., _, _, _ => rfl
  | .ret e _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, hG _ hT] <;> (try rfl)
  | .retWhy .., _, _, _ => rfl
  | .leave .., _, _, _ => rfl
  | .next .., _, _, _ => rfl

theorem Block.execHA_gleich {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → (∀ c ∈ blockOrteP P b, ¬ T c) → ∀ (σ : World D) (ρ : Env D Γ),
      execBlockHA S O U A passes R b σ ρ = execBlockHA S O U A' passes R b σ ρ
  | .nil, _, _, _ => rfl
  | .cons s rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ stmtOrteP P s, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, Stmt.execHA_gleich s h1, Block.execHA_gleich rest h2] <;> (try rfl)
  | .bind e rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ e.orte, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, hG _ h1, Block.execHA_gleich rest h2] <;> (try rfl)
  | .bindCall f args he _ hr rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ args.orte, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, hG _ h1, Block.execHA_gleich rest h2] <;> (try rfl)
  | .bindCallInd p args he _ hr rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ p.orte ++ args.orte, ¬ T x := fun x h => hT x (by
        simp only [List.mem_append] at h; rcases h with h | h <;> simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, hG _ h1, Block.execHA_gleich rest h2] <;> (try rfl)
  | .bindCallElse f args he _ _ err rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ args.orte, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h3 : ∀ x ∈ endblockOrteP P err, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, hG _ h1, Block.execHA_gleich rest h2,
        Endblock.execHA_gleich err h3] <;> (try rfl)
  | .bindAxiom a args he _ _ _ _ rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ args.orte, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, hG _ h1, Block.execHA_gleich rest h2] <;> (try rfl)
  | .bindAxiomElse a args he _ _ _ _ _ err rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ args.orte, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h3 : ∀ x ∈ endblockOrteP P err, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, hG _ h1, Block.execHA_gleich rest h2,
        Endblock.execHA_gleich err h3] <;> (try rfl)
  | .regRead r _ rest, hT, σ, ρ => by
      simp only [execBlockHA, Block.execHA_gleich rest hT] <;> (try rfl)
  | .regReadElse r _ zusage sonst rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ zusage.orte, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h3 : ∀ x ∈ endblockOrteP P sonst, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, hG _ h1, Block.execHA_gleich rest h2,
        Endblock.execHA_gleich sonst h3] <;> (try rfl)
  | .awaits g _ _ _ _ rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ [Sum.inr g], ¬ T x := fun x h => hT x (by
        simp only [List.mem_singleton] at h; simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, hG _ h1, Block.execHA_gleich rest h2] <;> (try rfl)
  | .exchange g neu _ _ rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ Sum.inr g :: neu.orte, ¬ T x := fun x h => hT x (by
        simp only [List.mem_cons] at h; rcases h with h | h <;> simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, hG _ h1, Block.execHA_gleich rest h2] <;> (try rfl)
  | .narrow e lo' hi' sonst rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ e.orte, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h3 : ∀ x ∈ endblockOrteP P sonst, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, hG _ h1, Block.execHA_gleich rest h2,
        Endblock.execHA_gleich sonst h3] <;> (try rfl)
  | .check c sonst rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ c.orte, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h3 : ∀ x ∈ endblockOrteP P sonst, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, hG _ h1, Block.execHA_gleich rest h2,
        Endblock.execHA_gleich sonst h3] <;> (try rfl)
  | .float op a b lo hi rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ a.orte ++ b.orte, ¬ T x := fun x h => hT x (by
        simp only [List.mem_append] at h; rcases h with h | h <;> simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, hG _ h1, Block.execHA_gleich rest h2] <;> (try rfl)
  | .floatLit q lo hi rest, hT, σ, ρ => by
      simp only [execBlockHA, Block.execHA_gleich rest hT] <;> (try rfl)
  | .floatOf e lo hi rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ e.orte, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, hG _ h1, Block.execHA_gleich rest h2] <;> (try rfl)
  | .floatNarrow e lo hi sonst rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ e.orte, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h3 : ∀ x ∈ endblockOrteP P sonst, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, hG _ h1, Block.execHA_gleich rest h2,
        Endblock.execHA_gleich sonst h3] <;> (try rfl)

theorem Endblock.execHA_gleich {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (b : Endblock D V l Γ Λ) → (∀ c ∈ endblockOrteP P b, ¬ T c) → ∀ (σ : World D) (ρ : Env D Γ),
      execEndHA S O U A passes R b σ ρ = execEndHA S O U A' passes R b σ ρ
  | .ret e _, hT, σ, ρ => by
      simp only [endblockOrteP] at hT
      simp only [execEndHA, hG _ hT] <;> (try rfl)
  | .retWhy .., _, _, _ => rfl
  | .leave .., _, _, _ => rfl
  | .next .., _, _, _ => rfl
  | .cons s rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ stmtOrteP P s, ¬ T x := fun x h => hT x (by simp [endblockOrteP, h])
      have h2 : ∀ x ∈ endblockOrteP P rest, ¬ T x := fun x h => hT x (by simp [endblockOrteP, h])
      simp only [execEndHA, Stmt.execHA_gleich s h1, Endblock.execHA_gleich rest h2] <;> (try rfl)
  | .bind e rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ e.orte, ¬ T x := fun x h => hT x (by simp [endblockOrteP, h])
      have h2 : ∀ x ∈ endblockOrteP P rest, ¬ T x := fun x h => hT x (by simp [endblockOrteP, h])
      simp only [execEndHA, hG _ h1, Endblock.execHA_gleich rest h2] <;> (try rfl)
  | .bindCall f args he _ hr rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ args.orte, ¬ T x := fun x h => hT x (by simp [endblockOrteP, h])
      have h2 : ∀ x ∈ endblockOrteP P rest, ¬ T x := fun x h => hT x (by simp [endblockOrteP, h])
      simp only [execEndHA, hG _ h1, Endblock.execHA_gleich rest h2] <;> (try rfl)
  | .bindCallElse f args he _ _ err rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ args.orte, ¬ T x := fun x h => hT x (by simp [endblockOrteP, h])
      have h2 : ∀ x ∈ endblockOrteP P rest, ¬ T x := fun x h => hT x (by simp [endblockOrteP, h])
      have h3 : ∀ x ∈ endblockOrteP P err, ¬ T x := fun x h => hT x (by simp [endblockOrteP, h])
      simp only [execEndHA, hG _ h1, Endblock.execHA_gleich rest h2,
        Endblock.execHA_gleich err h3] <;> (try rfl)
  | .bindAxiom a args he _ _ _ _ rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ args.orte, ¬ T x := fun x h => hT x (by simp [endblockOrteP, h])
      have h2 : ∀ x ∈ endblockOrteP P rest, ¬ T x := fun x h => hT x (by simp [endblockOrteP, h])
      simp only [execEndHA, hG _ h1, Endblock.execHA_gleich rest h2] <;> (try rfl)
  | .bindAxiomElse a args he _ _ _ _ _ err rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ args.orte, ¬ T x := fun x h => hT x (by simp [endblockOrteP, h])
      have h2 : ∀ x ∈ endblockOrteP P rest, ¬ T x := fun x h => hT x (by simp [endblockOrteP, h])
      have h3 : ∀ x ∈ endblockOrteP P err, ¬ T x := fun x h => hT x (by simp [endblockOrteP, h])
      simp only [execEndHA, hG _ h1, Endblock.execHA_gleich rest h2,
        Endblock.execHA_gleich err h3] <;> (try rfl)
  | .regRead r _ rest, hT, σ, ρ => by
      simp only [execEndHA, Endblock.execHA_gleich rest hT] <;> (try rfl)
  | .regReadElse r _ zusage sonst rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ zusage.orte, ¬ T x := fun x h => hT x (by simp [endblockOrteP, h])
      have h2 : ∀ x ∈ endblockOrteP P rest, ¬ T x := fun x h => hT x (by simp [endblockOrteP, h])
      have h3 : ∀ x ∈ endblockOrteP P sonst, ¬ T x := fun x h => hT x (by simp [endblockOrteP, h])
      simp only [execEndHA, hG _ h1, Endblock.execHA_gleich rest h2,
        Endblock.execHA_gleich sonst h3] <;> (try rfl)
  | .awaits g _ _ _ _ rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ [Sum.inr g], ¬ T x := fun x h => hT x (by
        simp only [List.mem_singleton] at h; simp [endblockOrteP, h])
      have h2 : ∀ x ∈ endblockOrteP P rest, ¬ T x := fun x h => hT x (by simp [endblockOrteP, h])
      simp only [execEndHA, hG _ h1, Endblock.execHA_gleich rest h2] <;> (try rfl)
  | .bindCallInd p args he _ hr rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ p.orte ++ args.orte, ¬ T x := fun x h => hT x (by
        simp only [List.mem_append] at h; rcases h with h | h <;> simp [endblockOrteP, h])
      have h2 : ∀ x ∈ endblockOrteP P rest, ¬ T x := fun x h => hT x (by simp [endblockOrteP, h])
      simp only [execEndHA, hG _ h1, Endblock.execHA_gleich rest h2] <;> (try rfl)

theorem Arms.execHA_gleich {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    (a : Arms D V l Γ Λ Λ' cs) → (∀ c ∈ armsOrteP P a, ¬ T c) →
      ∀ (v : Wert D (.sum cs)) (σ : World D) (ρ : Env D Γ),
      execArmsHA S O U A passes R a v σ ρ = execArmsHA S O U A' passes R a v σ ρ
  | .nil, _, ⟨⟨k, hk⟩, _⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | .cons b _, hT, ⟨⟨0, _⟩, nutz⟩, σ, ρ => by
      have h1 : ∀ x ∈ blockOrteP P b, ¬ T x := fun x h => hT x (by simp [armsOrteP, h])
      simp only [execArmsHA, Block.execHA_gleich b h1] <;> (try rfl)
  | .cons _ rest, hT, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ => by
      have h2 : ∀ x ∈ armsOrteP P rest, ¬ T x := fun x h => hT x (by simp [armsOrteP, h])
      simp only [execArmsHA]
      exact Arms.execHA_gleich rest h2 _ σ ρ

theorem GrundArms.execHA_gleich {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    (a : GrundArms D V l Γ Λ Λ' n) → (∀ c ∈ grundArmsOrteP P a, ¬ T c) →
      ∀ (r : Fin n) (σ : World D) (ρ : Env D Γ),
      execGrundHA S O U A passes R a r σ ρ = execGrundHA S O U A' passes R a r σ ρ
  | .nil, _, ⟨k, hk⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | .cons b _, hT, ⟨0, _⟩, σ, ρ => by
      have h1 : ∀ x ∈ blockOrteP P b, ¬ T x := fun x h => hT x (by simp [grundArmsOrteP, h])
      simp only [execGrundHA, Block.execHA_gleich b h1] <;> (try rfl)
  | .cons _ rest, hT, ⟨i + 1, h⟩, σ, ρ => by
      have h2 : ∀ x ∈ grundArmsOrteP P rest, ¬ T x := fun x h => hT x (by simp [grundArmsOrteP, h])
      simp only [execGrundHA]
      exact GrundArms.execHA_gleich rest h2 _ σ ρ

end

end Gleich
/-! ## A grown rely -/

section Wachs

/-- The environment restricted to the carriers of `T₁`: elsewhere it answers the world as it is. -/
noncomputable def einschraenken (T₁ : D.Tab ⊕ D.Glob → Prop) (A : AUmwelt D) : AUmwelt D :=
  fun X σ => mischT T₁ X σ (A X σ).speicher

theorem havocA_einschraenken (T₁ : D.Tab ⊕ D.Glob → Prop) (A : AUmwelt D) :
    HavocA T₁ (einschraenken T₁ A) :=
  fun X σ => ⟨mischT_spur T₁ X σ _, fun _ hc => mischT_aussen σ _ hc⟩

private theorem tg_symm {s s' : Speicher D} {c : D.Tab ⊕ D.Glob} (h : TraegerGleich s s' c) :
    TraegerGleich s' s c := by
  cases c <;> exact h.symm

private theorem tg_trans {s s' s'' : Speicher D} {c : D.Tab ⊕ D.Glob} (h1 : TraegerGleich s s' c)
    (h2 : TraegerGleich s' s'' c) : TraegerGleich s s'' c := by
  cases c <;> exact h1.trans h2

/-- On a read list with no carrier of `T₂` outside `T₁`, an environment of the class `T₂` answers as
    its restriction to `T₁`. -/
theorem lese_einschraenken {T₁ T₂ : D.Tab ⊕ D.Glob → Prop} {A : AUmwelt D} (hA : HavocA T₂ A) :
    ∀ X : List (D.Tab ⊕ D.Glob), (∀ c ∈ X, ¬ (T₂ c ∧ ¬ T₁ c)) → ∀ (σ : World D) (Λ : List (Res D)),
      leseA A σ Λ X = leseA (einschraenken T₁ A) σ Λ X := by
  intro X hX σ Λ
  unfold leseA einschraenken
  refine world_ext (fun c => ?_) ((hA X _).1.trans (mischT_spur T₁ X _ _).symm)
  by_cases h : c ∈ X ∧ T₁ c
  · exact tg_symm (mischT_innen _ _ h)
  · have h2 : ¬ (c ∈ X ∧ T₂ c) := fun ⟨hm, ht⟩ => h ⟨hm, Classical.byContradiction fun hn => hX c hm ⟨ht, hn⟩⟩
    exact tg_trans ((hA X _).2 c h2) (tg_symm (mischT_aussen _ _ h))

variable {P : Programm D} {passes : Nat} {Q : AxEns D} {S : SperrInv D} {T₁ T₂ : D.Tab ⊕ D.Glob → Prop}
  {f : D.Fn}

/-- **A grown rely asks a new proof only of a body that reads a carrier of the growth.** A body
    proved against the shared atomics `T₁` keeps its obligation against any `T₂` when none of its
    reads is a carrier of `T₂` outside `T₁` (`LiestNicht`). -/
theorem koerperGutSA_wachs (h : KoerperGutSA P passes Q S T₁ f)
    (hl : ∀ c ∈ endblockOrteP P (P.rumpf f), ¬ (T₂ c ∧ ¬ T₁ c)) : KoerperGutSA P passes Q S T₂ f := by
  refine ⟨fun O' a b c U hU A hA R hR hOV σ ρ hreq => ?_, fun O' a b c U hU A hA R hR hOL σ ρ hreq => ?_⟩
  · have e := fun R' => Endblock.execHA_gleich P S O' U A passes R' (einschraenken T₁ A) (lese_einschraenken hA)
      (P.rumpf f) hl σ ρ
    obtain ⟨h1, h2⟩ := h.1 O' a b c U hU _ (havocA_einschraenken T₁ A) R hR hOV σ ρ hreq
    refine ⟨fun σ' v hr => h1 σ' v ((e R).symm.trans hr), fun g hr => h2 g ((e _).symm.trans hr)⟩
  · have e := Endblock.execHA_gleich P S O' U A passes R (einschraenken T₁ A) (lese_einschraenken hA) (P.rumpf f) hl σ ρ
    exact fun e' hr => h.2 O' a b c U hU _ (havocA_einschraenken T₁ A) R hR hOL σ ρ hreq e'
      ((e).symm.trans hr)

theorem invGutSA_wachs (h : InvGutSA P passes Q S T₁ f)
    (hl : ∀ c ∈ endblockOrteP P (P.rumpf f), ¬ (T₂ c ∧ ¬ T₁ c)) : InvGutSA P passes Q S T₂ f :=
  fun O' a b c U hU A hA R hR hOV σ ρ hreq σ' v hr =>
    h O' a b c U hU _ (havocA_einschraenken T₁ A) R hR hOV σ ρ hreq σ' v
      ((Endblock.execHA_gleich P S O' U A passes R (einschraenken T₁ A) (lese_einschraenken hA) (P.rumpf f) hl σ ρ).symm.trans hr)

theorem invGutGrundA_wachs (h : InvGutGrundA P passes Q S T₁ f)
    (hl : ∀ c ∈ endblockOrteP P (P.rumpf f), ¬ (T₂ c ∧ ¬ T₁ c)) : InvGutGrundA P passes Q S T₂ f :=
  fun O' a b c U hU A hA R hR hOV σ ρ hreq σ' r hr =>
    h O' a b c U hU _ (havocA_einschraenken T₁ A) R hR hOV σ ρ hreq σ' r
      ((Endblock.execHA_gleich P S O' U A passes R (einschraenken T₁ A) (lese_einschraenken hA) (P.rumpf f) hl σ ρ).symm.trans hr)

end Wachs

#print axioms koerperGutSA_wachs

end Gabbro.Grammatik
