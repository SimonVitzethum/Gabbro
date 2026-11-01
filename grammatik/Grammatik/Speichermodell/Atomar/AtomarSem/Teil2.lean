module

public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem
public import Grammatik.Speichermodell.Atomar.AtomarSem.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Frei
set_option linter.unusedSectionVars false
variable (P : Programm D) (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (A : AUmwelt D)
  (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  {T : D.Tab ⊕ D.Glob → Prop} (hA : HavocA T A)
  (hRL : ∀ (g : D.Glob) (σ σ' : World D), GleichAuf [Sum.inr g] σ σ' →
    O.sichtbar g σ = O.sichtbar g σ')
include hA hRL

mutual

theorem Stmt.execHA_frei {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → (∀ c ∈ stmtOrteP P s, ¬ T c) → ∀ (σ : World D) (ρ : Env D Γ),
      execStmtHA S O U A passes R s σ ρ = execStmtH S O U passes R s σ ρ
  | .assignSlot t f i e _ _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, execStmtH, leseA_frei hA hT] <;> (try rfl)
  | .assignThru p t _ f i e _ _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, execStmtH, leseA_frei hA hT] <;> (try rfl)
  | .assignSlotRef r t _ _ f e _ _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, execStmtH, leseA_frei hA hT] <;> (try rfl)
  | .assignGlob g e _ _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, execStmtH, leseA_frei hA hT] <;> (try rfl)
  | .putBytes t f hf n i _ _ e _ _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, execStmtH, leseA_frei hA hT] <;> (try rfl)
  | .assignVar x e, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, execStmtH, leseA_frei hA hT] <;> (try rfl)
  | .shift t f hτ i von nach hn _ _ _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, execStmtH, leseA_frei hA hT] <;> (try rfl)
  | .ite c t e, hT, σ, ρ => by
      have h1 : ∀ x ∈ c.orte, ¬ T x := fun x h => hT x (by simp only [stmtOrteP, List.append_assoc, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ blockOrteP P t, ¬ T x := fun x h => hT x (by simp only [stmtOrteP, List.append_assoc, List.mem_append, h, true_or, or_true])
      have h3 : ∀ x ∈ blockOrteP P e, ¬ T x := fun x h => hT x (by simp only [stmtOrteP, List.append_assoc, List.mem_append, h, or_true])
      simp only [execStmtHA, execStmtH, leseA_frei hA h1, Block.execHA_frei t h2,
        Block.execHA_frei e h3] <;> (try rfl)
  | .onOption o p a, hT, σ, ρ => by
      have h1 : ∀ x ∈ o.orte, ¬ T x := fun x h => hT x (by simp only [stmtOrteP, List.append_assoc, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ blockOrteP P p, ¬ T x := fun x h => hT x (by simp only [stmtOrteP, List.append_assoc, List.mem_append, h, true_or, or_true])
      have h3 : ∀ x ∈ blockOrteP P a, ¬ T x := fun x h => hT x (by simp only [stmtOrteP, List.append_assoc, List.mem_append, h, or_true])
      simp only [execStmtHA, execStmtH, leseA_frei hA h1, Block.execHA_frei p h2,
        Block.execHA_frei a h3] <;> (try rfl)
  | .onTag v arms, hT, σ, ρ => by
      have h1 : ∀ x ∈ v.orte, ¬ T x := fun x h => hT x (by simp only [stmtOrteP, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ armsOrteP P arms, ¬ T x := fun x h => hT x (by simp only [stmtOrteP, List.mem_append, h, or_true])
      simp only [execStmtHA, execStmtH, leseA_frei hA h1, Arms.execHA_frei arms h2] <;> (try rfl)
  | .onWhy r arms, hT, σ, ρ => by
      have h1 : ∀ x ∈ r.orte, ¬ T x := fun x h => hT x (by simp only [stmtOrteP, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ grundArmsOrteP P arms, ¬ T x := fun x h => hT x (by simp only [stmtOrteP, List.mem_append, h, or_true])
      simp only [execStmtHA, execStmtH, leseA_frei hA h1]
      exact GrundArms.execHA_frei arms h2 _ _ _
  | .call f args _ hr, hT, σ, ρ => by
      have h1 : ∀ x ∈ args.orte, ¬ T x := fun x h => hT x (by simp only [stmtOrteP, List.mem_append, h, true_or])
      simp only [execStmtHA, execStmtH, leseA_frei hA h1] <;> (try rfl)
  | .callInd p args _ hr, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, execStmtH, leseA_frei hA hT] <;> (try rfl)
  | .locks L _ body, hT, σ, ρ => by
      simp only [execStmtHA, execStmtH, Block.execHA_frei body hT] <;> (try rfl)
  | .breaking _ body, hT, σ, ρ => by
      simp only [execStmtHA, execStmtH, Block.execHA_frei body hT] <;> (try rfl)
  | .traverse t inv body, hT, σ, ρ => by
      have h1 : ∀ x ∈ inv.orte, ¬ T x := fun x h => hT x (by simp only [stmtOrteP, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ blockOrteP P body, ¬ T x := fun x h => hT x (by simp only [stmtOrteP, List.mem_append, h, or_true])
      simp only [execStmtHA, execStmtH, leseA_frei hA h1]
      rw [show (fun σ ρ => execBlockHA S O U A passes R body σ ρ) =
        (fun σ ρ => execBlockH S O U passes R body σ ρ) from
          funext fun σ => funext fun ρ => Block.execHA_frei body h2 σ ρ]
  | .retry n bis body ueber, hT, σ, ρ => by
      have h1 : ∀ x ∈ bis.orte, ¬ T x := fun x h => hT x (by simp only [stmtOrteP, List.append_assoc, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ blockOrteP P body, ¬ T x := fun x h => hT x (by simp only [stmtOrteP, List.append_assoc, List.mem_append, h, true_or, or_true])
      have h3 : ∀ x ∈ blockOrteP P ueber, ¬ T x := fun x h => hT x (by simp only [stmtOrteP, List.append_assoc, List.mem_append, h, or_true])
      simp only [execStmtHA, execStmtH, leseA_frei hA h1]
      rw [show (fun σ ρ => execBlockHA S O U A passes R body σ ρ) =
          (fun σ ρ => execBlockH S O U passes R body σ ρ) from
            funext fun σ => funext fun ρ => Block.execHA_frei body h2 σ ρ,
        show (fun σ ρ => execBlockHA S O U A passes R ueber σ ρ) =
          (fun σ ρ => execBlockH S O U passes R ueber σ ρ) from
            funext fun σ => funext fun ρ => Block.execHA_frei ueber h3 σ ρ]
  | .forever a inv body, hT, σ, ρ => by
      have h1 : ∀ x ∈ inv.orte, ¬ T x := fun x h => hT x (by simp only [stmtOrteP, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ blockOrteP P body, ¬ T x := fun x h => hT x (by simp only [stmtOrteP, List.mem_append, h, or_true])
      simp only [execStmtHA, execStmtH, leseA_frei hA h1]
      rw [show (fun σ ρ => execBlockHA S O U A passes R body σ ρ) =
        (fun σ ρ => execBlockH S O U passes R body σ ρ) from
          funext fun σ => funext fun ρ => Block.execHA_frei body h2 σ ρ]
  | .axiomCall a args _ _ _ _ _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, execStmtH, leseA_frei hA hT] <;> (try rfl)
  | .regWrite r _ e, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, execStmtH, leseA_frei hA hT] <;> (try rfl)
  | .transition .., _, _, _ => rfl
  | .publish g e _ _ _ _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, execStmtH, leseA_frei hA hT] <;> (try rfl)
  | .advances .., _, _, _ => rfl
  | .retires .., _, _, _ => rfl
  | .ret e _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, execStmtH, leseA_frei hA hT] <;> (try rfl)
  | .retWhy .., _, _, _ => rfl
  | .leave .., _, _, _ => rfl
  | .next .., _, _, _ => rfl

theorem Block.execHA_frei {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → (∀ c ∈ blockOrteP P b, ¬ T c) → ∀ (σ : World D) (ρ : Env D Γ),
      execBlockHA S O U A passes R b σ ρ = execBlockH S O U passes R b σ ρ
  | .nil, _, _, _ => rfl
  | .cons s rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ stmtOrteP P s, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.mem_append, h, or_true])
      simp only [execBlockHA, execBlockH, Stmt.execHA_frei s h1, Block.execHA_frei rest h2] <;> (try rfl)
  | .bind e rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ e.orte, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.mem_append, h, or_true])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2] <;> (try rfl)
  | .bindCall f args he _ hr rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ args.orte, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.append_assoc, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.append_assoc, List.mem_append, h, or_true])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2] <;> (try rfl)
  | .bindCallInd p args he _ hr rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ p.orte ++ args.orte, ¬ T x := fun x h => hT x (by
        simp only [List.mem_append] at h; rcases h with h | h <;> simp only [blockOrteP, List.append_assoc, List.mem_append, h, true_or, or_true])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.append_assoc, List.mem_append, h, or_true])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2] <;> (try rfl)
  | .bindCallElse f args he _ _ err rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ args.orte, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.append_assoc, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.append_assoc, List.mem_append, h, or_true])
      have h3 : ∀ x ∈ endblockOrteP P err, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.append_assoc, List.mem_append, h, true_or, or_true])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2,
        Endblock.execHA_frei err h3] <;> (try rfl)
  | .bindAxiom a args he _ _ _ _ rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ args.orte, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.mem_append, h, or_true])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2] <;> (try rfl)
  | .bindAxiomElse a args he _ _ _ _ _ err rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ args.orte, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.append_assoc, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.append_assoc, List.mem_append, h, or_true])
      have h3 : ∀ x ∈ endblockOrteP P err, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.append_assoc, List.mem_append, h, true_or, or_true])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2,
        Endblock.execHA_frei err h3] <;> (try rfl)
  | .regRead r _ rest, hT, σ, ρ => by
      simp only [execBlockHA, execBlockH, Block.execHA_frei rest hT] <;> (try rfl)
  | .regReadElse r _ zusage sonst rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ zusage.orte, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.append_assoc, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.append_assoc, List.mem_append, h, or_true])
      have h3 : ∀ x ∈ endblockOrteP P sonst, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.append_assoc, List.mem_append, h, true_or, or_true])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2,
        Endblock.execHA_frei sonst h3] <;> (try rfl)
  | .awaits g _ _ _ _ rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ [Sum.inr g], ¬ T x := fun x h => hT x (by
        simp only [List.mem_singleton] at h; simp only [blockOrteP, h, List.mem_cons, true_or])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.mem_cons, h, or_true])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2,
        sichtbar_lese hRL] <;> (try rfl)
  | .exchange g neu _ _ rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ Sum.inr g :: neu.orte, ¬ T x := fun x h => hT x (by
        simp only [List.mem_cons] at h; rcases h with h | h <;> simp only [blockOrteP, List.cons_append, h, List.mem_cons, List.mem_append, true_or, or_true])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.cons_append, List.mem_cons, List.mem_append, h, or_true])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2] <;> (try rfl)
  | .narrow e lo' hi' sonst rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ e.orte, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.append_assoc, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.append_assoc, List.mem_append, h, or_true])
      have h3 : ∀ x ∈ endblockOrteP P sonst, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.append_assoc, List.mem_append, h, true_or, or_true])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2,
        Endblock.execHA_frei sonst h3] <;> (try rfl)
  | .check c sonst rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ c.orte, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.append_assoc, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.append_assoc, List.mem_append, h, or_true])
      have h3 : ∀ x ∈ endblockOrteP P sonst, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.append_assoc, List.mem_append, h, true_or, or_true])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2,
        Endblock.execHA_frei sonst h3] <;> (try rfl)
  | .float op a b lo hi rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ a.orte ++ b.orte, ¬ T x := fun x h => hT x (by
        simp only [List.mem_append] at h; rcases h with h | h <;> simp only [blockOrteP, List.append_assoc, List.mem_append, h, true_or, or_true])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.append_assoc, List.mem_append, h, or_true])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2] <;> (try rfl)
  | .floatLit q lo hi rest, hT, σ, ρ => by
      simp only [execBlockHA, execBlockH, Block.execHA_frei rest hT] <;> (try rfl)
  | .floatOf e lo hi rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ e.orte, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.mem_append, h, or_true])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2] <;> (try rfl)
  | .floatNarrow e lo hi sonst rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ e.orte, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.append_assoc, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.append_assoc, List.mem_append, h, or_true])
      have h3 : ∀ x ∈ endblockOrteP P sonst, ¬ T x := fun x h => hT x (by simp only [blockOrteP, List.append_assoc, List.mem_append, h, true_or, or_true])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2,
        Endblock.execHA_frei sonst h3] <;> (try rfl)

theorem Endblock.execHA_frei {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (b : Endblock D V l Γ Λ) → (∀ c ∈ endblockOrteP P b, ¬ T c) → ∀ (σ : World D) (ρ : Env D Γ),
      execEndHA S O U A passes R b σ ρ = execEndH S O U passes R b σ ρ
  | .ret e _, hT, σ, ρ => by
      simp only [endblockOrteP] at hT
      simp only [execEndHA, execEndH, leseA_frei hA hT] <;> (try rfl)
  | .retWhy .., _, _, _ => rfl
  | .leave .., _, _, _ => rfl
  | .next .., _, _, _ => rfl
  | .cons s rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ stmtOrteP P s, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ endblockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.mem_append, h, or_true])
      simp only [execEndHA, execEndH, Stmt.execHA_frei s h1, Endblock.execHA_frei rest h2] <;> (try rfl)
  | .bind e rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ e.orte, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ endblockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.mem_append, h, or_true])
      simp only [execEndHA, execEndH, leseA_frei hA h1, Endblock.execHA_frei rest h2] <;> (try rfl)
  | .bindCall f args he _ hr rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ args.orte, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.append_assoc, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ endblockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.append_assoc, List.mem_append, h, or_true])
      simp only [execEndHA, execEndH, leseA_frei hA h1, Endblock.execHA_frei rest h2] <;> (try rfl)
  | .bindCallElse f args he _ _ err rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ args.orte, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.append_assoc, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ endblockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.append_assoc, List.mem_append, h, or_true])
      have h3 : ∀ x ∈ endblockOrteP P err, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.append_assoc, List.mem_append, h, true_or, or_true])
      simp only [execEndHA, execEndH, leseA_frei hA h1, Endblock.execHA_frei rest h2,
        Endblock.execHA_frei err h3] <;> (try rfl)
  | .bindAxiom a args he _ _ _ _ rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ args.orte, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ endblockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.mem_append, h, or_true])
      simp only [execEndHA, execEndH, leseA_frei hA h1, Endblock.execHA_frei rest h2] <;> (try rfl)
  | .bindAxiomElse a args he _ _ _ _ _ err rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ args.orte, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.append_assoc, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ endblockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.append_assoc, List.mem_append, h, or_true])
      have h3 : ∀ x ∈ endblockOrteP P err, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.append_assoc, List.mem_append, h, true_or, or_true])
      simp only [execEndHA, execEndH, leseA_frei hA h1, Endblock.execHA_frei rest h2,
        Endblock.execHA_frei err h3] <;> (try rfl)
  | .regRead r _ rest, hT, σ, ρ => by
      simp only [execEndHA, execEndH, Endblock.execHA_frei rest hT] <;> (try rfl)
  | .regReadElse r _ zusage sonst rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ zusage.orte, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.append_assoc, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ endblockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.append_assoc, List.mem_append, h, or_true])
      have h3 : ∀ x ∈ endblockOrteP P sonst, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.append_assoc, List.mem_append, h, true_or, or_true])
      simp only [execEndHA, execEndH, leseA_frei hA h1, Endblock.execHA_frei rest h2,
        Endblock.execHA_frei sonst h3] <;> (try rfl)
  | .awaits g _ _ _ _ rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ [Sum.inr g], ¬ T x := fun x h => hT x (by
        simp only [List.mem_singleton] at h; simp only [endblockOrteP, h, List.mem_cons, true_or])
      have h2 : ∀ x ∈ endblockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.mem_cons, h, or_true])
      simp only [execEndHA, execEndH, leseA_frei hA h1, Endblock.execHA_frei rest h2,
        sichtbar_lese hRL] <;> (try rfl)
  | .bindCallInd p args he _ hr rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ p.orte ++ args.orte, ¬ T x := fun x h => hT x (by
        simp only [List.mem_append] at h; rcases h with h | h <;> simp only [endblockOrteP, List.append_assoc, List.mem_append, h, true_or, or_true])
      have h2 : ∀ x ∈ endblockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.append_assoc, List.mem_append, h, or_true])
      simp only [execEndHA, execEndH, leseA_frei hA h1, Endblock.execHA_frei rest h2] <;> (try rfl)
  | .narrow e lo' hi' sonst rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ e.orte, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.append_assoc, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ endblockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.append_assoc, List.mem_append, h, or_true])
      have h3 : ∀ x ∈ endblockOrteP P sonst, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.append_assoc, List.mem_append, h, true_or, or_true])
      simp only [execEndHA, execEndH, leseA_frei hA h1, Endblock.execHA_frei rest h2,
        Endblock.execHA_frei sonst h3] <;> (try rfl)
  | .exchange g neu _ _ rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ Sum.inr g :: neu.orte, ¬ T x := fun x h => hT x (by
        simp only [List.mem_cons] at h; rcases h with h | h <;> simp only [endblockOrteP, List.cons_append, h, List.mem_cons, List.mem_append, true_or, or_true])
      have h2 : ∀ x ∈ endblockOrteP P rest, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.cons_append, List.mem_cons, List.mem_append, h, or_true])
      simp only [execEndHA, execEndH, leseA_frei hA h1, Endblock.execHA_frei rest h2] <;> (try rfl)
  | .ite c t e, hT, σ, ρ => by
      have h1 : ∀ x ∈ c.orte, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.append_assoc, List.mem_append, h, true_or])
      have h2 : ∀ x ∈ endblockOrteP P t, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.append_assoc, List.mem_append, h, or_true])
      have h3 : ∀ x ∈ endblockOrteP P e, ¬ T x := fun x h => hT x (by simp only [endblockOrteP, List.append_assoc, List.mem_append, h, true_or, or_true])
      simp only [execEndHA, execEndH, leseA_frei hA h1, Endblock.execHA_frei t h2,
        Endblock.execHA_frei e h3] <;> (try rfl)

theorem Arms.execHA_frei {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    (a : Arms D V l Γ Λ Λ' cs) → (∀ c ∈ armsOrteP P a, ¬ T c) →
      ∀ (v : Wert D (.sum cs)) (σ : World D) (ρ : Env D Γ),
      execArmsHA S O U A passes R a v σ ρ = execArmsH S O U passes R a v σ ρ
  | .nil, _, ⟨⟨k, hk⟩, _⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | .cons b _, hT, ⟨⟨0, _⟩, nutz⟩, σ, ρ => by
      have h1 : ∀ x ∈ blockOrteP P b, ¬ T x := fun x h => hT x (by simp only [armsOrteP, List.mem_append, h, true_or])
      simp only [execArmsHA, execArmsH, Block.execHA_frei b h1] <;> (try rfl)
  | .cons _ rest, hT, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ => by
      have h2 : ∀ x ∈ armsOrteP P rest, ¬ T x := fun x h => hT x (by simp only [armsOrteP, List.mem_append, h, or_true])
      simp only [execArmsHA, execArmsH]
      exact Arms.execHA_frei rest h2 _ σ ρ

theorem GrundArms.execHA_frei {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    (a : GrundArms D V l Γ Λ Λ' n) → (∀ c ∈ grundArmsOrteP P a, ¬ T c) →
      ∀ (r : Fin n) (σ : World D) (ρ : Env D Γ),
      execGrundHA S O U A passes R a r σ ρ = execGrundH S O U passes R a r σ ρ
  | .nil, _, ⟨k, hk⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | .cons b _, hT, ⟨0, _⟩, σ, ρ => by
      have h1 : ∀ x ∈ blockOrteP P b, ¬ T x := fun x h => hT x (by simp only [grundArmsOrteP, List.mem_append, h, true_or])
      simp only [execGrundHA, execGrundH, Block.execHA_frei b h1] <;> (try rfl)
  | .cons _ rest, hT, ⟨i + 1, h⟩, σ, ρ => by
      have h2 : ∀ x ∈ grundArmsOrteP P rest, ¬ T x := fun x h => hT x (by simp only [grundArmsOrteP, List.mem_append, h, or_true])
      simp only [execGrundHA, execGrundH]
      exact GrundArms.execHA_frei rest h2 _ σ ρ

end

end Frei

/-- **The identity environment is no havoc**: with it the semantics is `execStmtH`, on every
    body (visibility local, `RegLokal`'s second half). -/
theorem execEndHA_id (P : Programm D) (S : SperrInv D) (O : Orakel D) (U : Umwelt D)
    (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
    (hRL : ∀ (g : D.Glob) (σ σ' : World D), GleichAuf [Sum.inr g] σ σ' →
      O.sichtbar g σ = O.sichtbar g σ')
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (b : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    execEndHA S O U idA passes R b σ ρ = execEndH S O U passes R b σ ρ :=
  Endblock.execHA_frei P S O U idA passes R (T := fun _ => False) (havocA_id _) hRL b
    (fun _ _ h => h) σ ρ

#print axioms Gabbro.Grammatik.leseA_frei
#print axioms Gabbro.Grammatik.Endblock.execHA_frei
#print axioms Gabbro.Grammatik.execEndHA_id

end Gabbro.Grammatik
