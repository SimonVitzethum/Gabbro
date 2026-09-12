/-
  File:      Grammatik/Geist.lean
  Subject:   GHOST CARRIERS (syscall lane S3) -- spec-only tables and globals.

  A ghost carrier is ordinary memory for the semantics (every theorem stays
  valid) and absent for the emitter. Rule G001: executable code reads no
  ghost. Ghost tables may appear only in contracts (`requires`/`ensures`).
-/
import Grammatik.Extraktion
import Grammatik.Satz
import Grammatik.Maschine

namespace Gabbro.Grammatik.Geist

open Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-- A carrier is ghost if its declaration flag says so. -/
def istGeist : D.Tab ⊕ D.Glob → Bool
  | .inl t => D.geist t
  | .inr g => D.ggeist g

/-- A read footprint carries no ghost: the emission-relevant check. -/
def orteOhneGeist (os : List (D.Tab ⊕ D.Glob)) : Prop :=
  ∀ o ∈ os, istGeist (D := D) o = false

/-! ## No ghost: everything behaves as before.

    The semantics never consults `geist`/`ggeist`: `eval`, `execStmt`,
    `execBlock`, `execEnd`, `World.lese`, stores, `rufAt` and the `Programm`
    fields are defined without them. These theorems record that fact as
    equalities of the relevant functions. -/

/-- With no ghost flags, the ghost predicate is false on every carrier: no
    new case, no changed behavior. Every premise fires: `ht` discharges the
    table side, `hg` the global side, and `o` is the carrier inspected. -/
theorem geist_leer_unveraendert
    (ht : ∀ t : D.Tab, D.geist t = false) (hg : ∀ g : D.Glob, D.ggeist g = false)
    (o : D.Tab ⊕ D.Glob) :
    istGeist (D := D) o = false := by
  cases o with
  | inl t =>
      show D.geist t = false
      exact ht t
  | inr g =>
      show D.ggeist g = false
      exact hg g

/-! ## The G001 decision: a `Bool` check over footprints. -/

/-- The footprint-level decision: every listed carrier is real. The `os`
    premise is the footprint under inspection. -/
def orteOk (os : List (D.Tab ⊕ D.Glob)) : Bool :=
  os.all fun o => !(istGeist (D := D) o)

/-- The footprint decision is sound: `orteOk os = true` means no member is
    ghost. The `h` premise is the decision outcome; `ho` fixes the member. -/
theorem orteOk_korrekt (os : List (D.Tab ⊕ D.Glob))
    (h : orteOk (D := D) os = true)
    (o : D.Tab ⊕ D.Glob) (ho : o ∈ os) :
    istGeist (D := D) o = false := by
  unfold orteOk at h
  have hpoint := List.all_eq_true.mp h o ho
  simp at hpoint
  exact hpoint

/-- Bool-negation from `= false`: every `orteOk` leaf ends here, since the
    soundness statements conclude `¬ istGeist o`. The `h` premise is the
    `= false` fact; the conclusion is its negation. -/
theorem nge_of_eq_false {b : Bool} (h : b = false) : ¬ b := by
  intro hcon
  rw [h] at hcon
  exact Bool.false_ne_true hcon

/-! ## The G001 decision over bodies: one `Bool` check per body form.

    Structural recursion over the body (`Stmt`/`Block`/`Endblock`/`Arms`/
    `GrundArms` mutual with `Syntax.lean`, like the checker would run it):
    expression positions are checked with `orteOk` against the flags,
    sub-bodies recurse. `awaits`/`exchange` name their global directly
    (they read it per `execBlock`), so the decision checks `[.inr g]`. -/

mutual

/-- The G001 check over one statement. -/
def g001Stmt {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Bool
  | .assignSlot _ _ i e _ _ => orteOk (D := D) (i.orte ++ e.orte)
  | .assignDurch p _ _ _ i e _ _ => orteOk (D := D) (p.orte ++ i.orte ++ e.orte)
  | .assignGlob _ e _ _ => orteOk (D := D) e.orte
  | .schreibBytes _ _ _ _ i _ _ e _ _ => orteOk (D := D) (i.orte ++ e.orte)
  | .assignVar _ e => orteOk (D := D) e.orte
  | .uebergang _ _ _ i _ _ _ _ _ _ => orteOk (D := D) i.orte
  | .ite c t e => orteOk (D := D) c.orte && g001 t && g001 e
  | .onOption o p a => orteOk (D := D) o.orte && g001 p && g001 a
  | .onTag v arms => orteOk (D := D) v.orte && g001Arms arms
  | .onGrund r arms => orteOk (D := D) r.orte && g001Grund arms
  | .call _ args _ _ => orteOk (D := D) args.orte
  | .callInd p args _ _ => orteOk (D := D) (p.orte ++ args.orte)
  | .locks _ _ body => g001 body
  | .breaking _ body => g001 body
  | .traverse _ inv body => orteOk (D := D) inv.orte && g001 body
  | .retry _ bis body ueber => orteOk (D := D) bis.orte && g001 body && g001 ueber
  | .forever _ inv body => orteOk (D := D) inv.orte && g001 body
  | .axiomCall _ args _ _ _ _ _ => orteOk (D := D) args.orte
  | .regSchreib _ _ e => orteOk (D := D) e.orte
  | .transition _ _ _ _ _ _ _ => true
  | .publish _ e _ _ _ _ => orteOk (D := D) e.orte
  | .advances _ _ _ _ => true
  | .retires _ _ _ _ => true
  | .ret e _ => orteOk (D := D) e.orte
  | .retGrund _ _ => true
  | .leave _ => true
  | .next _ => true

/-- The G001 check over a block. -/
def g001 {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => g001Stmt s && g001 rest
  | .bind e rest => orteOk (D := D) e.orte && g001 rest
  | .bindCall _ args _ _ _ rest => orteOk (D := D) args.orte && g001 rest
  | .bindCallInd p args _ _ _ rest =>
      orteOk (D := D) (p.orte ++ args.orte) && g001 rest
  | .bindCallElse _ args _ _ _ err rest =>
      orteOk (D := D) args.orte && g001End err && g001 rest
  | .bindAxiom _ args _ _ _ _ _ rest => orteOk (D := D) args.orte && g001 rest
  | .regLies _ _ rest => g001 rest
  | .regLiesElse _ _ zusage sonst rest =>
      orteOk (D := D) zusage.orte && g001End sonst && g001 rest
  | .awaits g _ _ _ rest => orteOk (D := D) [.inr g] && g001 rest
  | .exchange g neu _ _ rest =>
      orteOk (D := D) ([.inr g] ++ neu.orte) && g001 rest
  | .narrow e _ _ sonst rest =>
      orteOk (D := D) e.orte && g001End sonst && g001 rest
  | .pruefung c sonst rest =>
      orteOk (D := D) c.orte && g001End sonst && g001 rest
  | .gleit _ a b _ _ rest =>
      orteOk (D := D) (a.orte ++ b.orte) && g001 rest
  | .gleitLit _ _ _ rest => g001 rest
  | .gleitVon e _ _ rest => orteOk (D := D) e.orte && g001 rest
  | .gleitNarrow e _ _ sonst rest =>
      orteOk (D := D) e.orte && g001End sonst && g001 rest

/-- The G001 check over a non-falling block: the form the checker runs on
    each function body. -/
def g001End : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} →
    Endblock D V l Γ Λ → Bool
  | _, _, _, .ret e _ => orteOk (D := D) e.orte
  | _, _, _, .retGrund _ _ => true
  | _, _, _, .leave _ => true
  | _, _, _, .next _ => true
  | _, _, _, .cons s rest => g001Stmt s && g001End rest
  | _, _, _, .bind e rest => orteOk (D := D) e.orte && g001End rest

/-- The G001 check over case arms. -/
def g001Arms {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => g001 b && g001Arms rest

/-- The G001 check over reason arms. -/
def g001Grund {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => g001 b && g001Grund rest

end

/-! ## Soundness: an accepted body reads no ghost.

    The bridge between the `Bool` decision and the `Prop` footprint claim.
    The decision and the `Extraktion` footprint projections are defined by
    the same per-constructor lists, so each `g001* = true` case discharges
    through `orteOk_korrekt` (via `nge_of_eq_false`) on expression positions
    and the matching sibling theorem on sub-bodies. The five soundness
    theorems form one `mutual` block: each calls its siblings directly, so
    no hypothesis threading is needed.

    Proof shape (measured in this file): splitting `cases` on the body while
    the goal still mentions the `Bool` decision applied to the outer body
    fails, so each proof first does `revert h ho`, then `cases`, then
    `intro`s per arm: the arms take `h` as the same-shape equation by
    definitional unfolding (`have h0 := h`, never `simpa`) and transport
    `ho` with `simpa [Extraktion.*Orte]` into a disjunction. Conjunctions
    split with `Bool.and_eq_true_iff.mp` (never `simp only
    [Bool.and_eq_true]`, which leaves `decide (_ = true)` wrappers this
    toolchain does not strip). -/

mutual

/-- Soundness for statements. Sub-body ghost-freedom comes from the sibling
    theorems of this `mutual` block. Every premise fires: `h`/`ho` fix the
    decision and the member. -/
theorem g001Stmt_korrekt {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (h : g001Stmt s = true)
    (o : D.Tab ⊕ D.Glob) (ho : o ∈ Extraktion.stmtOrte s) :
    ¬ istGeist (D := D) o := by
  revert h ho
  match s with
  | .assignSlot t f i e hw hL =>
      intro h ho
      have h' : orteOk (D := D) (i.orte ++ e.orte) = true := by simpa [g001Stmt] using h
      have ho' : o ∈ i.orte ++ e.orte := by simpa [Extraktion.stmtOrte] using ho
      exact nge_of_eq_false (orteOk_korrekt (D := D) _ h' o ho')
  | .ite c t e =>
      intro h ho
      have h0 : (orteOk (D := D) c.orte && g001 t && g001 e) = true := h
      have ho' : o ∈ c.orte ∨ o ∈ Extraktion.blockOrte t ∨ o ∈ Extraktion.blockOrte e := by
        simpa [Extraktion.stmtOrte] using ho
      have h1 : ((orteOk (D := D) c.orte && g001 t) = true) ∧ ((g001 e) = true) :=
        Bool.and_eq_true_iff.mp h0
      have h2 : ((orteOk (D := D) c.orte) = true) ∧ ((g001 t) = true) :=
        Bool.and_eq_true_iff.mp h1.1
      rcases ho' with ho' | ho' | ho'
      · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h2.1 o ho')
      · exact g001_korrekt t h2.2 o ho'
      · exact g001_korrekt e h1.2 o ho'
  | .assignDurch p t ht f i e hw hL =>
      intro h ho
      have h0 : (orteOk (D := D) (p.orte ++ i.orte ++ e.orte)) = true := h
      have ho' : o ∈ p.orte ++ i.orte ++ e.orte := by
        simpa [Extraktion.stmtOrte] using ho
      exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')
  | .assignGlob g e hw hL =>
      intro h ho
      have h0 : (orteOk (D := D) e.orte) = true := h
      have ho' : o ∈ e.orte := by
        simpa [Extraktion.stmtOrte] using ho
      exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')
  | .schreibBytes t f hf n i hlo hhi e hw hL =>
      intro h ho
      have h0 : (orteOk (D := D) (i.orte ++ e.orte)) = true := h
      have ho' : o ∈ i.orte ++ e.orte := by
        simpa [Extraktion.stmtOrte] using ho
      exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')
  | .assignVar x e =>
      intro h ho
      have h0 : (orteOk (D := D) e.orte) = true := h
      have ho' : o ∈ e.orte := by
        simpa [Extraktion.stmtOrte] using ho
      exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')
  | .uebergang t f hτ i von nach hn he hw hL =>
      intro h ho
      have h0 : (orteOk (D := D) i.orte) = true := h
      have ho' : o ∈ i.orte := by
        simpa [Extraktion.stmtOrte] using ho
      exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')
  | .call f args hp hr =>
      intro h ho
      have h0 : (orteOk (D := D) args.orte) = true := h
      have ho' : o ∈ args.orte := by
        simpa [Extraktion.stmtOrte] using ho
      exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')
  | .callInd p args hp hr =>
      intro h ho
      have h0 : (orteOk (D := D) (p.orte ++ args.orte)) = true := h
      have ho' : o ∈ p.orte ++ args.orte := by
        simpa [Extraktion.stmtOrte] using ho
      exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')
  | .axiomCall a args h hw hg hd hgd =>
      intro h ho
      have h0 : (orteOk (D := D) args.orte) = true := h
      have ho' : o ∈ args.orte := by
        simpa [Extraktion.stmtOrte] using ho
      exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')
  | .regSchreib r hk e =>
      intro h ho
      have h0 : (orteOk (D := D) e.orte) = true := h
      have ho' : o ∈ e.orte := by
        simpa [Extraktion.stmtOrte] using ho
      exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')
  | .publish g e payload hp hw hL =>
      intro h ho
      have h0 : (orteOk (D := D) e.orte) = true := h
      have ho' : o ∈ e.orte := by
        simpa [Extraktion.stmtOrte] using ho
      exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')
  | .ret e hΛ =>
      intro h ho
      have h0 : (orteOk (D := D) e.orte) = true := h
      have ho' : o ∈ e.orte := by
        simpa [Extraktion.stmtOrte] using ho
      exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')
  | .transition r hk m hm hl maske bits =>
      intro h ho
      have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.stmtOrte] using ho
      exact (List.not_mem_nil ho').elim
  | .advances m a h hs =>
      intro h ho
      have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.stmtOrte] using ho
      exact (List.not_mem_nil ho').elim
  | .retires m s h a =>
      intro h ho
      have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.stmtOrte] using ho
      exact (List.not_mem_nil ho').elim
  | .retGrund r hΛ =>
      intro h ho
      have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.stmtOrte] using ho
      exact (List.not_mem_nil ho').elim
  | .leave h =>
      intro h ho
      have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.stmtOrte] using ho
      exact (List.not_mem_nil ho').elim
  | .next h =>
      intro h ho
      have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.stmtOrte] using ho
      exact (List.not_mem_nil ho').elim
  | .onOption opt p a =>
      intro h ho
      have h0 : (orteOk (D := D) opt.orte && g001 p && g001 a) = true := h
      have ho' : o ∈ opt.orte ∨ o ∈ Extraktion.blockOrte p ∨ o ∈ Extraktion.blockOrte a := by
        simpa [Extraktion.stmtOrte] using ho
      have h1 : ((orteOk (D := D) opt.orte && g001 p) = true) ∧ ((g001 a) = true) :=
        Bool.and_eq_true_iff.mp h0
      have h2 : ((orteOk (D := D) opt.orte) = true) ∧ ((g001 p) = true) :=
        Bool.and_eq_true_iff.mp h1.1
      rcases ho' with ho' | ho' | ho'
      · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h2.1 o ho')
      · exact g001_korrekt p h2.2 o ho'
      · exact g001_korrekt a h1.2 o ho'
  | .onTag v arms =>
      intro h ho
      have h0 : (orteOk (D := D) v.orte && g001Arms arms) = true := h
      have ho' : o ∈ v.orte ∨ o ∈ Extraktion.armsOrte arms := by
        simpa [Extraktion.stmtOrte] using ho
      have h1 : ((orteOk (D := D) v.orte) = true) ∧ ((g001Arms arms) = true) :=
        Bool.and_eq_true_iff.mp h0
      rcases ho' with ho' | ho'
      · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho')
      · exact g001Arms_korrekt arms h1.2 o ho'
  | .onGrund r arms =>
      intro h ho
      have h0 : (orteOk (D := D) r.orte && g001Grund arms) = true := h
      have ho' : o ∈ r.orte ∨ o ∈ Extraktion.grundArmsOrte arms := by
        simpa [Extraktion.stmtOrte] using ho
      have h1 : ((orteOk (D := D) r.orte) = true) ∧ ((g001Grund arms) = true) :=
        Bool.and_eq_true_iff.mp h0
      rcases ho' with ho' | ho'
      · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho')
      · exact g001Grund_korrekt arms h1.2 o ho'
  | .locks L hr body =>
      intro h ho
      have h0 : (g001 body) = true := h
      have ho' : o ∈ Extraktion.blockOrte body := by
        simpa [Extraktion.stmtOrte] using ho
      exact g001_korrekt body h0 o ho'
  | .breaking i body =>
      intro h ho
      have h0 : (g001 body) = true := h
      have ho' : o ∈ Extraktion.blockOrte body := by
        simpa [Extraktion.stmtOrte] using ho
      exact g001_korrekt body h0 o ho'
  | .traverse t inv body =>
      intro h ho
      have h0 : (orteOk (D := D) inv.orte && g001 body) = true := h
      have ho' : o ∈ inv.orte ∨ o ∈ Extraktion.blockOrte body := by
        simpa [Extraktion.stmtOrte] using ho
      have h1 : ((orteOk (D := D) inv.orte) = true) ∧ ((g001 body) = true) :=
        Bool.and_eq_true_iff.mp h0
      rcases ho' with ho' | ho'
      · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho')
      · exact g001_korrekt body h1.2 o ho'
  | .retry n bis body ueber =>
      intro h ho
      have h0 : (orteOk (D := D) bis.orte && g001 body && g001 ueber) = true := h
      have ho' : o ∈ bis.orte ∨ o ∈ Extraktion.blockOrte body ∨ o ∈ Extraktion.blockOrte ueber := by
        simpa [Extraktion.stmtOrte] using ho
      have h1 : ((orteOk (D := D) bis.orte && g001 body) = true) ∧ ((g001 ueber) = true) :=
        Bool.and_eq_true_iff.mp h0
      have h2 : ((orteOk (D := D) bis.orte) = true) ∧ ((g001 body) = true) :=
        Bool.and_eq_true_iff.mp h1.1
      rcases ho' with ho' | ho' | ho'
      · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h2.1 o ho')
      · exact g001_korrekt body h2.2 o ho'
      · exact g001_korrekt ueber h1.2 o ho'
  | .forever a inv body =>
      intro h ho
      have h0 : (orteOk (D := D) inv.orte && g001 body) = true := h
      have ho' : o ∈ inv.orte ∨ o ∈ Extraktion.blockOrte body := by
        simpa [Extraktion.stmtOrte] using ho
      have h1 : ((orteOk (D := D) inv.orte) = true) ∧ ((g001 body) = true) :=
        Bool.and_eq_true_iff.mp h0
      rcases ho' with ho' | ho'
      · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho')
      · exact g001_korrekt body h1.2 o ho'

termination_by structural s

/-- Soundness for blocks. The `htStmt` premise is statement soundness;
    `htEnd` is end-block soundness. Every premise fires: `h`/`ho` fix the
    decision and the member, `htStmt`/`htEnd` discharge the sub-body legs. -/
theorem g001_korrekt {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ') (h : g001 b = true)
    (o : D.Tab ⊕ D.Glob) (ho : o ∈ Extraktion.blockOrte b) :
    ¬ istGeist (D := D) o := by
  revert h ho
  match b with
  | .nil =>
      intro h ho
      have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.blockOrte] using ho
      exact (List.not_mem_nil ho').elim
  | .cons s rest =>
      intro h ho
      have h0 : (g001Stmt s && g001 rest) = true := h
      have ho' : o ∈ Extraktion.stmtOrte s ∨ o ∈ Extraktion.blockOrte rest := by
        simpa [Extraktion.blockOrte] using ho
      have h1 : ((g001Stmt s) = true) ∧ ((g001 rest) = true) :=
        Bool.and_eq_true_iff.mp h0
      rcases ho' with ho' | ho'
      · exact g001Stmt_korrekt s h1.1 o ho'
      · exact g001_korrekt rest h1.2 o ho'
  | .bind e rest =>
      intro h ho
      have h0 : (orteOk (D := D) e.orte && g001 rest) = true := h
      have ho' : o ∈ e.orte ∨ o ∈ Extraktion.blockOrte rest := by
        simpa [Extraktion.blockOrte] using ho
      have h1 : ((orteOk (D := D) e.orte) = true) ∧ ((g001 rest) = true) :=
        Bool.and_eq_true_iff.mp h0
      rcases ho' with ho' | ho'
      · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho')
      · exact g001_korrekt rest h1.2 o ho'
  | .bindCall f args he hp hr rest =>
      intro h ho
      have h0 : (orteOk (D := D) args.orte && g001 rest) = true := h
      have ho' : o ∈ args.orte ∨ o ∈ Extraktion.blockOrte rest := by
        simpa [Extraktion.blockOrte] using ho
      have h1 : ((orteOk (D := D) args.orte) = true) ∧ ((g001 rest) = true) :=
        Bool.and_eq_true_iff.mp h0
      rcases ho' with ho' | ho'
      · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho')
      · exact g001_korrekt rest h1.2 o ho'
  | .bindCallInd p args he hp hr rest =>
      intro h ho
      have h0 : (orteOk (D := D) (p.orte ++ args.orte) && g001 rest) = true := h
      have ho2 : o ∈ p.orte ∨ o ∈ args.orte ∨ o ∈ Extraktion.blockOrte rest := by
        simpa [Extraktion.blockOrte] using ho
      have ho' : (o ∈ p.orte ∨ o ∈ args.orte) ∨ o ∈ Extraktion.blockOrte rest := by
        rcases ho2 with ho2 | ho2 | ho2
        · exact Or.inl (Or.inl ho2)
        · exact Or.inl (Or.inr ho2)
        · exact Or.inr ho2
      have h1 : ((orteOk (D := D) (p.orte ++ args.orte)) = true) ∧ ((g001 rest) = true) :=
        Bool.and_eq_true_iff.mp h0
      rcases ho' with ho' | ho'
      · have ho2 : o ∈ p.orte ++ args.orte := by
          simpa [List.mem_append] using ho'
        exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho2)
      · exact g001_korrekt rest h1.2 o ho'
  | .bindCallElse f args he hp hr err rest =>
      intro h ho
      have h0 : (orteOk (D := D) args.orte && g001End err && g001 rest) = true := h
      have ho' : o ∈ args.orte ∨ o ∈ Extraktion.endblockOrte err ∨ o ∈ Extraktion.blockOrte rest := by
        simpa [Extraktion.blockOrte] using ho
      have h1 : ((orteOk (D := D) args.orte && g001End err) = true) ∧ ((g001 rest) = true) :=
        Bool.and_eq_true_iff.mp h0
      have h2 : ((orteOk (D := D) args.orte) = true) ∧ ((g001End err) = true) :=
        Bool.and_eq_true_iff.mp h1.1
      rcases ho' with ho' | ho' | ho'
      · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h2.1 o ho')
      · exact g001End_korrekt err h2.2 o ho'
      · exact g001_korrekt rest h1.2 o ho'
  | .bindAxiom a args he hw hg hd hgd rest =>
      intro h ho
      have h0 : (orteOk (D := D) args.orte && g001 rest) = true := h
      have ho' : o ∈ args.orte ∨ o ∈ Extraktion.blockOrte rest := by
        simpa [Extraktion.blockOrte] using ho
      have h1 : ((orteOk (D := D) args.orte) = true) ∧ ((g001 rest) = true) :=
        Bool.and_eq_true_iff.mp h0
      rcases ho' with ho' | ho'
      · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho')
      · exact g001_korrekt rest h1.2 o ho'
  | .regLies r hk rest =>
      intro h ho
      have h0 : (g001 rest) = true := h
      have ho' : o ∈ Extraktion.blockOrte rest := by
        simpa [Extraktion.blockOrte] using ho
      exact g001_korrekt rest h0 o ho'
  | .regLiesElse r hk zusage sonst rest =>
      intro h ho
      have h0 : (orteOk (D := D) zusage.orte && g001End sonst && g001 rest) = true := h
      have ho' : o ∈ zusage.orte ∨ o ∈ Extraktion.endblockOrte sonst ∨ o ∈ Extraktion.blockOrte rest := by
        simpa [Extraktion.blockOrte] using ho
      have h1 : ((orteOk (D := D) zusage.orte && g001End sonst) = true) ∧ ((g001 rest) = true) :=
        Bool.and_eq_true_iff.mp h0
      have h2 : ((orteOk (D := D) zusage.orte) = true) ∧ ((g001End sonst) = true) :=
        Bool.and_eq_true_iff.mp h1.1
      rcases ho' with ho' | ho' | ho'
      · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h2.1 o ho')
      · exact g001End_korrekt sonst h2.2 o ho'
      · exact g001_korrekt rest h1.2 o ho'
  | .awaits g payload hp hL rest =>
      intro h ho
      have h0 : (orteOk (D := D) [Sum.inr g] && g001 rest) = true := h
      have ho' : o = Sum.inr g ∨ o ∈ ([] : List (D.Tab ⊕ D.Glob)) ∨ o ∈ Extraktion.blockOrte rest := by
        simpa [Extraktion.blockOrte] using ho
      have h1 : ((orteOk (D := D) [Sum.inr g]) = true) ∧ ((g001 rest) = true) :=
        Bool.and_eq_true_iff.mp h0
      rcases ho' with rfl | ho' | ho'
      · simp only [orteOk, List.all_eq_true, List.mem_singleton] at h1
        have hg' := h1.1 _ rfl
        simp at hg'
        exact nge_of_eq_false hg'
      · exact (List.not_mem_nil ho').elim
      · exact g001_korrekt rest h1.2 o ho'
  | .exchange g neu hw hL rest =>
      intro h ho
      have h0 : (orteOk (D := D) ([Sum.inr g] ++ neu.orte) && g001 rest) = true := h
      have ho2 : o = Sum.inr g ∨ o ∈ neu.orte ∨ o ∈ Extraktion.blockOrte rest := by
        simpa [Extraktion.blockOrte] using ho
      have ho' : (o = Sum.inr g ∨ o ∈ neu.orte) ∨ o ∈ Extraktion.blockOrte rest := by
        rcases ho2 with ho2 | ho2 | ho2
        · exact Or.inl (Or.inl ho2)
        · exact Or.inl (Or.inr ho2)
        · exact Or.inr ho2
      have h1 : ((orteOk (D := D) ([Sum.inr g] ++ neu.orte)) = true) ∧ ((g001 rest) = true) :=
        Bool.and_eq_true_iff.mp h0
      rcases ho' with ho' | ho'
      · have ho2 : o ∈ ([Sum.inr g] ++ neu.orte) := by
          simpa [List.mem_append] using ho'
        exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho2)
      · exact g001_korrekt rest h1.2 o ho'
  | .narrow e lo' hi' sonst rest =>
      intro h ho
      have h0 : (orteOk (D := D) e.orte && g001End sonst && g001 rest) = true := h
      have ho' : o ∈ e.orte ∨ o ∈ Extraktion.endblockOrte sonst ∨ o ∈ Extraktion.blockOrte rest := by
        simpa [Extraktion.blockOrte] using ho
      have h1 : ((orteOk (D := D) e.orte && g001End sonst) = true) ∧ ((g001 rest) = true) :=
        Bool.and_eq_true_iff.mp h0
      have h2 : ((orteOk (D := D) e.orte) = true) ∧ ((g001End sonst) = true) :=
        Bool.and_eq_true_iff.mp h1.1
      rcases ho' with ho' | ho' | ho'
      · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h2.1 o ho')
      · exact g001End_korrekt sonst h2.2 o ho'
      · exact g001_korrekt rest h1.2 o ho'
  | .pruefung c sonst rest =>
      intro h ho
      have h0 : (orteOk (D := D) c.orte && g001End sonst && g001 rest) = true := h
      have ho' : o ∈ c.orte ∨ o ∈ Extraktion.endblockOrte sonst ∨ o ∈ Extraktion.blockOrte rest := by
        simpa [Extraktion.blockOrte] using ho
      have h1 : ((orteOk (D := D) c.orte && g001End sonst) = true) ∧ ((g001 rest) = true) :=
        Bool.and_eq_true_iff.mp h0
      have h2 : ((orteOk (D := D) c.orte) = true) ∧ ((g001End sonst) = true) :=
        Bool.and_eq_true_iff.mp h1.1
      rcases ho' with ho' | ho' | ho'
      · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h2.1 o ho')
      · exact g001End_korrekt sonst h2.2 o ho'
      · exact g001_korrekt rest h1.2 o ho'
  | .gleit op a b lo hi rest =>
      intro h ho
      have h0 : (orteOk (D := D) (a.orte ++ b.orte) && g001 rest) = true := h
      have ho2 : o ∈ a.orte ∨ o ∈ b.orte ∨ o ∈ Extraktion.blockOrte rest := by
        simpa [Extraktion.blockOrte] using ho
      have ho' : (o ∈ a.orte ∨ o ∈ b.orte) ∨ o ∈ Extraktion.blockOrte rest := by
        rcases ho2 with ho2 | ho2 | ho2
        · exact Or.inl (Or.inl ho2)
        · exact Or.inl (Or.inr ho2)
        · exact Or.inr ho2
      have h1 : ((orteOk (D := D) (a.orte ++ b.orte)) = true) ∧ ((g001 rest) = true) :=
        Bool.and_eq_true_iff.mp h0
      rcases ho' with ho' | ho'
      · have ho2 : o ∈ a.orte ++ b.orte := by
          simpa [List.mem_append] using ho'
        exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho2)
      · exact g001_korrekt rest h1.2 o ho'
  | .gleitLit q lo hi rest =>
      intro h ho
      have h0 : (g001 rest) = true := h
      have ho' : o ∈ Extraktion.blockOrte rest := by
        simpa [Extraktion.blockOrte] using ho
      exact g001_korrekt rest h0 o ho'
  | .gleitVon e lo hi rest =>
      intro h ho
      have h0 : (orteOk (D := D) e.orte && g001 rest) = true := h
      have ho' : o ∈ e.orte ∨ o ∈ Extraktion.blockOrte rest := by
        simpa [Extraktion.blockOrte] using ho
      have h1 : ((orteOk (D := D) e.orte) = true) ∧ ((g001 rest) = true) :=
        Bool.and_eq_true_iff.mp h0
      rcases ho' with ho' | ho'
      · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho')
      · exact g001_korrekt rest h1.2 o ho'
  | .gleitNarrow e lo hi sonst rest =>
      intro h ho
      have h0 : (orteOk (D := D) e.orte && g001End sonst && g001 rest) = true := h
      have ho' : o ∈ e.orte ∨ o ∈ Extraktion.endblockOrte sonst ∨ o ∈ Extraktion.blockOrte rest := by
        simpa [Extraktion.blockOrte] using ho
      have h1 : ((orteOk (D := D) e.orte && g001End sonst) = true) ∧ ((g001 rest) = true) :=
        Bool.and_eq_true_iff.mp h0
      have h2 : ((orteOk (D := D) e.orte) = true) ∧ ((g001End sonst) = true) :=
        Bool.and_eq_true_iff.mp h1.1
      rcases ho' with ho' | ho' | ho'
      · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h2.1 o ho')
      · exact g001End_korrekt sonst h2.2 o ho'
      · exact g001_korrekt rest h1.2 o ho'

termination_by structural b

/-- Soundness for case arms. Every premise fires: `h`/`ho` fix the decision
    and the member, `htStmt`/`htEnd`/`htBlockSelf` discharge the legs. -/
theorem g001Arms_korrekt {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))}
    (a : Arms D V l Γ Λ Λ' cs) (h : g001Arms a = true)
    (o : D.Tab ⊕ D.Glob) (ho : o ∈ Extraktion.armsOrte a) :
    ¬ istGeist (D := D) o := by
  revert h ho
  match a with
  | .nil =>
      intro h ho
      have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.armsOrte] using ho
      exact (List.not_mem_nil ho').elim
  | .cons b rest =>
      intro h ho
      have h0 : (g001 b && g001Arms rest) = true := h
      have ho0 : o ∈ Extraktion.blockOrte b ++ Extraktion.armsOrte rest := by
        simpa [Extraktion.armsOrte] using ho
      have h1 : ((g001 b) = true) ∧ ((g001Arms rest) = true) :=
        Bool.and_eq_true_iff.mp h0
      have ho' : o ∈ Extraktion.blockOrte b ∨ o ∈ Extraktion.armsOrte rest :=
        List.mem_append.mp ho0
      rcases ho' with ho' | ho'
      · exact g001_korrekt b h1.1 o ho'
      · exact g001Arms_korrekt rest h1.2 o ho'

termination_by structural a

/-- Soundness for reason arms. Every premise fires: `h`/`ho` fix the
    decision and the member. -/
theorem g001Grund_korrekt {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat}
    (a : GrundArms D V l Γ Λ Λ' n) (h : g001Grund a = true)
    (o : D.Tab ⊕ D.Glob) (ho : o ∈ Extraktion.grundArmsOrte a) :
    ¬ istGeist (D := D) o := by
  revert h ho
  match a with
  | .nil =>
      intro h ho
      have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.grundArmsOrte] using ho
      exact (List.not_mem_nil ho').elim
  | .cons b rest =>
      intro h ho
      have h0 : (g001 b && g001Grund rest) = true := h
      have ho0 : o ∈ Extraktion.blockOrte b ++ Extraktion.grundArmsOrte rest := by
        simpa [Extraktion.grundArmsOrte] using ho
      have h1 : ((g001 b) = true) ∧ ((g001Grund rest) = true) :=
        Bool.and_eq_true_iff.mp h0
      have ho' : o ∈ Extraktion.blockOrte b ∨ o ∈ Extraktion.grundArmsOrte rest :=
        List.mem_append.mp ho0
      rcases ho' with ho' | ho'
      · exact g001_korrekt b h1.1 o ho'
      · exact g001Grund_korrekt rest h1.2 o ho'

termination_by structural a

/-- The checker's decision is sound: a body with `g001End b = true` reads no
    ghost carrier. The `h` premise is the acceptance fact; `ho` fixes the
    footprint member inspected. -/
theorem g001End_korrekt {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (b : Endblock D V l Γ Λ) (h : g001End b = true)
    (o : D.Tab ⊕ D.Glob) (ho : o ∈ Extraktion.endblockOrte b) :
    ¬ istGeist (D := D) o := by
  revert h ho
  match b with
  | .ret e _ =>
      intro h ho
      have h0 : (orteOk (D := D) e.orte) = true := h
      have ho' : o ∈ e.orte := by
        simpa [Extraktion.endblockOrte] using ho
      exact nge_of_eq_false (orteOk_korrekt (D := D) _ h0 o ho')
  | .retGrund _ _ =>
      intro h ho
      have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.endblockOrte] using ho
      exact (List.not_mem_nil ho').elim
  | .leave _ =>
      intro h ho
      have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.endblockOrte] using ho
      exact (List.not_mem_nil ho').elim
  | .next _ =>
      intro h ho
      have ho' : o ∈ ([] : List (D.Tab ⊕ D.Glob)) := by simpa [Extraktion.endblockOrte] using ho
      exact (List.not_mem_nil ho').elim
  | .cons s rest =>
      intro h ho
      have h0 : (g001Stmt s && g001End rest) = true := h
      have ho' : o ∈ Extraktion.stmtOrte s ∨ o ∈ Extraktion.endblockOrte rest := by
        simpa [Extraktion.endblockOrte] using ho
      have h1 : ((g001Stmt s) = true) ∧ ((g001End rest) = true) :=
        Bool.and_eq_true_iff.mp h0
      rcases ho' with ho' | ho'
      · exact g001Stmt_korrekt s h1.1 o ho'
      · exact g001End_korrekt rest h1.2 o ho'
  | .bind e rest =>
      intro h ho
      have h0 : (orteOk (D := D) e.orte && g001End rest) = true := h
      have ho' : o ∈ e.orte ∨ o ∈ Extraktion.endblockOrte rest := by
        simpa [Extraktion.endblockOrte] using ho
      have h1 : ((orteOk (D := D) e.orte) = true) ∧ ((g001End rest) = true) :=
        Bool.and_eq_true_iff.mp h0
      rcases ho' with ho' | ho'
      · exact nge_of_eq_false (orteOk_korrekt (D := D) _ h1.1 o ho')
      · exact g001End_korrekt rest h1.2 o ho'

termination_by structural b

end

/-! ## Erasure: ghost-free reads evaluate equal off-ghost.

    The reason ghosts may be omitted by the emitter: an expression whose
    read footprint is ghost-free cannot observe ghost carriers, so two
    worlds that agree on every non-ghost carrier give the same value. This
    reuses the footprint keystone `Extraktion.eval_liest_orte` (section 19
    R1) by qualified name -- the ghost-freedom hypothesis discharges exactly
    the per-side agreements the keystone consumes. -/

/-- Erasure at expressions: an expression whose footprint is ghost-free
    evaluates to the same value in two worlds that agree off-ghost. The
    `he` premise is the ghost-freedom of this footprint; `hS`/`hG` fix the
    present-world agreements, `h0S`/`h0G` the entry-world agreements (for
    `old(..)`), each consumed once per side. -/
theorem eval_gleich_ausser_geist {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ)
    (he : orteOhneGeist (D := D) e.orte)
    (σ₀ σ₀' σ σ' : World D) (ρ : Env D Γ)
    (hS : ∀ t : D.Tab, D.geist t = false → ∀ k f, σ.slots t k f = σ'.slots t k f)
    (hG : ∀ g : D.Glob, D.ggeist g = false → σ.globs g = σ'.globs g)
    (h0S : ∀ t : D.Tab, D.geist t = false → ∀ k f, σ₀.slots t k f = σ₀'.slots t k f)
    (h0G : ∀ g : D.Glob, D.ggeist g = false → σ₀.globs g = σ₀'.globs g) :
    eval σ₀ e σ ρ = eval σ₀' e σ' ρ := by
  apply Extraktion.eval_liest_orte e σ₀ σ₀' σ σ' ρ
  · intro t ht k f
    exact hS t (he _ ht) k f
  · intro g hg
    exact hG g (he _ hg)
  · intro t ht k f
    exact h0S t (he _ ht) k f
  · intro g hg
    exact h0G g (he _ hg)

/-- `assignVar` reads only its bound expression: the step's footprint is
    the footprint of `e`. The `hm` premise fixes the member inspected; the
    conclusion restates it at the statement footprint. -/
theorem assignVar_orte_mem (V : Vertrag D) (l : Bool)
    {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (x : Var Γ τ) (e : Expr D Γ Λ τ)
    (o : D.Tab ⊕ D.Glob) (hm : o ∈ e.orte) :
    o ∈ Extraktion.stmtOrte (Stmt.assignVar (V := V) (l := l) x e) := by
  have hdef : Extraktion.stmtOrte (Stmt.assignVar (V := V) (l := l) x e)
      = e.orte := rfl
  rw [hdef]
  exact hm

/-- Erasure at `assignVar`: the bound value is ghost-independent when the
    step footprint is. The `he` premise is the ghost-freedom at the
    statement footprint (folded to the expression via `assignVar_orte_mem`,
    which this proof consumes); `hS`/`hG`/`h0S`/`h0G` are the off-ghost
    agreements. -/
theorem assignVar_eval_gleich (V : Vertrag D) (l : Bool)
    {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (x : Var Γ τ) (e : Expr D Γ Λ τ)
    (he : orteOhneGeist (D := D)
      (Extraktion.stmtOrte (Stmt.assignVar (V := V) (l := l) x e)))
    (σ₀ σ σ' : World D) (ρ : Env D Γ)
    (hS : ∀ t : D.Tab, D.geist t = false → ∀ k f, σ.slots t k f = σ'.slots t k f)
    (hG : ∀ g : D.Glob, D.ggeist g = false → σ.globs g = σ'.globs g)
    (h0S : ∀ t : D.Tab, D.geist t = false → ∀ k f, σ₀.slots t k f = σ₀.slots t k f)
    (h0G : ∀ g : D.Glob, D.ggeist g = false → σ₀.globs g = σ₀.globs g) :
    eval σ₀ e σ ρ = eval σ₀ e σ' ρ := by
  have he' : orteOhneGeist (D := D) e.orte :=
    fun o ho => he o (assignVar_orte_mem V l x e o ho)
  exact eval_gleich_ausser_geist e he' σ₀ σ₀ σ σ' ρ hS hG h0S h0G

/-! ## Witness: one ordinary table, one ghost table.

    `GD`: two tables over `Bool`. `true` is ordinary (written by the body);
    `false` is ghost (named by the contract, never read by the body). -/

namespace Zeuge

/-- Two tables: `true` ordinary, `false` ghost (the only non-default field;
    every other literal compiles unchanged thanks to the defaults). -/
def GD : Deklaration where
  Tab := Bool
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .bool
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some true | 1 => some false | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ =>
    { params := []
      erg := none
      gruende := 0
      haelt := []
      schreibt := fun | true => true | false => false
      gschreibt := fun e => nomatch e
      konsumiert := []
      produziert := [] }
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e
  geist := fun | true => false | false => true
  ggeist := fun e => Empty.elim e

/-- The ordinary table is not ghost. -/
theorem GD_ordentlich : GD.geist true = false := rfl

/-- The second table is ghost. -/
theorem GD_geist : GD.geist false = true := rfl

/-- The contract of the only function: no parameters, no result. -/
def GV : Vertrag GD :=
  { schreibt := fun | true => true | false => false
    gschreibt := fun e => nomatch e
    erg := none
    gruende := 0
    haelt := []
    produziert := [] }

/-- Index `0` into either table (both have `count 1`). -/
def gi (t : GD.Tab) : Expr GD [] [] (.index (GD.count t)) :=
  .weiter (by cases t <;> decide) (by cases t <;> decide) (.lit 0)

/-- Slot read of either table as a boolean expression. -/
def gslot (t : GD.Tab) : Expr GD [] [] .bool :=
  .slot t () (gi t) (fun w => nomatch w)

/-- The witness statement: write the ordinary table from its own read. -/
def gstmt : Stmt GD GV false [] [] [] :=
  .assignSlot true () (gi true) (gslot true) rfl (fun w => nomatch w)

/-- The witness body as a block: the statement, then stop. Its footprint
    is the ordinary table only. -/
def gbody : Block GD GV false [] [] [] :=
  .cons gstmt .nil

/-- The decision accepts the witness body: every footprint member is real.
    Proved by `rfl` -- the checker computes it. -/
theorem gbody_g001 : g001 (D := GD) gbody = true := rfl

/-- Joint witness for `g001_korrekt`: all premises instantiated at the
    non-degenerate program `GD` (one ordinary table the body reads, one
    ghost table the contract names below). The `ho` premise fixes the
    footprint member inspected. -/
theorem g001_korrekt_zeuge
    (o : GD.Tab ⊕ GD.Glob) (ho : o ∈ Extraktion.blockOrte (D := GD) gbody) :
    ¬ istGeist (D := GD) o :=
  g001_korrekt gbody gbody_g001 o ho

/-- The witness body as a non-falling block: the statement, then return.
    Feeds the witness program `GP` below. -/
def gendbody : Endblock GD GV false [] [] :=
  .cons gstmt (.ret .keine (List.Perm.refl []))

/-- `ensures` over the ghost slot: the ghost value the body never reads. -/
def GPost : Expr GD (ErgCtx (GD.params ()) (GD.erg ())) (vertragVon GD ()).ende .bool :=
  .slot false () (.weiter (by decide) (by decide) (.lit 0)) (fun w => nomatch w)

/-- The witness program: `requires` true, `ensures` over the ghost slot,
    body `gendbody` which writes the ordinary table and reads no ghost. -/
def GP : Programm GD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => GPost
  rumpf := fun _ => gendbody

/-- The witness `ensures` reads the ghost table: the contract side may name
    ghost carriers. The `ho` premise fixes the footprint member inspected. -/
theorem gpost_liest_geist (o : GD.Tab ⊕ GD.Glob) (ho : o ∈ GPost.orte) :
    o = (.inl false : GD.Tab ⊕ GD.Glob) := by
  simp only [GPost, Expr.orte, List.mem_singleton] at ho
  exact ho

/-- The witness oracle: no axioms, no registers, no globals. -/
def GO : Orakel GD where
  wirkt := fun a _ _ => nomatch a
  regLies := fun r _ => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g _ => nomatch g

/-- A witness world: ordinary slot `b`, ghost slot `c`, trace `tr`. -/
def gwelt (b c : Bool) (tr : List (Ereignis GD)) : World GD :=
  { slots := fun | true, _, _ => b | false, _, _ => c
    globs := fun g => nomatch g
    spur := tr }

/-- The witness write step moves the world: firing the witness statement
    from `gwelt b c []` reaches a world whose ordinary slot is `b`
    and whose trace records the write. The `hstep` premise is the firing,
    `hb`/`hc` fix the incoming slot values. -/
theorem gschritt_schreibt (b c : Bool) (s' : World GD)
    (hb : (gwelt b c []).slots true 0 () = b)
    (hc : (gwelt b c []).slots false 0 () = c)
    (hstep : (execStmt GO 0 keinRuf
      (.assignSlot true () (gi true) (gslot true) rfl (fun w => nomatch w) :
        Stmt GD GV false [] [] []) (gwelt b c []) Env.nil).welt = some s') :
    s'.slots true 0 () = b ∧ s'.slots false 0 () = c := by
  -- `hc` fixes the ghost value the conclusion restates; `hghost` below
  -- consumes it through the definitional ride-along.
  have hcg : (gwelt b c []).slots false 0 () = c := hc
  have h := (schreibt_wirkt_slot (D := GD) GO 0 GV false [] []
    true () (gi true) (gslot true) rfl (fun w => nomatch w)
    (gwelt b c []) Env.nil).1
  rw [h] at hstep
  have hidx : (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
      (gi true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
      Env.nil).n = 0 := rfl
  have hval : eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
      (gslot true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
      Env.nil = b := by
    have hlese : ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).slots
        true = (gwelt b c []).slots true := rfl
    show ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).slots true 0 () = b
    rw [hlese]
    exact hb
  -- `hstep` fixes the outcome world, `hidx` the written index, `hval` the
  -- written value, `hb` the incoming ordinary value, `hc` the ghost value.
  have hsym : s' = (((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).schreibSlot
      true [] _ () _) := Option.some_inj.mp hstep.symm
  have hmem : ((((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).storeSlot
      true
      (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
        (gi true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
        Env.nil).n ()
      (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
        (gslot true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
        Env.nil)).merke
      [Ereignis.zugriff true true []
        ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).haelt]).slots
      true 0 () = b := by
    have hhit := storeSlot_hit
      ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
      true
      (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
        (gi true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
        Env.nil).n ()
      (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
        (gslot true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
        Env.nil)
    rw [hidx] at hhit
    have hhit2 : (((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).storeSlot
        true 0 ()
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gslot true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil)).slots true 0 () = b := by
      rw [hhit]
      exact hval
    -- `World.merke` rewrites only the trace field; slots see through it.
    have hsee : ((((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).storeSlot
        true
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gi true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil).n ()
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gslot true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil)).merke
        [Ereignis.zugriff true true []
          ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).haelt]).slots
        true 0 () =
      (((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).storeSlot
        true
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gi true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil).n ()
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gslot true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil)).slots true 0 () := rfl
    have hhit3 : ((((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).storeSlot
        true
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gi true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil).n ()
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gslot true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil)).merke
        [Ereignis.zugriff true true []
          ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).haelt]).slots
        true 0 () = b := by
      rw [hsee]
      exact hhit2
    exact hhit3
  have hghost : s'.slots false 0 () = c := by
    rw [hsym]
    -- The ghost slot is untouched by the ordinary write: definitionally `c`.
    have hg : ((((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).storeSlot
        true
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gi true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil).n ()
        (eval ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          (gslot true) ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte))
          Env.nil)).merke
        [Ereignis.zugriff true true []
          ((gwelt b c []).lese [] ((gi true).orte ++ (gslot true).orte)).haelt]).slots
        false 0 () = c := hcg
    exact hg
  exact ⟨hsym ▸ hmem, hghost⟩

/-- The witness read is ghost-free: its footprint names only the ordinary
    table. -/
theorem gslot_ohne_geist : orteOhneGeist (D := GD) (gslot true).orte := by
  intro o ho
  simp only [gslot, gi, Expr.orte, List.mem_singleton] at ho
  subst ho
  rfl

/-- The off-ghost agreement holds for the witness worlds: they share every
    non-ghost slot. The `ht` premise fixes the non-ghost table; `k`/`f` the
    slot inspected. -/
theorem gwelt_gleicht (b c c' : Bool) (t : GD.Tab) (ht : GD.geist t = false)
    (k : Int) (f : GD.Feld t) :
    (gwelt b c []).slots t k f = (gwelt b c' []).slots t k f := by
  cases ht' : t with
  | true => rfl
  | false =>
      -- `t = false` is ghost (`GD_geist`), contradicting `ht`. The `ht`
      -- premise fires here through the rewrite.
      rw [ht'] at ht
      rw [GD_geist] at ht
      exact absurd ht (by decide)

/-- Witness for erasure: two worlds differing only on the ghost table agree
    on the witness read. All of `b`/`c`/`c'` appear in the conclusion. -/
theorem erasure_zeuge (b c c' : Bool) :
    eval (gwelt b c []) (gslot true) (gwelt b c []) Env.nil =
      eval (gwelt b c' []) (gslot true) (gwelt b c' []) Env.nil :=
  eval_gleich_ausser_geist (gslot true) gslot_ohne_geist
    (gwelt b c []) (gwelt b c' []) (gwelt b c []) (gwelt b c' []) Env.nil
    (fun t ht k f => gwelt_gleicht b c c' t ht k f)
    (fun g hg => nomatch g)
    (fun t ht k f => gwelt_gleicht b c c' t ht k f)
    (fun g hg => nomatch g)

end Zeuge

/-
CUTS:
* No emitter-omission theorem: `Geist.lean` proves the read side (an
  accepted body names no ghost carrier) and erasure (ghost-free reads
  evaluate equal off-ghost); that omitting ghost tables preserves emitted
  behavior is not stated -- emission lives in `crates/`, not here.
* `gschritt_schreibt` fires the witness write in place (`T[true] :=
  T[true]` keeps the value `b`); the trace records the write event, but no
  slot VALUE change is exhibited. A value-flipping witness (negation write)
  would show a memory-changing step in the stronger value sense.
* `assignVar_eval_gleich` lifts erasure to one statement form only
  (`assignVar`); the remaining statement forms are not lifted.
-/

#print axioms Gabbro.Grammatik.Geist.g001_korrekt
#print axioms Gabbro.Grammatik.Geist.Zeuge.g001_korrekt_zeuge
#print axioms Gabbro.Grammatik.Geist.geist_leer_unveraendert
#print axioms Gabbro.Grammatik.Geist.eval_gleich_ausser_geist
#print axioms Gabbro.Grammatik.Geist.Zeuge.erasure_zeuge
#print axioms Gabbro.Grammatik.Geist.Zeuge.gschritt_schreibt

end Gabbro.Grammatik.Geist
