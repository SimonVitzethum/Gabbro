/-
  File:      Grammatik/Geist.lean
  Subject:   GHOST CARRIERS (syscall lane S3) -- spec-only tables and globals.

  A ghost carrier is ordinary memory for the semantics (every theorem stays
  valid) and absent for the emitter. Rule G001: executable code reads no
  ghost. Ghost tables may appear only in contracts (`requires`/`ensures`).
-/
module
public import Grammatik.Kern.Syntax.Extraktion
public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Kern.Semantik.Maschine
@[expose] public section


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
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hpoint
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
  | .assignThru p _ _ _ i e _ _ => orteOk (D := D) (p.orte ++ i.orte ++ e.orte)
  | .assignThruOwn p _ _ _ i e _ _ _ _ _ _ _ => orteOk (D := D) (p.orte ++ i.orte ++ e.orte)
  | .assignSlotRef r _ _ _ _ e _ _ => orteOk (D := D) (r.orte ++ e.orte)
  | .assignGlob _ e _ _ => orteOk (D := D) e.orte
  | .putBytes _ _ _ _ i _ _ e _ _ => orteOk (D := D) (i.orte ++ e.orte)
  | .assignVar _ e => orteOk (D := D) e.orte
  | .shift _ _ _ i _ _ _ _ _ _ => orteOk (D := D) i.orte
  | .ite c t e => orteOk (D := D) c.orte && g001 t && g001 e
  | .onOption o p a => orteOk (D := D) o.orte && g001 p && g001 a
  | .onTag v arms => orteOk (D := D) v.orte && g001Arms arms
  | .onWhy r arms => orteOk (D := D) r.orte && g001Grund arms
  | .call _ args _ _ => orteOk (D := D) args.orte
  | .callInd p args _ _ => orteOk (D := D) (p.orte ++ args.orte)
  | .callIndElse p args _ _ _ err => orteOk (D := D) (p.orte ++ args.orte) && g001End err
  | .locks _ _ body => g001 body
  | .breaking _ body => g001 body
  | .traverse _ inv body => orteOk (D := D) inv.orte && g001 body
  | .consumeTraverse _ member edge inv _ mass body =>
      orteOk (D := D) (member.orte ++ edge.orte ++ inv.orte ++ mass.orte) && g001 body
  | .retScoped e _ => orteOk (D := D) e.orte
  | .retWhyScoped _ _ => true
  | .retry _ bis body ueber => orteOk (D := D) bis.orte && g001 body && g001 ueber
  | .forever _ inv body => orteOk (D := D) inv.orte && g001 body
  | .axiomCall _ args _ _ _ _ _ => orteOk (D := D) args.orte
  | .axiomCallElse _ _ args _ _ _ _ _ err =>
      orteOk (D := D) args.orte && g001End err
  | .regWrite _ _ e => orteOk (D := D) e.orte
  | .transition _ _ _ _ _ _ _ => true
  | .publish _ e _ _ _ _ => orteOk (D := D) e.orte
  | .advances _ _ _ _ => true
  | .retires _ _ _ _ => true
  | .ret e _ => orteOk (D := D) e.orte
  | .retWhy _ _ => true
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
  | .bindCallIndElse p args _ _ _ err rest =>
      orteOk (D := D) (p.orte ++ args.orte) && g001End err && g001 rest
  | .bindCallElse _ args _ _ _ err rest =>
      orteOk (D := D) args.orte && g001End err && g001 rest
  | .bindAxiom _ args _ _ _ _ _ rest => orteOk (D := D) args.orte && g001 rest
  | .bindAxiomElse _ args _ _ _ _ _ _ err rest =>
      orteOk (D := D) args.orte && g001End err && g001 rest
  | .bindAxiomOpt _ _ args _ _ _ _ rest => orteOk (D := D) args.orte && g001 rest
  | .bindAxiomOptElse _ _ args _ _ _ _ _ err rest =>
      orteOk (D := D) args.orte && g001End err && g001 rest
  | .regRead _ _ rest => g001 rest
  | .regReadElse _ _ zusage sonst rest =>
      orteOk (D := D) zusage.orte && g001End sonst && g001 rest
  | .awaits g _ _ _ _ rest => orteOk (D := D) [.inr g] && g001 rest
  | .exchange g neu _ _ rest =>
      orteOk (D := D) ([.inr g] ++ neu.orte) && g001 rest
  | .narrow e _ _ sonst rest =>
      orteOk (D := D) e.orte && g001End sonst && g001 rest
  | .narrowRequired e _ _ rest => orteOk (D := D) e.orte && g001 rest
  | .check c sonst rest =>
      orteOk (D := D) c.orte && g001End sonst && g001 rest
  | .float _ a b _ _ rest =>
      orteOk (D := D) (a.orte ++ b.orte) && g001 rest
  | .floatLit _ _ _ rest => g001 rest
  | .floatOf e _ _ rest => orteOk (D := D) e.orte && g001 rest
  | .floatNarrow e _ _ sonst rest =>
      orteOk (D := D) e.orte && g001End sonst && g001 rest

/-- The G001 check over a non-falling block: the form the checker runs on
    each function body. -/
def g001End : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} →
    Endblock D V l Γ Λ → Bool
  | _, _, _, .ret e _ => orteOk (D := D) e.orte
  | _, _, _, .retWhy _ _ => true
  | _, _, _, .retScoped e _ => orteOk (D := D) e.orte
  | _, _, _, .retWhyScoped _ _ => true
  | _, _, _, .leave _ => true
  | _, _, _, .next _ => true
  | _, _, _, .cons s rest => g001Stmt s && g001End rest
  | _, _, _, .bind e rest => orteOk (D := D) e.orte && g001End rest
  | _, _, _, .bindCall _ args _ _ _ rest => orteOk (D := D) args.orte && g001End rest
  | _, _, _, .bindCallElse _ args _ _ _ err rest =>
      orteOk (D := D) args.orte && g001End err && g001End rest
  | _, _, _, .bindAxiom _ args _ _ _ _ _ rest => orteOk (D := D) args.orte && g001End rest
  | _, _, _, .bindAxiomElse _ args _ _ _ _ _ _ err rest =>
      orteOk (D := D) args.orte && g001End err && g001End rest
  | _, _, _, .bindAxiomOpt _ _ args _ _ _ _ rest =>
      orteOk (D := D) args.orte && g001End rest
  | _, _, _, .bindAxiomOptElse _ _ args _ _ _ _ _ err rest =>
      orteOk (D := D) args.orte && g001End err && g001End rest
  | _, _, _, .regRead _ _ rest => g001End rest
  | _, _, _, .regReadElse _ _ zusage sonst rest =>
      orteOk (D := D) zusage.orte && g001End sonst && g001End rest
  | _, _, _, .awaits g _ _ _ _ rest => orteOk (D := D) [.inr g] && g001End rest
  | _, _, _, .bindCallInd p args _ _ _ rest =>
      orteOk (D := D) (p.orte ++ args.orte) && g001End rest
  | _, _, _, .bindCallIndElse p args _ _ _ err rest =>
      orteOk (D := D) (p.orte ++ args.orte) && g001End err && g001End rest
  | _, _, _, .narrow e _ _ sonst rest => orteOk (D := D) e.orte && g001End sonst && g001End rest
  | _, _, _, .narrowRequired e _ _ rest => orteOk (D := D) e.orte && g001End rest
  | _, _, _, .exchange g neu _ _ rest => orteOk (D := D) ([.inr g] ++ neu.orte) && g001End rest
  | _, _, _, .ite c t e => orteOk (D := D) c.orte && g001End t && g001End e

  | _, _, _, .float _ a b _ _ rest =>
      orteOk (D := D) (a.orte ++ b.orte) && g001End rest
  | _, _, _, .floatLit _ _ _ rest => g001End rest
  | _, _, _, .floatOf e _ _ rest => orteOk (D := D) e.orte && g001End rest
  | _, _, _, .floatNarrow e _ _ sonst rest =>
      orteOk (D := D) e.orte && g001End sonst && g001End rest
/-- The G001 check over case arms. -/
def g001Arms {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} :
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
end Gabbro.Grammatik.Geist
