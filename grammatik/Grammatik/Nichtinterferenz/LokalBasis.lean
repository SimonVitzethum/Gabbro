/-
  File:      Grammatik/Nichtinterferenz/Lokal.lean
  Subject:   THE FLOW CHECK OVER THE SYNTAX, AND THE LOCALITY OF ONE LEAF --
             `nS`/`nB`/`nE` (every read inside a carrier set `S`, every
             axiom admitted), the residue form `GRest.nR`, agreement of two
             worlds on a carrier set (`WRel`), the oracle condition
             (`OrakelTreu`), and the relational leaf lemma `blatt_rel`: a
             leaf whose reads lie in `S`, run in two worlds that agree on
             `T ⊇ S` (and on the trace), ends in two outcomes of the same
             shape, with equal environments and values, equal traces and
             memories that agree on `T`.
-/
module
public import Grammatik.Nichtinterferenz.SchrittTreu
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The flow check over the syntax -/

mutual

/-- Every carrier the statement reads (as the machine reads it: the
    expressions it evaluates, the device carriers of its register reads,
    the awaited/exchanged globals) is admitted by `S`; every axiom it calls
    is admitted by `Ax`. Nested blocks are checked too. -/
def nS (S : D.Tab ⊕ D.Glob → Bool) (Ax : D.Ax → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Bool
  | .assignSlot _ _ i e _ _ => i.orte.all S && e.orte.all S
  | .assignThru p _ _ _ i e _ _ => p.orte.all S && i.orte.all S && e.orte.all S
  | .assignThruOwn p _ _ _ i e _ _ _ _ _ _ _ => p.orte.all S && i.orte.all S && e.orte.all S
  | .assignSlotRef r _ _ _ _ e _ _ => r.orte.all S && e.orte.all S
  | .assignGlob _ e _ _ => e.orte.all S
  | .putBytes _ _ _ _ i _ _ e _ _ => i.orte.all S && e.orte.all S
  | .assignVar _ e => e.orte.all S
  | .shift t _ _ i _ _ _ _ _ _ => S (.inl t) && i.orte.all S
  | .ite c t e => c.orte.all S && nB S Ax t && nB S Ax e
  | .onOption o p a => o.orte.all S && nB S Ax p && nB S Ax a
  | .onTag v arms => v.orte.all S && nA S Ax arms
  | .onWhy r arms => r.orte.all S && nG S Ax arms
  | .call _ args _ _ => args.orte.all S
  | .callInd p args _ _ => p.orte.all S && args.orte.all S
  | .callIndElse p args _ _ _ err => p.orte.all S && args.orte.all S && nE S Ax err
  | .locks _ _ body => nB S Ax body
  | .breaking _ body => nB S Ax body
  | .traverse _ inv body => inv.orte.all S && nB S Ax body
  | .consumeTraverse _ member edge inv _ mass body =>
      member.orte.all S && edge.orte.all S && inv.orte.all S && mass.orte.all S && nB S Ax body
  | .retry _ bis body ueber => bis.orte.all S && nB S Ax body && nB S Ax ueber
  | .forever _ inv body => inv.orte.all S && nB S Ax body
  | .axiomCall a args _ _ _ _ _ => Ax a && args.orte.all S
  | .axiomCallElse _ a args _ _ _ _ _ err => Ax a && args.orte.all S && nE S Ax err
  | .regWrite _ _ e => e.orte.all S
  | .transition .. => true
  | .publish _ e _ _ _ _ => e.orte.all S
  | .advances .. => true
  | .retires .. => true
  | .ret e _ => e.orte.all S
  | .retWhy .. => true
  | .retScoped e _ => e.orte.all S
  | .retWhyScoped .. => true
  | .leave _ => true
  | .next _ => true

def nB (S : D.Tab ⊕ D.Glob → Bool) (Ax : D.Ax → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => nS S Ax s && nB S Ax rest
  | .bind e rest => e.orte.all S && nB S Ax rest
  | .bindCall _ args _ _ _ rest => args.orte.all S && nB S Ax rest
  | .bindCallInd p args _ _ _ rest => p.orte.all S && args.orte.all S && nB S Ax rest
  | .bindCallIndElse p args _ _ _ err rest => p.orte.all S && args.orte.all S && nE S Ax err && nB S Ax rest
  | .bindCallElse _ args _ _ _ err rest => args.orte.all S && nE S Ax err && nB S Ax rest
  | .bindAxiom a args _ _ _ _ _ rest => Ax a && args.orte.all S && nB S Ax rest
  | .bindAxiomElse a args _ _ _ _ _ _ err rest => Ax a && args.orte.all S && nE S Ax err && nB S Ax rest
  | .bindAxiomOpt _ a args _ _ _ _ rest => Ax a && args.orte.all S && nB S Ax rest
  | .bindAxiomOptElse _ a args _ _ _ _ _ err rest => Ax a && args.orte.all S && nE S Ax err && nB S Ax rest
  | .regRead r _ rest => (D.rtraeger r).all S && nB S Ax rest
  | .regReadElse r _ zusage sonst rest =>
      (D.rtraeger r).all S && zusage.orte.all S && nE S Ax sonst && nB S Ax rest
  | .awaits g _ _ _ _ rest => S (.inr g) && nB S Ax rest
  | .exchange g neu _ _ rest => S (.inr g) && neu.orte.all S && nB S Ax rest
  | .narrow e _ _ sonst rest => e.orte.all S && nE S Ax sonst && nB S Ax rest
  | .narrowRequired e _ _ rest => e.orte.all S && nB S Ax rest
  | .check c sonst rest => c.orte.all S && nE S Ax sonst && nB S Ax rest
  | .float _ a b _ _ rest => a.orte.all S && b.orte.all S && nB S Ax rest
  | .floatLit _ _ _ rest => nB S Ax rest
  | .floatOf e _ _ rest => e.orte.all S && nB S Ax rest
  | .floatNarrow e _ _ sonst rest => e.orte.all S && nE S Ax sonst && nB S Ax rest

def nE (S : D.Tab ⊕ D.Glob → Bool) (Ax : D.Ax → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : Endblock D V l Γ Λ → Bool
  | .ret e _ => e.orte.all S
  | .retWhy .. => true
  | .retScoped e _ => e.orte.all S
  | .retWhyScoped .. => true
  | .leave _ => true
  | .next _ => true
  | .cons s rest => nS S Ax s && nE S Ax rest
  | .bind e rest => e.orte.all S && nE S Ax rest
  | .bindCall _ args _ _ _ rest => args.orte.all S && nE S Ax rest
  | .bindCallElse _ args _ _ _ err rest => args.orte.all S && nE S Ax err && nE S Ax rest
  | .bindAxiom a args _ _ _ _ _ rest => Ax a && args.orte.all S && nE S Ax rest
  | .bindAxiomElse a args _ _ _ _ _ _ err rest => Ax a && args.orte.all S && nE S Ax err && nE S Ax rest
  | .bindAxiomOpt _ a args _ _ _ _ rest => Ax a && args.orte.all S && nE S Ax rest
  | .bindAxiomOptElse _ a args _ _ _ _ _ err rest => Ax a && args.orte.all S && nE S Ax err && nE S Ax rest
  | .regRead r _ rest => (D.rtraeger r).all S && nE S Ax rest
  | .regReadElse r _ zusage sonst rest =>
      (D.rtraeger r).all S && zusage.orte.all S && nE S Ax sonst && nE S Ax rest
  | .awaits g _ _ _ _ rest => S (.inr g) && nE S Ax rest
  | .bindCallInd p args _ _ _ rest => p.orte.all S && args.orte.all S && nE S Ax rest
  | .bindCallIndElse p args _ _ _ err rest => p.orte.all S && args.orte.all S && nE S Ax err && nE S Ax rest
  | .narrow e _ _ sonst rest => e.orte.all S && nE S Ax sonst && nE S Ax rest
  | .narrowRequired e _ _ rest => e.orte.all S && nE S Ax rest
  | .exchange g neu _ _ rest => S (.inr g) && neu.orte.all S && nE S Ax rest
  | .ite c t e => c.orte.all S && nE S Ax e && nE S Ax t

def nA (S : D.Tab ⊕ D.Glob → Bool) (Ax : D.Ax → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => nB S Ax b && nA S Ax rest

def nG (S : D.Tab ⊕ D.Glob → Bool) (Ax : D.Ax → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} : GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => nB S Ax b && nG S Ax rest

end

/-- **The residue form of the flow check**: every block, end block, loop
    head and loop body still to run passes `nB`/`nE`. -/
def GRest.nR (S : D.Tab ⊕ D.Glob → Bool) (Ax : D.Ax → Bool) {V : Vertrag D} :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Prop
  | _, _, _, .ende e => nE S Ax e = true
  | _, _, _, .dann b k => nB S Ax b = true ∧ k.nR S Ax
  | _, _, _, .schrumpf k => k.nR S Ax
  | _, _, _, .frei _ k => k.nR S Ax
  | _, _, _, .trav _ inv body _ k => inv.orte.all S = true ∧ nB S Ax body = true ∧ k.nR S Ax
  | _, _, _, .travRest _ inv body _ k =>
      inv.orte.all S = true ∧ nB S Ax body = true ∧ k.nR S Ax
  | _, _, _, .verbrauch _ member edge inv _ mass body _ k =>
      member.orte.all S = true ∧ edge.orte.all S = true ∧ inv.orte.all S = true ∧
        mass.orte.all S = true ∧ nB S Ax body = true ∧ k.nR S Ax
  | _, _, _, .verbrauchRest _ member edge inv _ mass body _ _ k =>
      member.orte.all S = true ∧ edge.orte.all S = true ∧ inv.orte.all S = true ∧
        mass.orte.all S = true ∧ nB S Ax body = true ∧ k.nR S Ax
  | _, _, _, .wieder _ bis body ueber k =>
      bis.orte.all S = true ∧ nB S Ax body = true ∧ nB S Ax ueber = true ∧ k.nR S Ax
  | _, _, _, .wiederRest _ bis body ueber k =>
      bis.orte.all S = true ∧ nB S Ax body = true ∧ nB S Ax ueber = true ∧ k.nR S Ax
  | _, _, _, .ewig _ _ inv body k => inv.orte.all S = true ∧ nB S Ax body = true ∧ k.nR S Ax
  | _, _, _, .ewigRest _ _ inv body k => inv.orte.all S = true ∧ nB S Ax body = true ∧ k.nR S Ax
  | _, _, _, .wartet b k => nB S Ax b = true ∧ k.nR S Ax
  | _, _, _, .wartetSonst _ err b k => nE S Ax err = true ∧ nB S Ax b = true ∧ k.nR S Ax
  | _, _, _, .abbruch k => k.nR S Ax
  | _, _, _, .leer => true
  | _, _, _, .rueckBereit _ k => k.nR S Ax
  | _, _, _, .zurueckgekehrt _ => True

/-- The flow check on every frame of a ghost-free thread state. -/
def KNR (S : D.Tab ⊕ D.Glob → Bool) (Ax : D.Ax → Bool) (k : KFaden D) : Prop :=
  ∀ F ∈ k.kopf :: k.stapel, F.rest.2.2.2.2.nR S Ax

/-! ## 2. Agreement of two worlds on a carrier set -/

/-- Two worlds with the same trace whose memories agree on `T`. -/
def WRel (T : D.Tab ⊕ D.Glob → Bool) (σ τ : World D) : Prop :=
  σ.spur = τ.spur ∧ SpeicherGleich T σ.speicher τ.speicher

section WRel

variable {T : D.Tab ⊕ D.Glob → Bool}

theorem WRel.welt {sp₁ sp₂ : Speicher D} (h : SpeicherGleich T sp₁ sp₂) (spur : List (Ereignis D)) :
    WRel T (sp₁.welt spur) (sp₂.welt spur) :=
  ⟨rfl, h⟩

/-- A question to the outside keeps the relation: both traces get the same event. -/
theorem WRel.fragt {σ τ : World D} (h : WRel T σ τ) (q : D.Ax ⊕ D.Reg ⊕ D.Glob) :
    WRel T (σ.fragt q) (τ.fragt q) :=
  ⟨congrArg (Ereignis.fremd q :: ·) h.1, h.2⟩

theorem WRel.lese {σ τ : World D} (h : WRel T σ τ) (Λ : List (Res D))
    (os : List (D.Tab ⊕ D.Glob)) : WRel T (σ.lese Λ os) (τ.lese Λ os) := by
  refine ⟨?_, h.2⟩
  simp only [World.lese, World.merke, World.haelt, h.1]

/-- Releases keep low-equivalence with the same scopes: same `gibt` events, same memory. -/
theorem WRel.gibt {σ τ : World D} (h : WRel T σ τ) (L : D.Lock) :
    WRel T (σ.gibt L) (τ.gibt L) := by
  refine ⟨?_, ?_⟩
  · simp only [World.gibt, h.1]
  · have ⟨hs, hg⟩ := World.gibt_speicher σ L
    have ⟨hs', hg'⟩ := World.gibt_speicher τ L
    intro c hc
    have := h.2 c hc
    cases c with
    | inl t => simp only [World.speicher, hs, hs'] at this ⊢; exact this
    | inr g => simp only [World.speicher, hg, hg'] at this ⊢; exact this

theorem WRel.gibt_foldl {σ τ : World D} (h : WRel T σ τ) (Ls : List D.Lock) :
    WRel T (Ls.foldl World.gibt σ) (Ls.foldl World.gibt τ) := by
  induction Ls generalizing σ τ with
  | nil => exact h
  | cons L Ls ih =>
      simp only [List.foldl_cons]
      exact ih (h.gibt L)

theorem gleichAuf_von_sg {σ τ : World D} (h : SpeicherGleich T σ.speicher τ.speicher)
    {os : List (D.Tab ⊕ D.Glob)} (hos : ∀ o ∈ os, T o = true) : GleichAuf os σ τ :=
  ⟨fun t ht => h (.inl t) (hos _ ht), fun g hg => h (.inr g) (hos _ hg)⟩

theorem sg_von_gleichAuf {σ τ : World D} (h : ∀ c, T c = true → GleichAuf [c] σ τ) :
    SpeicherGleich T σ.speicher τ.speicher := by
  intro c hc
  cases c with
  | inl t => exact (h _ hc).1 t List.mem_cons_self
  | inr g => exact (h _ hc).2 g List.mem_cons_self

theorem alle_von {S : D.Tab ⊕ D.Glob → Bool} (hST : ∀ c, S c = true → T c = true)
    {os : List (D.Tab ⊕ D.Glob)} (h : os.all S = true) : ∀ o ∈ os, T o = true :=
  fun o ho => hST o (List.all_eq_true.mp h o ho)

theorem WRel.eval {σ τ : World D} (h : WRel T σ τ) {Γ : Ctx} {Λ : List (Res D)} {τ' : Ty}
    (e : Expr D Γ Λ τ') (he : ∀ o ∈ e.orte, T o = true) (ρ : Env D Γ) :
    Gabbro.Grammatik.eval σ e σ ρ = Gabbro.Grammatik.eval τ e τ ρ :=
  eval_gleichAuf e (fun _ ho => ho) (gleichAuf_von_sg h.2 he) ρ

theorem WRel.evalArgs {σ τ : World D} (h : WRel T σ τ) {Γ : Ctx} {Λ : List (Res D)}
    {τs : List Ty} (a : Args D Γ Λ τs) (he : ∀ o ∈ a.orte, T o = true) (ρ : Env D Γ) :
    Gabbro.Grammatik.evalArgs σ a σ ρ = Gabbro.Grammatik.evalArgs τ a τ ρ :=
  evalArgs_gleichAuf a (fun _ ho => ho) (gleichAuf_von_sg h.2 he) ρ

theorem WRel.evalErg {σ τ : World D} (h : WRel T σ τ) {Γ : Ctx} {Λ : List (Res D)}
    {e : Option Ty} (x : ErgExpr D Γ Λ e) (he : ∀ o ∈ x.orte, T o = true) (ρ : Env D Γ) :
    Gabbro.Grammatik.evalErg σ x σ ρ = Gabbro.Grammatik.evalErg τ x τ ρ :=
  evalErg_gleichAuf x (fun _ ho => ho) (gleichAuf_von_sg h.2 he) ρ

theorem WRel.schreibSlot {σ τ : World D} (h : WRel T σ τ) (t : D.Tab) (Λ : List (Res D)) (k : Int)
    (f : D.Feld t) (v : Wert D (D.typ t f)) :
    WRel T (σ.schreibSlot t Λ k f v) (τ.schreibSlot t Λ k f v) := by
  refine ⟨?_, sg_von_gleichAuf fun c hc =>
    gleichAuf_schreibSlot (gleichAuf_von_sg h.2 (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, hc])) t Λ Λ k f v⟩
  simp only [World.schreibSlot, World.merke, World.storeSlot, World.haelt, h.1]

theorem WRel.schreibGlob {σ τ : World D} (h : WRel T σ τ) (g : D.Glob) (Λ : List (Res D))
    (v : Wert D (D.gtyp g)) : WRel T (σ.schreibGlob g Λ v) (τ.schreibGlob g Λ v) := by
  refine ⟨?_, sg_von_gleichAuf fun c hc =>
    gleichAuf_schreibGlob (gleichAuf_von_sg h.2 (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, hc])) g Λ Λ v⟩
  simp only [World.schreibGlob, World.merke, World.storeGlob, World.haelt, h.1]

theorem WRel.schreibBytes (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (Λ : List (Res D)) : ∀ (bs : List Byte) {σ τ : World D} (k : Int), WRel T σ τ →
      WRel T (σ.schreibBytes t f hf Λ k bs) (τ.schreibBytes t f hf Λ k bs)
  | [], _, _, _, h => h
  | _ :: bs, _, _, k, h => WRel.schreibBytes t f hf Λ bs (k + 1) (h.schreibSlot t Λ k f _)

end WRel


end Gabbro.Grammatik
