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
import Grammatik.Nichtinterferenz.SchrittTreu

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
  | .assignDurch p _ _ _ i e _ _ => p.orte.all S && i.orte.all S && e.orte.all S
  | .assignGlob _ e _ _ => e.orte.all S
  | .schreibBytes _ _ _ _ i _ _ e _ _ => i.orte.all S && e.orte.all S
  | .assignVar _ e => e.orte.all S
  | .uebergang t _ _ i _ _ _ _ _ _ => S (.inl t) && i.orte.all S
  | .ite c t e => c.orte.all S && nB S Ax t && nB S Ax e
  | .onOption o p a => o.orte.all S && nB S Ax p && nB S Ax a
  | .onTag v arms => v.orte.all S && nA S Ax arms
  | .onGrund r arms => r.orte.all S && nG S Ax arms
  | .call _ args _ _ => args.orte.all S
  | .callInd p args _ _ => p.orte.all S && args.orte.all S
  | .locks _ _ body => nB S Ax body
  | .breaking _ body => nB S Ax body
  | .traverse _ inv body => inv.orte.all S && nB S Ax body
  | .retry _ bis body ueber => bis.orte.all S && nB S Ax body && nB S Ax ueber
  | .forever _ inv body => inv.orte.all S && nB S Ax body
  | .axiomCall a args _ _ _ _ _ => Ax a && args.orte.all S
  | .regSchreib _ _ e => e.orte.all S
  | .transition .. => true
  | .publish _ e _ _ _ _ => e.orte.all S
  | .advances .. => true
  | .retires .. => true
  | .ret e _ => e.orte.all S
  | .retGrund .. => true
  | .leave _ => true
  | .next _ => true

def nB (S : D.Tab ⊕ D.Glob → Bool) (Ax : D.Ax → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => nS S Ax s && nB S Ax rest
  | .bind e rest => e.orte.all S && nB S Ax rest
  | .bindCall _ args _ _ _ rest => args.orte.all S && nB S Ax rest
  | .bindCallInd p args _ _ _ rest => p.orte.all S && args.orte.all S && nB S Ax rest
  | .bindCallElse _ args _ _ _ err rest => args.orte.all S && nE S Ax err && nB S Ax rest
  | .bindAxiom a args _ _ _ _ _ rest => Ax a && args.orte.all S && nB S Ax rest
  | .regLies r _ rest => (D.rtraeger r).all S && nB S Ax rest
  | .regLiesElse r _ zusage sonst rest =>
      (D.rtraeger r).all S && zusage.orte.all S && nE S Ax sonst && nB S Ax rest
  | .awaits g _ _ _ rest => S (.inr g) && nB S Ax rest
  | .exchange g neu _ _ rest => S (.inr g) && neu.orte.all S && nB S Ax rest
  | .narrow e _ _ sonst rest => e.orte.all S && nE S Ax sonst && nB S Ax rest
  | .pruefung c sonst rest => c.orte.all S && nE S Ax sonst && nB S Ax rest
  | .gleit _ a b _ _ rest => a.orte.all S && b.orte.all S && nB S Ax rest
  | .gleitLit _ _ _ rest => nB S Ax rest
  | .gleitVon e _ _ rest => e.orte.all S && nB S Ax rest
  | .gleitNarrow e _ _ sonst rest => e.orte.all S && nE S Ax sonst && nB S Ax rest

def nE (S : D.Tab ⊕ D.Glob → Bool) (Ax : D.Ax → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : Endblock D V l Γ Λ → Bool
  | .ret e _ => e.orte.all S
  | .retGrund .. => true
  | .leave _ => true
  | .next _ => true
  | .cons s rest => nS S Ax s && nE S Ax rest
  | .bind e rest => e.orte.all S && nE S Ax rest

def nA (S : D.Tab ⊕ D.Glob → Bool) (Ax : D.Ax → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} : Arms D V l Γ Λ Λ' cs → Bool
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
  | _, _, _, .wieder _ bis body ueber k =>
      bis.orte.all S = true ∧ nB S Ax body = true ∧ nB S Ax ueber = true ∧ k.nR S Ax
  | _, _, _, .wiederRest _ bis body ueber k =>
      bis.orte.all S = true ∧ nB S Ax body = true ∧ nB S Ax ueber = true ∧ k.nR S Ax
  | _, _, _, .ewig _ _ inv body k => inv.orte.all S = true ∧ nB S Ax body = true ∧ k.nR S Ax
  | _, _, _, .ewigRest _ _ inv body k => inv.orte.all S = true ∧ nB S Ax body = true ∧ k.nR S Ax
  | _, _, _, .wartet b k => nB S Ax b = true ∧ k.nR S Ax
  | _, _, _, .wartetSonst _ err b k => nE S Ax err = true ∧ nB S Ax b = true ∧ k.nR S Ax
  | _, _, _, .abbruch k => k.nR S Ax

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

theorem WRel.lese {σ τ : World D} (h : WRel T σ τ) (Λ : List (Res D))
    (os : List (D.Tab ⊕ D.Glob)) : WRel T (σ.lese Λ os) (τ.lese Λ os) := by
  refine ⟨?_, h.2⟩
  simp only [World.lese, World.merke, World.haelt, h.1]

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
    gleichAuf_schreibSlot (gleichAuf_von_sg h.2 (by simp [hc])) t Λ Λ k f v⟩
  simp only [World.schreibSlot, World.merke, World.storeSlot, World.haelt, h.1]

theorem WRel.schreibGlob {σ τ : World D} (h : WRel T σ τ) (g : D.Glob) (Λ : List (Res D))
    (v : Wert D (D.gtyp g)) : WRel T (σ.schreibGlob g Λ v) (τ.schreibGlob g Λ v) := by
  refine ⟨?_, sg_von_gleichAuf fun c hc =>
    gleichAuf_schreibGlob (gleichAuf_von_sg h.2 (by simp [hc])) g Λ Λ v⟩
  simp only [World.schreibGlob, World.merke, World.storeGlob, World.haelt, h.1]

theorem WRel.schreibBytes (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (Λ : List (Res D)) : ∀ (bs : List Byte) {σ τ : World D} (k : Int), WRel T σ τ →
      WRel T (σ.schreibBytes t f hf Λ k bs) (τ.schreibBytes t f hf Λ k bs)
  | [], _, _, _, h => h
  | _ :: bs, _, _, k, h => WRel.schreibBytes t f hf Λ bs (k + 1) (h.schreibSlot t Λ k f _)

end WRel

/-- **The oracle condition for a carrier set `T`**: every axiom `Ax`
    admits, called in two worlds that agree on `T` (and on the trace),
    answers the same and ends in two worlds that agree on `T` (and on the
    trace). The hardware answers `B`'s questions from `B`'s data only. -/
def OrakelTreu (T : D.Tab ⊕ D.Glob → Bool) (Ax : D.Ax → Bool) (O : Orakel D) : Prop :=
  ∀ a, Ax a = true → ∀ (σ τ : World D) (ρ : Env D (D.aparams a)), WRel T σ τ →
    (O.wirkt a σ ρ).2 = (O.wirkt a τ ρ).2 ∧ WRel T (O.wirkt a σ ρ).1 (O.wirkt a τ ρ).1

/-- The oracle condition read through `axiomAntwort`. -/
theorem axiomAntwort_rel (O : Orakel D) {T : D.Tab ⊕ D.Glob → Bool} {AxT : D.Ax → Bool}
    (hO : OrakelTreu T AxT O) {a : D.Ax} (ha : AxT a = true) {σ τ : World D} (h : WRel T σ τ)
    (x : Env D (D.aparams a)) :
    (axiomAntwort O a σ x).2 = (axiomAntwort O a τ x).2 ∧
      WRel T (axiomAntwort O a σ x).1 (axiomAntwort O a τ x).1 := by
  obtain ⟨e1, e2⟩ := hO a ha σ τ x h
  simp only [axiomAntwort]
  exact ⟨by rw [e1], e2⟩

/-! ## 3. Two outcomes of the same shape -/

/-- Two outcomes of a statement run in two related worlds: the same
    constructor, the same environment/value/reason, equal traces and
    memories agreeing on `T`. -/
def AusRel (T : D.Tab ⊕ D.Glob → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx} :
    Ausgang V l Γ → Ausgang V l Γ → Prop
  | .ok σ ρ, .ok σ' ρ' => WRel T σ σ' ∧ ρ = ρ'
  | .zurueck σ v, .zurueck σ' v' => WRel T σ σ' ∧ v = v'
  | .grund σ r, .grund σ' r' => WRel T σ σ' ∧ r = r'
  | .leave _ σ ρ, .leave _ σ' ρ' => WRel T σ σ' ∧ ρ = ρ'
  | .next _ σ ρ, .next _ σ' ρ' => WRel T σ σ' ∧ ρ = ρ'
  | .logik _, .logik _ => True
  | .hardware _, .hardware _ => True
  | _, _ => False

section Blatt

variable (O : Orakel D) (passes : Nat) {S T : D.Tab ⊕ D.Glob → Bool} {Ax AxT : D.Ax → Bool}

set_option maxHeartbeats 1000000 in
/-- **A leaf is local, relationally.** Its reads in `S ⊆ T`, its axioms in
    `Ax ⊆ AxT` with the oracle faithful on `T`: two related worlds give two
    related outcomes. -/
theorem blatt_rel (hST : ∀ c, S c = true → T c = true) (hAx : ∀ a, Ax a = true → AxT a = true)
    (hO : OrakelTreu T AxT O) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (hb : s.istBlatt = true) (hn : nS S Ax s = true)
    {σ τ : World D} (h : WRel T σ τ) (ρ : Env D Γ) :
    AusRel T (execStmt O passes keinRuf s σ ρ) (execStmt O passes keinRuf s τ ρ) := by
  cases s with
  | assignSlot t f i e hw hL =>
      simp only [nS, Bool.and_eq_true] at hn
      have h1 := h.lese Λ (i.orte ++ e.orte)
      simp only [execStmt, AusRel]
      rw [h1.eval i (alle_von hST hn.1) ρ, h1.eval e (alle_von hST hn.2) ρ]
      exact ⟨h1.schreibSlot _ _ _ _ _, trivial⟩
  | assignDurch p t ht f i e hw hL =>
      simp only [nS, Bool.and_eq_true] at hn
      have h1 := h.lese Λ (p.orte ++ i.orte ++ e.orte)
      simp only [execStmt, AusRel]
      rw [h1.eval i (alle_von hST hn.1.2) ρ, h1.eval e (alle_von hST hn.2) ρ]
      exact ⟨h1.schreibSlot _ _ _ _ _, trivial⟩
  | assignGlob g e hw hL =>
      simp only [nS] at hn
      have h1 := h.lese Λ e.orte
      simp only [execStmt, AusRel]
      rw [h1.eval e (alle_von hST hn) ρ]
      exact ⟨h1.schreibGlob _ _ _, trivial⟩
  | schreibBytes t f hf n i hlo hhi e hw hL =>
      simp only [nS, Bool.and_eq_true] at hn
      have h1 := h.lese Λ (i.orte ++ e.orte)
      simp only [execStmt, AusRel]
      rw [h1.eval i (alle_von hST hn.1) ρ, h1.eval e (alle_von hST hn.2) ρ]
      exact ⟨WRel.schreibBytes t f hf Λ _ _ h1, trivial⟩
  | assignVar x e =>
      simp only [nS] at hn
      have h1 := h.lese Λ e.orte
      simp only [execStmt, AusRel]
      rw [h1.eval e (alle_von hST hn) ρ]
      exact ⟨h1, rfl⟩
  | uebergang t f hτ i von nach hn' he hw hL =>
      simp only [nS, Bool.and_eq_true] at hn
      have h1 := h.lese Λ (.inl t :: i.orte)
      have hi := h1.eval i (alle_von hST hn.2) ρ
      have ht : (σ.lese Λ (.inl t :: i.orte)).slots t = (τ.lese Λ (.inl t :: i.orte)).slots t :=
        h1.2 (.inl t) (hST _ hn.1)
      simp only [execStmt]
      rw [hi, ht]
      split
      · exact ⟨h1.schreibSlot _ _ _ _ _, rfl⟩
      · trivial
  | axiomCall a args hnone hw hg hd hgd =>
      simp only [nS, Bool.and_eq_true] at hn
      have h1 := h.lese Λ args.orte
      have ha := h1.evalArgs args (alle_von hST hn.2) ρ
      obtain ⟨e1, e2⟩ := axiomAntwort_rel O hO (hAx a hn.1) h1
        (evalArgs (τ.lese Λ args.orte) args (τ.lese Λ args.orte) ρ)
      simp only [execStmt]
      rw [ha]
      revert e1 e2
      generalize axiomAntwort O a (σ.lese Λ args.orte)
        (evalArgs (τ.lese Λ args.orte) args (τ.lese Λ args.orte) ρ) = p₁
      generalize axiomAntwort O a (τ.lese Λ args.orte)
        (evalArgs (τ.lese Λ args.orte) args (τ.lese Λ args.orte) ρ) = p₂
      rintro e1 e2
      obtain ⟨w1, r1⟩ := p₁
      obtain ⟨w2, r2⟩ := p₂
      simp only at e1 e2 ⊢
      subst e1
      cases r1 <;> simp only [AusRel] <;> first | exact ⟨e2, trivial⟩ | exact ⟨e2, rfl⟩ | trivial
  | regSchreib r hk e =>
      simp only [execStmt, AusRel]
      exact ⟨h.lese Λ e.orte, trivial⟩
  | transition r hk m hm hl maske bits =>
      simp only [execStmt, AusRel]
      exact ⟨h, trivial⟩
  | publish g e payload hp hw hL =>
      simp only [nS] at hn
      have h1 := h.lese Λ e.orte
      simp only [execStmt, AusRel]
      rw [h1.eval e (alle_von hST hn) ρ]
      exact ⟨h1.schreibGlob _ _ _, trivial⟩
  | advances m a h' hs =>
      simp only [execStmt, AusRel]
      exact ⟨h, trivial⟩
  | retires m s' h' a =>
      simp only [execStmt, AusRel]
      exact ⟨h, trivial⟩
  | ret e hp =>
      simp only [nS] at hn
      have h1 := h.lese Λ e.orte
      simp only [execStmt, AusRel]
      rw [h1.evalErg e (alle_von hST hn) ρ]
      exact ⟨h1, rfl⟩
  | retGrund r hp =>
      simp only [execStmt, AusRel]
      exact ⟨h, trivial⟩
  | leave h' =>
      simp only [execStmt, AusRel]
      exact ⟨h, trivial⟩
  | next h' =>
      simp only [execStmt, AusRel]
      exact ⟨h, trivial⟩
  | _ => simp [Stmt.istBlatt] at hb

end Blatt

end Gabbro.Grammatik
