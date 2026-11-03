module
public import Grammatik.Kern.Syntax.Satz.T2
public import Grammatik.Kern.Syntax.Satz.T3a
@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration} {V : vertrag D}

/-! ### The lock floor of a body (held-set relaxation, 2026-09-13)

    `ueberBoden c`: every `locks L` in the syntax takes a lock of rank at
    least `c`. A function with floor `some c` (`Signatur.boden`) may run
    under extra locks of its caller of rank below `c` (`RufPasst.hx`); the
    Satz needs its body to take only locks at or above `c` (`StufenOk`), so
    that no `locks` inside the callee re-takes or undercuts a lock held by a
    caller it does not know of. Calls are not followed: the callee's own
    body is checked at its own floor. -/

section Boden

variable {V : Vertrag D}

mutual

def Stmt.ueberBoden {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (c : Int) :
    Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => t.ueberBoden c && e.ueberBoden c
  | .onOption _ p a => p.ueberBoden c && a.ueberBoden c
  | .onTag _ arms => arms.ueberBoden c
  | .onWhy _ arms => arms.ueberBoden c
  | .locks L _ body => decide (c ≤ D.rang L) && body.ueberBoden c
  | .breaking _ body => body.ueberBoden c
  | .traverse _ _ body => body.ueberBoden c
  | .consumeTraverse _ _ _ _ _ _ body => body.ueberBoden c
  | .retry _ _ body ueber => body.ueberBoden c && ueber.ueberBoden c
  | .forever _ _ body => body.ueberBoden c
  | .axiomCallElse _ _ _ _ _ _ _ _ err => err.ueberBoden c
  | .callIndElse _ _ _ _ _ err => err.ueberBoden c
  | _ => true

def Block.ueberBoden {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (c : Int) :
    Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => s.ueberBoden c && rest.ueberBoden c
  | .bind _ rest => rest.ueberBoden c
  | .bindCall _ _ _ _ _ rest => rest.ueberBoden c
  | .bindCallInd _ _ _ _ _ rest => rest.ueberBoden c
  | .bindCallIndElse _ _ _ _ _ err rest => err.ueberBoden c && rest.ueberBoden c
  | .bindCallElse _ _ _ _ _ err rest => err.ueberBoden c && rest.ueberBoden c
  | .bindAxiom _ _ _ _ _ _ _ rest => rest.ueberBoden c
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => err.ueberBoden c && rest.ueberBoden c
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => rest.ueberBoden c
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => err.ueberBoden c && rest.ueberBoden c
  | .regRead _ _ rest => rest.ueberBoden c
  | .regReadElse _ _ _ sonst rest => sonst.ueberBoden c && rest.ueberBoden c
  | .awaits _ _ _ _ _ rest => rest.ueberBoden c
  | .exchange _ _ _ _ rest => rest.ueberBoden c
  | .narrow _ _ _ sonst rest => sonst.ueberBoden c && rest.ueberBoden c
  | .narrowRequired _ _ _ rest => rest.ueberBoden c
  | .check _ sonst rest => sonst.ueberBoden c && rest.ueberBoden c
  | .float _ _ _ _ _ rest => rest.ueberBoden c
  | .floatLit _ _ _ rest => rest.ueberBoden c
  | .floatOf _ _ _ rest => rest.ueberBoden c
  | .floatNarrow _ _ _ sonst rest => sonst.ueberBoden c && rest.ueberBoden c

def Endblock.ueberBoden {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (c : Int) :
    Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retWhy .. => true
  | .retScoped .. => true
  | .retWhyScoped .. => true
  | .leave .. => true
  | .next .. => true
  | .cons s rest => s.ueberBoden c && rest.ueberBoden c
  | .bind _ rest => rest.ueberBoden c
  | .bindCall _ _ _ _ _ rest => rest.ueberBoden c
  | .bindCallElse _ _ _ _ _ err rest => err.ueberBoden c && rest.ueberBoden c
  | .bindAxiom _ _ _ _ _ _ _ rest => rest.ueberBoden c
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => err.ueberBoden c && rest.ueberBoden c
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => rest.ueberBoden c
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => err.ueberBoden c && rest.ueberBoden c
  | .regRead _ _ rest => rest.ueberBoden c
  | .regReadElse _ _ _ sonst rest => sonst.ueberBoden c && rest.ueberBoden c
  | .awaits _ _ _ _ _ rest => rest.ueberBoden c
  | .bindCallInd _ _ _ _ _ rest => rest.ueberBoden c
  | .bindCallIndElse _ _ _ _ _ err rest => err.ueberBoden c && rest.ueberBoden c
  | .narrow _ _ _ sonst rest => sonst.ueberBoden c && rest.ueberBoden c
  | .narrowRequired _ _ _ rest => rest.ueberBoden c
  | .exchange _ _ _ _ rest => rest.ueberBoden c
  | .ite _ t e => t.ueberBoden c && e.ueberBoden c

def Arms.ueberBoden {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    (c : Int) : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => b.ueberBoden c && rest.ueberBoden c

def GrundArms.ueberBoden {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} (c : Int) :
    GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => b.ueberBoden c && rest.ueberBoden c

end

/-- The syntax respects the floor `bo` (vacuous for `none`). -/
abbrev Stmt.BodenOk {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (bo : Option Int)
    (s : Stmt D V l Γ Λ Λ') : Prop := ∀ c, bo = some c → s.ueberBoden c = true
abbrev Block.BodenOk {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (bo : Option Int)
    (b : Block D V l Γ Λ Λ') : Prop := ∀ c, bo = some c → b.ueberBoden c = true
abbrev Endblock.BodenOk {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (bo : Option Int)
    (b : Endblock D V l Γ Λ) : Prop := ∀ c, bo = some c → b.ueberBoden c = true
abbrev Arms.BodenOk {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    (bo : Option Int) (a : Arms D V l Γ Λ Λ' cs) : Prop := ∀ c, bo = some c → a.ueberBoden c = true
abbrev GrundArms.BodenOk {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (bo : Option Int) (a : GrundArms D V l Γ Λ Λ' n) : Prop := ∀ c, bo = some c → a.ueberBoden c = true

end Boden
/-- **The floors of a program are respected** (decidable per program): the
    body of every function with floor `some c` takes only locks of rank at
    least `c`. Trivial for a declaration without floors (`stufenOk_ohne`). -/
def StufenOk (P : Programm D) : Prop :=
  ∀ f c, (D.signatur f).boden = some c → (P.rumpf f).ueberBoden c = true

theorem stufenOk_ohne (P : Programm D) (h : ∀ f : D.Fn, (D.signatur f).boden = none) :
    StufenOk P := fun f c hc => by rw [h f] at hc; cases hc

/-! ### Scope validity of scoped returns (C11)

    `scopesOk haelt boden`: every `retScoped`/`retWhyScoped` in the syntax releases
    only locks outside the residual (`haelt`) and at or above the floor. The Satz
    needs it at every scoped return to transport the caller's holdings through a
    releasing handler return: required locks survive (spare) and extras survive
    (rank + `RufPasst.hx`). The checker establishes it with the exact scope
    discipline (`RueckRessourcen.genau`); here it is a premise (`ScopesOkProg`),
    threaded like `BodenOk`. -/

section Scopes

variable {V : Vertrag D}

def scopesOkScopes (haelt : List D.Lock) (boden : Option Int) : List D.Lock → Bool
  | [] => true
  | L :: Ls => decide (L ∉ haelt) &&
      (match boden with | none => true | some c => decide (c ≤ D.rang L)) &&
      scopesOkScopes haelt boden Ls

/-- Every scope of the list avoids the residual and respects the floor. -/
theorem scopesOkScopes_mem {haelt : List D.Lock} {boden : Option Int} {Ls : List D.Lock}
    (h : scopesOkScopes haelt boden Ls = true) {L : D.Lock} (hm : L ∈ Ls) :
    L ∉ haelt ∧ ∀ c, boden = some c → c ≤ D.rang L := by
  induction Ls with
  | nil => simp only [List.not_mem_nil] at hm
  | cons M Ms ih =>
      simp only [scopesOkScopes, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hM, hrM⟩, hMs⟩ := h
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · refine ⟨hM, fun c hc => ?_⟩
        rw [hc] at hrM
        exact of_decide_eq_true hrM
      · exact ih hMs hm

mutual

def Stmt.scopesOk {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (haelt : List D.Lock)
    (boden : Option Int) : Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => t.scopesOk haelt boden && e.scopesOk haelt boden
  | .onOption _ p a => p.scopesOk haelt boden && a.scopesOk haelt boden
  | .onTag _ arms => arms.scopesOk haelt boden
  | .onWhy _ arms => arms.scopesOk haelt boden
  | .callIndElse _ _ _ _ _ err => err.scopesOk haelt boden
  | .locks _ _ body => body.scopesOk haelt boden
  | .breaking _ body => body.scopesOk haelt boden
  | .traverse _ _ body => body.scopesOk haelt boden
  | .consumeTraverse _ _ _ _ _ _ body => body.scopesOk haelt boden
  | .retry _ _ body ueber => body.scopesOk haelt boden && ueber.scopesOk haelt boden
  | .forever _ _ body => body.scopesOk haelt boden
  | .axiomCallElse _ _ _ _ _ _ _ _ err => err.scopesOk haelt boden
  | .retScoped _ R => scopesOkScopes haelt boden R.scopes
  | .retWhyScoped _ R => scopesOkScopes haelt boden R.scopes
  | _ => true

def Block.scopesOk {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (haelt : List D.Lock)
    (boden : Option Int) : Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => s.scopesOk haelt boden && rest.scopesOk haelt boden
  | .bind _ rest => rest.scopesOk haelt boden
  | .bindCall _ _ _ _ _ rest => rest.scopesOk haelt boden
  | .bindCallInd _ _ _ _ _ rest => rest.scopesOk haelt boden
  | .bindCallIndElse _ _ _ _ _ err rest => err.scopesOk haelt boden && rest.scopesOk haelt boden
  | .bindCallElse _ _ _ _ _ err rest => err.scopesOk haelt boden && rest.scopesOk haelt boden
  | .bindAxiom _ _ _ _ _ _ _ rest => rest.scopesOk haelt boden
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => err.scopesOk haelt boden && rest.scopesOk haelt boden
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => rest.scopesOk haelt boden
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => err.scopesOk haelt boden && rest.scopesOk haelt boden
  | .regRead _ _ rest => rest.scopesOk haelt boden
  | .regReadElse _ _ _ sonst rest => sonst.scopesOk haelt boden && rest.scopesOk haelt boden
  | .awaits _ _ _ _ _ rest => rest.scopesOk haelt boden
  | .exchange _ _ _ _ rest => rest.scopesOk haelt boden
  | .narrow _ _ _ sonst rest => sonst.scopesOk haelt boden && rest.scopesOk haelt boden
  | .narrowRequired _ _ _ rest => rest.scopesOk haelt boden
  | .check _ sonst rest => sonst.scopesOk haelt boden && rest.scopesOk haelt boden
  | .float _ _ _ _ _ rest => rest.scopesOk haelt boden
  | .floatLit _ _ _ rest => rest.scopesOk haelt boden
  | .floatOf _ _ _ rest => rest.scopesOk haelt boden
  | .floatNarrow _ _ _ sonst rest => sonst.scopesOk haelt boden && rest.scopesOk haelt boden

def Endblock.scopesOk {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (haelt : List D.Lock)
    (boden : Option Int) : Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retWhy .. => true
  | .retScoped _ R => scopesOkScopes haelt boden R.scopes
  | .retWhyScoped _ R => scopesOkScopes haelt boden R.scopes
  | .leave .. => true
  | .next .. => true
  | .cons s rest => s.scopesOk haelt boden && rest.scopesOk haelt boden
  | .bind _ rest => rest.scopesOk haelt boden
  | .bindCall _ _ _ _ _ rest => rest.scopesOk haelt boden
  | .bindCallElse _ _ _ _ _ err rest => err.scopesOk haelt boden && rest.scopesOk haelt boden
  | .bindAxiom _ _ _ _ _ _ _ rest => rest.scopesOk haelt boden
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => err.scopesOk haelt boden && rest.scopesOk haelt boden
  | .bindAxiomOpt _ _ _ _ _ _ _ rest => rest.scopesOk haelt boden
  | .bindAxiomOptElse _ _ _ _ _ _ _ _ err rest => err.scopesOk haelt boden && rest.scopesOk haelt boden
  | .regRead _ _ rest => rest.scopesOk haelt boden
  | .regReadElse _ _ _ sonst rest => sonst.scopesOk haelt boden && rest.scopesOk haelt boden
  | .awaits _ _ _ _ _ rest => rest.scopesOk haelt boden
  | .bindCallInd _ _ _ _ _ rest => rest.scopesOk haelt boden
  | .bindCallIndElse _ _ _ _ _ err rest => err.scopesOk haelt boden && rest.scopesOk haelt boden
  | .narrow _ _ _ sonst rest => sonst.scopesOk haelt boden && rest.scopesOk haelt boden
  | .narrowRequired _ _ _ rest => rest.scopesOk haelt boden
  | .exchange _ _ _ _ rest => rest.scopesOk haelt boden
  | .ite _ t e => t.scopesOk haelt boden && e.scopesOk haelt boden

def Arms.scopesOk {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    (haelt : List D.Lock) (boden : Option Int) : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => b.scopesOk haelt boden && rest.scopesOk haelt boden

def GrundArms.scopesOk {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (haelt : List D.Lock) (boden : Option Int) : GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => b.scopesOk haelt boden && rest.scopesOk haelt boden

end

/-- The scoped returns of a body respect residual and floor (vacuous without any). -/
abbrev Stmt.ScopesOk {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') : Prop := s.scopesOk V.haelt V.boden = true
abbrev Block.ScopesOk {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ') : Prop := b.scopesOk V.haelt V.boden = true
abbrev Endblock.ScopesOk {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (b : Endblock D V l Γ Λ) : Prop := b.scopesOk V.haelt V.boden = true
abbrev Arms.ScopesOk {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    (a : Arms D V l Γ Λ Λ' cs) : Prop := a.scopesOk V.haelt V.boden = true
abbrev GrundArms.ScopesOk {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (a : GrundArms D V l Γ Λ Λ' n) : Prop := a.scopesOk V.haelt V.boden = true

end Scopes
/-- **The scoped returns of a program respect residual and floor** (decidable per
    program): every `retScoped`/`retWhyScoped` in every body releases only locks
    outside the residual and at or above the floor. The checker establishes it
    with the exact scope discipline; the Satz carries it as a premise. -/
def ScopesOkProg (P : Programm D) : Prop :=
  ∀ f, (P.rumpf f).scopesOk (D.signatur f).haelt (D.signatur f).boden = true

/-! ### The counted scope check (C11, owner 2026-11-02)

    A predicate on a scope list decides the check; a scoped return at a
    counted frame meets it. Used by the derivation of `ScopesOkProg` from
    the floor (`Satz/T4/Teil3`). -/

/-- A predicate on a scope list decides the scope check. -/
theorem scopesOkScopes_of_forall {haelt : List D.Lock} {boden : Option Int} {Ls : List D.Lock}
    (h : ∀ L ∈ Ls, L ∉ haelt ∧ ∀ c, boden = some c → c ≤ D.rang L) :
    scopesOkScopes haelt boden Ls = true := by
  induction Ls with
  | nil => rfl
  | cons K Ks ih =>
      have ⟨hnK, hrK⟩ := h K List.mem_cons_self
      have hrest := ih (fun L hL => h L (List.mem_cons_of_mem _ hL))
      simp only [scopesOkScopes, Bool.and_eq_true]
      refine ⟨⟨decide_eq_true hnK, ?_⟩, hrest⟩
      cases hb : boden with
      | none => rfl
      | some c =>
          simp only [hb]
          exact decide_eq_true (hrK c hb)

/-- A scoped return at a counted frame meets the scope check. -/
theorem scopesOk_retScopedAux {V : Vertrag D} {Λ : List (Res D)}
    (R : RueckRessourcen D V Λ) (hcount : HCountScope V Λ) :
    scopesOkScopes V.haelt V.boden R.scopes = true := by
  apply scopesOkScopes_of_forall
  intro L hL
  have hmem : 0 < R.scopes.count L := List.count_pos_iff.mpr hL
  have hmap : (R.scopes.map Res.held).count (Res.held L) = R.scopes.count L :=
    count_held_map L R.scopes
  have hperm : Λ.count (Res.held L) = (V.ende ++ R.scopes.map Res.held).count (Res.held L) :=
    count_of_perm R.genau
  have hende : V.ende.count (Res.held L) = (V.haelt.map Res.held).count (Res.held L) := by
    unfold Vertrag.ende
    rw [List.count_append, count_held_marke_map, Nat.add_zero]
  have hgt : (V.haelt.map Res.held).count (Res.held L) < Λ.count (Res.held L) := by
    rw [hperm, List.count_append, hende, hmap]
    omega
  rcases hcount L with heq | hR
  · have hF : False := by omega
    exact hF.elim
  · exact hR

set_option hygiene false in
/-- Scope bookkeeping: the scope premise of a sub-block from the enclosing one (`hscope`). -/
macro "scopes_tac" : tactic => `(tactic|
  (have hsc := hscope
   simp only [Stmt.scopesOk, Block.scopesOk, Endblock.scopesOk, Arms.scopesOk,
     GrundArms.scopesOk, Bool.and_eq_true] at hsc
   first | exact hsc | exact hsc.1 | exact hsc.2 | exact hsc.2.1 | exact hsc.2.2 | exact hsc.1.1 | exact hsc.1.2))

set_option hygiene false in
/-- Floor bookkeeping: the floor premise of a sub-block from the enclosing one (`hbo`). -/
macro "boden_tac" : tactic => `(tactic|
  (intro c hc
   have hsc := hbo c hc
   simp only [Stmt.ueberBoden, Block.ueberBoden, Endblock.ueberBoden, Arms.ueberBoden,
     GrundArms.ueberBoden, Bool.and_eq_true, decide_eq_true_eq] at hsc
   first | exact hsc | exact hsc.1 | exact hsc.2 | exact hsc.2.1 | exact hsc.2.2 | exact hsc.1.1 | exact hsc.1.2))


end Gabbro.Grammatik
