/- Consuming traversal follows the current canonical fixed-sweep semantics. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Traversal
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

variable {D : Deklaration} {V : Vertrag D}

/-- The current model ignores membership, edges, bound and measure and runs
    exactly the ordinary traversal, including all invariant and exit checks. -/
theorem consumeTraverse_exec_eq_traverse (O : Orakel D) (passes : Nat)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (bound : Int) (mass : Expr D Γ Λ (.int 0 bound))
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ) (σ : World D) (ρ : Env D Γ) :
    execStmt O passes R (.consumeTraverse t member edge inv bound mass body : Stmt D V l Γ Λ Λ) σ ρ =
      execStmt O passes R (.traverse t inv body : Stmt D V l Γ Λ Λ) σ ρ := rfl

/-- Both statement forms share `travC`, so their emitted code, slot bound and
    refusals agree for every body and layout. -/
theorem consumeTraverse_lowS_eq_traverse (passes : Nat) (A : D.Fn → Nat)
    (L : Lay D) (layout : FrameLayout) (ens : List II × Nat) (pr : List Nat) (ex : Int × Int)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (bound : Int) (mass : Expr D Γ Λ (.int 0 bound))
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ) (reserved : Nat := 0) :
    lowS passes A L layout ens pr ex
        (.consumeTraverse t member edge inv bound mass body : Stmt D V l Γ Λ Λ) reserved =
      lowS passes A L layout ens pr ex (.traverse t inv body : Stmt D V l Γ Λ Λ) reserved := rfl

variable [Kern] {L : Lay D}

/-- Generic correctness of the canonical C11 sweep. The body hypothesis is
    the actual recursive compiler proof, with the selected index protected. -/
theorem consumeTraverse_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat}
    {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat}
    (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31)
    {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult)
    (hens : lowPost L (functionFrame P f) P f
      (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {t : D.Tab}
    {member : Expr D (.index (D.count t) :: Γ) Λ .bool}
    {edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool}
    {inv : Expr D Γ Λ .bool} {bound : Int} {mass : Expr D Γ Λ (.int 0 bound)}
    {body : Block D (vertragVon D f) true (.index (D.count t) :: Γ) Λ Λ} :
    (∀ {pr ex}, BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0
      cens tens pr ex body reserved) →
    StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex
      (show Stmt D (vertragVon D f) l Γ Λ Λ from
        .consumeTraverse t member edge inv bound mass body) reserved := by
  intro ihBody
  exact traverse_case (O := O) (passes := passes) (σ0 := σ0) hS hA hlo0 hens
    (t := t) (inv := inv) (body := body) ihBody

end Gabbro.Stage0.Senke
