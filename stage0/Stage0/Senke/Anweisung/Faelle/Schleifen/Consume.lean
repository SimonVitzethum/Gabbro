/- Current consuming semantics and its statement admission boundary. The old
   fixed-sweep equality is false after the C11 model change and is removed. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Traversal
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Lower
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Runtime
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Selection
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Consuming.Decrease
public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

variable {D : Deklaration} {V : Vertrag D}

/-- The canonical entry point, including read bookkeeping and the exact fuel.
    Selection is reevaluated after every completed body pass. The selected
    candidate is the second binder of the edge expression. -/
theorem consumeTraverse_exec (O : Orakel D) (passes : Nat)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (bound : Int) (mass : Expr D Γ Λ (.int 0 bound))
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (σ : World D) (ρ : Env D Γ) :
    execStmt O passes R
      (.consumeTraverse t member edge inv bound mass body : Stmt D V l Γ Λ Λ) σ ρ =
      verbrauchLauf t (fun σ ρ => execBlock O passes R body σ ρ)
        (fun σ ρ => let σ := σ.lese Λ inv.orte; (σ, wahr? (eval σ inv σ ρ)))
        (verbrauchSel t member edge)
        (fun σ ρ => let σ := σ.lese Λ mass.orte; (σ, (eval σ mass σ ρ).n))
        bound ((D.count t).toNat + bound.toNat + 1) σ ρ := rfl

/-- Refusal is explicit until the candidate loop has its concrete simulation.
    A source semantic change must not be hidden behind an old successful
    lowering or a theorem about an unrelated fixed-index traversal. -/
theorem consumeTraverse_lowS_refused (passes : Nat) (A : D.Fn → Nat)
    (L : Lay D) (layout : FrameLayout) (ens : List II × Nat)
    (pr : List Nat) (ex : Int × Int)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool)
    (inv : Expr D Γ Λ .bool) (bound : Int) (mass : Expr D Γ Λ (.int 0 bound))
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (reserved : Nat := 0) :
    lowS passes A L layout ens pr ex
      (.consumeTraverse t member edge inv bound mass body : Stmt D V l Γ Λ Λ) reserved = none := rfl

/-- The source entry always has fuel for its initial invariant/selection
    round, even for an empty index domain and a zero measure bound. Fuel
    exhaustion can occur only on a subsequent continuing round. -/
theorem consumeTraverse_initial_fuel (t : D.Tab) (bound : Int) :
    0 < (D.count t).toNat + bound.toNat + 1 := by
  omega

variable [Kern] {L : Lay D}

/-- The statement theorem remains connected to the actual lowS path. This
    case establishes only rejection, not admission or consuming execution.

    OPEN: discharge the instruction-level premises of `Consuming.runtime`
    for `Consuming.lower`, then replace this refusal case with that proof.
    Initialization, selector bounds, membership binder restoration and the
    post-body measure check now have concrete instruction lemmas in Blocks,
    Selection and Decrease. The scan induction lemmas in Scan still require
    their concrete per-iteration paths to be instantiated here.
    Remaining premises include current-world first-minimal selection, cycle
    versus empty-domain distinction, saved measure preservation across every
    actual body outcome, bounded strict decrease and the leave invariant.
    The body hypothesis below is retained for that structural proof. -/
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
  intro ihBody c top emitted
  simp only [lowS, reduceCtorEq] at emitted

/-- Neither unused control arguments nor zero measure can reinstate the
    retired fixed sweep. This quantifies over every actual body candidate,
    not over a single witness program. -/
theorem consumeTraverse_no_fixed_sweep (passes : Nat) (A : D.Fn → Nat)
    (L : Lay D) (layout : FrameLayout) (ens : List II × Nat)
    (pr : List Nat) (ex : Int × Int)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (reserved : Nat := 0) :
    lowS passes A L layout ens pr ex
      (.consumeTraverse t .fls .tru .tru 0 (.lit 0) body : Stmt D V l Γ Λ Λ) reserved = none := rfl

end Gabbro.Stage0.Senke
