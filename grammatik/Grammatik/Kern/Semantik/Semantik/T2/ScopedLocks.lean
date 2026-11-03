/- Canonical lock-wrapper equations: scoped returns release once, before propagation. -/
module
public import Grammatik.Kern.Semantik.Semantik.T2.Teil2
@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
variable (O : Orakel D) (passes : Nat)
variable (Ruf : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- Terminal outcomes already carry the exact cleanup performed by their typed
    return. All other outcomes keep the previous mapWelt behavior, including the
    wrapper's single release on normal, leave and next continuation. -/
theorem execStmt_locks_outcome (L : D.Lock)
    (rank : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (.held L :: Λ) (.held L :: Λ)) (σ : World D) (ρ : Env D Γ) :
    execStmt O passes Ruf (.locks L rank body) σ ρ =
      match execBlock O passes Ruf body (σ.nimmt L) ρ with
      | .zurueck σ' value => .zurueck σ' value
      | .why σ' reason => .why σ' reason
      | outcome => outcome.mapWelt (·.gibt L) := by
  rfl

/-- Any surrounding lexical lock propagates a completed value return unchanged. -/
theorem execStmt_locks_return (L : D.Lock)
    (rank : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (.held L :: Λ) (.held L :: Λ))
    (σ σ' : World D) (ρ : Env D Γ) (value : ErgVal D V.erg)
    (returned : execBlock O passes Ruf body (σ.nimmt L) ρ = .zurueck σ' value) :
    execStmt O passes Ruf (.locks L rank body) σ ρ = .zurueck σ' value := by
  rw [execStmt_locks_outcome, returned]

/-- The same rule applies to the reason channel, retaining the returned reason. -/
theorem execStmt_locks_reason (L : D.Lock)
    (rank : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (.held L :: Λ) (.held L :: Λ))
    (σ σ' : World D) (ρ : Env D Γ) (reason : Fin V.gruende)
    (returned : execBlock O passes Ruf body (σ.nimmt L) ρ = .why σ' reason) :
    execStmt O passes Ruf (.locks L rank body) σ ρ = .why σ' reason := by
  rw [execStmt_locks_outcome, returned]

/-- The canonical read world and saved result precede all cleanup. Resource
    exactness is the existing RueckRessourcen evidence of retScoped; the wrapper
    appends no release to its recorded list, which may cross outer scopes too. -/
theorem execStmt_locks_retScoped (L : D.Lock)
    (rank : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (e : ErgExpr D Γ (.held L :: Λ) V.erg)
    (cleanup : RueckRessourcen D V (.held L :: Λ)) (σ : World D) (ρ : Env D Γ) :
    let read := (σ.nimmt L).lese (.held L :: Λ) e.orte
    execStmt O passes Ruf (.locks L rank (.cons (.retScoped e cleanup) .nil)) σ ρ =
      .zurueck (cleanup.scopes.foldl World.gibt read) (evalErg read e read ρ) := by
  rfl

/-- No surrounding wrapper releases again after a reason's exact cleanup. -/
theorem execStmt_locks_retWhyScoped (L : D.Lock)
    (rank : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (reason : Fin V.gruende) (cleanup : RueckRessourcen D V (.held L :: Λ))
    (σ : World D) (ρ : Env D Γ) :
    execStmt O passes Ruf (.locks L rank (.cons (.retWhyScoped reason cleanup) .nil)) σ ρ =
      .why (cleanup.scopes.foldl World.gibt (σ.nimmt L)) reason := by
  rfl

/-- The complete return trace has precisely the declared cleanup prefix, and all
    memory is the pre-release read memory. This is the fold of G7's one-lock steps. -/
theorem execStmt_locks_retScoped_trace (L : D.Lock)
    (rank : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (e : ErgExpr D Γ (.held L :: Λ) V.erg)
    (cleanup : RueckRessourcen D V (.held L :: Λ)) (σ : World D) (ρ : Env D Γ) :
    let read := (σ.nimmt L).lese (.held L :: Λ) e.orte
    ∃ result, execStmt O passes Ruf (.locks L rank (.cons (.retScoped e cleanup) .nil)) σ ρ =
        .zurueck result (evalErg read e read ρ) ∧
      result.spur = cleanup.scopes.reverse.map Ereignis.gibt ++ read.spur ∧
      result.slots = read.slots ∧ result.globs = read.globs := by
  dsimp only
  refine ⟨_, execStmt_locks_retScoped O passes Ruf L rank e cleanup σ ρ,
    World.gibt_foldl_spur _ _, ?_⟩
  exact World.gibt_foldl_speicher _ _

end Gabbro.Grammatik
