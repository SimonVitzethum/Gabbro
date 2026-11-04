module

public import Grammatik.Kern.Semantik.Semantik

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The outcome of a call is an error: a `logik` or a `hardware` outcome. (Until 2026-10-18 this
    lived with the C correspondence of the calls, `CFormenM.lean`.) -/
def RufAusgang.istFehler {f : D.Fn} : RufAusgang f → Bool
  | .logik _ => true
  | .hardware _ => true
  | _ => false

/-! ## 1. A handler that answers no hardware outcome -/

/-- A handler that answers no `hardware` outcome: a callee whose own body
    carries no oracle form and whose callees answer none either. The twin of
    `OhneLogik` (`ZielOrtGanz.lean`). -/
def OhneHardware (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)) (e : Hardware D),
    R g σ ρ ≠ RufAusgang.hardware e

/-! ## 2. The syntactic check: no oracle form -/

section Check

variable {V : Vertrag D}

mutual

/-- The statement carries no source of a `hardware` outcome: no axiom call
    and no `forever` (whose budget is `Hardware.fortschritt`). -/
def Stmt.hardwareFrei {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => t.hardwareFrei && e.hardwareFrei
  | .onOption _ p a => p.hardwareFrei && a.hardwareFrei
  | .onTag _ arms => arms.hardwareFrei
  | .onWhy _ arms => arms.hardwareFrei
  | .locks _ _ body => body.hardwareFrei
  | .breaking _ body => body.hardwareFrei
  | .traverse _ _ body => body.hardwareFrei
  | .consumeTraverse _ _ _ _ _ _ body => body.hardwareFrei
  | .retry _ _ body ueber => body.hardwareFrei && ueber.hardwareFrei
  | .forever .. => false
  | .axiomCall .. => false
  | .axiomCallElse .. => false
  | .callIndElse _ _ _ _ _ err => err.hardwareFrei
  | _ => true

/-- The block carries no source of a `hardware` outcome: no axiom bind, no
    register read, no `awaits`. -/
def Block.hardwareFrei {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => s.hardwareFrei && rest.hardwareFrei
  | .bind _ rest => rest.hardwareFrei
  | .bindCall _ _ _ _ _ rest => rest.hardwareFrei
  | .bindCallInd _ _ _ _ _ rest => rest.hardwareFrei
  | .bindCallIndElse _ _ _ _ _ err rest => err.hardwareFrei && rest.hardwareFrei
  | .bindCallElse _ _ _ _ _ err rest => err.hardwareFrei && rest.hardwareFrei
  | .bindAxiom .. => false
  | .bindAxiomElse .. => false
  | .bindAxiomOpt .. => false
  | .bindAxiomOptElse .. => false
  | .regRead .. => false
  | .regReadElse .. => false
  | .awaits .. => false
  | .exchange _ _ _ _ rest => rest.hardwareFrei
  | .narrow _ _ _ sonst rest => sonst.hardwareFrei && rest.hardwareFrei
  | .narrowRequired _ _ _ rest => rest.hardwareFrei
  | .check _ sonst rest => sonst.hardwareFrei && rest.hardwareFrei
  | .float _ _ _ _ _ rest => rest.hardwareFrei
  | .floatLit _ _ _ rest => rest.hardwareFrei
  | .floatOf _ _ _ rest => rest.hardwareFrei
  | .floatNarrow _ _ _ sonst rest => sonst.hardwareFrei && rest.hardwareFrei

def Endblock.hardwareFrei {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retWhy .. => true
  | .retScoped .. => true
  | .retWhyScoped .. => true
  | .leave .. => true
  | .next .. => true
  | .cons s rest => s.hardwareFrei && rest.hardwareFrei
  | .bind _ rest => rest.hardwareFrei
  | .bindCall _ _ _ _ _ rest => rest.hardwareFrei
  | .bindCallElse _ _ _ _ _ err rest => err.hardwareFrei && rest.hardwareFrei
  | .bindAxiom .. => false
  | .bindAxiomElse .. => false
  | .bindAxiomOpt .. => false
  | .bindAxiomOptElse .. => false
  | .regRead .. => false
  | .regReadElse .. => false
  | .awaits .. => false
  | .bindCallInd _ _ _ _ _ rest => rest.hardwareFrei
  | .bindCallIndElse _ _ _ _ _ err rest => err.hardwareFrei && rest.hardwareFrei
  | .narrow _ _ _ sonst rest => sonst.hardwareFrei && rest.hardwareFrei
  | .narrowRequired _ _ _ rest => rest.hardwareFrei
  | .exchange _ _ _ _ rest => rest.hardwareFrei
  | .ite _ t e => t.hardwareFrei && e.hardwareFrei

  | .float _ _ _ _ _ rest => rest.hardwareFrei
  | .floatLit _ _ _ rest => rest.hardwareFrei
  | .floatOf _ _ _ rest => rest.hardwareFrei
  | .floatNarrow _ _ _ sonst rest => sonst.hardwareFrei && rest.hardwareFrei
def Arms.hardwareFrei {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => b.hardwareFrei && rest.hardwareFrei

def GrundArms.hardwareFrei {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => b.hardwareFrei && rest.hardwareFrei

end

end Check

/-! ## 3. Soundness of the check -/

section HardwareFrei

variable {V : Vertrag D}

theorem Ausgang.schrumpf_hardware {l : Bool} {Γ : Ctx} {τ : Ty} {o : Ausgang V l (τ :: Γ)}
    {e : Hardware D} (h : o.schrumpf = .hardware e) : o = .hardware e := by
  cases o <;> simp_all [Ausgang.schrumpf]

theorem Ausgang.schrumpfArm_hardware {l : Bool} {Γ : Ctx} {c : Option Ty}
    {o : Ausgang V l (ArmCtx Γ c)} {e : Hardware D}
    (h : Ausgang.schrumpfArm c o = .hardware e) : o = .hardware e := by
  cases c with
  | none => exact h
  | some p => exact Ausgang.schrumpf_hardware (by simpa [Ausgang.schrumpfArm] using h)

theorem EndAusgang.schrumpf_hardware {l : Bool} {Γ : Ctx} {τ : Ty}
    {o : EndAusgang V l (τ :: Γ)} {e : Hardware D} (h : o.schrumpf = .hardware e) :
    o = .hardware e := by
  cases o <;> simp_all [EndAusgang.schrumpf]

theorem EndAusgang.zuAusgang_hardware {l : Bool} {Γ : Ctx} {o : EndAusgang V l Γ}
    {e : Hardware D} (h : o.zuAusgang = .hardware e) : o = .hardware e := by
  cases o <;> simp_all [EndAusgang.zuAusgang]

theorem Ausgang.mapWelt_hardware {l : Bool} {Γ : Ctx} {o : Ausgang V l Γ}
    {f : World D → World D} {e : Hardware D} (h : o.mapWelt f = .hardware e) :
    o = .hardware e := by
  cases o <;> simp_all [Ausgang.mapWelt]

theorem traverseLauf_ohneHardware {l : Bool} {Γ : Ctx} {τ : Ty}
    (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ e, schritt σ ρ ≠ .hardware e) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ) (e : Hardware D),
      traverseLauf (l := l) schritt inv ks σ ρ ≠ .hardware e
  | [], σ, ρ, e => by
      intro h
      simp only [traverseLauf] at h
      split at h <;> cases h
  | k :: ks, σ, ρ, e => by
      intro h
      simp only [traverseLauf] at h
      split at h
      · cases h
      · split at h
        · exact traverseLauf_ohneHardware schritt inv hs ks _ _ e h
        · exact traverseLauf_ohneHardware schritt inv hs ks _ _ e h
        · split at h <;> cases h
        · cases h
        · cases h
        · cases h
        · rename_i heq
          cases h
          exact hs _ _ _ heq

/-- A consuming run answers no hardware failure when its body never does:
    by induction on the fuel; every failing check is `.logik .schleife`. -/
theorem verbrauchLauf_ohneHardware {l : Bool} {Γ : Ctx} (t : D.Tab)
    (schritt : World D → Env D (.index (D.count t) :: Γ) →
      Ausgang V true (.index (D.count t) :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (sel : World D → Env D Γ →
      World D × Option (Wert D (.index (D.count t))) × Bool)
    (massW : World D → Env D Γ → World D × Int) (bound : Int)
    (hs : ∀ σ ρ e, schritt σ ρ ≠ .hardware e) :
    ∀ (fuel : Nat) (σ : World D) (ρ : Env D Γ) (e : Hardware D),
      verbrauchLauf (l := l) t schritt inv sel massW bound fuel σ ρ ≠ .hardware e
  | 0, σ, ρ, e => by
      intro h
      simp only [verbrauchLauf] at h
      cases h
  | n + 1, σ, ρ, e => by
      intro h
      simp only [verbrauchLauf] at h
      split at h
      · cases h
      · split at h
        · cases h
        · cases h
        · rename_i σr k _ hsel_eq
          split at h
          · rename_i σ1 ρ1 hstep_eq
            split at h
            · exact verbrauchLauf_ohneHardware t schritt inv sel massW bound hs
                n _ _ e h
            · cases h
          · rename_i σ1 ρ1 hstep_eq
            split at h
            · exact verbrauchLauf_ohneHardware t schritt inv sel massW bound hs
                n _ _ e h
            · cases h
          · rename_i σ1 ρ1 hstep_eq
            split at h
            · split at h <;> cases h
            · cases h
          · rename_i σ1 v hstep_eq
            cases h
          · rename_i σ1 r hstep_eq
            cases h
          · cases h
          · rename_i heq
            cases h
            exact hs _ _ _ heq

theorem retryLauf_ohneHardware {l : Bool} {Γ : Ctx}
    (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) (ueber : World D → Env D Γ → Ausgang V l Γ)
    (hs : ∀ σ ρ e, schritt σ ρ ≠ .hardware e) (hu : ∀ σ ρ e, ueber σ ρ ≠ .hardware e) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ) (e : Hardware D),
      retryLauf schritt bis ueber n σ ρ ≠ .hardware e
  | 0, σ, ρ, e => by
      intro h
      simp only [retryLauf] at h
      split at h
      · cases h
      · exact hu _ ρ e h
  | n + 1, σ, ρ, e => by
      intro h
      simp only [retryLauf] at h
      split at h
      · cases h
      · split at h
        · exact retryLauf_ohneHardware schritt bis ueber hs hu n _ _ e h
        · exact retryLauf_ohneHardware schritt bis ueber hs hu n _ _ e h
        · cases h
        · cases h
        · cases h
        · cases h
        · rename_i heq
          cases h
          exact hs _ _ _ heq

variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

end HardwareFrei
end Gabbro.Grammatik
