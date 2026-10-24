import Grammatik.Bausteine.Arena.Ownership.World

/-! Ownership specifications at the real `rufAt` boundary. Argument and result
values occur in the specification: this is not the carrier-level `own` mark.
The recursive theorem derives callee respect from checked bodies, at every fuel;
it does not assume that the concrete call handler preserves ownership. -/

namespace Gabbro.Grammatik.ArenaOwnership

variable {D : Deklaration}

inductive Answer (f : D.Fn) where
  | value (v : ErgVal D (D.erg f))
  | reason (r : Fin (D.gruende f))

/-- Resource pre/postconditions are independent of trace bookkeeping. They
refer to actual parameter values and the actual value/reason returned. -/
structure Contract (D : Deklaration) (f : D.Fn) where
  requires : Frame → State → Env D (D.params f) → Prop
  ensures : Frame → State → Env D (D.params f) → State → Answer f → Prop

def Contract.post (A : FreiForm D) (C : Contract D f) (frame : Frame)
    (s : State) (ρ : Env D (D.params f)) : RufAusgang f → Prop
  | .ok σ' v => ∃ s', s'.agrees A σ' ∧ A.FreiOk σ' ∧ C.ensures frame s ρ s' (.value v)
  | .why σ' r => ∃ s', s'.agrees A σ' ∧ A.FreiOk σ' ∧ C.ensures frame s ρ s' (.reason r)
  | .logik _ => True
  | .hardware _ => True

def Contract.bodyPost (A : FreiForm D) (C : Contract D f) (frame : Frame)
    (s : State) (ρ : Env D (D.params f)) :
    EndAusgang (vertragVon D f) false (D.params f) → Prop
  | .zurueck σ' v => ∃ s', s'.agrees A σ' ∧ A.FreiOk σ' ∧ C.ensures frame s ρ s' (.value v)
  | .why σ' r => ∃ s', s'.agrees A σ' ∧ A.FreiOk σ' ∧ C.ensures frame s ρ s' (.reason r)
  | .leave h _ _ => False.elim (Bool.noConfusion h)
  | .next h _ _ => False.elim (Bool.noConfusion h)
  | .logik _ => True
  | .hardware _ => True

/-- A returning block has the same result contract as an end block, and
cannot silently fall through or leave its enclosing loop. -/
def Contract.blockPost (A : FreiForm D) (C : Contract D f) (frame : Frame)
    (s : State) (ρ : Env D (D.params f)) {l : Bool} {Γ : Ctx} :
    Ausgang (vertragVon D f) l Γ → Prop
  | .zurueck σ' v => ∃ s', s'.agrees A σ' ∧ A.FreiOk σ' ∧ C.ensures frame s ρ s' (.value v)
  | .why σ' r => ∃ s', s'.agrees A σ' ∧ A.FreiOk σ' ∧ C.ensures frame s ρ s' (.reason r)
  | .ok _ _ => False
  | .leave _ _ _ => False
  | .next _ _ _ => False
  | .logik _ => True
  | .hardware _ => True

theorem Contract.blockPost_shrink (A : FreiForm D) (C : Contract D f) (frame : Frame)
    (s : State) (ρ : Env D (D.params f)) {l : Bool} {Γ : Ctx} {τ : Ty}
    (out : Ausgang (vertragVon D f) l (τ :: Γ)) (hp : C.blockPost A frame s ρ out) :
    C.blockPost A frame s ρ out.schrumpf := by
  cases out <;> exact hp

theorem Contract.blockPost_after_stmt (A : FreiForm D) (C : Contract D f) (frame : Frame)
    (s : State) (entry : Env D (D.params f)) (O : Orakel D) (passes : Nat)
    (R : ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (stmt : Stmt D (vertragVon D f) l Γ Λ Λ') (σ : World D) (ρ : Env D Γ)
    (hp : C.blockPost A frame s entry (execStmt O passes R stmt σ ρ)) :
    C.blockPost A frame s entry (execBlock O passes R (.cons stmt .nil) σ ρ) := by
  simp only [execBlock]
  generalize he : execStmt O passes R stmt σ ρ = out at hp ⊢
  cases out <;> exact hp

theorem Contract.blockPost_ite (A : FreiForm D) (C : Contract D f) (frame : Frame)
    (s : State) (entry : Env D (D.params f)) (O : Orakel D) (passes : Nat)
    (R : ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (t e : Block D (vertragVon D f) l Γ Λ Λ') (σ : World D) (ρ : Env D Γ)
    (hp : C.blockPost A frame s entry
      (if wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) then
        execBlock O passes R t (σ.lese Λ c.orte) ρ
      else execBlock O passes R e (σ.lese Λ c.orte) ρ)) :
    C.blockPost A frame s entry (execBlock O passes R (.cons (.ite c t e) .nil) σ ρ) :=
  Contract.blockPost_after_stmt A C frame s entry O passes R (.ite c t e) σ ρ hp

def Respects (A : FreiForm D) (C : ∀ f, Contract D f)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ f frame s σ ρ, s.agrees A σ → A.FreiOk σ → (C f).requires frame s ρ →
    (∀ σ' v, R f σ ρ = .ok σ' v → (C f).post A frame s ρ (.ok σ' v)) ∧
    (∀ σ' r, R f σ ρ = .why σ' r → (C f).post A frame s ρ (.why σ' r))

/-- The body obligation that the source ownership judgment must discharge.
It is universally quantified over the call handler; the recursive theorem
below instantiates it with the actual handler, not an assumed callee effect. -/
def Bodies (P : Programm D) (A : FreiForm D) (C : ∀ f, Contract D f)
    (O : Orakel D) (passes : Nat) : Prop :=
  ∀ R, Respects A C R → ∀ f frame s σ ρ,
    s.agrees A σ → A.FreiOk σ → (C f).requires frame s ρ →
      (C f).bodyPost A frame s ρ (execEnd O passes R (P.rumpf f) σ ρ)

theorem free_invariant_reads {A : FreiForm D} {σ : World D} (hf : A.FreiOk σ)
    (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) : A.FreiOk (σ.lese Λ os) :=
  A.freiOk_gleich (σ := σ) (σ' := σ.lese Λ os) rfl (fun _ => rfl) rfl hf

theorem fold_reads {A : FreiForm D} {σ : World D} {s : State}
    (ha : s.agrees A σ) (hf : A.FreiOk σ) (is : List D.Inv)
    (rs : D.Inv → List (Res D)) (os : D.Inv → List (D.Tab ⊕ D.Glob)) :
    s.agrees A (is.foldl (fun w i => w.lese (rs i) (os i)) σ) ∧
      A.FreiOk (is.foldl (fun w i => w.lese (rs i) (os i)) σ) := by
  induction is generalizing σ with
  | nil => exact ⟨ha, hf⟩
  | cons i is ih => exact ih (State.agrees_reads ha (rs i) (os i)) (free_invariant_reads hf _ _)

/-- Every actual call, including nested/recursive calls and declared reason
returns, obeys the value-dependent ownership contract once the bodies have
been checked. No ownership-preserving oracle premise is introduced. -/
theorem rufAt_ownership (P : Programm D) (A : FreiForm D) (C : ∀ f, Contract D f)
    (O : Orakel D) (passes : Nat) (hb : Bodies P A C O passes) :
    ∀ n, Respects A C (rufAt P O passes n) := by
  intro n
  induction n with
  | zero =>
    intro f frame s σ ρ _ _ _
    constructor
    · intro _ _ h; cases h
    · intro _ _ h; cases h
  | succ n ih =>
    intro f frame s σ ρ ha hf hpre
    have ha1 := State.agrees_reads ha (Signatur.anfang D (D.signatur f)) (P.requires f).orte
    have hf1 := free_invariant_reads hf (Signatur.anfang D (D.signatur f)) (P.requires f).orte
    have hout := hb _ ih f frame s _ ρ ha1 hf1 hpre
    constructor
    · intro σ' v hrun
      simp only [rufAt] at hrun
      split at hrun
      · cases hrun
      · revert hrun hout
        generalize execEnd O passes (rufAt P O passes n) (P.rumpf f)
          (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ = out
        cases out with
        | zurueck σ2 v2 =>
          intro hout hrun
          obtain ⟨s', ha', hf', hens⟩ := hout
          simp only at hrun
          split at hrun
          · cases hrun
          · split at hrun
            · cases hrun
            · cases hrun
              obtain ⟨ha2, hf2⟩ := fold_reads
                (State.agrees_reads ha' (vertragVon D f).ende (P.ensures f).orte)
                (free_invariant_reads hf' (vertragVon D f).ende (P.ensures f).orte)
                (D.invs.filter (schuldet f)) (invSicht D) (fun i => (P.invariante i).orte)
              exact ⟨s', ha2, hf2, hens⟩
        | why σ2 r => intro _ h; cases h
        | leave h _ _ => exact False.elim (Bool.noConfusion h)
        | next h _ _ => exact False.elim (Bool.noConfusion h)
        | logik _ => intro _ h; cases h
        | hardware _ => intro _ h; cases h
    · intro σ' r hrun
      simp only [rufAt] at hrun
      split at hrun
      · cases hrun
      · revert hrun hout
        generalize execEnd O passes (rufAt P O passes n) (P.rumpf f)
          (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ = out
        cases out with
        | zurueck σ2 v2 =>
          intro _ hrun
          simp only at hrun
          split at hrun
          · cases hrun
          · split at hrun <;> cases hrun
        | why σ2 r2 => intro hout h; cases h; exact hout
        | leave h _ _ => exact False.elim (Bool.noConfusion h)
        | next h _ _ => exact False.elim (Bool.noConfusion h)
        | logik _ => intro _ h; cases h
        | hardware _ => intro _ h; cases h

#print axioms rufAt_ownership

end Gabbro.Grammatik.ArenaOwnership
