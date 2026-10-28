import Grammatik.Bausteine.Arena.Ownership.Source.Allocation
import Grammatik.Bausteine.Arena.Ownership.Witness

namespace Gabbro.Grammatik.ArenaOwnership.Source.Witness

open ArenaOwnership.Witness (D A world state caller callee handle tab_right glob_right free_ok agrees)

abbrev Γ : Ctx := [Ty.index 4, Ty.index 4]

def context : Context :=
  ⟨[some 0, some 0], fun i => if i = 0 then some .owned else none, 1⟩
def ghosts : Ghost := fun i => if i = 0 then some handle else none
def rho : Env D Γ := .cons ⟨0, by decide, by decide⟩ (.cons ⟨0, by decide, by decide⟩ .nil)

theorem bounded : context.bounded := by
  constructor
  · intro i hi
    have hne : i ≠ 0 := by change 1 ≤ i at hi; omega
    simp only [context, hne, ↓reduceIte]
  · intro ref hm i hi
    have he : ref = some 0 := by simpa [context] using hm
    have hz : i = 0 := (Option.some.inj (he.symm.trans hi)).symm
    subst i
    decide

theorem references : References context ghosts rho := by
  refine ⟨rfl, ?_⟩
  intro τ x i hi
  cases x with
  | here =>
    have hz : i = 0 := by simpa [Context.reference, context, Var.unten] using hi.symm
    subst i
    exact ⟨handle, rfl, rfl⟩
  | there x =>
    cases x with
    | here =>
      have hz : i = 0 := by simpa [Context.reference, context, Var.unten] using hi.symm
      subst i
      exact ⟨handle, rfl, rfl⟩
    | there x => cases x

theorem rights : Rights context ghosts state caller := by
  constructor
  · intro i mode hi
    by_cases hz : i = 0
    · subst i
      have hm : mode = .owned := by simpa [context] using hi.symm
      subst mode
      exact ⟨handle, rfl, ArenaOwnership.Witness.owns⟩
    · simp only [context, hz, ↓reduceIte, reduceCtorEq] at hi
  · intro i j p q hi hj hne _ h k hg hk
    have hiz : i = 0 := by
      by_contra hn
      simp only [context, hn, ↓reduceIte, reduceCtorEq] at hi
    have hjz : j = 0 := by
      by_contra hn
      simp only [context, hn, ↓reduceIte, reduceCtorEq] at hj
    exact False.elim (hne (hiz.trans hjz.symm))

theorem realizes : Realizes context ghosts A caller state world rho :=
  ⟨agrees, free_ok, bounded, references, rights⟩

def readAlias : Expr D Γ [] (D.typ A.tab A.feld) :=
  .slot A.tab A.feld (.var (.there .here)) tab_right

theorem alias_read_accepted : checkExpression A context readAlias = true := by decide
theorem consume_name : consume (D := D) context (.var (Λ := []) (.here : Var Γ _)) = some (context.kill 0, 0) := rfl
theorem alias_read_refused : checkExpression A (context.kill 0) readAlias = false := by decide
theorem second_consume_refused : consume (D := D) (context.kill 0) (.var (Λ := []) (.there .here : Var Γ _)) = none := rfl

/-- The checker invalidates the other alias after a source free and the
computed context really describes the world of the executed G block. -/
theorem checked_release_witness (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) :
    ∃ (s' : State) (σ' : World D),
      execBlock (V := vertragVon D ()) (l := false) O passes R
        (Block.freiVar A (.here : Var Γ _) rfl tab_right rfl (glob_right _) .nil) world rho = .ok σ' rho ∧
      Realizes (context.kill 0) ghosts A caller s' σ' rho ∧
      checkExpression A (context.kill 0) readAlias = false ∧ (∀ frame, ¬ s'.access frame handle) := by
  obtain ⟨s', σ', h, hrun, hreal, hg, hdead⟩ := checked_release (V := vertragVon D ()) (l := false)
    O passes R A context (context.kill 0) ghosts caller state world rho (.here : Var Γ _) 0
    rfl tab_right rfl (glob_right _) .nil consume_name realizes
  have hh : h = handle := by simpa [ghosts] using hg.symm
  subst h
  exact ⟨s', σ', hrun, hreal, alias_read_refused, hdead⟩

/-- Rebinding a fresh slot does not give the old aliases its new origin,
even if all three runtime index values happen to be zero. -/
def readOldAfterReuse : Expr D (Ty.index 4 :: Γ) [] (D.typ A.tab A.feld) :=
  .slot A.tab A.feld (.var (.there (.there .here))) tab_right

def readNewAfterReuse : Expr D (Ty.index 4 :: Γ) [] (D.typ A.tab A.feld) :=
  .slot A.tab A.feld (.var .here) tab_right

theorem reuse_cannot_restore_alias :
    checkExpression A (context.kill 0).bindFresh readOldAfterReuse = false ∧
    checkExpression A (context.kill 0).bindFresh readNewAfterReuse = true := by decide

theorem borrowed_parameter_cannot_be_consumed :
    consume (D := D) { context with rights := fun i => if i = 0 then some .borrowed else none }
      (.var (Λ := []) (.here : Var Γ _)) = none := rfl

#print axioms checked_release_witness
#print axioms reuse_cannot_restore_alias

end Gabbro.Grammatik.ArenaOwnership.Source.Witness
