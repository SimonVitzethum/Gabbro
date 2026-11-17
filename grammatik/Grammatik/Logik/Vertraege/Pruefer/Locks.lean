module

public import Grammatik.Logik.Vertraege.Pruefer.Loops

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC
open Invarianten.Frag.Symbolic Symbolic

variable {D : Deklaration} {V : Vertrag D} {S : SperrInv D} {program : Programm D}

theorem releasing_sound {context : Context A next} {l : Bool} {Γ : Ctx}
    (goals : Symbolic.Goals (program := program) (S := S) context V Γ) (item : A)
    (runtime : Runtime program (fun _ => []) S) (allowed : Logik D → Prop)
    (lock : D.Lock) (fact : LockFormula S lock) (outcome : Ausgang V l Γ)
    (valid : (goals.releasing lock fact.formula).holds item runtime allowed outcome) :
    goals.holds item runtime allowed (freiH S lock outcome) := by
  cases outcome with
  | ok world actual =>
      have invariant := (fact.correct world).mp valid.1
      simpa only [freiH, invariant, ↓reduceIte, Symbolic.Goals.holds, Continuation.atWorld] using valid.2
  | leave h world actual =>
      have invariant := (fact.correct world).mp valid.1
      simpa only [freiH, invariant, ↓reduceIte, Symbolic.Goals.holds, Continuation.atWorld] using valid.2
  | next h world actual =>
      have invariant := (fact.correct world).mp valid.1
      simpa only [freiH, invariant, ↓reduceIte, Symbolic.Goals.holds, Continuation.atWorld] using valid.2
  | zurueck world value => exact valid.2
  | why world reason => exact valid.2
  | logik error => exact valid
  | hardware error => trivial

def lockCondition {context : Context A next} (policy : A → CallObligation program)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (lock : D.Lock) (rank : ∀ other, Res.held other ∈ Λ → D.rang other < D.rang lock)
    (body : Block D V l Γ (Res.held lock :: Λ) (Res.held lock :: Λ))
    (symbols : SymEnv D Nat Γ) (goals : Symbolic.Goals (program := program) (S := S) context V Γ)
    (fact : LockFormula S lock)
    (compiled : Symbolic.BlockCondition policy body symbols (goals.releasing lock fact.formula)) :
    Symbolic.StatementCondition policy (.locks lock rank body) symbols goals where
  formula := havocFormula (protectedObservation S lock)
    (.imp (renameProp Sum.inl (quoteQF fact.formula)) compiled.formula)
  sound := fun valuation item present runtime world valid actual realized allowed safe => by
    let acquired := runtime.environment lock world
    have ready := havocFormula_sound (protectedObservation S lock) _ valuation world acquired valid
      (fun key unchanged => acquire_frame runtime lock world key unchanged)
    have known := (fact.correct acquired).mpr (runtime.havoc lock world).2.2
    have pre := ready ((renameProp_denote Sum.inl (fun _ _ same => Sum.inl.inj same) _ _).mpr
      ((quoteQF_denote fact.formula (assignment acquired)).mpr known))
    have bodyReady := compiled.sound valuation item present runtime (acquired.nimmt lock) (by
      rw [symbolic_values_equal valuation (acquired.nimmt lock) acquired (assignment_nimmt acquired lock)]
      exact pre) actual ((symbols.realizes_world actual valuation world (acquired.nimmt lock)).mp realized) allowed safe
    exact releasing_sound goals item runtime allowed lock fact _ bodyReady

def scopedReturnCondition {context : Context A next} (policy : A → CallObligation program)
    (facts : ∀ lock, Except Frag.Refusal (LockFormula S lock))
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (expression : ErgExpr D Γ Λ V.erg) (cleanup : RueckRessourcen D V Λ)
    (symbols : SymEnv D Nat Γ) (bounded : symbols.Bounded next)
    (goals : Symbolic.Goals (program := program) (S := S) context V Γ) :
    Except Frag.Refusal (Symbolic.StatementCondition policy (.retScoped (l := l) expression cleanup) symbols goals) := do
  let releases ← cleanupFormula facts cleanup.scopes
  let post := goals.returned.atWorld (fun world => cleanup.scopes.foldl World.gibt world)
    (fun world => assignment_cleanup world cleanup.scopes)
  let returned ← Symbolic.returnCondition symbols bounded V.erg expression post
  return {
    formula := .and (renameProp Sum.inl (quoteQF releases.formula)) returned.formula
    sound := fun valuation item present runtime world valid actual realized allowed _ => by
      let read := world.lese Λ expression.orte
      have same := symbolic_values_equal valuation read world (assignment_lese _ _ _)
      have releaseAtWorld := (quoteQF_denote releases.formula (assignment world)).mp
        ((renameProp_denote Sum.inl (fun _ _ same => Sum.inl.inj same) _ _).mp valid.1)
      have cleanupReady := (releases.correct read).mp (by rw [assignment_lese]; exact releaseAtWorld)
      change scopesInvH S cleanup.scopes (world.lese Λ expression.orte) = true at cleanupReady
      have ready := returned.sound valuation item present runtime read (by rw [same]; exact valid.2)
        actual ((symbols.realizes_world actual valuation world read).mp realized)
      unfold Runtime.wpS
      simp only [execStmtH, cleanupReady, ↓reduceIte, Symbolic.Goals.holds]
      exact ready }

def scopedReasonCondition {context : Context A next} (policy : A → CallObligation program)
    (facts : ∀ lock, Except Frag.Refusal (LockFormula S lock))
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (reason : Fin V.gruende) (cleanup : RueckRessourcen D V Λ)
    (symbols : SymEnv D Nat Γ) (goals : Symbolic.Goals (program := program) (S := S) context V Γ) :
    Except Frag.Refusal (Symbolic.StatementCondition policy (.retWhyScoped (l := l) reason cleanup) symbols goals) := do
  let releases ← cleanupFormula facts cleanup.scopes
  let post ← (goals.reason.atWorld (fun world => cleanup.scopes.foldl World.gibt world)
    (fun world => assignment_cleanup world cleanup.scopes)).encode next (Nat.le_refl next) .nil trivial
  return {
    formula := .and (renameProp Sum.inl (quoteQF releases.formula)) post.formula
    sound := fun valuation item present runtime world valid actual realized allowed _ => by
      have released := (quoteQF_denote releases.formula (assignment world)).mp
        ((renameProp_denote Sum.inl (fun _ _ same => Sum.inl.inj same) _ _).mp valid.1)
      have cleanupReady := (releases.correct world).mp released
      unfold Runtime.wpS
      simp only [execStmtH, cleanupReady, ↓reduceIte, Symbolic.Goals.holds]
      exact post.sound valuation item present runtime world valid.2 .nil trivial }

end Gabbro.Grammatik.Vertraege.Pruefer
