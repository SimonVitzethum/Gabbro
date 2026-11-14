module

public import Grammatik.Logik.Vertraege.Pruefer.Loops

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.VC

variable {D : Deklaration} {V : Vertrag D} {S : SperrInv D} {program : Programm D}
variable {policy : CallPolicy program}

/-- Release is checked for every state-bearing exit. A failed release cannot
    hide behind the permissive error branch of the old invariant-only WP. -/
theorem releasing_sound {l : Bool} {Γ : Ctx} (goals : Goals D V Γ) (allowed : Logik D → Prop)
    (lock : D.Lock) (fact : LockFormula S lock) (outcome : Ausgang V l Γ)
    (valid : (goals.releasing fact.formula).holds allowed outcome) :
    goals.holds allowed (freiH S lock outcome) := by
  cases outcome with
  | ok world locals =>
      have parts := (denotes_map_conj _ _ _).mp valid
      have invariant := (fact.correct world).mp parts.1
      simpa only [freiH, invariant, ↓reduceIte, Goals.holds] using
        (denotes_assignment _ world (world.gibt lock) (assignment_gibt world lock).symm).mp parts.2
  | leave h world locals =>
      have parts := (denotes_map_conj _ _ _).mp valid
      have invariant := (fact.correct world).mp parts.1
      simpa only [freiH, invariant, ↓reduceIte, Goals.holds] using
        (denotes_assignment _ world (world.gibt lock) (assignment_gibt world lock).symm).mp parts.2
  | next h world locals =>
      have parts := (denotes_map_conj _ _ _).mp valid
      have invariant := (fact.correct world).mp parts.1
      simpa only [freiH, invariant, ↓reduceIte, Goals.holds] using
        (denotes_assignment _ world (world.gibt lock) (assignment_gibt world lock).symm).mp parts.2
  | zurueck world value => exact ((denotes_map_conj _ _ _).mp valid).2
  | why world reason => exact ((conj_denote _ _ _).mp valid).2
  | logik error => exact valid
  | hardware error => trivial

/-- Acquire uses only the declared lock formula, decoded ranges and frame.
    Missing expression evidence is a refusal in the strengthened checker. -/
def lockCondition {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (lock : D.Lock) (rank : ∀ other, Res.held other ∈ Λ → D.rang other < D.rang lock)
    (body : Block D V l Γ (Res.held lock :: Λ) (Res.held lock :: Λ))
    (locals : Env D Γ) (goals : Goals D V Γ) (fact : LockFormula S lock)
    (compiled : BlockCondition (S := S) policy body locals (goals.releasing fact.formula)) :
    StatementCondition (S := S) policy (.locks lock rank body) locals goals where
  formula := havoc (protectedObservation S lock)
    (lower (.imp (.and (typeFacts (qfKeys fact.formula ++ qfKeys compiled.formula))
      (quoteQF fact.formula)) (quoteQF compiled.formula)))
  sound := fun runtime world valid allowed safe => by
    let acquired := runtime.environment lock world
    have ready := havoc_sound (protectedObservation S lock) _ (assignment world) (assignment acquired)
      valid (fun key _ unchanged => acquire_frame runtime lock world key unchanged)
    have known := (fact.correct acquired).mpr (runtime.havoc lock world).2.2
    have pre := (quoteQF_denote _ _).mp (((lower_denote _ _).mp ready)
      ⟨typeFacts_sound _ acquired, (quoteQF_denote _ _).mpr known⟩)
    have bodyReady := compiled.sound runtime (acquired.nimmt lock) (by
      rw [assignment_nimmt]
      exact pre) allowed safe
    exact releasing_sound goals allowed lock fact _ bodyReady

/-- Lexical cleanup checks every owed lock before returning the actual value. -/
def scopedReturnCondition (budget : Nat)
    (facts : ∀ lock, Except Refusal (LockFormula S lock))
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (expression : ErgExpr D Γ Λ V.erg) (cleanup : RueckRessourcen D V Λ)
    (locals : Env D Γ) (goals : Goals D V Γ) :
    Except Refusal (StatementCondition (S := S) policy (.retScoped expression cleanup) locals goals) := do
  let releases ← cleanupFormula facts cleanup.scopes
  let returned ← returnCondition (S := S) budget expression locals goals
  return { formula := conj releases.formula returned.formula
      sound := fun runtime world valid allowed safe => by
        have parts := (conj_denote _ _ _).mp valid
        let read := world.lese Λ expression.orte
        have same : assignment read = assignment world := assignment_lese _ _ _
        have cleanupReady := (releases.correct read).mp (by rw [same]; exact parts.1)
        have ready := returned.sound runtime read (by rw [same]; exact parts.2)
        unfold Runtime.wpS
        simp only [execStmtH, cleanupReady, ↓reduceIte, Goals.holds]
        exact (denotes_assignment _ read (cleanup.scopes.foldl World.gibt read)
          (assignment_cleanup read cleanup.scopes).symm).mp ready }

end Gabbro.Grammatik.Vertraege.Pruefer
