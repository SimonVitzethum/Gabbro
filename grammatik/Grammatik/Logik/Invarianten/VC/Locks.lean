module

public import Grammatik.Logik.Invarianten.VC.Loops
public import Grammatik.Kern.Syntax.Satz.T4.Teil3

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.VC

open Frag Elim Elim.Korrekt Modell

variable {D : Deklaration} {V : Vertrag D} {S : SperrInv D}
variable {program : Programm D} {checked : D.Fn → List D.Inv}

/-- P20 supplies these by translating declared lock predicates, not contracts. -/
structure LockFormula (S : SperrInv D) (lock : D.Lock) where
  formula : QF (Observation D)
  correct : ∀ world, formula.denote (assignment world) ↔ S.inv lock world.speicher = true

def Goals.releasing {Γ : Ctx} (goals : Goals D Γ) (fact : QF (Observation D)) : Goals D Γ where
  normal := fun locals => (goals.normal locals).map (conj fact)
  escape := fun locals => (goals.escape locals).map (conj fact)
  again := fun locals => (goals.again locals).map (conj fact)
  terminal := conj fact goals.terminal

theorem denotes_map_conj (result : Except Refusal (QF (Observation D)))
    (fact : QF (Observation D)) (world : World D) :
    denotes (result.map (conj fact)) world ↔ fact.denote (assignment world) ∧ denotes result world := by
  cases result with
  | error cause => simp [Except.map, denotes]
  | ok formula => exact conj_denote _ _ _

theorem denotes_assignment (result : Except Refusal (QF (Observation D)))
    (world next : World D) (same : assignment world = assignment next) :
    denotes result world ↔ denotes result next := by
  cases result <;> simp only [denotes, same]

theorem assignment_nimmt (world : World D) (lock : D.Lock) :
    assignment (world.nimmt lock) = assignment world := by
  funext key
  cases key <;> rfl

theorem assignment_gibt (world : World D) (lock : D.Lock) :
    assignment (world.gibt lock) = assignment world := by
  funext key
  cases key <;> rfl

/-- Normal, break and continue exits all discharge the release VC. Return and
    reason exits already performed lexical cleanup, and retain the final VC. -/
theorem releasing_sound {l : Bool} {Γ : Ctx} (goals : Goals D Γ) (lock : D.Lock)
    (fact : LockFormula S lock) (outcome : Ausgang V l Γ)
    (valid : (goals.releasing fact.formula).holds outcome) :
    goals.holds (freiH S lock outcome) := by
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
  | zurueck world value => exact ((conj_denote _ _ _).mp valid).2
  | why world reason => exact ((conj_denote _ _ _).mp valid).2
  | logik error => trivial
  | hardware error => trivial

/-- The release duty is a boundary fact, separately available to P22's
    lock-move replay. Stops have no released post-state. -/
def releaseBoundary {l : Bool} {Γ : Ctx} (S : SperrInv D) (lock : D.Lock) : Ausgang V l Γ → Prop
  | .ok world _ | .leave _ world _ | .next _ world _ | .zurueck world _ | .why world _ => S.inv lock world.speicher = true
  | .logik _ | .hardware _ => True

theorem releasing_boundary {l : Bool} {Γ : Ctx} (goals : Goals D Γ) (lock : D.Lock)
    (fact : LockFormula S lock) (outcome : Ausgang V l Γ)
    (valid : (goals.releasing fact.formula).holds outcome) : releaseBoundary S lock outcome := by
  cases outcome with
  | ok world locals => exact (fact.correct world).mp ((denotes_map_conj _ _ _).mp valid).1
  | leave h world locals => exact (fact.correct world).mp ((denotes_map_conj _ _ _).mp valid).1
  | next h world locals => exact (fact.correct world).mp ((denotes_map_conj _ _ _).mp valid).1
  | zurueck world value => exact (fact.correct world).mp ((conj_denote _ _ _).mp valid).1
  | why world reason => exact (fact.correct world).mp ((conj_denote _ _ _).mp valid).1
  | logik error => trivial
  | hardware error => trivial

def protectedObservation (S : SperrInv D) (lock : D.Lock) : Observation D → Bool
  | .glob name => decide (.inr name ∈ S.orte lock)
  | .slot table _ _ => decide (.inl table ∈ S.orte lock)

theorem acquire_frame (runtime : Runtime program checked S) (lock : D.Lock)
    (world : World D) (key : Observation D) (unchanged : protectedObservation S lock key = false) :
    assignment world key = assignment (runtime.environment lock world) key := by
  have frame := (runtime.havoc lock world).2.1
  cases key with
  | glob name =>
      have absent : Sum.inr name ∉ S.orte lock := by simpa [protectedObservation] using unchanged
      exact congrArg (scalarValue (D.gtyp name)) (frame (.inr name) absent).symm
  | slot table field index =>
      have absent : Sum.inl table ∉ S.orte lock := by simpa [protectedObservation] using unchanged
      exact congrArg (scalarValue (D.typ table field)) (congrFun (congrFun (frame (.inl table) absent) index) field).symm

/-- Acquire havocs the protected footprint and assumes only the checked lock
    predicate and decoded ranges. Release is owed on every state-bearing exit. -/
def lockCondition {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (lock : D.Lock) (rank : ∀ other, Res.held other ∈ Λ → D.rang other < D.rang lock)
    (body : Block D V l Γ (Res.held lock :: Λ) (Res.held lock :: Λ))
    (locals : Env D Γ) (goals : Goals D Γ) (fact : LockFormula S lock)
    (compiled : BlockCondition program checked S body locals (goals.releasing fact.formula)) :
    StatementCondition program checked S (.locks lock rank body) locals goals where
  formula := havoc (protectedObservation S lock)
    (lower (.imp (.and (typeFacts (qfKeys fact.formula ++ qfKeys compiled.formula))
      (quoteQF fact.formula)) (quoteQF compiled.formula)))
  sound := fun runtime world valid => by
    let acquired := runtime.environment lock world
    have ready := havoc_sound (protectedObservation S lock) _ (assignment world) (assignment acquired)
      valid (fun key _ unchanged => acquire_frame runtime lock world key unchanged)
    have known := (fact.correct acquired).mpr (runtime.havoc lock world).2.2
    have pre := (quoteQF_denote _ _).mp (((lower_denote _ _).mp ready)
      ⟨typeFacts_sound _ acquired, (quoteQF_denote _ _).mpr known⟩)
    have bodyReady := compiled.sound runtime (acquired.nimmt lock) (by
      rw [assignment_nimmt]
      exact pre)
    exact releasing_sound goals lock fact _ bodyReady

/-- With no reified lock predicate, no arithmetic fact is learned at acquire.
    The old semantic release check may stop with logik; proving absence of
    that stop remains user logic. This rule proves only the enclosing writer's
    declared Expr invariants, not an opaque lock predicate. -/
theorem opaque_release_sound {l : Bool} {Γ : Ctx} (goals : Goals D Γ) (lock : D.Lock)
    (outcome : Ausgang V l Γ) (valid : goals.holds outcome) :
    goals.holds (freiH S lock outcome) := by
  cases outcome with
  | ok world locals | leave h world locals | next h world locals =>
      cases invariant : S.inv lock world.speicher with
      | false => simp only [freiH, invariant, Bool.false_eq_true, ↓reduceIte, Goals.holds]
      | true =>
          simpa only [freiH, invariant, ↓reduceIte, Goals.holds] using
            (denotes_assignment _ world (world.gibt lock) (assignment_gibt world lock).symm).mp valid
  | zurueck world value => exact valid
  | why world reason => exact valid
  | logik error => trivial
  | hardware error => trivial

def opaqueLockCondition {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (lock : D.Lock) (rank : ∀ other, Res.held other ∈ Λ → D.rang other < D.rang lock)
    (body : Block D V l Γ (Res.held lock :: Λ) (Res.held lock :: Λ))
    (locals : Env D Γ) (goals : Goals D Γ)
    (compiled : BlockCondition program checked S body locals goals) :
    StatementCondition program checked S (.locks lock rank body) locals goals where
  formula := havoc (protectedObservation S lock)
    (lower (.imp (typeFacts (qfKeys compiled.formula)) (quoteQF compiled.formula)))
  sound := fun runtime world valid => by
    let acquired := runtime.environment lock world
    have ready := havoc_sound (protectedObservation S lock) _ (assignment world) (assignment acquired)
      valid (fun key _ unchanged => acquire_frame runtime lock world key unchanged)
    have pre := (quoteQF_denote _ _).mp (((lower_denote _ _).mp ready) (typeFacts_sound _ acquired))
    have bodyReady := compiled.sound runtime (acquired.nimmt lock) (by
      rw [assignment_nimmt]
      exact pre)
    exact opaque_release_sound goals lock _ bodyReady

/-- U003 is inherited from the canonical declaration: a writer reading an
    owed invariant holds every lock required by that predicate. No invariant
    truth is assumed merely because a lock is held inside a running writer. -/
theorem owed_invariant_read_held (program : Programm D) (f : D.Fn) (item : D.Inv)
    (world : World D)
    (held : HeldIn (Signatur.anfang D (D.signatur f)) world.haelt)
    (owed : schuldet f item = true) : HeldIn (invSicht D item) world.haelt :=
  heldIn_invarianten program f held item owed

end Gabbro.Grammatik.Invarianten.VC
