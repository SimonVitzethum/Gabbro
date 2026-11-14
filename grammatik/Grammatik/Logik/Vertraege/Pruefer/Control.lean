module

public import Grammatik.Logik.Vertraege.Pruefer.Current

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.VC

variable {D : Deklaration} {V : Vertrag D} {S : SperrInv D} {program : Programm D}

/-- Every call has an entry obligation. The default is the declared requires;
    the measure checker adds its cycle's strict-decrease condition. -/
structure CallPolicy (program : Programm D) where
  holds : ∀ f, World D → Env D (D.params f) → Prop
  requires : ∀ f world locals, holds f world locals → ReqAmEintritt program f world locals
  encode : ∀ f locals, Except Invarianten.Frag.Refusal { formula : QF (Observation D) //
    ∀ world, formula.denote (assignment world) ↔ holds f world locals }

def requiresPolicy (program : Programm D) : CallPolicy program where
  holds := ReqAmEintritt program
  requires := fun _ _ _ h => h
  encode := fun f locals => do
    let encoded ← translate (program.requires f) locals
    return ⟨lower encoded.payload, fun world => (lower_denote _ _).trans (encoded.bool_iff world).symm⟩

/-- Error inheritance is conditional on the CHECKED call obligation. This
    supports ordinary, requires-gated and measure-gated handlers uniformly. -/
def HandlerSafe (policy : CallPolicy program)
    (runtime : Runtime program (fun _ => []) S) (allowed : Logik D → Prop) : Prop :=
  RespektiertRahmen program runtime.calls ∧
  ∀ f world locals, policy.holds f world locals → ∀ error,
    runtime.calls f world locals = .logik error → allowed error

/-- Return goals depend on the actual value. Local updates only affect the
    three ordinary continuations; the function's entry arguments stay fixed. -/
structure Goals (D : Deklaration) (V : Vertrag D) (Γ : Ctx) where
  normal : Env D Γ → Except Invarianten.Frag.Refusal (QF (Observation D))
  escape : Env D Γ → Except Invarianten.Frag.Refusal (QF (Observation D))
  again : Env D Γ → Except Invarianten.Frag.Refusal (QF (Observation D))
  returned : ErgVal D V.erg → Except Invarianten.Frag.Refusal (QF (Observation D))
  reason : QF (Observation D)

def Goals.holds {l : Bool} {Γ : Ctx} (goals : Goals D V Γ)
    (allowed : Logik D → Prop) : Ausgang V l Γ → Prop
  | .ok world locals => denotes (goals.normal locals) world
  | .leave _ world locals => denotes (goals.escape locals) world
  | .next _ world locals => denotes (goals.again locals) world
  | .zurueck world value => denotes (goals.returned value) world
  | .why world _ => goals.reason.denote (assignment world)
  | .logik error => allowed error
  | .hardware _ => True

def Goals.endHolds {l : Bool} {Γ : Ctx} (goals : Goals D V Γ)
    (allowed : Logik D → Prop) : EndAusgang V l Γ → Prop
  | .leave _ world locals => denotes (goals.escape locals) world
  | .next _ world locals => denotes (goals.again locals) world
  | .zurueck world value => denotes (goals.returned value) world
  | .why world _ => goals.reason.denote (assignment world)
  | .logik error => allowed error
  | .hardware _ => True

def Goals.shrink {Γ : Ctx} (goals : Goals D V Γ) (τ : Ty) : Goals D V (τ :: Γ) where
  normal := fun locals => goals.normal locals.tail
  escape := fun locals => goals.escape locals.tail
  again := fun locals => goals.again locals.tail
  returned := goals.returned
  reason := goals.reason

theorem Goals.holds_shrink {l : Bool} {Γ : Ctx} (goals : Goals D V Γ)
    (τ : Ty) (allowed : Logik D → Prop) (outcome : Ausgang V l (τ :: Γ)) :
    (goals.shrink τ).holds allowed outcome ↔ goals.holds allowed outcome.schrumpf := by
  cases outcome <;> rfl

theorem Goals.endHolds_shrink {l : Bool} {Γ : Ctx} (goals : Goals D V Γ)
    (τ : Ty) (allowed : Logik D → Prop) (outcome : EndAusgang V l (τ :: Γ)) :
    (goals.shrink τ).endHolds allowed outcome ↔ goals.endHolds allowed outcome.schrumpf := by
  cases outcome <;> rfl

abbrev StatementCondition (policy : CallPolicy program)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (code : Stmt D V l Γ Λ Λ') (locals : Env D Γ) (goals : Goals D V Γ) :=
  Condition (fun runtime : Runtime program (fun _ => []) S => fun world =>
    ∀ allowed, HandlerSafe policy runtime allowed → runtime.wpS code (goals.holds allowed) world locals)

abbrev BlockCondition (policy : CallPolicy program)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (code : Block D V l Γ Λ Λ') (locals : Env D Γ) (goals : Goals D V Γ) :=
  Condition (fun runtime : Runtime program (fun _ => []) S => fun world =>
    ∀ allowed, HandlerSafe policy runtime allowed → runtime.wpB code (goals.holds allowed) world locals)

abbrev EndCondition (policy : CallPolicy program)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (code : Endblock D V l Γ Λ) (locals : Env D Γ) (goals : Goals D V Γ) :=
  Condition (fun runtime : Runtime program (fun _ => []) S => fun world =>
    ∀ allowed, HandlerSafe policy runtime allowed → runtime.wpE code (goals.endHolds allowed) world locals)

/-- Keep the checked return post on a release, including early exits. -/
def Goals.releasing {Γ : Ctx} (goals : Goals D V Γ) (fact : QF (Observation D)) : Goals D V Γ where
  normal := fun env => (goals.normal env).map (conj fact)
  escape := fun env => (goals.escape env).map (conj fact)
  again := fun env => (goals.again env).map (conj fact)
  returned := fun value => (goals.returned value).map (conj fact)
  reason := conj fact goals.reason

end Gabbro.Grammatik.Vertraege.Pruefer
