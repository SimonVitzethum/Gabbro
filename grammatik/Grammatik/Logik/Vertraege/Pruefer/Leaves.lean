module

public import Grammatik.Logik.Vertraege.Pruefer.Control

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.VC

variable {D : Deklaration} {V : Vertrag D} {S : SperrInv D} {program : Programm D}
variable (policy : CallPolicy program)

/-- A range check selects its exact typed value or the explicit failure arm.
    The original expression remains correlated with the selected branch. -/
def narrowingCondition (budget : Nat) (expression : Expr D Γ Λ (.int lo hi))
    (low high : Int) (locals : Env D Γ)
    (success : Zahl low high → Runtime program (fun _ => []) S → World D → Prop)
    (failure : Runtime program (fun _ => []) S → World D → Prop)
    (compile : ∀ value, Except Frag.Refusal (Condition (success value)))
    (compileFailure : Except Frag.Refusal (Condition failure)) :
    Except Frag.Refusal (Condition (fun runtime world =>
      let value := eval world expression world locals
      if fits : low ≤ value.n ∧ value.n ≤ high then
        success ⟨value.n, fits.1, fits.2⟩ runtime world else failure runtime world)) :=
  localSelect budget expression locals
    (fun value runtime world =>
      if fits : low ≤ value.n ∧ value.n ≤ high then
        success ⟨value.n, fits.1, fits.2⟩ runtime world else failure runtime world)
    (fun value => by
      by_cases fits : low ≤ value.n ∧ value.n ≤ high
      · simpa only [dif_pos fits] using compile ⟨value.n, fits.1, fits.2⟩
      · simpa only [dif_neg fits] using compileFailure)

/-- A return is checked against its actual typed result. Complete finite
    domains are budgeted; an oversized range is refused, never sampled. -/
def returnCondition (budget : Nat) {Γ : Ctx} {Λ : List (Res D)} {result : Option Ty}
    (expression : ErgExpr D Γ Λ result) (locals : Env D Γ)
    (returned : ErgVal D result → Except Invarianten.Frag.Refusal (QF (Observation D))) :
    Except Invarianten.Frag.Refusal (Condition (fun (_ : Runtime program (fun _ => []) S) world =>
      denotes (returned (evalErg world expression world locals)) world)) :=
  match result, expression, returned with
  | none, .empty, returned => requireCondition (returned ())
  | some _, .val (.var name), returned => requireCondition (returned (locals.get name))
  | some _, .val (.widen low high body), returned =>
      returnCondition budget (.val body) locals (fun value => returned (Zahl.weiter low high value))
  | some _, .val expression, returned =>
      localSelect budget expression locals
        (fun value _ world => denotes (returned value) world)
        (fun value => requireCondition (returned value))
termination_by sizeOf expression
decreasing_by all_goals simp_wf

/-- Scalar updates reuse P20's substitution; the post is stronger at logic
    stops and value returns. Unsupported leaves have no accepting fallback. -/
def leafCondition (budget : Nat) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (code : Stmt D V l Γ Λ Λ') (locals : Env D Γ) (goals : Goals D V Γ) :
    Except Invarianten.Frag.Refusal (StatementCondition (S := S) policy code locals goals) :=
  match code with
  | .assignGlob name expression _ _ | .publish name expression _ _ _ _ => do
      match h : goals.normal locals with
      | .error cause => .error cause
      | .ok normal => do
          let pre ← scalarWP expression locals (.glob name) normal
          return {
              formula := pre.formula
              sound := fun runtime world valid allowed safe => by
                unfold Runtime.wpS
                simp only [execStmtH, Goals.holds, h, denotes]
                rw [assignment_schreibGlob]
                apply pre.sound
                rw [assignment_lese]
                exact valid }
  | .assignSlot table field index expression _ _ | .assignThru _ table _ field index expression _ _
    | .assignThruOwn _ table _ field index expression _ _ _ _ _ _ _ => do
      match h : goals.normal locals with
      | .error cause => .error cause
      | .ok normal => do
          let encodedIndex ← translate index locals
          let offset ← encodedIndex.constantIndex
          let pre ← scalarWP expression locals (.slot table field offset.val) normal
          return {
              formula := pre.formula
              sound := fun runtime world valid allowed safe => by
                unfold Runtime.wpS
                simp only [execStmtH, Goals.holds, h, denotes]
                rw [assignment_schreibSlot, offset.property]
                apply pre.sound
                rw [assignment_lese]
                exact valid }
  | .assignVar name expression => do
      let pre ← localSelect budget expression locals
        (fun value _ world => denotes (goals.normal (locals.set name value)) world)
        (fun value => requireCondition (goals.normal (locals.set name value)))
      return (pre.read Λ expression.orte).map (fun _ _ valid _ _ => valid)
  | .shift (lo := lo) (hi := hi) table field kind index source destination bounded _ _ access => do
      match h : goals.normal locals with
      | .error cause => .error cause
      | .ok normal => do
          let encodedIndex ← translate index locals
          let offset ← encodedIndex.constantIndex
          let observed ← translateScalar (.slot table field index access) locals
          let post := normal.subst (.slot table field offset.val) (.konst destination)
          return {
              formula := lower (.and (.eq observed.term (.konst source)) (quoteQF post))
              sound := fun runtime world valid allowed _ => by
                have transport {a b : Ty} (same : a = b) (value : Wert D a) :
                    scalarValue b (same ▸ value) = scalarValue a value := by
                  cases same
                  rfl
                have reverseTransport {a b : Ty} (same : a = b) (value : Wert D b) :
                    scalarValue a (same ▸ value) = scalarValue b value := by
                  cases same
                  rfl
                let read := world.lese Λ (.inl table :: index.orte)
                have parts := (lower_denote _ (assignment read)).mp (by
                  rw [assignment_lese]
                  exact valid)
                have taken : (kind ▸ read.slots table (eval read index read locals).n field).n = source := by
                  have observedValue := parts.1
                  change observed.term.denote (assignment read) = source at observedValue
                  rw [observed.correct read] at observedValue
                  change scalarValue _ (read.slots table (eval read index read locals).n field) = source at observedValue
                  exact (transport kind _).trans observedValue
                dsimp only [read] at taken
                unfold Runtime.wpS
                simp only [execStmtH, taken, ↓reduceIte, Goals.holds, h, denotes]
                rw [assignment_schreibSlot, offset.property]
                have stored : scalarValue (D.typ table field)
                    (kind ▸ (show Wert D (.int lo hi) from ⟨destination, bounded.1, bounded.2⟩)) = destination :=
                  reverseTransport kind _
                rw [stored]
                exact (subst_denote _ _ normal (assignment read)).mp ((quoteQF_denote _ _).mp parts.2) }
  | .advances .. | .retires .. | .transition .. => do
      let pre ← requireCondition (program := program) (checked := fun _ => []) (S := S) (goals.normal locals)
      return pre.map (fun _ _ ready _ _ => ready)
  | .regWrite _ _ expression => do
      let pre ← requireCondition (program := program) (checked := fun _ => []) (S := S) (goals.normal locals)
      return (pre.read Λ expression.orte).map (fun _ _ ready _ _ => ready)
  | .ret expression _ => do
      let pre ← returnCondition (S := S) budget expression locals goals.returned
      return (pre.read Λ expression.orte).map (fun _ _ valid _ _ => valid)
  | .retWhy _ _ => .ok
      { formula := goals.reason
        sound := fun _ _ valid _ _ => valid }
  | .leave _ => do
      let pre ← requireCondition (program := program) (checked := fun _ => []) (S := S) (goals.escape locals)
      return pre.map (fun _ _ valid _ _ => valid)
  | .next _ => do
      let pre ← requireCondition (program := program) (checked := fun _ => []) (S := S) (goals.again locals)
      return pre.map (fun _ _ valid _ _ => valid)
  | .assignSlotRef .. => .error (.unsupported "contract reference store needs a tracked cell identity")
  | .putBytes .. => .error (.unsupported "contract byte store needs bytewise observation substitution")
  | .onOption .. => .error (.unsupported "contract option dispatch needs a typed payload observation")
  | .onTag .. => .error (.unsupported "contract tagged dispatch needs a typed payload observation")
  | .callInd .. | .callIndElse .. =>
      .error (.unsupported "contract indirect call needs a checked finite target dispatch")
  | .axiomCall .. | .axiomCallElse .. =>
      .error (.unsupported "contract oracle call needs quantified answer and poststate observations")
  | .forever .. => .error (.unsupported "contract forever loop needs a checked inductive invariant")
  | .consumeTraverse .. => .error (.unsupported "contract consuming traversal needs a checked membership and measure invariant")
  | _ => .error (.unsupported "contract structured statement needs the recursive control compiler")

end Gabbro.Grammatik.Vertraege.Pruefer
