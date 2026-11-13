module

public import Grammatik.Logik.Invarianten.Frag.Support
public import Grammatik.Kern.Semantik.Semantik.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag

variable {D : Deklaration}

/-- A canonical state observation. Repeated reads of the same cell use the SAME
    variable, even when their access proofs or integer widening differ. String
    observations denote their length, never their contents. Assignments in the QE
    core are unconstrained integers; writer VCs must add the model's type bounds
    before counterexample assignments can be reconstructed as typed worlds. -/
inductive Observation (D : Deklaration) where
  | glob (name : D.Glob)
  | slot (table : D.Tab) (field : D.Feld table) (index : Int)
  deriving DecidableEq

def observationType : Observation D → Ty
  | .glob name => D.gtyp name
  | .slot table field _ => D.typ table field

/-- Only these memory representations can occur in a successful translation. -/
def ScalarObservation (key : Observation D) : Prop :=
  match observationType key with
  | .int _ _ | .str _ => True
  | _ => False

/-- Only the integer and string branches are admitted by the translator. The
    remaining branches make the assignment total without accepting those types. -/
def scalarValue : (τ : Ty) → Wert D τ → Int
  | .int _ _, value => value.n
  | .str _, value => value.val.length
  | _, _ => 0

def assignment (world : World D) : Assignment (Observation D)
  | .glob name => scalarValue (D.gtyp name) (world.globs name)
  | .slot table field index => scalarValue (D.typ table field) (world.slots table index field)

/-- A named declaration refusal, with an expression path added on propagation. -/
inductive Refusal where
  | outsideCarriers
  | atomicCarrier
  | nonlinear
  | crossEntry
  | unsupported (ctorName : String)
  | within (part : String) (cause : Refusal)
  deriving DecidableEq, Repr

def Refusal.message : Refusal → String
  | .outsideCarriers => "invariant reads outside its declared carriers"
  | .atomicCarrier => "invariant reads an atomic carrier; use a guarded scalar carrier"
  | .nonlinear => "variable multiplication; use a literal coefficient"
  | .crossEntry => "cross-entry relation; use one local predicate per slot"
  | .unsupported ctorName => "unsupported invariant constructor: " ++ ctorName
  | .within part cause => part ++ ": " ++ cause.message

/-- Encodings exist for integers, Boolean predicates, and string lengths only. -/
def Payload (D : Deklaration) : Ty → Type
  | .int _ _ => LTerm (Observation D)
  | .bool => LProp (Observation D)
  | .str _ => LTerm (Observation D)
  | _ => Empty

def payloadObservations : (τ : Ty) → Payload D τ → List (Observation D)
  | .int _ _, term => term.variables
  | .bool, formula => formula.freeVariables
  | .str _, term => term.variables
  | _, _ => []

def PayloadSupported (τ : Ty) (payload : Payload D τ) : Prop :=
  ∀ key ∈ payloadObservations τ payload, ScalarObservation key

def Represents (world : World D) : (τ : Ty) → Payload D τ → Wert D τ → Prop
  | .int _ _, term, value => term.denote (assignment world) = value.n
  | .bool, formula, value => value = true ↔ formula.denote (assignment world)
  | .str _, term, value => term.denote (assignment world) = (value.val.length : Int)
  | _, _, _ => False

/-- Correctness travels with the computed payload; proofs erase from executable
    code. This is not a user-supplied obligation or a decision oracle. -/
structure Encoded (D : Deklaration) (τ : Ty) (value : World D → Wert D τ) where
  payload : Payload D τ
  correct : ∀ world, Represents world τ payload (value world)
  supported : PayloadSupported τ payload

/-- The Boolean correctness field read through `wahr?`, whose type is syntactically
    `Bool`. `Wert D .bool` is `Bool` only after unfolding `Val`, which rewriting and
    lemma instantiation do not do; Boolean proofs therefore go through this form. -/
theorem Encoded.bool_iff {value : World D → Wert D Ty.bool} (encoded : Encoded D Ty.bool value)
    (world : World D) :
    wahr? (value world) = true ↔ LProp.denote (assignment world) encoded.payload :=
  encoded.correct world

/-- The constant formula of a Boolean value, independent of the world. -/
def boolFormula (value : Bool) : LProp (Observation D) := cond value LProp.tru LProp.fls

theorem boolFormula_represents (world : World D) (value : Bool) :
    value = true ↔ LProp.denote (assignment world) (boolFormula (D := D) value) := by
  cases value
  · constructor
    · intro h
      cases h
    · intro h
      exact False.elim h
  · constructor
    · intro _
      exact trivial
    · intro _
      rfl

theorem boolFormula_observations (value : Bool) :
    payloadObservations (D := D) Ty.bool (boolFormula (D := D) value) = [] := by
  cases value
  · rfl
  · rfl

theorem boolFormula_supported (value : Bool) :
    PayloadSupported (D := D) Ty.bool (boolFormula (D := D) value) := by
  intro key member
  rw [boolFormula_observations] at member
  exact False.elim (List.not_mem_nil member)

/-- A variable's integer value or string length is fixed by the supplied local
    environment. Invariant environments are empty except for bounded slot binders. -/
def encodeConstant (τ : Ty) (value : Wert D τ) :
    Except Refusal (Encoded D τ (fun _ => value)) :=
  match τ, value with
  | .int _ _, value => .ok
      { payload := .konst value.n
        correct := fun _ => rfl
        supported := by simp [PayloadSupported, payloadObservations, LTerm.variables] }
  | .bool, value => .ok
      { payload := boolFormula (D := D) value
        correct := fun world => boolFormula_represents world value
        supported := boolFormula_supported value }
  | .str _, value => .ok
      { payload := .konst value.val.length
        correct := fun _ => rfl
        supported := by simp [PayloadSupported, payloadObservations, LTerm.variables] }
  | _, _ => .error (.unsupported "non-scalar local")

/-- The type test is explicit and refuses Boolean memory and every non-linear
    aggregate representation. Integer fields and string lengths share one variable. -/
def encodeObservation (τ : Ty) (key : Observation D) (value : World D → Wert D τ)
    (typed : observationType key = τ)
    (same : ∀ world, assignment world key = scalarValue τ (value world)) :
    Except Refusal (Encoded D τ value) :=
  match τ, value, typed, same with
  | .int _ _, _, typed, same => .ok
      { payload := .var key
        correct := same
        supported := by
          simp [PayloadSupported, payloadObservations, LTerm.variables, ScalarObservation, typed] }
  | .str _, _, typed, same => .ok
      { payload := .var key
        correct := same
        supported := by
          simp [PayloadSupported, payloadObservations, LTerm.variables, ScalarObservation, typed] }
  | _, _, _, _ => .error (.unsupported "non-integer memory or string contents")

/-- Evaluate a certified constant term without consulting the world. -/
def Encoded.constantIndex {lo hi : Int} {value : World D → Wert D (.int lo hi)}
    (encoded : Encoded D (.int lo hi) value) :
    Except Refusal { index : Int // ∀ world, (value world).n = index } :=
  match h : encoded.payload.constant? with
  | none => .error .crossEntry
  | some index => .ok ⟨index, fun world =>
      (encoded.correct world).symm.trans (LTerm.constant?_sound h (assignment world))⟩

end Gabbro.Grammatik.Invarianten.Frag
