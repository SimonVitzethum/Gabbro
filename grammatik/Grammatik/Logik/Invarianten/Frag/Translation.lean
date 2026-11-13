module

public import Grammatik.Logik.Invarianten.Frag.Bounded

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag

variable {D : Deklaration}

/-- Translate typed expressions with a concrete local environment. The public
    invariant entry point supplies `Env.nil`; only bounded slot indices extend it.
    This helper is not a symbolic translation of arbitrary function arguments.
    Every successful branch constructs its semantic proof at the same time. -/
def translate (e : Expr D Γ Λ τ) (locals : Env D Γ) :
    Except Refusal (Encoded D τ (fun world => eval world e world locals)) :=
  match e with
  | .lit n => .ok
      { payload := .konst n
        correct := fun _ => rfl
        supported := by simp [PayloadSupported, payloadObservations, LTerm.variables] }
  | .tru => .ok
      { payload := .tru
        correct := fun _ => ⟨fun _ => trivial, fun _ => rfl⟩
        supported := by simp [PayloadSupported, payloadObservations, LProp.freeVariables] }
  | .fls => .ok
      { payload := .fls
        correct := fun _ => ⟨fun h => absurd h Bool.false_ne_true, fun h => False.elim h⟩
        supported := by simp [PayloadSupported, payloadObservations, LProp.freeVariables] }
  | .var name => encodeConstant _ (locals.get name)
  | .glob name _ =>
      encodeObservation (D.gtyp name) (.glob name) (fun world => world.globs name)
        rfl (fun _ => rfl)
  | .slot table field index _ => do
      let indexTerm ← located "slot.index" (translate index locals)
      let offset ← located "slot.index" indexTerm.constantIndex
      let result ← encodeObservation (D.typ table field) (.slot table field offset.val)
        (fun world => world.slots table offset.val field) rfl (fun _ => rfl)
      return {
          payload := result.payload
          correct := fun world => by
            change Represents world _ _ (world.slots table (eval world index world locals).n field)
            rw [offset.property world]
            exact result.correct world
          supported := result.supported }
  | .widen _ _ body => do
      let result ← located "widen" (translate body locals)
      return {
          payload := result.payload
          correct := result.correct
          supported := result.supported }
  | .add a b => do
      let left ← located "add.left" (translate a locals)
      let right ← located "add.right" (translate b locals)
      return {
          payload := .add left.payload right.payload
          correct := fun world => by
            change left.payload.denote _ + right.payload.denote _ =
              (eval world a world locals).n + (eval world b world locals).n
            rw [left.correct world, right.correct world]
          supported := by
            simpa only [PayloadSupported, payloadObservations, LTerm.variables,
              List.forall_mem_append] using And.intro left.supported right.supported }
  | .sub a b => do
      let left ← located "sub.left" (translate a locals)
      let right ← located "sub.right" (translate b locals)
      return {
          payload := .sub left.payload right.payload
          correct := fun world => by
            change left.payload.denote _ - right.payload.denote _ =
              (eval world a world locals).n - (eval world b world locals).n
            rw [left.correct world, right.correct world]
          supported := by
            simpa only [PayloadSupported, payloadObservations, LTerm.variables,
              List.forall_mem_append] using And.intro left.supported right.supported }
  | .neg body => do
      let result ← located "neg" (translate body locals)
      return {
          payload := .sub (.konst 0) result.payload
          correct := fun world => by
            change 0 - result.payload.denote _ = _
            rw [result.correct world]
            simp [eval, Zahl.neg]
          supported := by
            simpa only [PayloadSupported, payloadObservations, LTerm.variables,
              List.nil_append] using result.supported }
  | .mul a b => do
      let left ← located "mul.left" (translate a locals)
      let right ← located "mul.right" (translate b locals)
      if literalB a then
        let coefficient ← left.constantIndex
        return {
            payload := .scale coefficient.val right.payload
            correct := fun world => by
              change coefficient.val * right.payload.denote _ =
                (eval world a world locals).n * (eval world b world locals).n
              rw [right.correct world, ← coefficient.property world]
            supported := right.supported }
      else if literalB b then
        let coefficient ← right.constantIndex
        return {
            payload := .scale coefficient.val left.payload
            correct := fun world => by
              change coefficient.val * left.payload.denote _ =
                (eval world a world locals).n * (eval world b world locals).n
              rw [left.correct world, ← coefficient.property world]
              change (eval world b world locals).n * (eval world a world locals).n =
                (eval world a world locals).n * (eval world b world locals).n
              exact Int.mul_comm _ _
            supported := left.supported }
      else .error .nonlinear
  | .lt a b => do
      let left ← located "lt.left" (translate a locals)
      let right ← located "lt.right" (translate b locals)
      return {
          payload := .lt left.payload right.payload
          correct := fun world => by
            change decide ((eval world a world locals).n < (eval world b world locals).n) = true ↔
              left.payload.denote _ < right.payload.denote _
            rw [left.correct world, right.correct world]
            simp only [decide_eq_true_eq]
          supported := by
            simpa only [PayloadSupported, payloadObservations, LProp.freeVariables,
              List.forall_mem_append] using And.intro left.supported right.supported }
  | .le a b => do
      let left ← located "le.left" (translate a locals)
      let right ← located "le.right" (translate b locals)
      return {
          payload := .le left.payload right.payload
          correct := fun world => by
            change decide ((eval world a world locals).n ≤ (eval world b world locals).n) = true ↔
              left.payload.denote _ ≤ right.payload.denote _
            rw [left.correct world, right.correct world]
            simp only [decide_eq_true_eq]
          supported := by
            simpa only [PayloadSupported, payloadObservations, LProp.freeVariables,
              List.forall_mem_append] using And.intro left.supported right.supported }
  | .eq a b => do
      let left ← located "eq.left" (translate a locals)
      let right ← located "eq.right" (translate b locals)
      return {
          payload := .eq left.payload right.payload
          correct := fun world => by
            change decide ((eval world a world locals).n = (eval world b world locals).n) = true ↔
              left.payload.denote _ = right.payload.denote _
            rw [left.correct world, right.correct world]
            simp only [decide_eq_true_eq]
          supported := by
            simpa only [PayloadSupported, payloadObservations, LProp.freeVariables,
              List.forall_mem_append] using And.intro left.supported right.supported }
  | .and a b => do
      let left ← located "and.left" (translate a locals)
      let right ← located "and.right" (translate b locals)
      return {
          payload := .and left.payload right.payload
          correct := fun world => by
            change (wahr? (eval world a world locals) && wahr? (eval world b world locals)) = true ↔
              LProp.denote (assignment world) left.payload ∧
                LProp.denote (assignment world) right.payload
            exact Bool.and_eq_true_iff.trans
              (and_congr (left.bool_iff world) (right.bool_iff world))
          supported := by
            simpa only [PayloadSupported, payloadObservations, LProp.freeVariables,
              List.forall_mem_append] using And.intro left.supported right.supported }
  | .or a b => do
      let left ← located "or.left" (translate a locals)
      let right ← located "or.right" (translate b locals)
      return {
          payload := .or left.payload right.payload
          correct := fun world => by
            change (wahr? (eval world a world locals) || wahr? (eval world b world locals)) = true ↔
              LProp.denote (assignment world) left.payload ∨
                LProp.denote (assignment world) right.payload
            exact Bool.or_eq_true_iff.trans
              (or_congr (left.bool_iff world) (right.bool_iff world))
          supported := by
            simpa only [PayloadSupported, payloadObservations, LProp.freeVariables,
              List.forall_mem_append] using And.intro left.supported right.supported }
  | .not body => do
      let result ← located "not" (translate body locals)
      return {
          payload := .not result.payload
          correct := fun world => by
            change (!wahr? (eval world body world locals)) = true ↔
              ¬ LProp.denote (assignment world) result.payload
            simpa only [Bool.not_eq_true', Bool.not_eq_true] using
              not_congr (result.bool_iff world)
          supported := result.supported }
  | .strLit bytes _ => .ok
      { payload := .konst bytes.length
        correct := fun _ => rfl
        supported := by simp [PayloadSupported, payloadObservations, LTerm.variables] }
  | .strLen body => do
      let result ← located "strLen" (translate body locals)
      return {
          payload := result.payload
          correct := result.correct
          supported := result.supported }
  | .strCat a b => do
      let left ← located "strCat.left" (translate a locals)
      let right ← located "strCat.right" (translate b locals)
      return {
          payload := .add left.payload right.payload
          correct := fun world => by
            change left.payload.denote _ + right.payload.denote _ = _
            rw [left.correct world, right.correct world]
            simp [eval, strCatW]
          supported := by
            simpa only [PayloadSupported, payloadObservations, LTerm.variables,
              List.forall_mem_append] using And.intro left.supported right.supported }
  | .forallSlots table body _ =>
      encodeAll (alleIndizes (D.count table))
        (fun index world => eval world body world (.cons index locals))
        (fun index => translate body (.cons index locals))
  | _ => .error (.unsupported "expression outside the linear fragment")

/-- Admission and translation for a closed model invariant. `D.count` is a
    declaration-time integer and is represented by ordinary source literals.
    `Expr.count` is a predicate fold, and is explicitly refused by `checkShape`.
    The fragment has no dependence on the environment-contract remainder. -/
def translateInvariant (carriers : List (D.Tab ⊕ D.Glob)) (e : Expr D [] Λ .bool) :
    Except Refusal (Encoded D .bool (fun world => eval world e world .nil)) := do
  checkCarriers carriers e
  checkShape none e
  translate e .nil

/-- A refusal retains its named cause and subexpression path. -/
def uebersetzeB (carriers : List (D.Tab ⊕ D.Glob)) (e : Expr D [] Λ .bool) :
    Except Refusal (LProp (Observation D)) :=
  match translateInvariant carriers e with
  | .ok encoded => .ok encoded.payload
  | .error cause => .error cause

def imFragmentB (carriers : List (D.Tab ⊕ D.Glob)) (e : Expr D [] Λ .bool) : Bool :=
  match uebersetzeB carriers e with
  | .ok _ => true
  | .error _ => false

theorem uebersetzeB_sound (carriers : List (D.Tab ⊕ D.Glob))
    (e : Expr D [] Λ .bool) (formula : LProp (Observation D))
    (success : uebersetzeB carriers e = .ok formula) (world : World D) :
    eval world e world .nil = true ↔ formula.denote (assignment world) := by
  cases h : translateInvariant carriers e with
  | error cause => simp [uebersetzeB, h] at success
  | ok encoded =>
      simp only [uebersetzeB, h] at success
      have payload_eq := Except.ok.inj success
      subst formula
      exact encoded.correct world

/-- All free observations have a supported typed representation. Together with
    `LProp.keys_supported`, this removes both hidden key-coverage obligations. -/
theorem uebersetzeB_supported (carriers : List (D.Tab ⊕ D.Glob))
    (e : Expr D [] Λ .bool) (formula : LProp (Observation D))
    (success : uebersetzeB carriers e = .ok formula) :
    ∀ key ∈ formula.keys, ScalarObservation key := by
  cases h : translateInvariant carriers e with
  | error cause => simp [uebersetzeB, h] at success
  | ok encoded =>
      simp only [uebersetzeB, h] at success
      have payload_eq := Except.ok.inj success
      subst formula
      intro key member
      exact encoded.supported key ((encoded.payload.mem_keys key).mp member)

/-- The declaration wrapper takes the carriers from the canonical invariant
    declaration; callers enumerate the declared invariants with `D.invs`. -/
def translateDeclared (program : Programm D) (name : D.Inv) :=
  uebersetzeB (D.traeger name) (program.invariante name)

theorem translateDeclared_sound (program : Programm D) (name : D.Inv)
    (formula : LProp (Observation D)) (success : translateDeclared program name = .ok formula)
    (world : World D) :
    eval world (program.invariante name) world .nil = true ↔ formula.denote (assignment world) :=
  uebersetzeB_sound (D.traeger name) (program.invariante name) formula success world

end Gabbro.Grammatik.Invarianten.Frag
