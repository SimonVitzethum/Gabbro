module

public import Grammatik.Logik.Invarianten.Frag.Symbolic.Encoding

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.Symbolic

open Elim Elim.Korrekt

/-- The value of a local comes from Realizes. No unknown integer is decoded,
    sampled or enumerated while constructing this certificate. -/
def encodeValue (symbol : SymValue D Nat τ) : Except Refusal
    { payload : Payload D τ // ∀ valuation world actual,
      symbol.Realizes valuation world actual → Represents valuation world τ payload actual } :=
  match symbol with
  | .known value => do
      let encoded ← encodeConstant τ value
      return ⟨liftPayload τ encoded.payload, fun valuation world actual realized => by
          change value = actual at realized
          rw [← realized]
          exact (liftPayload_represents τ encoded.payload valuation world value).mpr (encoded.correct world)⟩
  | .integer term => .ok ⟨renameTerm Sum.inr term, fun valuation world actual realized => by
        change (renameTerm Sum.inr term).denote _ = _
        rw [renameTerm_denote]
        exact realized⟩

def encodeVariable (symbols : SymEnv D Nat Γ) (name : Var Γ τ) :
    Except Refusal (Encoding symbols τ (fun _ actual => actual.get name)) := do
  let encoded ← encodeValue (symbols.get name)
  return {
    payload := encoded.val
    correct := fun valuation world actual realized =>
      encoded.property valuation world (actual.get name)
        (symbols.realizes_get actual valuation world name realized) }

def translate (expression : Expr D Γ Λ τ) (symbols : SymEnv D Nat Γ) :
    Except Refusal (Encoding symbols τ (fun world actual => eval world expression world actual)) :=
  match expression with
  | .lit number => .ok { payload := .konst number, correct := fun _ _ _ _ => rfl }
  | .tru => .ok { payload := .tru, correct := fun _ _ _ _ => ⟨fun _ => trivial, fun _ => rfl⟩ }
  | .fls => .ok { payload := .fls, correct := fun _ _ _ _ =>
      ⟨fun impossible => Bool.noConfusion impossible, fun impossible => False.elim impossible⟩ }
  | .var name => encodeVariable symbols name
  | .glob name _ => do
      let encoded ← encodeObservation (D.gtyp name) (.glob name)
        (fun world => world.globs name) rfl (fun _ => rfl)
      return ofMemory symbols encoded
  | .slot table field index _ | .thru _ table _ field index _ => do
      let encodedIndex ← translate index symbols
      let offset ← encodedIndex.constantIndex
      let encoded ← encodeObservation (D.typ table field) (.slot table field offset.val)
        (fun world => world.slots table offset.val field) rfl (fun _ => rfl)
      return {
        payload := liftPayload _ encoded.payload
        correct := fun valuation world actual realized => by
          change Represents valuation world _ _ (world.slots table (eval world index world actual).n field)
          rw [offset.property valuation world actual realized]
          exact (liftPayload_represents _ encoded.payload valuation world _).mpr (encoded.correct world) }
  | .widen _ _ body => do
      let encoded ← translate body symbols
      return { payload := encoded.payload, correct := encoded.correct }
  | .add left right => do
      let a ← translate left symbols
      let b ← translate right symbols
      return {
        payload := .add a.payload b.payload
        correct := fun valuation world actual realized => by
          change a.payload.denote _ + b.payload.denote _ =
            (eval world left world actual).n + (eval world right world actual).n
          rw [a.correct valuation world actual realized, b.correct valuation world actual realized] }
  | .sub left right => do
      let a ← translate left symbols
      let b ← translate right symbols
      return {
        payload := .sub a.payload b.payload
        correct := fun valuation world actual realized => by
          change a.payload.denote _ - b.payload.denote _ =
            (eval world left world actual).n - (eval world right world actual).n
          rw [a.correct valuation world actual realized, b.correct valuation world actual realized] }
  | .neg body => do
      let encoded ← translate body symbols
      return {
        payload := .sub (.konst 0) encoded.payload
        correct := fun valuation world actual realized => by
          change 0 - encoded.payload.denote _ = _
          rw [encoded.correct valuation world actual realized]
          simp only [eval, Zahl.neg, Int.zero_sub] }
  | .mul left right => do
      let a ← translate left symbols
      let b ← translate right symbols
      if a.payload.constant?.isSome then
        let coefficient ← a.constantIndex
        return {
          payload := .scale coefficient.val b.payload
          correct := fun valuation world actual realized => by
            change coefficient.val * b.payload.denote _ =
              (eval world left world actual).n * (eval world right world actual).n
            rw [b.correct valuation world actual realized, ← coefficient.property valuation world actual realized] }
      else if b.payload.constant?.isSome then
        let coefficient ← b.constantIndex
        return {
          payload := .scale coefficient.val a.payload
          correct := fun valuation world actual realized => by
            change coefficient.val * a.payload.denote _ =
              (eval world left world actual).n * (eval world right world actual).n
            rw [a.correct valuation world actual realized, ← coefficient.property valuation world actual realized]
            exact Int.mul_comm _ _ }
      else .error .nonlinear
  | .lt left right => do
      let a ← translate left symbols
      let b ← translate right symbols
      return {
        payload := .lt a.payload b.payload
        correct := fun valuation world actual realized => by
          change decide ((eval world left world actual).n < (eval world right world actual).n) = true ↔ _
          change _ ↔ a.payload.denote _ < b.payload.denote _
          rw [a.correct valuation world actual realized, b.correct valuation world actual realized]
          simp only [decide_eq_true_eq] }
  | .le left right => do
      let a ← translate left symbols
      let b ← translate right symbols
      return {
        payload := .le a.payload b.payload
        correct := fun valuation world actual realized => by
          change decide ((eval world left world actual).n ≤ (eval world right world actual).n) = true ↔ _
          change _ ↔ a.payload.denote _ ≤ b.payload.denote _
          rw [a.correct valuation world actual realized, b.correct valuation world actual realized]
          simp only [decide_eq_true_eq] }
  | .eq left right => do
      let a ← translate left symbols
      let b ← translate right symbols
      return {
        payload := .eq a.payload b.payload
        correct := fun valuation world actual realized => by
          change decide ((eval world left world actual).n = (eval world right world actual).n) = true ↔ _
          change _ ↔ a.payload.denote _ = b.payload.denote _
          rw [a.correct valuation world actual realized, b.correct valuation world actual realized]
          simp only [decide_eq_true_eq] }
  | .and left right => do
      let a ← translate left symbols
      let b ← translate right symbols
      return {
        payload := .and a.payload b.payload
        correct := fun valuation world actual realized =>
          Bool.and_eq_true_iff.trans (and_congr
            (a.bool_iff valuation world actual realized) (b.bool_iff valuation world actual realized)) }
  | .or left right => do
      let a ← translate left symbols
      let b ← translate right symbols
      return {
        payload := .or a.payload b.payload
        correct := fun valuation world actual realized =>
          Bool.or_eq_true_iff.trans (or_congr
            (a.bool_iff valuation world actual realized) (b.bool_iff valuation world actual realized)) }
  | .not body => do
      let encoded ← translate body symbols
      return {
        payload := .not encoded.payload
        correct := fun valuation world actual realized => by
          change (!wahr? (eval world body world actual)) = true ↔
            ¬ encoded.payload.denote (values valuation world)
          simpa only [Bool.not_eq_true', Bool.not_eq_true] using
            not_congr (encoded.bool_iff valuation world actual realized) }
  | .strLit bytes _ => .ok { payload := .konst bytes.length, correct := fun _ _ _ _ => rfl }
  | .strLen body => do
      let encoded ← translate body symbols
      return { payload := encoded.payload, correct := encoded.correct }
  | .strCat left right => do
      let a ← translate left symbols
      let b ← translate right symbols
      return {
        payload := .add a.payload b.payload
        correct := fun valuation world actual realized => by
          change a.payload.denote _ + b.payload.denote _ = _
          rw [a.correct valuation world actual realized, b.correct valuation world actual realized]
          simp only [eval, strCatW, List.length_append, Int.natCast_add] }
  | .forallSlots table body _ =>
      allEncoding symbols (alleIndizes (D.count table))
        (fun index world actual => eval world body world (.cons index actual))
        (fun index => do
          let encoded ← translate body (.cons (.known index) symbols)
          return {
            payload := encoded.payload
            correct := fun valuation world actual realized =>
              encoded.correct valuation world (.cons index actual) ⟨rfl, realized⟩ })
  | other => concreteEncoding other symbols

end Gabbro.Grammatik.Invarianten.Frag.Symbolic
