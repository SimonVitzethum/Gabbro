module

@[expose] public section

namespace Gabbro.Grammatik

/-- A successful computation is `.ok` of its extracted value (how a unit
    instance names the parser's output without retyping it). -/
theorem except_ok_get {ε α : Type} {x : Except ε α} (h : x.toOption.isSome = true) :
    x = .ok (x.toOption.get h) := by
  cases x with
  | error e => simp only [Except.toOption, Option.isSome_none, Bool.false_eq_true] at h
  | ok a => rfl

end Gabbro.Grammatik
