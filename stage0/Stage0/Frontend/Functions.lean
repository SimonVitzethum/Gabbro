module
public import Grammatik.Parser.Elab.Konst.Scopes.Functions
public import Stage0.Frontend.Aliases
@[expose] public section


namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- The old base-ignoring reader admitted this nonnumeric range. The canonical reader refuses. -/
theorem fieldType_noninteger_range_refused_zeuge :
    uFeldTyp [] (.range (.atom "bool") (.lit 0) (.lit 1) false) =
      .error "range requires a numeric type and known bounds" := rfl

/-- Shadowing a reserved spelling in scalar candidates cannot turn Bool into an integer. -/
theorem fieldType_builtin_shadow_refused_zeuge :
    uFeldTyp [("bool", (0, 1))] (.atom "bool") =
      .error "field type without G form: bool" := rfl

/-- Ordinary integer aliases retain their exact original bounds. -/
theorem fieldType_sound_zeuge :
    uTyp [("Small", (-10, 100))] [] [] [] (.atom "Small") = .ok (.int (-10) 100) :=
  fieldType_sound _ _ _ _ rfl

theorem constantFunction_sound_zeuge :
    FunctionMeaning [("Count", (0, 100))]
      (.fnT ⟨"const", "identity", [("x", .atom "Count")], some (.atom "Count"), none, [], []⟩
        (.block [] (some (.ret (some (.variable "x"))))))
      ⟨"identity", [("x", .int 0 100)], .int 0 100, .block [] (some (.ret (some (.variable "x")))), ⟨"const", "identity", [("x", .atom "Count")], some (.atom "Count"), none, [], []⟩, [], []⟩ :=
  constantFunction_sound _ _ _ (by rfl)

end Gabbro.Stage0.Frontend
