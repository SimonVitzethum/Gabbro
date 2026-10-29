/- Shared signed-key comparisons for float expressions and range checks. -/
import Stage0.Senke.Ausdruck.Gleit.Code

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D}

theorem floatKeyL_room {d top : Nat} {a b : Option (List II × Nat)} {c : List II}
    (h : floatKeyL d a b = some (c, top)) : d + 5 ≤ top := by
  cases a with
  | none => cases h
  | some a => cases b with
    | none => cases h
    | some b => exact (floatKeyL_top h).1

end Gabbro.Stage0.Senke
