module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil5

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Floors participate in the returned verdict. They are ordinary expressions,
    resolved at each return's actual scope, after the measured locals are bound.
    No assertion about claim text is introduced. -/
def floorUrteil (floors : List SExpr) (verdict : SExpr) : SExpr :=
  floors.foldl (fun result floor => .bin "&&" result floor) verdict

/-- Each step of the actual floor expansion elaborates to the same ordinary
    conjunction, for any source expressions and any correctly resolved scope.
    The existing `lowEns` conjunction case and its compiler proof then apply. -/
theorem uSichert_floor_step (ctx : UCtx) (verdict floor : SExpr)
    (value outcome : UEns) (hv : uSichert ctx verdict = .ok value)
    (hf : uSichert ctx floor = .ok outcome) :
    uSichert ctx (floorUrteil [floor] verdict) = .ok (.and value outcome) := by
  change uSichert ctx (.bin "&&" verdict floor) = _
  change (match uSichert ctx verdict with
    | .error error => .error error
    | .ok left => match uSichert ctx floor with
      | .error error => .error error
      | .ok right => .ok (.and left right)) = _
  rw [hv, hf]

/-- Non-degenerate instance of the generic expansion: a failing comparison is
    preserved as code, rather than replaced by a claimed true outcome. -/
theorem uSichert_floor_step_zeuge (ctx : UCtx) :
    uSichert ctx (floorUrteil [.bin ">=" (.lit 1) (.lit 2)] .tru) =
      .ok (.and .tru (.cmp ">=" (.lit 1) (.lit 2))) :=
  uSichert_floor_step ctx _ _ _ _ rfl rfl

/-- The value of a lowered floor conjunction. Both false and true are ordinary
    completed verdicts; neither removes the returning resource obligation. -/
theorem floorUrteil_bool (verdict floor : Bool) :
    (verdict && floor) = true ↔ verdict = true ∧ floor = true :=
  Bool.and_eq_true_iff

end Gabbro.Grammatik.Parser.Uebersetze
