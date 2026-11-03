module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil5

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Floors participate in the returned verdict. They are ordinary expressions,
    resolved at each return's actual scope, after the measured locals are bound.
    No assertion about claim text is introduced. -/
def floorUrteil (floors : List SExpr) (verdict : SExpr) : SExpr :=
  floors.foldl (fun result floor => .bin "&&" result floor) verdict

/-- Expand every returning path, including nested error handlers. Fuel exhaustion
    is a refusal, so no unchecked return can survive an incomplete traversal. -/
def floorCode : Nat → List SExpr → SAnw → Except String SAnw
  | 0, _, _ => .error "check floor expansion exhausted"
  | n + 1, floors, body => do
    let recur := floorCode n floors
    match body with
    | .ret (some value) => pure (.ret (some (floorUrteil floors value)))
    | .block statements ending =>
      let statements ← statements.mapM recur
      let ending := ending.map fun
        | .ret (some value) => .ret (some (floorUrteil floors value))
        | other => other
      pure (.block statements ending)
    | .cond condition yes branches no =>
      pure (.cond condition (← recur yes) (← branches.mapM recur)
        (← no.mapM recur))
    | .elsif condition branch => pure (.elsif condition (← recur branch))
    | .cases value arms => pure (.cases value (← arms.mapM recur))
    | .arm tag binding branch => pure (.arm tag binding (← recur branch))
    | .bindElse name ty call reason branch =>
      pure (.bindElse name ty call reason (← recur branch))
    | .bindAxiomOptElse name ty call reason branch =>
      pure (.bindAxiomOptElse name ty call reason (← recur branch))
    | .each name start kind subject mode measure invariant branch =>
      pure (.each name start kind subject mode measure invariant (← recur branch))
    | .retry header branch => pure (.retry header (← recur branch))
    | .loop header branch => pure (.loop header (← recur branch))
    | .waive names branch => pure (.waive names (← recur branch))
    | .trim value ty branch => pure (.trim value ty (← recur branch))
    | .locks acquire target branch => pure (.locks acquire target (← recur branch))
    | .watch name branch => pure (.watch name (← recur branch))
    | .alloc mut name ty arena count branch =>
      pure (.alloc mut name ty arena count (← branch.mapM recur))
    | .grow arena count branch => pure (.grow arena count (← recur branch))
    | .child branch => pure (.child (← recur branch))
    | other => pure other

/-- No floors preserves the written body exactly, including its return shape. -/
def checkProbeCode (c : SCheck) : Except String SAnw :=
  if c.boden.isEmpty then .ok c.canFail else floorCode 100000 c.boden c.canFail

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
  Bool.and_eq_true

end Gabbro.Grammatik.Parser.Uebersetze
