module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil5Rest

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- An option value of the table `num`: `None`, `Some(i)`, or what `uOptEin` reads (its table must be `num`). -/
def uOpt (ctx : UCtx) (num : Nat) : SExpr → Except String UOpt
  | .call "None" [] => .ok .nichts
  | .call "Some" [a] =>
    match ctx.tabs[num]? with
    | .none => .error "option table unknown"
    | .some tb =>
      match uIndex ctx tb.name num a with
      | .error e => .error e
      | .ok ix => .ok (.etwas ix)
  | e =>
    match uOptEin ctx e with
    | .error x => .error x
    | .ok (o, m) => if m == num then .ok o else .error "option of a foreign table"

/-- Read complete typed values through the ordinary body and predicate readers.
    Nested tagged constructors retain their declared schema, never a scalar encoding. -/
def uPayload (ctx : UCtx) (τ : Ty) (e : SExpr) : Except String USide :=
  if τ = .bool then (uBool ctx e).map .predicate else
  match τ, e with
  | .opt n, .call "None" [] => .ok (.absent n)
  | .opt n, .call "Some" [value] => (uWertBody ctx value).map (.present n)
  | .why count, .why family name => do
      let declared ← uSuch "reason" (ctx.whys.map (fun w => (w.name, w))) family
      if declared.cases.length != count then throw "wrong tagged payload reason"
      match declared.cases.findIdx? (strEq · name) with
      | some i => pure (.reason count i)
      | none => .error "unknown tagged payload reason case"
  | .fnptr signature, .fnref name => .ok (.function signature name)
  | _, .variable name =>
    match uParamNr ctx name with
    | .ok _ => .ok (.param name)
    | .error _ =>
      match τ with
      | .sum cs =>
        match ctx.sums.find? (fun s => s.spec = cs) with
        | none => .error "unknown nested tagged payload type"
        | some s =>
          match s.cases.findIdx? (fun c => strEq c.1 name && c.2.isNone) with
          | some i => .ok (.taggedEmpty cs i)
          | none => uWertBody ctx (.variable name)
      | _ => uWertBody ctx (.variable name)
  | .sum cs, .call name [value] =>
    match ctx.sums.find? (fun s => s.spec = cs) with
    | none => .error "unknown nested tagged payload type"
    | some s =>
      match s.cases.findIdx? (fun c => strEq c.1 name),
          (s.cases.find? (fun c => strEq c.1 name)).bind (·.2) with
      | some i, some payloadTy => do
        let payload ← uPayload ctx payloadTy value
        pure (.taggedValue cs i payload)
      | _, _ => .error "missing or extra nested tagged payload"
  | .opt _, _ => do
      let (value, number) ← uOptEin ctx e
      pure (.option number value)
  | _, _ => uWertBody ctx e

end Gabbro.Grammatik.Parser.Uebersetze
