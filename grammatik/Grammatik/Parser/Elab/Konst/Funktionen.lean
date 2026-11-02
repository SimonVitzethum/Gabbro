module

public import Grammatik.Parser.Item.ElementTief

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- A constant function retains its source signature and statement body.

    Restored here (C17): the `Uebersetze/Teil2.lean` home of this
    representation was lost in the C01 merge `ae2cfb480` (new-path stub
    kept, C01-side old-path file dropped). This file carries the exact
    post-`4c3b3f314` shape so `uKonstWert`, `uKonstFns` and the certified
    call-site substitution resolve again. When the core `Teil2` is
    restored by the lead, delete this file and its import in `Teil3`. -/
structure UKonstFn where
  name : String
  params : List (String × Ty)
  erg : Ty
  rumpf : SAnw
  signature : FnSig

/-- Bind integer arguments only when their checked parameter types admit them. -/
def uKonstBinde : List (String × Ty) → List Int → Option (List (String × Int))
  | [], [] => some []
  | (n, .int pl ph) :: ps, v :: vs =>
    if pl ≤ v ∧ v ≤ ph then (uKonstBinde ps vs).map (fun r => (n, v) :: r) else none
  | _, _ => none

end Gabbro.Grammatik.Parser.Uebersetze
