module

public import Grammatik.Parser.Spec.Items

@[expose] public section

namespace Gabbro.Grammatik.Parser.Spec

/-- Check model A: check interfaces, materialize concrete bodies, resolve every abstract call,
    and validate that only existing forms remain. Real contracts travel with the concrete calls. -/
def expand (items : List SItemTief) : Except String (List SItemTief) := do
  check items
  let concrete := materialize items
  if !uniqueNames ((functionHeads concrete).map (·.name)) then throw "spec.function.collision"
  let output ← concrete.mapM ((Walk.mk items true).item 100000)
  if ordinary items output then return output else throw "spec.output"

/-- Every successful instantiation passes the ordinary-form gate, for arbitrary input programs.
    The existing elaborator subsequently checks types and the implementations' actual contracts. -/
theorem expand_ordinary {items output : List SItemTief} (h : expand items = .ok output) :
    ordinary items output = true := by
  unfold expand at h
  cases hc : check items with
  | error e => simp [hc] at h
  | ok u =>
    simp only [hc, bind, Except.bind] at h
    split at h
    · simp at h
    · cases hw : (materialize items).mapM ((Walk.mk items true).item 100000) with
      | error e => simp [hw] at h
      | ok result =>
        simp only [hw, bind, Except.bind] at h
        split at h
        · have he : result = output := by simpa using h
          subst output
          assumption
        · simp at h

/-- Preserve the existing front-end path for units with no spec-group items. -/
def prepare (items : List SItemTief) : Except String (List SItemTief) :=
  if items.any (fun | .specGroupT .. | .implGroupT .. => true | _ => false) then expand items
  else .ok items

end Gabbro.Grammatik.Parser.Spec

