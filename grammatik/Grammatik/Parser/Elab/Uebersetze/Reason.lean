module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil11

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Read codes through the existing constant/range reader, checking the full source domain. -/
def uReasonCodes (alias : List (String × (Int × Int))) :
    List (String × SExpr × String) → Except String (List ReasonCode)
  | [] => .ok []
  | (_, e, _) :: rest =>
    match uSchranke alias e with
    | none => .error "reason code without a constant G form"
    | some n =>
      if h : 0 ≤ n ∧ n < (2 ^ 128 : Nat) then
        match uReasonCodes alias rest with
        | .error e => .error e
        | .ok cs => .ok (⟨n.toNat, by omega⟩ :: cs)
      else .error "reason code outside u128"

/-- Resolve one declaration without discarding code values, openness or nominal identity. -/
def uReasonSpec (alias : List (String × (Int × Int))) (identity : Nat)
    (cs : List (String × SExpr × String)) (closed : Bool) : Except String ReasonSpec :=
  if (cs.map (·.1)).Nodup then
    match uReasonCodes alias cs with
    | .error e => .error e
    | .ok codes =>
      if h : codes.Nodup then .ok ⟨identity, codes, closed, h⟩
      else .error "duplicate reason code"
  else .error "duplicate reason case name"

/-- Successful collection preserves the exact declaration identity and open/closed flag. -/
theorem uReasonSpec_identity {alias : List (String × (Int × Int))} {identity : Nat}
    {cs : List (String × SExpr × String)} {closed : Bool} {r : ReasonSpec}
    (h : uReasonSpec alias identity cs closed = .ok r) :
    r.name = identity ∧ r.closed = closed := by
  unfold uReasonSpec at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
        exact ⟨rfl, rfl⟩
      · cases h
  · cases h

end Gabbro.Grammatik.Parser.Uebersetze
