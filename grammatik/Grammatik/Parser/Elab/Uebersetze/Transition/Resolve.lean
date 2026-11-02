module

public import Grammatik.Parser.Elab.Uebersetze.Teil6

public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Private function identity includes both the state and the named clause. -/
@[expose] def uTransitionFunction (state clause : String) : String :=
  "#transition#" ++ state ++ "#" ++ clause

/-- The exact entry-expression argument list, before any store. -/
@[expose] def uTransitionArguments (writes : List UTransitionWrite) (relative : Option UIdx) :
    Except String (List UArg) := do
  let args ← uSeq (writes.map fun w => do
    let endpoints := [UArg.val w.source, UArg.val w.target]
    match w.place with
    | .glob _ => pure endpoints
    | .relative _ => throw "transition target scope unresolved"
    | .slot _ _ index =>
      let index ← match index with
        | .param "#transitionIndex" =>
          match relative with
          | some index => pure index
          | none => throw "transition requires an explicit target index"
        | index => pure index
      pure (UArg.val (match index with | .lit n => .lit n | .param n => .param n) :: endpoints))
  pure args.flatten

/-- Unique primitive clause resolution, retaining identity even when two
    clauses of one state share endpoints. Clauses cannot use the raw shift. -/
@[expose] def uZustandVon (zs : List UZustand) (von nach : String) : Except String (String × Nat × Nat) :=
  let hits := zs.flatMap fun z =>
    match z.stufen.findIdx? (strEq · von), z.stufen.findIdx? (strEq · nach) with
    | some a, some b =>
      z.transitions.filterMap fun tr =>
        if tr.writes.any (fun w => w.source == .lit (Int.ofNat a) && w.target == .lit (Int.ofNat b)) then
          some (z.name, a, b, tr.primitive)
        else none
    | _, _ => []
  match hits with
  | [(state, a, b, true)] => .ok (state, a, b)
  | [_] => .error "transition clause requires a checked generated call"
  | [] => .error "transition not declared by a state"
  | _ => .error "transition declared by two clauses or states"

/-- Named source calls resolve a declaration, never an endpoint pair.
    Hidden snapshot parameters are supplied by this expansion only. -/
@[expose] def uNamedTransition (states : List UZustand) (name : String) :
    Option (Except String (String × UTransition)) :=
  let hits := states.flatMap fun state => state.transitions.filterMap fun tr =>
    if strEq name tr.name || strEq name (state.name ++ "::" ++ tr.name) then some (state.name, tr) else none
  match hits with
  | [] => none
  | [hit] => some (.ok hit)
  | _ => some (.error "transition name is ambiguous; qualify its state")

/-- A field use selects exactly one complete declaration. A multi-write
    declaration is invoked as a whole; an individual edge cannot erase it. -/
@[expose] def uTransitionAt (states : List UZustand) (table field : String) (index : UIdx)
    (source target : String) : Except String UStmt := do
  let hits := states.flatMap fun state =>
    match state.stufen.findIdx? (strEq · source), state.stufen.findIdx? (strEq · target) with
    | some a, some b => state.transitions.filterMap fun tr =>
      if tr.writes.any (fun w =>
          (match w.place with
            | .relative f => strEq f field
            | .slot t f (.param "#transitionIndex") => strEq t table && strEq f field
            | _ => false) &&
          w.source == .lit (Int.ofNat a) && w.target == .lit (Int.ofNat b)) then
        some (state.name, a, b, tr)
      else none
    | _, _ => []
  match hits with
  | [(state, a, b, tr)] =>
    if tr.primitive then pure (.shiftTab table field index state (Int.ofNat a) (Int.ofNat b))
    else
      let args ← uTransitionArguments tr.writes (some index)
      pure (.call (uTransitionFunction state tr.name) args)
  | [] => throw "transition not declared by a state"
  | _ => throw "transition declared by two clauses or states"

end Gabbro.Grammatik.Parser.Uebersetze
