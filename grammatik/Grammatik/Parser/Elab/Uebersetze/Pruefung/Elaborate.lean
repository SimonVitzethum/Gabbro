/- C16: elaboration of `check` items -- from `SCheck` to `UCheck`.

   `uMessOrt` resolves one measured place by its source shape; anything else keeps
   the named refusal. `uCheck` resolves one item: the gates must name unit functions
   or sibling checks (a gate that is neither is refused, never auto-run), the
   floors elaborate with the ordinary predicate reader (a floor over a place whose
   scope exists only inside the not-yet-generated probe keeps its refusal), and
   `probe` records the generated producer name (`Erzeuge.uProbeFns` elaborates the
   `can_fail` body under that name; a probe never shares its name with a written
   function). -/
module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil5
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Data

public section

namespace Gabbro.Grammatik.Parser.Uebersetze

set_option maxRecDepth 100000

/-- Resolve one measured place by its source shape. -/
def uMessOrt : SExpr → Except String UMessOrt
  | .variable n => .ok (.variable n)
  | .field (.variable b) f => .ok (.feld b f)
  | .field (.index (.field (.variable b) s) (.lit n)) f =>
    if strEq s "slots" then .ok (.stelle b f (Int.ofNat n)) else .error "measure without G form"
  | _ => .error "measure without G form"

/-- A duplicate check name is refused, never merged. -/
def uCheckDoppelt (bekannt : List String) (n : String) : Except String Unit :=
  if bekannt.any (fun m => strEq m n) then .error ("duplicate check: " ++ n) else .ok ()

/-- Elaborate one `check` item against the unit's function and sibling-check names. -/
def uCheck (tabs : List UTab) (globs : List UGlob) (fns : List String) (checks : List String)
    (c : SCheck) : Except String UCheck := do
  let misst ← uSeq (c.misst.map uMessOrt)
  let tore ← uSeq (c.gates.map fun g =>
    if fns.any (fun n => strEq n g) || checks.any (fun n => strEq n g) then .ok g
    else .error ("unknown gate: " ++ g))
  let ctx : UCtx :=
    { names := [], kinds := [], types := [], tabs := tabs, locks := [], held := [], res := none, fname := c.cname, globs := globs }
  let boeden ← uSeq (c.boden.map (uSichert ctx))
  .ok { name := c.cname, claim := c.claim, misst := misst, tore := tore, boeden := boeden, sonde := c.sonde, probe := probeFnName c.cname, duty := dutyName c.cname }

def uChecksAux (tabs : List UTab) (globs : List UGlob) (fns namen bekannt : List String) :
    List SCheck → Except String (List UCheck)
  | [] => .ok []
  | c :: rest =>
    match uCheckDoppelt bekannt c.cname with
    | .error e => .error e
    | .ok _ =>
      match uCheck tabs globs fns namen c with
      | .error e => .error e
      | .ok u =>
        match uChecksAux tabs globs fns namen (c.cname :: bekannt) rest with
        | .error e => .error e
        | .ok us => .ok (u :: us)

/-- Elaborate every `check` item of the unit. -/
def uChecks (tabs : List UTab) (globs : List UGlob) (ms : List SItemTief) :
    Except String (List UCheck) :=
  uChecksAux tabs globs
    (ms.filterMap (fun | .fnT s _ => some s.name | _ => none))
    (ms.filterMap (fun | .checkT d => some d.cname | _ => none))
    [] (ms.filterMap (fun | .checkT c => some c | _ => none))

end Gabbro.Grammatik.Parser.Uebersetze
