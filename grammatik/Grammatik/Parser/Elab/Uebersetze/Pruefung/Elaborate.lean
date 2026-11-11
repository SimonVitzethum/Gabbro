/- C16: elaboration of `check` items -- from `SCheck` to `UCheck`.

   `uMessOrt` resolves one measured place by its source shape; anything else keeps
   the named refusal. `uCheck` resolves one item: the gates must name unit functions,
   C08 foreign bodies or sibling checks (a gate that is none of the three is refused,
   never auto-run), the floors elaborate with the ordinary predicate reader (a floor
   over measured numeric locals retain symbolic references; their actual type and
   scope are checked at every generated return), and `probe` records the generated producer name (`Erzeuge.uProbeFns`
   elaborates the `can_fail` body under that name; a probe never shares its name with
   a written function). -/
module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil5Rest
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Data

public section

namespace Gabbro.Grammatik.Parser.Uebersetze

set_option maxRecDepth 100000

/-- Resolve one measured place by its source shape. -/
@[expose] def uMessOrt : SExpr → Except String UMessOrt
  | .variable n => .ok (.variable n)
  | .field (.variable b) f => .ok (.feld b f)
  | .field (.index (.field (.variable b) s) (.lit n)) f =>
    if strEq s "slots" then .ok (.stelle b f (Int.ofNat n)) else .error "measure without G form"
  | _ => .error "measure without G form"

/-- A duplicate check name is refused, never merged. -/
@[expose] def uCheckDoppelt (bekannt : List String) (n : String) : Except String Unit :=
  if bekannt.any (fun m => strEq m n) then .error ("duplicate check: " ++ n) else .ok ()

/-- The foreign bodies of the unit that a gate may name (C08): `extern`/`raw`/`prim`
    declarations and `asm` bodies (`protoT`/`asmT`), `axiom` items without `requires`
    (read as `extern fn`), and `syscall` gates. Mirrors the canonical `uFremdSig`
    name set (`Einheit/Signatures`), inlined here: that module already imports this
    one, so importing it would close a cycle. -/
@[expose] def uFremdNamen : List SItemTief → List String
  | [] => []
  | .protoT sig :: rest => sig.name :: uFremdNamen rest
  | .asmT sig _ :: rest => sig.name :: uFremdNamen rest
  | .axiomT n _ _ .none _ _ :: rest => n :: uFremdNamen rest
  | .callT sc :: rest => sc.name :: uFremdNamen rest
  | _ :: rest => uFremdNamen rest

/-- Elaborate one `check` item against the unit's function, foreign-body and
    sibling-check names. -/
@[expose] def uCheck (tabs : List UTab) (globs : List UGlob) (fns : List String)
    (checks : List String) (fremd : List String) (c : SCheck) : Except String UCheck := do
  let misst ← uSeq (c.misst.map uMessOrt)
  let tore ← uSeq (c.gates.map fun g =>
    if fns.any (fun n => strEq n g) || checks.any (fun n => strEq n g) ||
        fremd.any (fun n => strEq n g) then .ok g
    else .error ("unknown gate: " ++ g))
  -- This is the symbolic floor descriptor, not a typed scope certificate. The
  -- generated ordinary probe resolves these references again at each return;
  -- missing locals, wrong types and early returns are refused there.
  let locals := c.misst.filterMap fun | .variable name => some name | _ => none
  let ctx : UCtx :=
    { names := locals
      kinds := locals.map fun _ => .int
      types := []
      tabs := tabs
      locks := []
      held := []
      res := none
      fname := c.cname
      alias := []
      lits := []
      globs := globs }
  let boeden ← uSeq (c.boden.map (uSichert ctx))
  -- The parser stores (text, expects-name); the kernel stores (name, text).
  .ok { name := c.cname, claim := c.claim, misst := misst, tore := tore, boeden := boeden, sonde := c.sonde.map fun pair => (pair.2, pair.1), probe := probeFnName c.cname, duty := dutyName c.cname }

@[expose] def uChecksAux (tabs : List UTab) (globs : List UGlob) (fns namen fremd bekannt : List String) :
    List SCheck → Except String (List UCheck)
  | [] => .ok []
  | c :: rest =>
    match uCheckDoppelt bekannt c.cname with
    | .error e => .error e
    | .ok _ =>
      match uCheck tabs globs fns namen fremd c with
      | .error e => .error e
      | .ok u =>
        match uChecksAux tabs globs fns namen fremd (c.cname :: bekannt) rest with
        | .error e => .error e
        | .ok us => .ok (u :: us)

/-- Elaborate every `check` item of the unit. -/
@[expose] def uChecks (tabs : List UTab) (globs : List UGlob) (ms : List SItemTief) :
    Except String (List UCheck) :=
  uChecksAux tabs globs
    (ms.filterMap (fun | .fnT s _ => some s.name | _ => none))
    (ms.filterMap (fun | .checkT d => some d.cname | _ => none))
    (uFremdNamen ms)
    [] (ms.filterMap (fun | .checkT c => some c | _ => none))

end Gabbro.Grammatik.Parser.Uebersetze
