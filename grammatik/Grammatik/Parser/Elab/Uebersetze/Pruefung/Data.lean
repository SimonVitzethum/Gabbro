/- C16: declared checks in elaborated form -- the U side of `SCheck`.

   A `UCheck` retains all seven source fields of one `check` item in elaborated
   form: the name and claim, the measured places (`UMessOrt`: a variable, a field
   of a named carrier, or an indexed slot -- resolved from the source shape, with
   no guessed table for a dynamically returned region), the resolved gate names,
   the floors as `UEns` predicates, the unique optional external counterprobe and
   the build mode. `probe` names the generated Boolean producer elaborated from
   the `can_fail` body (`Erzeuge.uProbeFns`); `duty` names the Duty mark the probe
   threads and the gate wrappers consume (`Torhuelle.uTorHuellen`); the mode is the
   checked shipping default, selection under C14 supplies the test mode. -/
module

public import Grammatik.Parser.Elab.Uebersetze.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

set_option maxRecDepth 100000

/-- A measured place of a declared check, resolved from its source shape. -/
inductive UMessOrt where
  | variable (name : String)
  | feld (basis : String) (feld : String)
  | stelle (basis : String) (feld : String) (index : Int)
  deriving DecidableEq, Repr

/-- One declared check in elaborated form. -/
structure UCheck where
  name : String
  claim : String
  misst : List UMessOrt
  tore : List String
  boeden : List UEns
  sonde : Option (String × String)
  /-- The build mode (`false` = shipping; the test mode comes from C14 selection). -/
  testbau : Bool := false
  /-- The generated Boolean producer elaborated from the `can_fail` body. -/
  probe : String := ""
  /-- The Duty mark this check threads (C16): consumed by its gate wrappers, produced by its
      probe on every normal return. Named after the check, like the probe. -/
  duty : String := ""
  deriving DecidableEq, Repr

/-- The Duty mark of a check: it cannot collide with a written
    function, since `#` never stands in a source identifier. -/
def dutyName (cname : String) : String := cname ++ "#duty"

/-- The generated producer of a check: its name cannot collide with a written
    function, since `#` never stands in a source identifier. -/
def probeFnName (cname : String) : String := cname ++ "#probe"

end Gabbro.Grammatik.Parser.Uebersetze
