/- C16: declared checks in elaborated form -- the U side of `SCheck`.

   A `UCheck` retains all seven source fields of one `check` item in elaborated
   form: the name and claim, the measured places (`UMessOrt`: a variable, a field
   of a named carrier, or an indexed slot -- resolved from the source shape, with
   no guessed table for a dynamically returned region), the resolved gate names,
   the floors as `UEns` predicates, the unique optional external counterprobe and
   the build mode. The `can_fail` body has no U form yet: lowering it into the
   generated probe and gate functions is the open remainder, and elaboration
   keeps refusing any unit with a check (`check without G form`). The mode is
   the checked shipping default; selection under C14 supplies the test mode. -/
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
  deriving DecidableEq, Repr

end Gabbro.Grammatik.Parser.Uebersetze
