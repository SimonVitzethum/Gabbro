module

public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Lex.Lexer

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Resolve an owner name against the unit's declared owner namespace (C12):
    the index of the name among the declared owners, `none` for anything else.
    The namespace is collected by the unit elaborator from the `linear` type
    items and the tables' `owner` marks; `""` (the implicit owner of bare
    `own`) never resolves here -- bare `own` is the consumes/allocs sugar and
    needs the C09 signature flow before admission. -/
def uEignerNr (eigner : List String) (name : String) : Option Nat :=
  eigner.findIdx? (fun m => strEq m name)

/-- The unit's raw owner namespace (C12): the `linear` type names and every
    table's `owner` mark, in declaration order. The caller deduplicates
    (`uOhneDoppelte`); resolution (`uEignerNr`) is positional, so declaration
    order is the index order. -/
def uEignerMs (ms : List SItemTief) : List String :=
  (ms.filterMap fun | .typeT flags n _ _ _ =>
    if flags.any (fun f => strEq f "linear") then some n else none | _ => none) ++
    (ms.filterMap fun | .tableT _ _ _ _ o _ _ => o | _ => none)

/-- The declared linear marks (C12): the `linear`-flagged type names in
    declaration order. A table `owner M` must name one of them; anything else
    is refused (`uPruefEigner`), never elaborated to an unholdable guard. -/
def uLinearNamen (ms : List SItemTief) : List String :=
  ms.filterMap fun | .typeT flags n _ _ _ =>
    if flags.any (fun f => strEq f "linear") then some n else none | _ => none

/-- A table `owner` mark against the declared linear marks (C12): `none` travels,
    a declared linear mark travels, anything else is refused by name. -/
def uPruefEigner (linear : List String) (o : Option String) : Except String Unit :=
  match o with
  | none => .ok ()
  | some m => if linear.any (fun l => strEq l m) then .ok ()
    else .error ("owner without declared linear mark: " ++ m)

/-- A mark name as a declaration mark: its index in the unit's mark table
    (`u.marken`), if declared. Undeclared names have no mark and can never
    satisfy a guard. -/
def markFin (marken : List String) (m : String) : Option (Fin marken.length) :=
  (List.finRange marken.length).find? (fun i => strEq (marken.get i) m)

end Gabbro.Grammatik.Parser.Uebersetze
