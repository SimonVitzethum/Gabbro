module

public import Grammatik.Korpus.Programme.Export104
public import Grammatik.Parser.Item.ElementTief
public import Grammatik.Parser.Elab.Export.ExportMetadata
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil18
public import Grammatik.Parser.Elab.Uebersetze.Transition.Generate
public import Grammatik.Parser.Stmt.LibrarySource
public import Grammatik.Parser.TaggedDispatch.Frontend
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil17
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
public import Grammatik.Parser.Elab.Konst.Export
public import Grammatik.Parser.Elab.Konst.ErsetzungTor

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil11
public import Grammatik.Parser.Elab.Generic.PointerTypes
@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

/-! ## Function-pointer types (2026-10-21, contracts C06 since 2026-11-02)

  A `fn(..) [-> T] effects { .. } costs <= e ops` type of the unit is read once by its text (the type reader keeps
  it raw, `STyp.raw`) into a head like a function's and a signature with an empty body (`UProg.ptrs`). Its number
  stands behind the functions'; a function conforms to it by `Deklaration.passt` (`passtAt`, decided: structural
  `SigPasst` plus the decidable contract inclusion `vertragPasstAt`). The contract rides the type into `UProg.ptrs`
  (`needs`/`gives`, lowered to `Programm.ptrVertrag` by `lowerPtrAt`); `costs` travels nowhere,
  as at a function. No lock crosses an indirect call (a `locks` effect at the type is refused, as `N036` does, and
  so is `requires Held(..)`): the floor of the type is one above the highest rank of the unit. -/

/-- The names a unit declares as memory: tables, arenas, statics, atomics. -/
def uSpeicherNamen (ms : List SItemTief) : List String :=
  ms.filterMap fun
    | .tableT n .. => some n
    | .arenaT n .. => some n
    | .globT _ n .. => some n
    | .atomT n .. => some n
    | _ => none

/-- The writes of a clause list that name no memory of the unit. -/
def uFremdeSchreibe (mem : List String) (ks : List SKlausel) : List String :=
  ks.flatMap fun
    | .effs es => es.filterMap fun
      | .writes (.variable n) => if mem.any (strEq · n) then none else some n
      | _ => none
    | _ => []

/-- The clause list without the writes of the sinks. -/
def uKlauselnOhne (senken : List String) (ks : List SKlausel) : List SKlausel :=
  ks.map fun
    | .effs es => .effs (es.filter fun
      | .writes (.variable n) => !(senken.any (strEq · n))
      | _ => true)
    | k => k

/-- **Sinks** (`writes ausgabe` at an `extern fn`): a name that is no memory of the unit, written by a foreign body,
    is what lies behind it outside the program -- no carrier of G; the call itself is the trace event
    (`Ereignis.fremd`). Such a name may stand in the `writes` of the foreign bodies and of the functions that call
    them; it is dropped there. A name no foreign body declares stays and is refused as an unknown carrier. -/
def uOhneSenken (ms : List SItemTief) : List SItemTief :=
  let mem := uSpeicherNamen ms
  let senken := ms.flatMap fun
    | .protoT sig => uFremdeSchreibe mem sig.klauseln
    | .asmT sig _ => uFremdeSchreibe mem sig.klauseln
    | .axiomT _ _ _ _ effs _ => uFremdeSchreibe mem [.effs effs]
    | _ => []
  if senken.isEmpty then ms else
  ms.map fun
    | .fnT sig b => .fnT { sig with klauseln := uKlauselnOhne senken sig.klauseln } b
    | .protoT sig => .protoT { sig with klauseln := uKlauselnOhne senken sig.klauseln }
    | .asmT sig c => .asmT { sig with klauseln := uKlauselnOhne senken sig.klauseln } c
    | .axiomT n ps r q effs k =>
      .axiomT n ps r q (match uKlauselnOhne senken [.effs effs] with | [.effs es] => es | _ => effs) k
    | m => m

/-- The signature of a foreign body item and whether it is `= asm { .. }`: `extern`/`raw`/`prim`/`divergent` declarations,
    `asm` bodies, and `axiom` items without a `requires` (read as an `extern fn` with their effects). -/
def uFremdSig : SItemTief → Option (FnSig × Bool)
  | .protoT sig => some (sig, false)
  | .asmT sig _ => some (sig, true)
  | .axiomT n ps res .none effs _ =>
    some ({ art := "extern", name := n, params := ps, res, fehler := .none, klauseln := [.effs effs] }, false)
  | _ => none

end Gabbro.Grammatik.Parser.Uebersetze
