module
public import Grammatik.Parser.Elab.Uebersetze.Einheit.Signatures
@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

/-- Lower foreign contracts in their own declared scope and retain their named origin. -/
def uForeign (alias : List (String × (Int × Int))) (consts : List (String × Int))
    (tabs : List UTab) (globs : List UGlob) (whys : List UWhy)
    (assumptions : List String) (k : UFnKopf)
    (eigner : List String := []) (spaces : List String := []) : Except String UAx := do
  let ctx := { uCtxVon alias consts tabs [] globs k k.name assumptions whys with
    eigner := eigner
    spaces := spaces }
  let (gives, needs) ← elabKlauseln ctx k.clauses
  pure {
    name := k.name
    params := k.types
    kinds := k.kinds
    res := k.axErg
    gruende := (k.kanal.map (·.2)).getD 0
    puts := k.puts
    gputs := k.gputs
    beleg := k.annahme.bind (fun n => assumptions.findIdx? fun x => strEq x n)
    names := k.names
    needs
    gives
  }

end Gabbro.Grammatik.Parser.Uebersetze
