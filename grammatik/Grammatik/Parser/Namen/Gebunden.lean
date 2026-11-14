module

public import Grammatik.Parser.Stmt.Anweisung.Kopf

@[expose] public section

namespace Gabbro.Grammatik.Parser.Aufloesung

open Gabbro.Grammatik.Parser

/-- The names a statement binds for the statements after it. -/
def gebunden : SAnw → List String
  | .bind _ x _ _ => bindingNames x
  | .bindAxiomOpt x _ _ => [x]
  | .bindElse x _ _ _ _ | .bindAxiomOptElse x _ _ _ _ => [x]
  | .bindQ _ x _ _ => [x]
  | .bindLib _ x _ _ => [x]
  | .alloc _ x _ _ _ _ => [x]
  | .allocVon _ x _ _ => [x]
  | .await x _ _ _ => [x]
  | .swap x _ _ _ => [x]
  | _ => []

end Gabbro.Grammatik.Parser.Aufloesung
