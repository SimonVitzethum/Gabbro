import Grammatik.Parser.Elab.UebersetzeAllg3.Rest3
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg2
#eval match elabU (pre108 items108) with
  | .ok u => s!"{u == uExp108}\n{repr u}"
  | .error e => e
#eval match elabU (pre108 items104) with
  | .ok u => s!"{u == uExp104}\n{repr u}"
  | .error e => e
