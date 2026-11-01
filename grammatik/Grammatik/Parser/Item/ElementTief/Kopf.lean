/-
  File:      Grammatik/Parser/ElementTief.lean
  Subject:   T3 PART 3: Gabbro items in depth (SYNTAX.md sections 1-2,
               6, 9-14) over the Lean statement reader.

  The surface types `STyp`/`SEffekt`/`SKlausel`/`FnSig`/`SItemTief`
  with fuel-indexed readers (`parseItemTief`, `parseTopTief`).
  Probes live in `Parser/Item/ElementTiefProben1..7.lean`.
-/
module

public import Grammatik.Parser.Item.ElementTief.Kopf.Teil1
public import Grammatik.Parser.Item.ElementTief.Kopf.Teil2
