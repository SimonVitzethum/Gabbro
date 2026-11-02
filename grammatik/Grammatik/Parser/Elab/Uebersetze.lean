/-
  File:      Grammatik/Parser/Uebersetze.lean
  Subject:   T3 PART 4: from the parsed surface tree to the G program.

  The Lean parser covers the whole surface (lanes 135/154/157);
  the Rust exporter `gabbro lean-g` (lane 144,
  `crates/gabbro-check/src/lean_g.rs`) turns a checked unit into
  the G program term `gP : Programm gD` (see
  `grammatik/Grammatik/Export104.lean`). This file closes the
  loop in Lean: an elaborator from the parsed surface tree
  (`SItemTief` list) to the same declaration/program shape the
  exporter produces.

  Two stages, like the exporter (collect, then translate):

  * surface to U: `elabU` maps the fragment `lean_g.rs`
    exports -- tables, locks with `Held`, `impl` fns with
    pointer/index/range params, comparison contracts over slot
    reads/`old`/`result`/literals, straight-line bodies of slot
    writes, direct calls, trailing return -- to plain data
    (`UProg`). Every other form is an explicit `.error`
    (the `Except String` channel; no new diagnostic codes).
  * U to G: `lowerU` assembles the `Programm gD` term over the
    exporter's declaration universe `G104_referenz.gD`.

  The 104 instance: `tt104` (token literal), `items104` (parse
  result literal), `uExp104` (elaboration result literal), with
  one kernel check per stage (`u104lex`, `u104parse`,
  `u104elab`) plus the lowering pin (`u104lower : ... = ...
  := rfl`, proof irrelevance covering the proof terms), the
  data agreement (`u104data`, same shape as `export104_data`)
  and the fragment/footprint checks on the Lean-parsed program
  (`u104fragment`, `u104fuss`).
-/
module

public import Grammatik.Parser.Elab.Uebersetze.Teil1
public import Grammatik.Parser.Elab.Uebersetze.Teil2
public import Grammatik.Parser.Elab.Uebersetze.Teil3
public import Grammatik.Parser.Elab.Uebersetze.Eingebaut
public import Grammatik.Parser.Elab.Uebersetze.Teil4
public import Grammatik.Parser.Elab.Uebersetze.Teil5
public import Grammatik.Parser.Elab.Uebersetze.Teil5Rest
public import Grammatik.Parser.Elab.Uebersetze.Teil6
public import Grammatik.Parser.Elab.Uebersetze.Teil7
public import Grammatik.Parser.Elab.Uebersetze.Teil8
public import Grammatik.Parser.Elab.Uebersetze.Teil9
public import Grammatik.Parser.Elab.Uebersetze.Teil10
public import Grammatik.Parser.Elab.Uebersetze.Teil11
public import Grammatik.Parser.Elab.Uebersetze.Teil12
public import Grammatik.Parser.Elab.Uebersetze.Teil13
public import Grammatik.Parser.Elab.Uebersetze.Teil14
public import Grammatik.Parser.Elab.Uebersetze.Teil15
public import Grammatik.Parser.Elab.Uebersetze.Teil16
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Data
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
public import Grammatik.Parser.Elab.Uebersetze.Teil17
