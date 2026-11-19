module

public import Grammatik.Logik.Ruf.FremdRuf.T1
public import Grammatik.Logik.Ruf.FremdRuf.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik

/-! ## 10. From single calls to call sequences (lane 262, OFFEN O23)

  `hardware_aus_vertragP` (§9) bridges one call: on a well-formed call the
  re-dressed oracle IS the machine's oracle (`mitVorbedingung_gleich`). What a
  gate client runs is a SEQUENCE of calls threading worlds -- open, then read
  in the world the open answered. This section lifts the coincidence to such
  sequences, at the oracle layer: if every call of the sequence meets the
  gate's precondition, folding the re-dressed oracle over the sequence gives
  the same worlds and raw answers as folding the machine's oracle.

  This is deliberately NOT a program run: no `Stmt`, no `execStmt`, no
  `bindAxiom` is involved, and nothing here is called a semantics. A machine
  run stepping through gate calls would need the F-machine residue shape
  (see CUTS). What is proved is the oracle-layer coincidence a run-level
  bridge stands on: under the caller's obligations at every call site, the two
  oracles agree on every call of the sequence. -/

/-- A sequence of oracle calls: each call names its gate and carries its own
    argument environment. The world is threaded, not stored: each call runs in
    the world the previous call answered. -/
def rufFolgeWirkt {D : Deklaration} (O : Orakel D) : World D →
    List (Σ a : D.Ax, Env D (D.aparams a)) → World D × List Int
  | σ, [] => (σ, [])
  | σ, ⟨a, ρ⟩ :: rest =>
    let (σ', w) := O.wirkt a σ ρ
    let (σ'', ws) := rufFolgeWirkt O σ' rest
    (σ'', w :: ws)


end Gabbro.Grammatik
