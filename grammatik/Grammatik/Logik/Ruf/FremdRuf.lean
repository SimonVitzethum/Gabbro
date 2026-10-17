/-
  File:      Grammatik/FremdRuf.lean
  Subject:   FOREIGN CALLS WITH DESCRIPTOR CARRIERS (lane 233) -- the
             user-declared gate shape: a descriptor as an opaque carrier
             value plus gates as oracle calls whose dispatch labels,
             register bindings, costs and effects are program DATA, with
             answers constrained only by the declared ensures.

  Modelled shape: one gate hands out a descriptor value in a narrow
  carrier range, a second gate takes such a value and answers a count.
  The WITNESS oracle `fdO` ignores the passed descriptor (`fd_opak`, a
  fact about `fdO` only, proved by `rfl`); language-level opacity of the
  carrier is NOT modelled here -- the descriptor is a plain `.int 0 7`
  that expressions may compute on (review G10). Section 9 (fix lane F5)
  splits the gate contract into the caller's argument precondition and
  the hardware premise over well-formed calls, and bridges back to the
  goal theorem's premise (c) without changing it. The goal theorem's
  hardware premise (c) arrives as `GutO` (frame) plus `AxVertragO`
  (declared ensures); the per-gate theorem (`fremdruf_gate_gilt`) and
  the two-gate composition (`fremdruf_offen_lesen`) say exactly that,
  in the gate's own effect terms. Dispatch labels, register bindings
  and costs live only in `GateData` and constrain no answer.

  No dispatch table of any platform is baked in: every label, binding,
  cost and effect below is a field of program data, and the witness
  uses illustration labels only.
-/

import Grammatik.Logik.Ruf.FremdRuf.T1
import Grammatik.Logik.Ruf.FremdRuf.T2
import Grammatik.Logik.Ruf.FremdRuf.T3
