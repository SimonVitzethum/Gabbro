/-
  File:      Arm/Mem/Model.lean
  Subject:   The assembled Arm axiomatic model with hand-built litmus verdicts
             (MP, SB, LB, 2+2W, R, S), each as `Exec` values with `decide`
             verdicts under `noParts` (agents 09/10 not merged yet).
  Model:     same sources as `Arm/Mem/Axiomatic.lean` (Arm ARM B2.3,
             `aarch64.cat` from knowledge, not a measured copy). Initial
             writes sit on core 9 (a pseudo-core distinct from the actors).
-/
import Arm.Mem.Axiomatic

namespace Arm

/-- The assembled model: `consistent` is exactly the conjunction of the
    three axioms. (`consistent` itself is defined once in `Axiomatic.lean`.) -/
theorem model_asm (parts : OrderingParts) (x : Exec) :
    consistent parts x = (internal x && external parts x && atomic x) := rfl

/-- Message passing, classic outcome: the reader sees the flag and the data. -/
def mpAllowed : Exec :=
  { evs := [⟨0, 0, .write (acc 0#64), 1⟩, ⟨1, 0, .write (acc 8#64), 1⟩,
            ⟨2, 1, .read (acc 8#64), 1⟩, ⟨3, 1, .read (acc 0#64), 1⟩,
            ⟨4, 9, .write (acc 0#64), 0⟩, ⟨5, 9, .write (acc 8#64), 0⟩]
    po := [(0, 1), (2, 3)], addr := [], data := [], ctrl := []
    rf := [(1, 2), (0, 3)], co := [(4, 0), (5, 1)], rmw := [] }

/-- Message passing, suspicious outcome: flag seen, data missed. Allowed
    without barriers; forbidden once `bob` orders both sides (agent 10). -/
def mpForbidden : Exec :=
  { evs := [⟨0, 0, .write (acc 0#64), 1⟩, ⟨1, 0, .write (acc 8#64), 1⟩,
            ⟨2, 1, .read (acc 8#64), 1⟩, ⟨3, 1, .read (acc 0#64), 0⟩,
            ⟨4, 9, .write (acc 0#64), 0⟩, ⟨5, 9, .write (acc 8#64), 0⟩]
    po := [(0, 1), (2, 3)], addr := [], data := [], ctrl := []
    rf := [(1, 2), (4, 3)], co := [(4, 0), (5, 1)], rmw := [] }

/-- MP classic outcome is consistent. -/
theorem mp_allowed : consistent noParts mpAllowed = true := by decide

/-- MP suspicious outcome is consistent WITHOUT barriers (flips to `false`
    once `bob` orders the writer pair and the reader pair: then
    `W[x] -bob-> W[y] -rfe-> R[y] -bob-> R[x] -fre-> W[x]` cycles). -/
theorem mp_forbidden_allowed_without_barriers :
    consistent noParts mpForbidden = true := by decide

/-- Store buffering, classic outcome: both reads see the fresh writes. -/
def sbAllowed : Exec :=
  { evs := [⟨0, 0, .write (acc 0#64), 1⟩, ⟨1, 0, .read (acc 8#64), 1⟩,
            ⟨2, 1, .write (acc 8#64), 1⟩, ⟨3, 1, .read (acc 0#64), 1⟩,
            ⟨4, 9, .write (acc 0#64), 0⟩, ⟨5, 9, .write (acc 8#64), 0⟩]
    po := [(0, 1), (2, 3)], addr := [], data := [], ctrl := []
    rf := [(2, 1), (0, 3)], co := [(4, 0), (5, 2)], rmw := [] }

/-- Store buffering, suspicious outcome: both reads see the initial zeros.
    Allowed without barriers; forbidden once `bob` orders each write before
    its core's read (then `W[x] -bob-> R[y] -fre-> W[y] -bob-> R[x] -fre->
    W[x]` cycles). -/
def sbForbidden : Exec :=
  { evs := [⟨0, 0, .write (acc 0#64), 1⟩, ⟨1, 0, .read (acc 8#64), 0⟩,
            ⟨2, 1, .write (acc 8#64), 1⟩, ⟨3, 1, .read (acc 0#64), 0⟩,
            ⟨4, 9, .write (acc 0#64), 0⟩, ⟨5, 9, .write (acc 8#64), 0⟩]
    po := [(0, 1), (2, 3)], addr := [], data := [], ctrl := []
    rf := [(5, 1), (4, 3)], co := [(4, 0), (5, 2)], rmw := [] }

/-- SB classic outcome is consistent. -/
theorem sb_allowed : consistent noParts sbAllowed = true := by decide

/-- SB suspicious outcome is consistent WITHOUT barriers. -/
theorem sb_forbidden_allowed_without_barriers :
    consistent noParts sbForbidden = true := by decide

/-- Load buffering, classic outcome: both reads see the initial zeros. -/
def lbAllowed : Exec :=
  { evs := [⟨0, 0, .read (acc 0#64), 0⟩, ⟨1, 0, .write (acc 8#64), 1⟩,
            ⟨2, 1, .read (acc 8#64), 0⟩, ⟨3, 1, .write (acc 0#64), 1⟩,
            ⟨4, 9, .write (acc 0#64), 0⟩, ⟨5, 9, .write (acc 8#64), 0⟩]
    po := [(0, 1), (2, 3)], addr := [], data := [], ctrl := []
    rf := [(4, 0), (5, 2)], co := [(4, 3), (5, 1)], rmw := [] }

/-- Load buffering, suspicious outcome: each read sees the other core's
    write. Allowed for PLAIN accesses (no dependency); the same outcome with
    address dependencies is `xLbAddr` in `Axiomatic.lean` and is inconsistent
    via `dob` alone — no barrier needed, none can repair it. -/
def lbForbidden : Exec :=
  { evs := [⟨0, 0, .read (acc 0#64), 1⟩, ⟨1, 0, .write (acc 8#64), 1⟩,
            ⟨2, 1, .read (acc 8#64), 1⟩, ⟨3, 1, .write (acc 0#64), 1⟩,
            ⟨4, 9, .write (acc 0#64), 0⟩, ⟨5, 9, .write (acc 8#64), 0⟩]
    po := [(0, 1), (2, 3)], addr := [], data := [], ctrl := []
    rf := [(3, 0), (1, 2)], co := [(4, 3), (5, 1)], rmw := [] }

/-- LB classic outcome is consistent. -/
theorem lb_allowed : consistent noParts lbAllowed = true := by decide

/-- LB suspicious outcome is consistent for PLAIN accesses. -/
theorem lb_forbidden_allowed_without_dependencies :
    consistent noParts lbForbidden = true := by decide

end Arm

/-
CUTS: skeleton; verdict theorems and the SB/LB/2+2W/R/S shapes follow.
-/
