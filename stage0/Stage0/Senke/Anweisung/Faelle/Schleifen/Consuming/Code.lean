/- Candidate emission for current-state consuming traversal. Admission requires
   the connected simulation; this module does not authorize lowS to emit it. -/
module
public import Stage0.Senke.Anweisung.Faelle.Hilfen
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

namespace Consuming

/-- Labels are local to one consuming fragment, including both body exits. -/
inductive Label where
  | header | candidate | predecessor | predecessorNext | candidateNext
  | different | selected | exhausted | afterBody | leaveBody | stop | done
  deriving DecidableEq

/-- Symbolic control flow is resolved before instructions reach the runner.
    There is no new instruction or execution semantics. -/
inductive Piece where
  | code (instructions : List II)
  | label (name : Label)
  | jump (target : Label)
  | zero (slot : Nat) (target : Label)

def Piece.width : Piece → Nat
  | .code instructions => instructions.length
  | .label _ => 0
  | .jump _ | .zero _ _ => 1

/-- Instruction positions, not byte positions. Labels produce no instructions. -/
def position (target : Label) : List Piece → Nat → Option Nat
  | [], _ => none
  | .label name :: rest, pc =>
      if name = target then some pc else position target rest pc
  | piece :: rest, pc => position target rest (pc + piece.width)

private def encode (whole : List Piece) : List Piece → Nat → Option (List II)
  | [], _ => some []
  | .label _ :: rest, pc => encode whole rest pc
  | .code instructions :: rest, pc => do
      let tail ← encode whole rest (pc + instructions.length)
      pure (instructions ++ tail)
  | .jump target :: rest, pc => do
      let destination ← position target whole 0
      let tail ← encode whole rest (pc + 1)
      pure (ci 18 (16 * ((destination : Int) - pc)) 0 0 :: tail)
  | .zero slot target :: rest, pc => do
      let destination ← position target whole 0
      let tail ← encode whole rest (pc + 1)
      pure (ci 19 slot (16 * ((destination : Int) - pc)) 0 :: tail)

/-- Reject oversized fragments before any signed branch immediate is truncated. -/
def assemble (pieces : List Piece) : Option (List II) := do
  let instructions ← encode pieces pieces 0
  if 16 * instructions.length < 2 ^ 31 then some instructions else none

/-- Compare the new measure, preserving it until all three obligations have
    been checked. Typed measure bounds are checked at run time as well. -/
def decrease (scratch saved failure : Nat) (bound : Int) (measure : List II) : List II :=
  narrowC scratch 0 bound measure (stopC failure scratch)
    ([ci 2 (scratch + 1) saved 0, ci 13 scratch scratch (scratch + 1)] ++
      guardC scratch failure scratch)

/-- `s` is the selected-index binder. `s+1` is the predecessor binder,
    `s+2` records that at least one live member was seen; expression scratch
    starts at `s+3`. Counter and saved measure are below the lexical context.
    `member` reads candidate::Γ; `preMember` and `edge` read predecessor::candidate::Γ.
    A predecessor edge immediately rejects the current candidate. Self edges
    are ignored, exactly as in `keinVorgaenger`. -/
def pieces (s counter saved fuel failure : Nat) (count bound : Int)
    (invariant member preMember edge measure body : List II) : List Piece :=
  let d := s + 3
  let post := decrease d saved failure bound measure
  [ .code (travCountC counter fuel), .label .header,
    .zero counter .stop,
    .code [ci 1 d 1 0, ci 4 counter counter d],
    .code invariant, .zero d .stop,
    .code [ci 1 s 0 0, ci 1 (s + 2) 0 0],
    .label .candidate,
    .code (travCountC (d + 1) count ++ [ci 13 d s (d + 1)]),
    .zero d .exhausted,
    .code member, .zero d .candidateNext,
    .code [ci 1 (s + 2) 1 0, ci 1 (s + 1) 0 0],
    .label .predecessor,
    .code (travCountC (d + 1) count ++ [ci 13 d (s + 1) (d + 1)]),
    .zero d .selected,
    .code [ci 14 d (s + 1) s], .zero d .different,
    .jump .predecessorNext, .label .different,
    .code preMember, .zero d .predecessorNext,
    .code edge, .zero d .predecessorNext,
    .jump .candidateNext,
    .label .predecessorNext,
    .code [ci 1 d 1 0, ci 3 (s + 1) (s + 1) d],
    .jump .predecessor,
    .label .candidateNext,
    .code [ci 1 d 1 0, ci 3 s s d], .jump .candidate,
    .label .exhausted, .zero (s + 2) .done, .jump .stop,
    .label .selected,
    .code measure, .code [ci 2 saved d 0],
    .code body,
    .label .afterBody, .code post, .jump .header,
    .label .leaveBody, .code post, .code invariant,
    .zero d .stop, .jump .done,
    .label .stop, .code (stopC failure d), .label .done ]

/-- Recover body-relative targets from the same symbolic fragment that is
    assembled. No separately maintained instruction-count formulas are used. -/
def targets (fragment : List Piece) : Option (Int × Int) := do
  let after ← position .afterBody fragment 0
  let leave ← position .leaveBody fragment 0
  pure (16 * ((leave : Int) - after), 0)

/-- The probe body is used only to locate labels. The actual body is lowered
    with those exact targets, and emission refuses if relocation changes its
    length. `next` and fallthrough both enter the post-measure check. -/
def emit (s counter saved fuel failure : Nat) (count bound : Int)
    (invariant member preMember edge measure : List II × Nat)
    (body : Int × Int → Option (List II × Nat)) : Option (List II × Nat) := do
  if fuel < 2 ^ 31 ∧ failure < 2 ^ 31 ∧ inW count count = true ∧ inW 0 bound = true then
    let probe ← body (0, 0)
    let fragment := pieces s counter saved fuel failure count bound
      invariant.1 member.1 preMember.1 edge.1 measure.1 probe.1
    let exits ← targets fragment
    let actual ← body exits
    if actual.1.length = probe.1.length then
      let instructions ← assemble (pieces s counter saved fuel failure count bound
        invariant.1 member.1 preMember.1 edge.1 measure.1 actual.1)
      pure (instructions,
        max invariant.2 (max member.2 (max preMember.2 (max edge.2
          (max measure.2 (max actual.2 (max (counter + 1) (max (saved + 1) (s + 11)))))))))
    else none
  else none

end Consuming
end Gabbro.Stage0.Senke
