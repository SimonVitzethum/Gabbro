module

public import Grammatik.Parser.Elab.UebersetzeAllg.Teil2
public import Grammatik.Parser.Elab.Generic.C09Flows

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg

open Gabbro.Grammatik.Parser.Uebersetze

/-! ## Resolved owner-flow signatures (C09): moves, loans and mints -/

/-- The owner flow of a signature number: the moves, loans and mints of the resolved function
    (C12 loans, C09 moves and mints) -- the dummy has none. -/
theorem sigAt_owner (u : UProg) (n : Nat) (h : n < (sigFns u).length) :
    (sigAt u n).owner = { moves := ownerMovesAt u ((sigFns u).get ⟨n, h⟩),
      loans := leihtAt u ((sigFns u).get ⟨n, h⟩),
      mints := praegtAt u ((sigFns u).get ⟨n, h⟩) } := by
  unfold sigAt
  rw [dif_pos h]

/-- The owner flow of an elaborated function: its resolved moves, loans and mints. -/
theorem signaturOwner (u : UProg) (f : Fin u.fns.length) :
    ((declOf u).signatur f).owner = { moves := ownerMovesAt u (fnAt u f),
      loans := leihtAt u (fnAt u f), mints := praegtAt u (fnAt u f) } := by
  show (sigAt u f.val).owner = _
  rw [sigAt_get]

/-- The contract end: held locks plus produced marks (resolved, C16), the
    handed-back moves (C09) and the returned call-scoped loans (C12) -- loans
    come back on normal return -- plus the checked mints (C09). -/
theorem ende_eq (u : UProg) (f : Fin u.fns.length) :
    (vertragVon (declOf u) f).ende =
      (heldAt u (fnAt u f)).map (Res.held (D := declOf u)) ++
        (((gibtAt u (fnAt u f)) ++ (bewegtAt u (fnAt u f)) ++ (leihtAt u (fnAt u f)) ++
          (praegtAt u (fnAt u f))).map (Res.vonMarke (declOf u))) := by
  have hO : ((declOf u).signatur f).owner = { moves := ownerMovesAt u (fnAt u f),
      loans := leihtAt u (fnAt u f), mints := praegtAt u (fnAt u f) } :=
    signaturOwner u f
  have hOut : ((declOf u).signatur f).owner.outputs =
      (bewegtAt u (fnAt u f)) ++ (leihtAt u (fnAt u f)) ++ (praegtAt u (fnAt u f)) := by
    rw [hO]
    simp only [OwnerFlow.outputs, ownerMovesAt_outputs]
  simp only [vertragVon, Vertrag.vonSig, Vertrag.ende, Deklaration.signatur,
    declOf, sigAt_haelt, sigAt_produziert, hO, hOut, Signatur.outputMarks,
    List.map_append]

end Gabbro.Grammatik.Parser.UebersetzeAllg
