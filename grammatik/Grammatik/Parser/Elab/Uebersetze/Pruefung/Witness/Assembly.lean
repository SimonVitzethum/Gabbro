module

public import Grammatik.Parser.Elab.UebersetzeAllg3.TransitionCert
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a

public section
namespace Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

-- Replay the complete real assembler with symbolic dependent endpoints.
-- Each check remains mandatory; the value is precisely progOfFn's full pair,
-- including invariants, pointer/foreign contracts and the actual measure gate.
private theorem check_assembly (u : UProg)
    (functions : ∀ f : Fin u.fns.length, EnsTy u f × RumpTy u f × ReqTy u f)
    (made : ∀ f : Fin u.fns.length, lowerFnAt u f = .ok (functions f))
    (invariants : lowerInvs u (List.finRange u.invs.length) = .ok ())
    (each : lowerEach u (List.finRange u.fns.length) = .ok ())
    (contracts : contractGate u = true)
    (measures : ∀ P : Programm (declOf u),
      Measures.checkedProgram u P = .ok (P, List.finRange u.fns.length)) :
    lowerAllg u = .ok
      (progOfFn u
        (fun f => (functions f).1)
        (fun f => (functions f).2.1)
        (fun f => (functions f).2.2)
        (fun i => lowerInvGut u i
          (lowerInvs_all_ok u _ i (List.mem_finRange i) invariants))
        (ptrVertragOf u)
        (fun a => axVertragOf u a (Bool.and_eq_true_iff.mp contracts).2),
        List.finRange u.fns.length) := by
  have paired (f : Fin u.fns.length) (success : ∃ value, lowerFnAt u f = .ok value) :
      lowerAtPair u f success = functions f :=
    lowerAtPair_of_ok u f success (made f)
  simp only [lowerAllg, invariants, each, dif_pos contracts, measures, paired] <;> rfl

end Gabbro.Grammatik.Parser.Uebersetze
