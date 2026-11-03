module
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil5
@[expose] public section
namespace Gabbro.Grammatik.Parser.UebersetzeAllg2
open Uebersetze UebersetzeAllg

/-- The foreign contract's parameter names and result context, with no body. -/
def axContractFn (u : UProg) (a : Fin u.axs.length) : UFn :=
  let ax := uaxAt u a
  { name := ax.name, params := ax.names.zip ax.params, kinds := ax.kinds,
    res := none, resTy := ax.res, held := [], puts := ax.puts, gputs := ax.gputs,
    needs := ax.needs, gives := ax.gives, body := [], ret := .empty }

/-- Foreign contracts use the canonical C08 signature, including its exact
    argument and result types. Lowering failure is part of the unit gate. -/
def lowerAxContract (u : UProg) (a : Fin u.axs.length) :
    Except String (CallContract (declOf u) ((declOf u).asignatur a)) := do
  let pre ← lowEnsList u ((declOf u).aparams a) [] (axContractFn u a) none
    (uaxAt u a).needs
  let post ← lowEnsList u (ErgCtx ((declOf u).aparams a) ((declOf u).aerg a)) []
    (axContractFn u a) ((declOf u).aerg a) (uaxAt u a).gives
  pure { pre, post }

/-- Every foreign contract must lower; a bad predicate is never replaced by true. -/
def axContractsB (u : UProg) : Bool :=
  (List.finRange u.axs.length).all fun a => (lowerAxContract u a).isOk

/-- Total projection for program assembly, used only behind axContractsB.
    The success theorem below identifies the exact retained contract. -/
def axVertragOf (u : UProg) (a : Fin u.axs.length) :
    CallContract (declOf u) ((declOf u).asignatur a) :=
  (lowerAxContract u a).toOption.getD (callVertragWahr (declOf u) _)

theorem axVertragOf_exact (u : UProg) (a : Fin u.axs.length)
    (h : axContractsB u = true) :
    lowerAxContract u a = .ok (axVertragOf u a) := by
  have ha := List.all_eq_true.mp h a (List.mem_finRange a)
  cases hl : lowerAxContract u a with
  | error error => simp [hl] at ha
  | ok contract => simp [axVertragOf, hl]

end Gabbro.Grammatik.Parser.UebersetzeAllg2
