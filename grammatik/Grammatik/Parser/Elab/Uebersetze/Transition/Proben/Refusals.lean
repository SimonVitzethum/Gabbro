module

public import Grammatik.Parser.Elab.Uebersetze.Transition.Proben.Export

public section

namespace Gabbro.Grammatik.Parser.TransitionProben

open Uebersetze UebersetzeAllg UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 0

@[expose] def refused : Except String α → Bool
  | .error _ => true
  | .ok _ => false

theorem omitted_effect_refused_zeuge :
    refused (uZustand "S" [{ guarded with wirkung := [] }] ctx) = true := by decide +kernel

theorem omitted_lock_refused_zeuge :
    refused (uZustand "S" [{ guarded with voraus := some (slot 1 "flag") }] ctx) = true := by
  decide +kernel

theorem pure_store_refused_zeuge :
    refused (uZustand "S" [{ ordered with wirkung := .pure :: ordered.wirkung }] ctx) = true := by
  decide +kernel

theorem resource_flow_refused_zeuge :
    refused (uZustand "S" [{ ordered with wirkung := .takes (.variable "M") :: ordered.wirkung }] ctx) = true := by
  decide +kernel

theorem lock_effect_does_not_acquire_zeuge :
    refused (uZustand "S" [{ ordered with wirkung := .locks false (.variable "L") :: ordered.wirkung }] ctx) = true := by
  decide +kernel

@[expose] def atomicCtx : UCtx :=
  { ctx with globs := { name := "A", ty := .int 0 2, init := 0, var := true,
      atomic := true, shared := true } :: ctx.globs }

theorem shared_atomic_precondition_refused_zeuge :
    refused (uZustand "S" [{ ordered with voraus := some (.bin "==" (.variable "A") (.lit 0)) }]
      atomicCtx) = true := by decide +kernel

@[expose] def aliasedDeclaration : Option (Except String UFn) := do
  let state ← (uZustand "S" [{ ordered with schritte := [(slot 0 "s", .lit 0, .lit 1),
      (slot 0 "s", .lit 0, .lit 2)] }] ctx).toOption
  let tr ← state.transitions.head?
  pure (uGenerateTransition ctx state.name tr)

theorem aliases_refused_zeuge : aliasedDeclaration =
    some (.error "transition targets alias or lack an equal-result agreement proof") := by
  decide +kernel

@[expose] def ambiguous : Option (Except String UStmt) := do
  let state ← (uZustand "S" [guarded, { falseGuard with tname := "other" }] ctx).toOption
  pure (uTransitionAt [state] "T" "s" (.lit 1) "Idle" "Busy")

theorem equal_edges_do_not_identify_clauses_zeuge : ambiguous =
    some (.error "transition declared by two clauses or states") := by decide +kernel

@[expose] def unboundEndpoint : STrans :=
  { ordered with schritte := [(slot 0 "s", .lit 0, .bin "+" (.variable "capture") (.lit 1))] }

theorem unbound_capture_refused_zeuge :
    refused (uZustand "S" [unboundEndpoint] ctx) = true := by decide +kernel

/-- Only ordinary function lowering is exercised here. This candidate unit
    is deliberately rejected by the source expansion gate in lowerAllg. -/
@[expose] def candidate (tr : STrans) (callerHeld : List String := ["L"]) : Option UProg := do
  let state ← (uZustand "S" [tr] ctx).toOption
  let tr ← state.transitions.head?
  let generated ← (uGenerateTransition ctx state.name tr).toOption
  let args ← (uTransitionArguments tr.writes none).toOption
  let caller : UFn :=
    { name := "caller", params := [], kinds := [], res := none, held := callerHeld,
      puts := generated.puts, gputs := generated.gputs, gives := [],
      body := [.call generated.name args], ret := .empty }
  pure (uMitBoden { tabs := ctx.tabs, locks := ctx.locks, globs := ctx.globs,
    fns := [caller, generated], zustaende := [state] })

@[expose] def candidateCallLowers (tr : STrans) (callerHeld : List String := ["L"]) : Bool :=
  match candidate tr callerHeld with
  | none => false
  | some u =>
    if h : 0 < u.fns.length then
      match lowerFnAt u ⟨0, h⟩ with
      | .ok _ => true
      | .error _ => false
    else false

theorem ordinary_call_lowering_zeuge : candidateCallLowers ordered = true := by decide +kernel

theorem out_of_range_endpoint_refused_zeuge :
    candidateCallLowers { ordered with schritte := [(slot 0 "s", .lit 0, .lit 3)] } = false := by
  decide +kernel

theorem ordinary_resource_check_retained_zeuge : candidateCallLowers ordered [] = false := by
  decide +kernel

end Gabbro.Grammatik.Parser.TransitionProben
