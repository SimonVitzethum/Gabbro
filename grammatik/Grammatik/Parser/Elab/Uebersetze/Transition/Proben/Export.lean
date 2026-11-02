module

public import Grammatik.Parser.Elab.UebersetzeAllg3

public section

namespace Gabbro.Grammatik.Parser.TransitionProben

open Uebersetze UebersetzeAllg UebersetzeAllg2

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Direct surface trees avoid unrelated lexer/parser fuel in these probes. -/
@[expose] def ctx : UCtx :=
  { names := [], kinds := [], types := [], res := none, fname := "transition", alias := [], lits := [],
    tabs := [{ name := "T", count := 2, cols := [("s", (0, 2)), ("t", (0, 2)), ("flag", (0, 1))],
      bools := ["flag"] }],
    globs := [{ name := "G", ty := .int 0 2, init := 0, var := true }],
    locks := [{ name := "L", rank := 0, guard := ["T", "G"] }], held := [] }

@[expose] def slot (i : Nat) (field : String) : SExpr :=
  .field (.index (.field (.variable "T") "slots") (.lit i)) field

@[expose] def held : SExpr := .call "Held" [.variable "L"]

@[expose] def guarded : STrans :=
  { tname := "begin", schritte := [(.variable "s", .variable "Idle", .variable "Busy")],
    voraus := some (.bin "&&" held (slot 1 "flag")),
    wirkung := [.writes (.field (.variable "T") "slots")] }

@[expose] def falseGuard : STrans := { guarded with voraus := some (.bin "&&" held .fls) }

@[expose] def requiresOnly : STrans :=
  { tname := "ready", schritte := [], voraus := some held, wirkung := [.pure] }

/-- The second endpoint reads the first target in the entry world. -/
@[expose] def ordered : STrans :=
  { tname := "cycle", schritte := [(slot 0 "s", .lit 0, .lit 1),
      (.variable "G", .lit 0, slot 0 "s")], voraus := some held,
    wirkung := [.writes (.field (.variable "T") "slots"), .writes (.variable "G")] }

@[expose] def summary (tr : STrans) : Option (List String × List UEns × List UStmt) := do
  let state ← (uZustand "S" [tr] ctx).toOption
  let f ← (uGenerateTransitions ctx.tabs ctx.globs [state]).toOption
  let f ← f.head?
  pure (f.params.map (·.1), f.needs, f.body)

/-- A guarded single constant edge generates the primitive shift of its state,
    capturing only its index; its edge joins the state graph. -/
theorem guarded_generation_zeuge :
    (summary guarded).map (fun (params, _, body) => (params, body)) =
      some (["#index0"], [.shiftTab "T" "s" (.param "#index0") "S" 0 1]) := by decide +kernel

theorem guarded_edge_in_graph_zeuge :
    ((uZustand "S" [guarded] ctx).toOption.map (·.paare)) = some [(0, 1)] := by decide +kernel

/-- A declaration of several writes keeps the captured stores and adds no graph edge. -/
theorem ordered_adds_no_graph_edge_zeuge :
    ((uZustand "S" [ordered] ctx).toOption.map (·.paare)) = some [] := by decide +kernel

theorem false_guard_preserved_zeuge :
    (summary falseGuard).map (fun (_, needs, _) => needs.head?) = some (some (.and .fls .tru)) := by
  decide +kernel

theorem requires_only_generation_zeuge : summary requiresOnly = some ([], [.tru], []) := by
  decide +kernel

theorem ordered_entry_endpoints_zeuge :
    (summary ordered).map (fun (_, _, body) => body) =
      some [.assignTab "T" "s" (.param "#index0") (.param "#target0"),
        .assignGlob "G" (.param "#target1")] := by decide +kernel

@[expose] def namedCandidates : Option (String × List UArg) := do
  let state ← (uZustand "S" [ordered] ctx).toOption
  let tr ← state.transitions.head?
  let args ← (uTransitionArguments tr none).toOption
  pure (uTransitionFunction state.name tr.name, args)

theorem entry_capture_arguments_zeuge : namedCandidates =
    some ("#transition#S#cycle", [.val (.lit 0), .val (.lit 0), .val (.lit 1),
      .val (.lit 0), .val (.tab "T" "s" (.lit 0))]) := by decide +kernel

/-- The constant edge supplies only its index at a use site. -/
theorem shift_capture_arguments_zeuge :
    (do let state ← (uZustand "S" [guarded] ctx).toOption
        let tr ← state.transitions.head?
        (uTransitionArguments tr (some (.lit 1))).toOption) = some [UArg.val (.lit 1)] := by
  decide +kernel

end Gabbro.Grammatik.Parser.TransitionProben
