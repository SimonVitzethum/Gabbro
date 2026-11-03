module
public import Grammatik.Parser.Elab.Modules.Frontend

import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section
namespace Gabbro.Grammatik.Parser.Instantiation

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private def sig (name : String) (params : List (String × STyp)) (result : Option STyp) : FnSig :=
  { art := "", name, params, res := result, fehler := none, klauseln := [] }

private def returnX : SAnw := .block [] (some (.ret (some (.variable "x"))))

/-- One module template, two generative uses; one generic function reached at two different
    types. Both modules also use the same capture-free callback literal, which must be shared
    and materialized only after the generic instance closure. -/
def fixture : List SItemTief :=
  [.fnT { sig "identity" [("x", .atom "T")] (some (.atom "T")) with
      generics := [.type "T" []] } returnX,
   .moduleTemplateT "box" [.type "T" [],
      .function "g" (.raw "fn(u8) -> u8 effects {} costs <= 8 ops")]
     [.fnT (sig "value" [("x", .atom "T")] (some (.atom "T")))
        (.block [.bind false "copy" none
          (.ext .instantiate ["identity", "T"] [.variable "x"])]
          (some (.ret (some (.variable "copy"))))),
      .fnT (sig "run" [("x", .atom "u8")] (some (.atom "u8")))
        (.block [.bind false "copy" none (.call "g" [.variable "x"])]
          (some (.ret (some (.variable "copy")))))],
   .moduleUseT "Bytes" ["box"] ["u8",
     "fn(x: u8) -> u8 effects {} costs <= 3 ops { return x; }"],
   .moduleUseT "Words" ["box"] ["u16",
     "fn(x: u8) -> u8 effects {} costs <= 3 ops { return x; }"]]

def fixtureOutput : List SItemTief := (Modules.instantiate fixture).toOption.getD []

/-- This proves successful expansion and its non-degeneracy jointly: seven different function
    declarations, both module copies, both concrete function instances and one named literal.
    An empty/default output, refused input or an unused generic declaration cannot satisfy it. -/
theorem fixture_shape_zeuge :
    (Modules.instantiate fixture).map (fun q =>
      (functionNames q).length == 7 &&
      (Modules.generatedOutputNames fixture q).length == 7 &&
      (directReferences q).length == 4 &&
      ([Modules.memberName ["Bytes", "value"], Modules.memberName ["Bytes", "run"],
        Modules.memberName ["Words", "value"], Modules.memberName ["Words", "run"],
        Generic.instanceName ⟨"identity", ["u8"]⟩,
        Generic.instanceName ⟨"identity", ["u16"]⟩,
        Generic.literalName "fn ( x : u8 ) -> u8 effects { } costs <= 3 ops { return x ; }"].all
        ((functionNames q).contains))) = .ok true := by decide +kernel

private theorem fixture_success : Modules.instantiate fixture = .ok fixtureOutput := by
  have shape := fixture_shape_zeuge
  unfold fixtureOutput
  cases hr : Modules.instantiate fixture with
  | error error => simp [hr] at shape
  | ok output => rfl

/-- The exact same successful, non-degenerate output inhabits all generic theorem premises. -/
theorem instantiate_zeuge :
    Modules.instantiate fixture = .ok fixtureOutput ∧
    ohneGenerik fixtureOutput = true ∧
    (Modules.generatedOutputNames fixture fixtureOutput).Nodup ∧
    (∀ name ∈ Modules.generatedOutputNames fixture fixtureOutput, name ∉ Modules.userNames fixture) ∧
    (∀ name ∈ directReferences fixtureOutput, name ∈ functionNames fixtureOutput) := by
  have hygiene := Modules.instantiate_nameHygiene fixture fixtureOutput fixture_success
  exact ⟨fixture_success, Modules.instantiate_ohneGenerik _ _ fixture_success,
    hygiene.1, hygiene.2, Modules.instantiate_closed _ _ fixture_success⟩

/-- Collision checking refuses repeated generated names as well as source-name collisions. -/
theorem collision_check_zeuge :
    Generic.checkInstanceNames [] [⟨"f", ["u8"]⟩, ⟨"f", ["u8"]⟩] =
      .error "generic-instance-name-collision: generated instance name is already declared" ∧
    Generic.checkInstanceNames [Generic.instanceName ⟨"f", ["u8"]⟩] [⟨"f", ["u8"]⟩] =
      .error "generic-instance-name-collision: generated instance name is already declared" := by
  decide +kernel

/-- A generic expression hidden below a condition and a block ender is not an ordinary form. -/
theorem nested_generic_form_refused_zeuge :
    Modules.instantiate [.fnT (sig "entry" [] none)
      (.block [.cond .tru (.block [] (some (.ret (some
        (.ext .instantiate ["f", "fn() effects {} costs <= 1 ops { return; }"] []))))) [] none]
        none)] =
      .error "dyn.output" := rfl

/-- Unchanged direct calls are checked too, recursively inside argument expressions. -/
theorem nested_dangling_refused_zeuge :
    Modules.instantiate [.fnT (sig "entry" [] none)
      (.block [.call "entry" [.call "missing" []]] none)] =
      .error "generic-output: residual syntax, name collision or unresolved direct global reference" := rfl

/-- Function addresses participate even if they are never called. -/
theorem dangling_address_refused_zeuge :
    Modules.instantiate [.constT "address" (.raw "fn() effects {} costs <= 1 ops")
      (.one (.fnref "missing"))] =
      .error "generic-output: residual syntax, name collision or unresolved direct global reference" := rfl

/-- Local indirect calls and builtin heads keep the old path; this is no acceptance claim. -/
theorem builtin_and_indirect_exception_zeuge :
    (Modules.instantiate [.fnT
      (sig "entry" [("callback", .raw "fn() effects {} costs <= 1 ops")] none)
      (.block [.call "callback" [], .bind false "value" none (.call "Some" [.lit 1])]
        (some (.ret none)))]).toOption.isSome = true := rfl

/-- A later binder cannot turn an earlier unresolved global call into an indirect call. -/
theorem later_local_does_not_hide_global_zeuge :
    Modules.instantiate [.fnT (sig "entry" [] none)
      (.block [.call "missing" [], .bind false "missing" none (.lit 0)] none)] =
      .error "generic-output: residual syntax, name collision or unresolved direct global reference" := rfl

/-- Reserved generated targets are checked even under a malicious same-spelling local binder. -/
theorem generated_target_cannot_be_hidden_zeuge :
    Modules.instantiate [.fnT (sig "entry" [("$literal$missing", .atom "u8")] none)
      (.block [.call "$literal$missing" []] none)] =
      .error "generic-output: residual syntax, name collision or unresolved direct global reference" := rfl

/-- The same surface address constructor can denote a table capability. That case remains
    outside function-reference closedness; a genuine function address is still checked. -/
theorem table_address_exception_zeuge :
    (Modules.instantiate [.tableT "Cells" none (some (.lit 1)) none none false [],
      .fnT (sig "entry" [] none) (.block
        [.bind false "cells" none (.fnref "Cells"),
         .bind false "function" none (.fnref "entry")] none)]).toOption.isSome = true := rfl

theorem function_address_is_global_under_local_shadowing_zeuge :
    Modules.instantiate [.fnT (sig "entry" [("missing", .atom "u8")] none)
      (.block [.bind false "function" none (.fnref "missing")] none)] =
      .error "generic-output: residual syntax, name collision or unresolved direct global reference" := rfl

end Gabbro.Grammatik.Parser.Instantiation
