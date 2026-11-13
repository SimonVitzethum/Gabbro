module
public import Grammatik.Parser.Elab.Export.ExportMetadata
import Grammatik.Kern.Taktik.KernelRfl
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

namespace Gabbro.Grammatik.Parser.ExportMetadata

/-- The header of the corpus loops is covered by the same declared effect, an unlisted declared
    effect is not, and a header with a second clause is refused. -/
theorem touchesCovered_zeuge :
    touchesCovered [.effs [.reads (.field (.variable "t") "slots"), .writes (.field (.variable "t") "slots")]]
      "touches writes t.slots" = true ∧
    touchesCovered [.effs [.reads (.field (.variable "t") "slots"), .writes (.variable "g")]]
      "touches reads t.slots" = false ∧
    touchesCovered [] "touches reads t.slots decreases n" = false := by
  decide +kernel

/-- A loop that assigns one static verifies a header listing it, although the function also
    writes a table; a header that omits the assigned static, or a body with a call, does not. -/
theorem touchesVerified_zeuge :
    touchesVerified "touches reads t.slots, writes sum"
      (.block [.set (.variable "sum") "=" (.lit 1)] none) = true ∧
    touchesVerified "touches reads t.slots"
      (.block [.set (.variable "sum") "=" (.lit 1)] none) = false ∧
    touchesVerified "touches writes sum"
      (.block [.set (.variable "sum") "=" (.call "f" [])] none) = false := by
  decide +kernel

/-- The header of the corpus loops is bound; one with a further section or without `progress` is not. -/
theorem retryHeaderBound_zeuge :
    retryHeaderBound "attempt until false bounded 3 ops progress tick on_exceeded sched_yield" = true ∧
    retryHeaderBound "attempt until false bounded 3 ops progress tick on_exceeded sched_yield effects { pure }" = false ∧
    retryHeaderBound "attempt until false bounded 3 ops on_exceeded sched_yield" = false := by
  decide +kernel

/-- The header of the corpus loops is bound and its plain form is read completely; a header with
    another handler, or without the pass bound, is not bound. -/
theorem foreverHeader_zeuge :
    ((foreverHeader "service per_pass bounded 16 ops on_exceeded stopped effects { pure } progress tick").map
      fun k => (k.label, k.bound, k.effects, k.progress, foreverPlain k.plain)) =
        some ("service", 16, "touches pure", "tick", true) ∧
    (foreverHeader "service per_pass bounded 16 ops on_exceeded halt effects { pure } progress tick").isNone = true ∧
    (foreverHeader "service per_pass bounded 16 ms on_exceeded stopped effects { pure } progress tick").isNone = true ∧
    (foreverHeader "service effects { pure } progress tick").isNone = true ∧
    foreverPlain "service per_pass bounded 16 ops on_exceeded stopped effects { pure } progress tick" = false := by
  decide +kernel

/-- A covered header of an ordinary traversal is erased, an uncovered one and a consuming header stay. -/
theorem eraseCovered_zeuge (body : SAnw) :
    eraseCovered (fun _ raw _ => raw == "h") [] 2 (.each "i" none "slots" (.variable "t") "unvisited" "h" none body) =
      .each "i" none "slots" (.variable "t") "unvisited" "" none (eraseCovered (fun _ raw _ => raw == "h") ["i"] 1 body) ∧
    eraseCovered (fun _ raw _ => raw == "h") [] 2 (.each "i" none "slots" (.variable "t") "unvisited" "x" none body) =
      .each "i" none "slots" (.variable "t") "unvisited" "x" none (eraseCovered (fun _ raw _ => raw == "h") ["i"] 1 body) ∧
    eraseCovered (fun _ raw _ => raw == "h") [] 2 (.each "i" none "slots" (.variable "t") "consuming" "h" none body) =
      .each "i" none "slots" (.variable "t") "consuming" "h" none (eraseCovered (fun _ raw _ => raw == "h") ["i"] 1 body) :=
  ⟨rfl, rfl, rfl⟩

/-- A loop that adds into a local of the enclosing block verifies a header that lists no write;
    the same assignment to a name that is no local in scope does not. -/
theorem touchesVerified_local_zeuge :
    touchesVerified "touches reads t.slots" (.block [.set (.variable "total") "=" (.lit 1)] none)
      ["total"] = true ∧
    touchesVerified "touches reads t.slots" (.block [.set (.variable "total") "=" (.lit 1)] none)
      [] = false := by
  decide +kernel

/-- Entry 13: a bound call, call-dependent narrowing with `next`, and an enclosing local update. -/
def traverseCallBody : SAnw :=
  .block [.bind false "v" none (.call "val" [.variable "i"]),
    .bind false "s" none (.bin "+" (.variable "acc") (.variable "v")),
    .trim (.variable "s") "0 .. 100" (.block [] (some (.next "i"))),
    .set (.variable "acc") "=" (.variable "s")] none

/-- Reads do not require header entries; the callee's write does. -/
def traverseCallEffects : CalleeEffects := fun name =>
  if name == "val" then some [.reads (.variable "source"), .writes (.variable "calls")] else none

theorem touchesVerified_call_zeuge :
    touchesVerified "touches writes calls" traverseCallBody ["i", "acc"] traverseCallEffects = true := by
  decide +kernel

theorem touchesVerified_call_unlisted_zeuge :
    touchesVerified "touches reads t.slots" traverseCallBody ["i", "acc"] traverseCallEffects = false := by
  decide +kernel

theorem touchesVerified_call_unknown_zeuge :
    touchesVerified "touches writes calls" traverseCallBody ["i", "acc"] (fun _ => none) = false := by
  decide +kernel

/-- A local pointer cannot borrow the effects of a unit function with the same name. -/
theorem touchesVerified_call_shadowed_zeuge :
    touchesVerified "touches writes calls" traverseCallBody ["i", "acc", "val"] traverseCallEffects = false ∧
    touchesVerified "touches writes calls"
      (.block [.bind false "val" none (.variable "pointer"), .call "val" []] none)
      [] traverseCallEffects = false := by
  decide +kernel

/-- Statement calls, calls in arguments, fallible bindings and handlers, and returned calls
    all contribute, in source order. Constructors themselves contribute no callee. -/
theorem bodyCalls_arguments_zeuge :
    bodyCalls 10 (.block
      [.call "outer" [.call "arg" []],
       .bindElse "x" none (.call "fallible" [.call "Some" [.call "nested" []]]) "why"
         (.block [.callElse "handle" [.call "input" []] "why" (.block [.call "recover" []] none)] none)]
      (some (.ret (some (.call "result" []))))) =
        some ["outer", "arg", "fallible", "nested", "handle", "input", "recover", "result"] := by
  kernel_rfl

/-- The production gate uses the unit signatures. An unrelated function write prevents the
    enclosing-signature shortcut, so these fixtures exercise body verification and erasure. -/
def traverseCallItems (header : String) (callee : String := "val") : List SItemTief :=
  [.fnT ⟨"impl", "val", [], none, none, [.effs [.writes (.variable "calls")]], []⟩ (.block [] none),
   .fnT ⟨"impl", "main", [], none, none,
      [.effs [.writes (.variable "calls"), .writes (.variable "spare")]], []⟩
     (.block [.bind true "acc" none (.lit 0),
       .each "i" none "slots" (.variable "t") "unvisited" header none
         (if callee == "val" then traverseCallBody else .block [.call callee []] none)] none)]

theorem touchesVerified_call_gate_zeuge :
    check (traverseCallItems "touches writes calls") = .ok () ∧
    check (traverseCallItems "touches reads t.slots") =
      .error "source export: function type/proof/header duties lack a checked source binding: main" ∧
    check (traverseCallItems "touches writes calls" "unknown") =
      .error "source export: function type/proof/header duties lack a checked source binding: main" := by
  refine ⟨by kernel_rfl, by kernel_rfl, by kernel_rfl⟩

end Gabbro.Grammatik.Parser.ExportMetadata
