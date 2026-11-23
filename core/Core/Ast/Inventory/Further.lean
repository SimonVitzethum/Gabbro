module

public import Core.Ast.Inventory.Entry

@[expose] public section

namespace Gabbro.Core.Inventory

/-- The additional source and authority forms of M6F. -/
def further : List SurfaceForm :=
[
  ⟨"further.async.function", "An async function with its ordinary contract and explicit suspension points", ⟨"dokumente/PLAN-COMPILER-READY.md", "S8"⟩⟩,
  ⟨"further.async.await", "Await a child call or a stored future", ⟨"dokumente/PLAN-COMPILER-READY.md", "S8"⟩⟩,
  ⟨"further.async.join", "Join futures, including heterogeneous child results", ⟨"dokumente/PLAN-COMPILER-READY.md", "S8"⟩⟩,
  ⟨"further.async.select", "Select a ready future and cancel the losers", ⟨"dokumente/PLAN-COMPILER-READY.md", "S8/O22"⟩⟩,
  ⟨"further.async.cancel", "Cancel explicitly and release the saved state under its contract", ⟨"dokumente/PLAN-COMPILER-READY.md", "S8/O22"⟩⟩,
  ⟨"further.async.spawn", "Spawn a task by transferring ownership of a future", ⟨"dokumente/PLAN-COMPILER-READY.md", "S8"⟩⟩,
  ⟨"further.async.blockOn", "Run a future to completion through the executor", ⟨"dokumente/PLAN-COMPILER-READY.md", "S8"⟩⟩,
  ⟨"further.async.executor", "Task queues, worker threads, wakeups, timers and readiness bindings", ⟨"dokumente/PLAN-COMPILER-READY.md", "S8"⟩⟩,
  ⟨"further.internal.index", "Statically checked internal index, slot, length and range access", ⟨"dokumente/PLAN-COMPILER-READY.md", "S9"⟩⟩,
  ⟨"further.internal.boundary", "Validate an outside value before putting it into internal state", ⟨"dokumente/PLAN-COMPILER-READY.md", "S9"⟩⟩,
  ⟨"further.internal.narrow", "Explicit failure path for validation or capacity exhaustion", ⟨"dokumente/PLAN-COMPILER-READY.md", "S9"⟩⟩,
  ⟨"further.internal.exit", "Maintain representation guarantees on success, reason and publishing exits", ⟨"dokumente/PLAN-COMPILER-READY.md", "S9"⟩⟩,
  ⟨"further.region.scope", "Declare a region whose authority ends at the enclosing block", ⟨"dokumente/PLAN-COMPILER-READY.md", "S10"⟩⟩,
  ⟨"further.region.allocate", "Allocate in a scope region with a declared capacity and failure channel", ⟨"dokumente/PLAN-COMPILER-READY.md", "S10"⟩⟩,
  ⟨"further.region.exit", "Release the region on normal, loop, return and reason exits", ⟨"dokumente/PLAN-COMPILER-READY.md", "S10"⟩⟩,
  ⟨"further.payload.publish", "Publish a plain payload through an atomic release", ⟨"dokumente/PLAN-COMPILER-READY.md", "B12"⟩⟩,
  ⟨"further.payload.await", "Acquire a plain payload through the confirming atomic observation", ⟨"dokumente/PLAN-COMPILER-READY.md", "B12"⟩⟩,
  ⟨"further.writer.invariant", "Declare an intermediate invariant inside a running writer", ⟨"dokumente/PLAN-COMPILER-READY.md", "B14"⟩⟩,
  ⟨"further.writer.mask", "Exclude handler observation of a writer's broken state by a checked mask", ⟨"dokumente/PLAN-COMPILER-READY.md", "B14"⟩⟩,
  ⟨"further.domain.declaration", "Declare a guest, process or compartment isolation domain", ⟨"dokumente/PLAN-COMPILER-READY.md", "B18"⟩⟩,
  ⟨"further.domain.channel", "Declare an authority-tracked channel between domains", ⟨"dokumente/PLAN-COMPILER-READY.md", "B18"⟩⟩]

end Gabbro.Core.Inventory
