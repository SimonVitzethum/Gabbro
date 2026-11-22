module

public import Stage0.Frontend.Async.Lowering

namespace Gabbro.Stage0.Frontend.Async
open Gabbro.Grammatik Gabbro.Grammatik.Async
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Async.Segment
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Async.Representation

public structure PollEntry (u : UProg) where
  sourceName : String
  slot : (declOf u).Fn
  selected : fnNr u (pollName sourceName) = .ok slot
  body : Endblock (declOf u) (vertragVon (declOf u) slot) false
    ((declOf u).params slot) (Signatur.anfang (declOf u) ((declOf u).signatur slot))

@[expose] public def NamedPoll.entry {u : UProg} {ctx : UCtx} {function : AsyncFn} {types : TypeResolution}
    {children : (fn : (declOf u).Fn) → (name : String) →
      Option (ResolvedPoll u (verOf u fn) (resOf u fn) types name)}
    (resolved : NamedPoll u ctx function types children) : PollEntry u :=
  ⟨function.name, resolved.poll, resolved.selected, resolved.body⟩

/-- Install a body at its dependent function slot. Every ordinary body
    outside that slot is preserved. -/
@[expose] public def PollEntry.install {u : UProg}
    (entry : PollEntry u) (program : Programm (declOf u)) :
    Programm (declOf u) :=
  letI : DecidableEq (declOf u).Fn := inferInstanceAs (DecidableEq (Fin u.fns.length))
  { program with rumpf := fun fn =>
      if equal : fn = entry.slot then equal.symm ▸ entry.body
      else program.rumpf fn }

public theorem PollEntry.install_body {u : UProg} (entry : PollEntry u)
    (program : Programm (declOf u)) :
    (entry.install program).rumpf entry.slot = entry.body := by
  simp only [PollEntry.install, dite_true]

public theorem PollEntry.install_other {u : UProg} (entry : PollEntry u)
    (program : Programm (declOf u)) (fn : (declOf u).Fn) (other : fn ≠ entry.slot) :
    (entry.install program).rumpf fn = program.rumpf fn := by
  simp only [PollEntry.install, dite_eq_right other]

@[expose] public def NamedPoll.install {u : UProg} {ctx : UCtx} {function : AsyncFn} {types : TypeResolution}
    {children : (fn : (declOf u).Fn) → (name : String) →
      Option (ResolvedPoll u (verOf u fn) (resOf u fn) types name)}
    (resolved : NamedPoll u ctx function types children) (program : Programm (declOf u)) :
    Programm (declOf u) :=
  resolved.entry.install program

public theorem NamedPoll.install_body {u : UProg} {ctx : UCtx} {function : AsyncFn} {types : TypeResolution}
    {children : (fn : (declOf u).Fn) → (name : String) →
      Option (ResolvedPoll u (verOf u fn) (resOf u fn) types name)}
    (resolved : NamedPoll u ctx function types children) (program : Programm (declOf u)) :
    (resolved.install program).rumpf resolved.poll = resolved.body :=
  resolved.entry.install_body program

public theorem NamedPoll.install_other {u : UProg} {ctx : UCtx} {function : AsyncFn} {types : TypeResolution}
    {children : (fn : (declOf u).Fn) → (name : String) →
      Option (ResolvedPoll u (verOf u fn) (resOf u fn) types name)}
    (resolved : NamedPoll u ctx function types children) (program : Programm (declOf u))
    (fn : (declOf u).Fn) (other : fn ≠ resolved.poll) :
    (resolved.install program).rumpf fn = program.rumpf fn :=
  resolved.entry.install_other program fn other

@[expose] public def installPollEntries {u : UProg} (program : Programm (declOf u)) :
    List (PollEntry u) → Programm (declOf u)
  | [] => program
  | entry :: rest => entry.install (installPollEntries program rest)

public theorem installPollEntries_other {u : UProg} (program : Programm (declOf u))
    (fn : (declOf u).Fn) (entries : List (PollEntry u))
    (outside : fn ∉ entries.map PollEntry.slot) :
    (installPollEntries program entries).rumpf fn = program.rumpf fn := by
  induction entries with
  | nil => rfl
  | cons entry rest preserve =>
    rw [List.map_cons, List.mem_cons] at outside
    rw [installPollEntries, entry.install_other _ fn (fun same => outside (.inl same))]
    exact preserve (fun inside => outside (.inr inside))

public theorem installPollEntries_body {u : UProg} (program : Programm (declOf u))
    (entry : PollEntry u) (entries : List (PollEntry u))
    (distinct : (entries.map PollEntry.slot).Nodup) (present : entry ∈ entries) :
    (installPollEntries program entries).rumpf entry.slot = entry.body := by
  induction entries with
  | nil => cases present
  | cons first rest found =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp distinct
    rcases List.mem_cons.mp present with same | later
    · subst first
      exact entry.install_body _
    · have other : entry.slot ≠ first.slot := by
        intro equal
        have member : entry.slot ∈ rest.map PollEntry.slot := List.mem_map_of_mem later
        exact fresh (equal ▸ member)
      rw [installPollEntries, first.install_other _ entry.slot other]
      exact found tail later

private theorem fnIdx_name {functions : List UFn} {name : String} {index : Fin functions.length}
    (selected : fnIdx functions name = .ok index) : (functions.get index).name = name := by
  induction functions with
  | nil => exact index.elim0
  | cons first rest ih =>
    by_cases named : (first.name == name) = true
    · simp only [fnIdx, named, ite_true, Except.ok.injEq] at selected
      subst index
      exact eq_of_beq named
    · cases found : fnIdx rest name with
      | error failure =>
        simp only [fnIdx, named, ite_false, found] at selected
        cases selected
      | ok next =>
        simp only [fnIdx, named, Bool.false_eq_true, ite_false, found, Except.ok.injEq] at selected
        subst index
        exact ih found

private theorem PollEntry.name_of_same_slot {u : UProg} {left right : PollEntry u}
    (same : left.slot = right.slot) : left.sourceName = right.sourceName := by
  have names := (fnIdx_name left.selected).symm.trans (same.symm ▸ fnIdx_name right.selected)
  exact (String.append_right_inj "$async$poll$").mp names

private theorem pollSlots_distinct {u : UProg} {entries : List (PollEntry u)}
    (names : (entries.map PollEntry.sourceName).Nodup) : (entries.map PollEntry.slot).Nodup := by
  induction entries with
  | nil => exact List.nodup_nil
  | cons first rest ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp names
    apply List.nodup_cons.mpr
    refine ⟨?_, ih tail⟩
    rintro member
    obtain ⟨other, present, same⟩ := List.mem_map.mp member
    exact fresh (List.mem_map.mpr ⟨other, present, PollEntry.name_of_same_slot same⟩)

/-- Distinct source declarations place every generated body in its own
    slot. The linked program is constructed directly from that property. -/
public structure LinkedPolls (u : UProg) (base : Programm (declOf u))
    (entries : List (PollEntry u)) where
  program : Programm (declOf u)
  installed : program = installPollEntries base entries
  distinct : (entries.map PollEntry.slot).Nodup

private def lowerPollEntries {u : UProg}
    (lower : (function : AsyncFn) → Except String { entry : PollEntry u // entry.sourceName = function.name }) :
    (functions : List AsyncFn) → Except String
      { entries : List (PollEntry u) // entries.map PollEntry.sourceName = functions.map AsyncFn.name }
  | [] => .ok ⟨[], rfl⟩
  | function :: rest => do
    let entry ← lower function
    let tail ← lowerPollEntries lower rest
    pure ⟨entry.val :: tail.val, by simp only [List.map_cons, entry.property, tail.property]⟩

/-- Lower the checked order, retaining its exact declaration names.
    Slot uniqueness follows from canonical resolution of those names. -/
public def linkPolls {u : UProg} {functions : List AsyncFn}
    (base : Programm (declOf u)) (order : OrderedAsync functions)
    (lower : (function : AsyncFn) → Except String { entry : PollEntry u // entry.sourceName = function.name }) :
    Except String (Σ entries : List (PollEntry u), LinkedPolls u base entries) := do
  let ⟨entries, names⟩ ← lowerPollEntries lower order.declarations
  have distinct : (entries.map PollEntry.sourceName).Nodup := names.symm ▸ (asyncOrder_sound order.checked).1
  pure ⟨entries, ⟨installPollEntries base entries, rfl, pollSlots_distinct distinct⟩⟩

public theorem LinkedPolls.body {u : UProg} {base : Programm (declOf u)} {entries : List (PollEntry u)}
    (linked : LinkedPolls u base entries) (entry : PollEntry u) (present : entry ∈ entries) :
    linked.program.rumpf entry.slot = entry.body := by
  rw [linked.installed]
  exact installPollEntries_body base entry entries linked.distinct present

public theorem LinkedPolls.other {u : UProg} {base : Programm (declOf u)} {entries : List (PollEntry u)}
    (linked : LinkedPolls u base entries) (fn : (declOf u).Fn) (outside : fn ∉ entries.map PollEntry.slot) :
    linked.program.rumpf fn = base.rumpf fn := by
  rw [linked.installed]
  exact installPollEntries_other base fn entries outside

@[expose] public def pollCallOutcome {D : Deklaration} (fn : D.Fn) {Γ : Ctx} :
    EndAusgang (vertragVon D fn) false Γ → RufAusgang fn
  | .zurueck after value => .ok after value
  | .why after reason => .why after reason
  | .logik failure => .logik failure
  | .hardware failure => .hardware failure
  | .leave impossible .. | .next impossible .. => nomatch impossible

private theorem pollCallContext {D : Deklaration} {fn : D.Fn} {Γ Δ : Ctx} {Λ : List (Res D)}
    (context : Γ = Δ) (body : Endblock D (vertragVon D fn) false Δ Λ)
    (oracle : Orakel D) (passes : Nat) (calls : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (world : World D) (args : Env D Δ) :
    pollCallOutcome fn (execEnd oracle passes calls (context.symm ▸ body) world (context.symm ▸ args)) =
      pollCallOutcome fn (execEnd oracle passes calls body world args) := by
  cases context
  rfl

private theorem rufRumpf_pollOutcome {D : Deklaration} (program : Programm D) (oracle : Orakel D)
    (passes depth : Nat) (fn : D.Fn) (world : World D) (args : Env D (D.params fn)) :
    rufRumpf program oracle passes (depth + 1) fn world args =
      pollCallOutcome fn (execEnd oracle passes (rufRumpf program oracle passes depth) (program.rumpf fn) world args) := by
  rw [rufRumpf]
  cases execEnd oracle passes (rufRumpf program oracle passes depth) (program.rumpf fn) world args with
  | leave impossible | next impossible => cases impossible
  | zurueck | why | logik | hardware => rfl

/-- The actual call handler runs the selected body in the fully linked
    program. Every child call uses that same program at the smaller depth. -/
public theorem NamedPoll.linkedCall_refines {u : UProg} {ctx : UCtx}
    {function : AsyncFn} {types : TypeResolution}
    {children : (fn : (declOf u).Fn) → (name : String) →
      Option (ResolvedPoll u (verOf u fn) (resOf u fn) types name)}
    (resolved : NamedPoll u ctx function types children) (program : Programm (declOf u))
    (linked : program.rumpf resolved.poll = resolved.body)
    (oracle : Orakel (declOf u)) (passes depth : Nat) (prices : (declOf u).Fn → Nat)
    (inventory : Inventory (declOf u)) (fixed : FixedActivationInventory (f := function) inventory)
    (source : State (Value (declOf u)) (Child (declOf u) types)) (world : World (declOf u))
    (record : Wert (declOf u) (stateType types function))
    (represented : Inv function types inventory source record) :
    let calls := rufRumpf program oracle passes depth
    let actual := execEnd oracle passes calls
      (pollFunction resolved.expanded.phases resolved.result resolved.inventory) world (.cons record .nil)
    rufRumpf program oracle passes (depth + 1) resolved.poll world
        (resolved.input.symm ▸ Env.cons record .nil) = pollCallOutcome resolved.poll actual ∧
      PollFunctionRefines inventory resolved.result actual
        (resolvedPoll resolved.expanded.elaboration calls prices source world) := by
  intro calls actual
  refine ⟨?_, pollFunction_refines resolved.expanded.phases inventory fixed resolved.result resolved.inventory
    oracle passes calls prices source world record represented⟩
  rw [rufRumpf_pollOutcome, linked]
  change pollCallOutcome resolved.poll (execEnd oracle passes calls
      (resolved.input.symm ▸ pollFunction resolved.expanded.phases resolved.result resolved.inventory)
      world (resolved.input.symm ▸ Env.cons record .nil)) = _
  exact pollCallContext resolved.input _ oracle passes calls world _

public theorem NamedPoll.call_refines {u : UProg} {ctx : UCtx}
    {function : AsyncFn} {types : TypeResolution}
    {children : (fn : (declOf u).Fn) → (name : String) →
      Option (ResolvedPoll u (verOf u fn) (resOf u fn) types name)}
    (resolved : NamedPoll u ctx function types children) (program : Programm (declOf u))
    (oracle : Orakel (declOf u)) (passes depth : Nat) (prices : (declOf u).Fn → Nat)
    (inventory : Inventory (declOf u)) (fixed : FixedActivationInventory (f := function) inventory)
    (source : State (Value (declOf u)) (Child (declOf u) types)) (world : World (declOf u))
    (record : Wert (declOf u) (stateType types function))
    (represented : Inv function types inventory source record) :
    let installed := resolved.install program
    let calls := rufRumpf installed oracle passes depth
    let actual := execEnd oracle passes calls
      (pollFunction resolved.expanded.phases resolved.result resolved.inventory) world (.cons record .nil)
    rufRumpf installed oracle passes (depth + 1) resolved.poll world
        (resolved.input.symm ▸ Env.cons record .nil) = pollCallOutcome resolved.poll actual ∧
      PollFunctionRefines inventory resolved.result actual
        (resolvedPoll resolved.expanded.elaboration calls prices source world) :=
  resolved.linkedCall_refines (resolved.install program) (resolved.install_body program)
    oracle passes depth prices inventory fixed source world record represented

end Gabbro.Stage0.Frontend.Async
