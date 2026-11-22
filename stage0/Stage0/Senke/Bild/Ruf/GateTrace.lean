module

public import Stage0.Senke.Images.Correctness
import Mathlib.Data.List.Forall2

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner Runner.IR Runner.Beweis Runner.Mach

variable {src : String} {reserve : Nat} {options : Profil.Options}

/-- A guarded oracle call contributes exactly one source foreign event.
    Reading the arguments and recording the declared writes retain their
    order in the full run without adding another foreign event. -/
theorem imageSourceForeignEvents_call {D : Deklaration} {O : Orakel D} (oracle : GutO O)
    (thread : Faden) (routine : D.Ax) (before : World D) (held : List (Res D))
    (reads : List (D.Tab ⊕ D.Glob)) (arguments : Env D (D.aparams routine))
    (writeTabs : ∀ t, D.aschreibt routine t = true → ∀ l, Sum.inl l ∈ D.braucht t → l ∈ before.haelt)
    (writeGlobs : ∀ g, D.agschreibt routine g = true → ∀ l, Sum.inl l ∈ D.gbraucht g → l ∈ before.haelt)
    {added : List (Ereignis D)}
    (events : (O.wirkt routine ((before.lese held reads).fragt (.inl routine)) arguments).1.spur =
      added ++ before.spur) :
    imageSourceForeignEvents (rufEigenG thread added) = [(thread, routine)] := by
  let readEvent : D.Tab ⊕ D.Glob → Ereignis D := fun carrier => match carrier with
    | .inl table => .zugriff table false held before.haelt
    | .inr global => .gzugriff global false held before.haelt
  let question := (before.lese held reads).fragt (.inl routine)
  have sameHeld : question.haelt = before.haelt := by
    change (before.lese held reads).haelt = before.haelt
    exact lese_haelt before held reads
  obtain ⟨tabs, globs, visible, _, _, _, _, _, _, written⟩ :=
    (oracle routine question arguments).2.2 (sameHeld.symm ▸ writeTabs) (sameHeld.symm ▸ writeGlobs)
  let writes := axiomSpur tabs globs routine visible question.haelt
  have logEq : added = writes ++ [.fremd (.inl routine)] ++ reads.map readEvent := by
    apply List.append_cancel_right (bs := before.spur)
    change (O.wirkt routine question arguments).1.spur = added ++ before.spur at events
    rw [← events, written]
    simp only [question, writes, World.fragt, World.lese, World.merke, readEvent, List.append_assoc]
  let observation : Ereignis D → Option (Faden × D.Ax) := fun event => match event with
    | .fremd (.inl called) => some (thread, called)
    | _ => none
  have readsSilent : (reads.map readEvent).filterMap observation = [] := by
    rw [List.filterMap_map]
    apply List.filterMap_eq_nil_iff.mpr
    intro carrier _
    cases carrier <;> rfl
  have writesSilent : writes.filterMap observation = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro event member
    rcases axiomSpur_mem member with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
  have projected : ((writes ++ [.fremd (.inl routine)] ++ reads.map readEvent).reverse).filterMap
      observation = [(thread, routine)] := by
    simp only [List.reverse_append, List.filterMap_append, List.filterMap_reverse,
      readsSilent, writesSilent, List.reverse_nil, List.nil_append, List.append_nil]
    rfl
  rw [logEq]
  simpa only [imageSourceForeignEvents, rufEigenG, List.filterMap_map, Function.comp_apply] using projected

/-- Internal runner requests leave the foreign history intact when the
    corresponding GX segment adds no foreign event. -/
theorem ImageForeignTrace.appendInternal {output : Emitted src reserve options}
    {history events : List Ev} {before after : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (matched : ImageForeignTrace output history before)
    (internal : ∀ event ∈ events, imageExternalEvent event = false)
    (silent : imageSourceForeignEvents after.m.lauf = imageSourceForeignEvents before.m.lauf) :
    ImageForeignTrace output (history ++ events) after := by
  have noExternal : events.filter imageExternalEvent = [] :=
    List.filter_eq_nil_iff.mpr (fun event member => by rw [internal event member]; decide)
  simpa only [ImageForeignTrace, List.filter_append, noExternal, List.append_nil, silent] using matched

/-- A matched host response extends the global trace by the call taken
    by the actual issuing GX thread. -/
theorem ImageForeignTrace.appendGate [Kern] {output : Emitted src reserve options}
    {E : Einheit (declOf output.compiled.unit)} {O : Orakel (declOf output.compiled.unit)}
    {history : List Ev} {event : Ev} {returned : Cfg imageTSO (Res T)}
    {before after : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (matched : ImageForeignTrace output history before) (external : imageExternalEvent event = true)
    (call : ImageGateEvent output E O before after returned event) :
    ImageForeignTrace output (history ++ [event]) after := by
  obtain ⟨_, _, routine, _, _, _, _, _, _, log, gate, _, _, present, number, _⟩ := call
  unfold ImageForeignTrace at matched ⊢
  rw [log, List.filter_append]
  simp only [List.filter_cons, external, ite_true, List.filter_nil]
  exact List.rel_append matched (.cons ⟨rfl, gate, present, number⟩ .nil)

end Gabbro.Stage0
