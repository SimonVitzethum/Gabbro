module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Lauf.History
public import Grammatik.Zielsatz.Kern.Spec.Teil4

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

open Gabbro.Grammatik.Parser.UebersetzeAllg

/-- Every entry belongs to this probe; consumption names this selected gate.
    Sample data are immutable under both permitted history mutations. -/
def CheckHistoryForm {D : Deklaration} (c : CheckDecl D) (gate : D.Fn)
    (history : List (CheckEvidenz D)) : Prop :=
  ∀ entry ∈ history, entry.erzeuger = c.probe ∧
    (entry.lebt = false → entry.tor = some gate)

theorem checkHistoryForm_cons {D : Deklaration} {c : CheckDecl D} {gate : D.Fn}
    {entry : CheckEvidenz D} {rest : List (CheckEvidenz D)}
    (head : entry.erzeuger = c.probe ∧ (entry.lebt = false → entry.tor = some gate))
    (tail : CheckHistoryForm c gate rest) : CheckHistoryForm c gate (entry :: rest) := by
  intro item member
  rcases List.mem_cons.mp member with same | member
  · subst same
    exact head
  · exact tail item member

/-- A physical consumer cannot redirect another report or modify its producer. -/
theorem consumeCheckEntry_form {D : Deklaration} {c : CheckDecl D} {gate : D.Fn}
    {history result : List (CheckEvidenz D)} (form : CheckHistoryForm c gate history)
    (consumed : consumeCheckEntry gate history = some result) :
    CheckHistoryForm c gate result := by
  revert form consumed
  induction history generalizing result with
  | nil =>
    intro form consumed
    simp [consumeCheckEntry] at consumed
  | cons entry rest ih =>
    intro form consumed
    have head := form entry (List.mem_cons_self)
    have tail : CheckHistoryForm c gate rest := fun item member =>
      form item (List.mem_cons_of_mem _ member)
    by_cases live : entry.lebt = true
    · simp [consumeCheckEntry, live] at consumed
      cases consumed
      exact checkHistoryForm_cons ⟨head.1, fun _ => rfl⟩ tail
    · cases next : consumeCheckEntry gate rest with
      | none => simp [consumeCheckEntry, live, next] at consumed
      | some remaining =>
        simp [consumeCheckEntry, live, next] at consumed
        cases consumed
        exact checkHistoryForm_cons head (ih tail next)

theorem checkGhostConsume_form {D : Deklaration} {c : CheckDecl D} {gate : D.Fn}
    (state : CheckGhostState D) (form : CheckHistoryForm c gate state.history) :
    CheckHistoryForm c gate (checkGhostConsume gate state).history := by
  cases consumed : consumeCheckEntry gate state.history with
  | none => simpa [checkGhostConsume, consumed] using form
  | some history =>
    simpa [checkGhostConsume, consumed] using consumeCheckEntry_form form consumed

-- Capturing a reporter's actual return updates pending observations only.
-- Prove the whole Option/pair/Bool projection before instantiating it with
-- dependent event arguments, so no return-signature index is eliminated.
private theorem captured_history {D : Deklaration} (check : String)
    (state : CheckGhostState D) (captured : Option (String × CheckReport)) :
    (match captured with
      | some (name, report) =>
        if name == check then
          { state with pending := some (stampCheckReport state.activation report) }
        else state
      | none => state).history = state.history := by
  cases captured with
  | none => rfl
  | some sampled =>
    rcases sampled with ⟨name, report⟩
    split <;> rfl

/-- Every actual event preserves producer identity and the chosen consumer.
    No user-provided report or assumption about memory values is needed. -/
theorem checkGhostStep_form (u : UProg) (c : CheckDecl (declOf u))
    (consumer gate : (declOf u).Fn) (state : CheckGhostState (declOf u))
    (event : RufEreignisF (declOf u)) (form : CheckHistoryForm c gate state.history) :
    CheckHistoryForm c gate (checkGhostStep u c consumer gate state event).history := by
  cases event with
  | eintritt f env before => exact form
  | why f env reason before after =>
    simp only [checkGhostStep]
    split
    · exact form
    · split
      · exact checkGhostConsume_form _ form
      · exact form
  | rueck f env value before after =>
    simp only [checkGhostStep]
    split
    · exact form
    · split
      · cases pending : state.pending with
        | none => exact form
        | some report =>
          split
          · let entry : CheckEvidenz (declOf u) := ⟨c.probe, report, true, none⟩
            have head : entry.erzeuger = c.probe ∧
                (entry.lebt = false → entry.tor = some gate) := by
              refine ⟨rfl, ?_⟩
              intro dead
              have impossible : (true : Bool) = false := dead
              cases impossible
            have appended : CheckHistoryForm c gate (entry :: state.history) :=
              checkHistoryForm_cons (entry := entry) head form
            exact appended
          · exact form
      · split
        · exact checkGhostConsume_form _ form
        · split
          · let popped : CheckGhostState (declOf u) :=
              { state with frames := state.frames.drop 1 }
            have preserved := captured_history c.name popped (actualCheckReturn u f env value)
            exact (congrArg (CheckHistoryForm c gate) preserved).mpr form
          · exact form

/-- The whole chronological fold preserves its inventory, not merely one
    fixture or one isolated producer/consumer cycle. -/
theorem checkGhostHistory_form (u : UProg) (c : CheckDecl (declOf u))
    (consumer gate : (declOf u).Fn) (log : List (RufEreignisF (declOf u))) :
    CheckHistoryForm c gate (checkGhostHistory u c consumer gate log).history := by
  have foldForm : ∀ (events : List (RufEreignisF (declOf u))) (state : CheckGhostState (declOf u)),
      CheckHistoryForm c gate state.history →
      CheckHistoryForm c gate
        (events.foldl (checkGhostStep u c consumer gate) state).history := by
    intro events
    induction events with
    | nil => intro state form; exact form
    | cons event rest ih =>
      intro state form
      exact ih _ (checkGhostStep_form u c consumer gate state event form)
  exact foldForm log.reverse {} (by intro entry member; cases member)

/-- Completion through the selected consumer establishes the existing goal
    leg for the actual machine-indexed history. Both equal and unequal sample
    reports are handled generically; all completed tokens have been retired. -/
theorem checkGhostHistory_treu (u : UProg) (P : Programm (declOf u))
    (c : CheckDecl (declOf u)) (consumer gate : (declOf u).Fn)
    (declared : gate ∈ c.gates) (log : List (RufEreignisF (declOf u)))
    (complete : checkGhostComplete (checkGhostHistory u c consumer gate log) = true) :
    Zielsatz.CheckTreueG P [c] (checkGhostHistory u c consumer gate log).history := by
  let state := checkGhostHistory u c consumer gate log
  have form := checkGhostHistory_form u c consumer gate log
  have closed : state.history.all (fun entry => !entry.lebt) = true := by
    change checkGhostComplete state = true at complete
    cases hr : state.refused <;> cases hp : state.pending.isNone <;>
      simp_all [checkGhostComplete]
  have dead : ∀ entry ∈ state.history, entry.lebt = false := by
    intro entry member
    simpa only [Bool.not_eq_true'] using List.all_eq_true.mp closed entry member
  have selected : ∀ entry ∈ state.history, entry.tor = some gate := by
    intro entry member
    exact (form entry member).2 (dead entry member)
  refine ⟨?_, ?_, ?_⟩
  · intro entry member
    exact ⟨c, List.mem_singleton_self _, (form entry member).1⟩
  · intro entry member check checkMember _
    have same := List.mem_singleton.mp checkMember
    subst same
    exact Or.inr ⟨dead entry member, gate, declared, selected entry member⟩
  · intro check checkMember first firstMember second secondMember _ _ _ _
    exact ⟨(dead first firstMember).trans (dead second secondMember).symm,
      (selected first firstMember).trans (selected second secondMember).symm⟩

/-- G/GX use the same actual log and therefore the same completed goal leg. -/
theorem checkGhostGX_treu (u : UProg) (P : Programm (declOf u))
    (M : RufMaschineG (declOf u)) (thread : Faden) (c : CheckDecl (declOf u))
    (consumer gate : (declOf u).Fn) (declared : gate ∈ c.gates)
    (complete : checkGhostComplete (checkGhostGX u M thread c consumer gate) = true) :
    Zielsatz.CheckTreueG P [c] (checkGhostGX u M thread c consumer gate).history :=
  checkGhostHistory_treu u P c consumer gate declared (M.faeden thread).log complete

end Gabbro.Grammatik.Parser.Uebersetze
