module

public import Core.Ast.Program.Execution

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

/-- Exiting a loop includes returning from its surrounding function or requesting its handler. -/
def SchleifenAusgang (first limit : Nat) (before after : Rahmen) : Prop :=
  after.stopp.isSome = true ∨ after.rueckgabe.isSome = true ∨
    after.fortsetzungen.length < before.fortsetzungen.length ∨
    (after.fortsetzungen.length = before.fortsetzungen.length ∧
      (after.pc < first ∨ limit ≤ after.pc))

/-- One successful loop body segment either exits or reaches its back-edge on the
    same stack. Its budget includes all calls and nested loop instructions. -/
def SchleifenKoerper (code : List Befehl) (origin : Rahmen) (first limit body back budget : Nat) : Prop :=
  ∀ frame, (∃ n, Rahmen.LaufN code n origin frame) → frame.Aktiv →
    frame.pc = body → frame.fortsetzungen.length = origin.fortsetzungen.length →
    Binnen code budget frame (fun out =>
      SchleifenAusgang first limit origin out ∨
        out.Aktiv ∧ out.pc = back ∧ out.fortsetzungen.length = origin.fortsetzungen.length)

/-- An instruction either runs in place or changes the stack by a matching
    call or return. The counter of a preceding instruction is left alone. -/
private inductive Rahmen.SchrittForm (key distance : Nat) (before : Rahmen) : Rahmen → Prop where
  | lokal : after.fortsetzungen = before.fortsetzungen → before.pc - distance ≤ after.pc →
      (key < before.pc → after.zaehler key = before.zaehler key) → SchrittForm key distance before after
  | ruf (saved : Fortsetzung) :
      after.fortsetzungen = saved :: before.fortsetzungen → saved.pc = before.pc + 1 →
      saved.zaehler = before.zaehler → SchrittForm key distance before after
  | rueck (saved : Fortsetzung) :
      before.fortsetzungen = saved :: after.fortsetzungen → after.pc = saved.pc →
      after.zaehler = saved.zaehler → SchrittForm key distance before after

private theorem SchrittForm.halt (frame : Rahmen) (reason : Abschluss) :
    Rahmen.SchrittForm key distance frame (frame.halt reason) :=
  .lokal rfl (Nat.sub_le _ _) (fun _ => rfl)

private theorem SchrittForm.rufform (frame : Rahmen) (name : Identifier)
    (sources : List (Ty .value)) (bind : Option (Ty .value)) :
    Rahmen.SchrittForm key 0 frame (frame.ruf name sources bind) := by
  unfold Rahmen.ruf
  cases bind <;> simp only [Id.run]
  all_goals
    repeat' first
    | exact SchrittForm.halt frame _
    | exact .ruf _ rfl rfl rfl
    | split

private theorem SchrittForm.rueckform (frame : Rahmen) (value : Option Dynamisch) :
    Rahmen.SchrittForm key 0 frame (frame.rueckkehr value) := by
  unfold Rahmen.rueckkehr
  split
  · exact .lokal rfl (Nat.le_succ _) (fun _ => rfl)
  · rename_i saved stack stackEq
    exact .rueck saved stackEq rfl rfl

private theorem SchrittForm.passform (frame : Rahmen) (bit : Bool) (exit : Nat)
    (handler : Option Identifier) : Rahmen.SchrittForm key 0 frame (frame.pass bit exit handler) := by
  unfold Rahmen.pass
  repeat' first
  | exact SchrittForm.halt frame _
  | refine .lokal rfl (Nat.le_add_right _ _) (fun h => ?_)
    exact Function.update_of_ne (Nat.ne_of_lt h) _ _
  | split

private theorem SchrittForm.withLocals {frame out : Rahmen} {locals : List (Option Dynamisch)}
    (step : Rahmen.SchrittForm key distance { frame with lokale := locals } out) :
    Rahmen.SchrittForm key distance frame out := by
  cases step with
  | lokal same pc counters => exact .lokal same pc counters
  | ruf saved stack pc counters => exact .ruf saved stack pc counters
  | rueck saved stack pc counters => exact .rueck saved stack pc counters

private theorem Befehl.schrittForm (b : Befehl) (frame : Rahmen) (key : Nat) :
    Rahmen.SchrittForm key b.rueckweite frame (b.auswerten frame) := by
  cases b <;> simp only [Befehl.rueckweite, Befehl.auswerten, Id.run]
  all_goals
    try exact .lokal rfl (Nat.le_add_right _ _) (fun _ => rfl)
  all_goals
    try exact .lokal rfl (Nat.le_refl _) (fun _ => rfl)
  case rufe => exact SchrittForm.rufform frame _ _ _
  case zurueck => exact SchrittForm.rueckform frame _
  case rueckVoid => exact SchrittForm.rueckform frame _
  case pruefeMass =>
    unfold Rahmen.setzeMass
    simp only [Id.run]
    repeat' first
    | exact SchrittForm.halt frame _
    | exact .lokal rfl (Nat.le_succ _) (fun _ => rfl)
    | split
  case setzePasszahl =>
    split
    · exact .lokal rfl (Nat.le_succ _) (fun h => Function.update_of_ne (by omega) _ _)
    · exact SchrittForm.halt frame _
  case whileTest =>
    split
    · exact SchrittForm.passform frame _ _ _
    · exact SchrittForm.halt frame _
  case forAnfang =>
    repeat' first
    | exact SchrittForm.halt frame _
    | exact .lokal rfl (Nat.le_add_right _ _) (fun _ => rfl)
    | exact .lokal rfl (Nat.le_succ _) (fun h => Function.update_of_ne (by omega) _ _)
    | split
  case forTest =>
    repeat' first
    | exact SchrittForm.halt frame _
    | exact SchrittForm.passform frame _ _ _
    | split
  case forNaechster =>
    repeat' first
    | exact SchrittForm.halt frame _
    | exact .lokal rfl (Nat.le_refl _) (fun _ => rfl)
    | split
  case starte name =>
    repeat' first
    | exact SchrittForm.halt frame _
    | exact SchrittForm.withLocals (frame := frame) (locals := [])
        (SchrittForm.rufform { frame with lokale := [] } name []
          ((Funktion.finde frame.funktionen name).bind Funktion.result))
    | split
  case textIndex | substring =>
    repeat' first
    | exact SchrittForm.halt frame _
    | exact .lokal rfl (Nat.le_succ _) (fun _ => rfl)
    | split
  case waehleVariante =>
    repeat' first
    | exact SchrittForm.halt frame _
    | exact .lokal rfl (Nat.le_add_right _ _) (fun _ => rfl)
    | split

/-- Follow the same activation through a call by following the saved
    continuation underneath all younger calls. -/
private inductive Rahmen.LoopFrame (base lower key remaining : Nat) : Rahmen → Prop where
  | here : frame.fortsetzungen.length = base → lower ≤ frame.pc →
      frame.zaehler key = some remaining → LoopFrame base lower key remaining frame
  | saved (above : List Fortsetzung) (caller : Fortsetzung) (below : List Fortsetzung) :
      frame.fortsetzungen = above ++ caller :: below → below.length = base →
      lower ≤ caller.pc → caller.zaehler key = some remaining → LoopFrame base lower key remaining frame

private theorem Rahmen.LoopFrame.counter {frame : Rahmen}
    (inv : frame.LoopFrame base lower key remaining) (depth : frame.fortsetzungen.length = base) :
    frame.zaehler key = some remaining := by
  cases inv with
  | here _ _ count => exact count
  | saved above caller below stack baseDepth _ _ =>
    rw [stack, List.length_append, List.length_cons, baseDepth] at depth
    omega

private theorem Rahmen.LoopFrame.step {frame out : Rahmen} (inv : frame.LoopFrame base lower key remaining)
    (form : Rahmen.SchrittForm key distance frame out) (beforeKey : key < lower)
    (within : frame.fortsetzungen.length = base → distance ≤ frame.pc - lower) :
    out.fortsetzungen.length < base ∨ out.LoopFrame base lower key remaining := by
  cases inv with
  | here depth entry count =>
    cases form with
    | lokal same pc countSame =>
      have bounded := within depth
      exact .inr (.here (same ▸ depth) (by omega) ((countSame (by omega)).trans count))
    | ruf saved stack pc counters =>
      exact .inr (.saved [] saved frame.fortsetzungen stack depth (by omega) (by rw [counters, count]))
    | rueck saved stack _ _ =>
      rw [stack, List.length_cons] at depth
      exact .inl (by omega)
  | saved above caller below stack depth pc counter =>
    cases form with
    | lokal same _ _ => exact .inr (.saved above caller below (same.trans stack) depth pc counter)
    | ruf saved push _ _ =>
      exact .inr (.saved (saved :: above) caller below (push.trans (congrArg (saved :: ·) stack))
        depth pc counter)
    | rueck saved pop outPC outCounter =>
      have heads := pop.symm.trans stack
      cases above with
      | nil =>
        have h := List.cons.inj heads
        exact .inr (.here (h.2 ▸ depth) (by rwa [outPC, h.1]) (by rwa [outCounter, h.1]))
      | cons first tail =>
        exact .inr (.saved tail caller below (List.cons.inj heads).2 depth pc counter)

theorem SchleifenAusgang.stopped {out : Rahmen} (stopped : ¬ out.Aktiv) :
    SchleifenAusgang first limit origin out := by
  unfold SchleifenAusgang
  cases h : out.stopp with
  | some => exact .inl rfl
  | none =>
    cases r : out.rueckgabe with
    | some => exact .inr (.inl rfl)
    | none => exact (stopped ⟨h, r⟩).elim

/-- Stop at the first exit or back-edge. Later steps in the supplied body walk
    cannot invalidate the counter at that earlier cut. -/
private theorem body_first_cut (walk : Rahmen.LaufN code n frame last)
    (shape : ∀ pc (b : Befehl), lower ≤ pc → pc ≠ back → code[pc]? = some b → b.rueckweite ≤ pc - lower)
    (beforeKey : key < lower) (inv : frame.LoopFrame origin.fortsetzungen.length lower key remaining)
    (lastDone : SchleifenAusgang 0 code.length origin last ∨
      last.Aktiv ∧ last.pc = back ∧ last.fortsetzungen.length = origin.fortsetzungen.length) :
    Binnen code n frame (fun out => SchleifenAusgang 0 code.length origin out ∨
      out.Aktiv ∧ out.pc = back ∧ out.fortsetzungen.length = origin.fortsetzungen.length ∧
        out.zaehler key = some remaining) := by
  revert inv lastDone
  induction walk with
  | @null frame =>
    intro inv lastDone
    refine ⟨0, frame, Nat.le_refl _, .null, lastDone.imp_right ?_⟩
    intro ⟨active, atBack, depth⟩
    exact ⟨active, atBack, depth, inv.counter depth⟩
  | @step instruction n last frame live returned lookup walk ih =>
    intro inv lastDone
    by_cases atBack : frame.pc = back ∧ frame.fortsetzungen.length = origin.fortsetzungen.length
    · exact ⟨0, frame, Nat.zero_le _, .null, .inr ⟨⟨live, returned⟩, atBack.1, atBack.2,
        inv.counter atBack.2⟩⟩
    have bound : frame.fortsetzungen.length = origin.fortsetzungen.length →
        instruction.rueckweite ≤ frame.pc - lower := by
      intro depth
      have notBack : frame.pc ≠ back := fun same => atBack ⟨same, depth⟩
      apply shape _ _ _ notBack lookup
      cases inv with
      | here _ entry _ => exact entry
      | saved above caller below stack base _ _ =>
        rw [stack, List.length_append, List.length_cons, base] at depth
        omega
    rcases inv.step (instruction.schrittForm frame key) beforeKey bound with shallow | nextInv
    · exact ⟨1, _, by omega, .step live returned lookup .null, .inl (.inr (.inr (.inl shallow)))⟩
    · obtain ⟨m, out, budget, front, done⟩ := ih nextInv lastDone
      exact ⟨m + 1, out, Nat.add_le_add_right budget 1, .step live returned lookup front, done⟩

theorem SchleifenKoerper.zaehler (body : SchleifenKoerper code origin 0 code.length lower back budget)
    (shape : ∀ pc (b : Befehl), lower ≤ pc → pc ≠ back → code[pc]? = some b → b.rueckweite ≤ pc - lower)
    (beforeKey : key < lower) (reach : ∃ n, Rahmen.LaufN code n origin frame)
    (active : frame.Aktiv) (atBody : frame.pc = lower)
    (depth : frame.fortsetzungen.length = origin.fortsetzungen.length)
    (counter : frame.zaehler key = some remaining) :
    Binnen code budget frame (fun out => SchleifenAusgang 0 code.length origin out ∨
      out.Aktiv ∧ out.pc = back ∧ out.fortsetzungen.length = origin.fortsetzungen.length ∧
        out.zaehler key = some remaining) := by
  obtain ⟨n, last, cost, walk, done⟩ := body frame reach active atBody depth
  obtain ⟨m, out, prefixCost, front, ready⟩ :=
    body_first_cut walk shape beforeKey (.here depth (Nat.le_of_eq atBody.symm) counter) done
  exact ⟨m, out, Nat.le_trans prefixCost cost, front, ready⟩

end Gabbro.Core.Ast.Semantik
