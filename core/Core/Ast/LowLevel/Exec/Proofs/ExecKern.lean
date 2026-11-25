module

public import Core.Ast.LowLevel.Exec.Obligations

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Gabbro.Core.Text Katalog Maschine Waechter
open Gabbro.Core.Annahme
open Gabbro.Core.Aussen
open Gabbro.Core.Sicherheit (Absturz NeueWirkungen)

theorem execHead_some_iff (op : ExecInstruction)
    (s : ExecState) (c : Kontext) :
    execHead [op] s c = some op ↔
      s.status c = .laeuft ∧ c = entryContext ∧ (s.lokal c).pc = 0 ∧
        (op.evaluate s c).isSome = true := by
  unfold execHead
  constructor
  · intro h
    by_cases hc : c = entryContext
    · subst c
      cases hs : s.status entryContext with
      | laeuft =>
          simp only [hs] at h
          dsimp at h
          cases hpc : [op][(s.lokal entryContext).pc]? with
          | none =>
              simp only [hpc, Option.bind_none] at h
              cases h
          | some instr =>
              simp only [hpc, Option.bind_some] at h
              cases hpci : (s.lokal entryContext).pc with
              | zero =>
                  simp only [hpci, List.getElem?_cons_zero] at hpc
                  cases hpc
                  split at h
                  · rename_i hev
                    exact ⟨rfl, rfl, rfl, hev⟩
                  · cases h
              | succ n =>
                  simp only [hpci, List.getElem?_cons_succ, List.getElem?_nil] at hpc
                  cases hpc
      | ruht =>
          simp only [hs] at h
          cases h
      | beendet e =>
          simp only [hs] at h
          cases h
    · simp only [hc, ↓reduceIte] at h
      cases h
  · rintro ⟨hs, rfl, hpci, hev⟩
    simp only [hs, hpci, List.getElem?_cons_zero, ↓reduceIte]
    dsimp
    rw [if_pos hev]

theorem execRealisiert (form : ExecForm) : ExecRealisiertAussage form := by
  intro k scope tree op _
  intro s c
  change execHead [op] s c = some op ↔
    s.status c = .laeuft ∧ c = entryContext ∧ (s.lokal c).pc = 0 ∧
      (op.evaluate s c).isSome = true
  exact execHead_some_iff _ _ _

theorem execRegelLokal (k : Katalog) (op : ExecInstruction) :
    Annahme.RegelLokal (execUnit k op) op := by
  intro c s u w P hideal
  change ∃ frame, op.evaluate s c = some frame ∧ [P] = [plan] ∧
    u = frame.advance c s at hideal
  rcases hideal with ⟨frame, heval, hP, hu⟩
  have hP' : P = plan := by simpa using hP
  subst P
  have hfuss : plan.fuss = [] := rfl
  have hlesen : plan.lesen = [] := rfl
  rw [Annahme.Befugt, hfuss, hlesen]
  constructor
  · intro x hx
    cases hx
  · intro l hl
    cases hl

theorem execAnnahme (form : ExecForm) : ExecAnnahmeAussage form := by
  intro k scope tree op _
  exact execRegelLokal k op

theorem execIdeal (form : ExecForm) : ExecIdealAussage form := by
  intro scope tree op _
  change Ideal.RegelBestimmt (ExecInstruction.rule op)
  intro c s w es es' s1 s2 h1 h2
  change ∃ frame, op.evaluate s c = some frame ∧ es = [plan] ∧
    s1 = frame.advance c s at h1
  change ∃ frame, op.evaluate s c = some frame ∧ es' = [plan] ∧
    s2 = frame.advance c s at h2
  rcases h1 with ⟨t1, he1, hes1, hs1⟩
  rcases h2 with ⟨t2, he2, hes2, hs2⟩
  constructor
  · rw [hes1, hes2]
  · have ht : t1 = t2 := by
      rw [he1] at he2
      cases he2
      rfl
    rw [hs1, hs2, ht]

theorem execFortschritt (form : ExecForm) : ExecFortschrittAussage form := by
  intro k scope tree op _
  intro s c hhead
  left
  change execHead [op] s c = some op at hhead
  cases hEval : op.evaluate s c with
  | none =>
      have hnot : ¬ (s.status c = .laeuft ∧ c = entryContext ∧ (s.lokal c).pc = 0 ∧
          (op.evaluate s c).isSome = true) := by
        rintro ⟨_, _, _, hisSome⟩
        rw [hEval] at hisSome
        cases hisSome
      exact (hnot ((execHead_some_iff op s c).1 hhead)).elim
  | some frame =>
      refine ⟨(), [plan], frame.advance c s, ?_⟩
      exact ⟨frame, hEval, rfl, rfl⟩

theorem execImplTransfer {op : ExecInstruction} {c : Kontext}
    {s : ExecState} {w : PUnit} {plans : List Plan} {u : ExecState}
    (h : op.step c s w plans u) :
    ∃ frame, op.evaluate s c = some frame ∧ plans = [plan] ∧ u = frame.advance c s := h

theorem execVollzug (frame : ExecFrame) (t : Nat) (c : Kontext) (s : ExecState) :
    FuehrtSchrittAus execSetup t c s (frame.advance c s) plan ⟨[], []⟩ (frame.advance c s) := by
  refine ⟨?_, ?_, [], frame.advance c s, ?_, ?_, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro l hl
    simp only [plan] at hl
    cases hl
  · change FuehrtAus execSetup t c s (frame.advance c s) .intern [] [] (frame.advance c s)
    exact FuehrtAus.intern
  · change Speicherfolge s.initial (.kontext c) s.graph [] [] (frame.advance c s).graph
    exact Speicherfolge.nil _

theorem execGenauInternal {t : Nat} {c : Kontext} {s u : ExecState}
    {trace : SchrittSpur Nat UInt8} {next : ExecState}
    (execute : FuehrtSchrittAus execSetup t c s u plan trace next) :
    trace = ⟨[], []⟩ ∧ next = u := by
  obtain ⟨rahmen, _, _, _, action, memory, nextEq⟩ := execute
  cases trace with
  | mk events outside =>
      cases action
      simp only [plan, List.nil_append, schreibEreignisse, List.map_nil, List.filter_nil, List.append_nil] at memory
      have unchanged : ∀ {recorded graph},
          Speicherfolge s.initial (.kontext c) s.graph [] recorded graph →
            recorded = [] ∧ graph = s.graph := by
        intro _ _ run
        cases run
        exact ⟨rfl, rfl⟩
    obtain ⟨rfl, graph⟩ := unchanged memory
    rw [graph] at next
    rw [← rahmen.graph] at next
    exact ⟨rfl, nextEq⟩

/-- Every execution of an exec instruction records the empty cut, so every head form meets
    the isolation duty under every domain plan. -/
theorem execDomaenenLokal (k : Katalog) (code : List ExecInstruction) :
    DomaenenLokal (execProgram k code) := by
  intro dplan s c i _ t c' sv u sv' w qq spur himpl haus
  obtain ⟨_, _, planEq, _⟩ := himpl
  cases (List.cons.inj planEq).1
  obtain ⟨rfl, _⟩ := execGenauInternal haus
  exact spurRespektiert_leer _ _ _

theorem execAbgleich (k : Katalog) (op : ExecInstruction) :
    I.RegelAbgleich (execUnit k op) op := by
  intro hw t c w s u s' i stepPlan trace related normal ready head impl execute
  obtain ⟨protocol, frames⟩ := related
  change s.lokal = i.lokal at frames
  change { s with lokal := i.lokal } = i at protocol
  rw [← frames] at protocol
  subst i
  obtain ⟨frame, evaluate, planEq, hu⟩ := execImplTransfer (op := op) (w := w) impl
  subst u
  exact Or.inl ⟨s', .kontext normal ready ⟨op, head, ⟨frame, evaluate, planEq, rfl⟩⟩ execute,
    I.ProtokollBezug.refl _, rfl⟩

theorem execKomponierbar (k : Katalog) (op : ExecInstruction) :
    I.RegelKomponierbar (execUnit k op).einrichtung (execUnit k op).system op := by
  intro t s c w plans u head gut ideal
  obtain ⟨frame, evaluate, planEq, hu⟩ := execImplTransfer (op := op) (w := w) ideal
  subst u
  exact ⟨plan, ⟨[], []⟩, frame.advance c s, planEq, execVollzug frame t c s⟩

theorem execErhaltung (form : ExecForm) : ExecErhaltungAussage form := by
  intro k scope tree op _
  exact ⟨execAbgleich k op, execKomponierbar k op⟩

theorem execRegelSicher (k : Katalog) (op : ExecInstruction) :
    Gabbro.Core.Sicherheit.RegelSicher (execSafetyUnit k op) op := by
  intro H ρ t c w vor zwischen nach stepPlan trace head impl execute
  obtain ⟨frame, _, planEq, _⟩ := execImplTransfer (op := op) (w := w) impl
  subst zwischen
  cases (List.cons.inj planEq).1
  obtain ⟨traceEq, nextEq⟩ := execGenauInternal execute
  subst trace
  subst nach
  have ohneAbsturz : ¬ Absturz (⟨[], []⟩ : SchrittSpur Nat UInt8) := List.not_mem_nil
  have wirkungen : NeueWirkungen vor (frame.advance c vor) (⟨[], []⟩ : SchrittSpur Nat UInt8) [] :=
    Or.inr ⟨ohneAbsturz, (List.append_nil _).symm⟩
  refine ⟨⟨?_, [], wirkungen, ?_⟩, ?_, ?_, fun ordered => ordered, ?_, ?_⟩
  · intro i actor access recorded _
    cases recorded
  · refine ⟨List.nodup_nil, fun _ _ mem => (List.not_mem_nil mem).elim, ?_⟩
    intro _ obj alive lost
    exact nomatch alive.symm.trans lost
  · intro _
    refine ⟨fun _ _ => trivial, ?_⟩
    intro i d declared _
    change [][i]? = some d at declared
    cases declared
  · intro _ l changeOwner
    exact (changeOwner rfl).elim
  · exact ⟨fun _ mem => (List.not_mem_nil mem).elim, [], wirkungen,
      fun _ mem => (List.not_mem_nil mem).elim⟩
  · exact ⟨fun _ mem => (List.not_mem_nil mem).elim, [], wirkungen,
      fun _ mem => (List.not_mem_nil mem).elim⟩

theorem execSicher (form : ExecForm) : ExecRegelSicherAussage form := by
  intro k scope tree op _
  exact execRegelSicher k op

theorem execRegelAntwortSicher (form : ExecForm) : ExecRegelAntwortSicherAussage form := by
  intro k scope tree op _
  constructor
  · intro t c w vor zwischen nach p trace _ impl execute befugt
    obtain ⟨frame, _, planEq, rfl⟩ := impl
    cases (List.cons.inj planEq).1
    rcases trace with ⟨memory, events⟩
    obtain ⟨_, _, _, _, action, _, after⟩ := execute
    cases action
    rw [after]
    exact befugt
  · intro t c s w middle next p trace impl execute
    obtain ⟨_, _, planEq, rfl⟩ := impl
    cases (List.cons.inj planEq).1
    rcases trace with ⟨memory, events⟩
    obtain ⟨_, _, _, _, action, _, after⟩ := execute
    cases action
    rw [after]
    exact ⟨fun _ => List.not_mem_nil, rfl⟩

theorem execAussenLokalUnit (k : Katalog) (op : ExecInstruction) :
    Gabbro.Core.Annahme.AussenLokal (execUnit k op) := by
  refine ⟨zulassung_m2 _, ?_⟩
  apply aussen_gueltig_aus_kontext
  intro run t s c w spur s' step
  cases step with
  | kontext _ _ regel execute =>
    obtain ⟨_, _, frame, _, planEq, rfl⟩ := regel
    cases (List.cons.inj planEq).1
    obtain ⟨rfl, rfl⟩ := execGenauInternal execute
    exact ⟨⟨fun _ mem => (List.not_mem_nil mem).elim, [],
      (List.append_nil _).symm, fun _ mem => (List.not_mem_nil mem).elim⟩, fun h => h⟩

theorem execAussen (form : ExecForm) : ExecAussenLokalAussage form :=
  fun k _ _ op _ => execAussenLokalUnit k op

theorem execKostenUnit (k : Katalog) (op : ExecInstruction) :
    ∀ t c s w middle next p trace, op.step c s w [p] middle →
      FuehrtSchrittAus (execUnit k op).einrichtung t c s middle p trace next →
      trace = ⟨[], []⟩ ∧ (execUnit k op).stotterLaenge op = 0 := by
  intro t c s w middle next p trace impl execute
  obtain ⟨_, _, hp, _⟩ := execImplTransfer (op := op) (w := w) impl
  cases (List.cons.inj hp).1
  exact ⟨(execGenauInternal execute).1, rfl⟩

theorem execKosten (form : ExecForm) : ExecKostenAussage form := by
  intro k scope tree op _
  exact execKostenUnit k op

/-- Every execution instruction uses the public frame and emits no output. -/
theorem execProgramFlussLokal (k : Katalog) (code : List ExecInstruction) :
    Beobachtung.FlussLokal (execProgram k code) := by
  constructor
  · intro s₁ s₂ same
    have regions : s₁.regions = s₂.regions := congrArg (fun p => p.2.2.1) same
    refine ⟨?_, fun _ => rfl, fun _ => rfl, ?_, rfl, fun _ => rfl⟩
    · intro c _ _
      simp only [I.start, execProgram, execBoot, Zustand.start, regions]
    · simp only [I.start, execProgram, execBoot, Zustand.start, regions]
  · intro f
    constructor
    · intro c v w p u _
      refine ⟨⟨rfl, fun _ _ _ mem => (List.not_mem_nil mem).elim⟩, fun privateControl => ?_⟩
      exact (Bool.false_ne_true privateControl.symm).elim
    · intro _ c v₁ w₁ p₁ u₁ v₂ w₂ p₂ u₂ same step₁ step₂
      have run₁ : f.step c v₁ w₁ [p₁] u₁ := step₁.2
      have run₂ : f.step c v₂ w₂ [p₂] u₂ := step₂.2
      obtain ⟨frame₁, eval₁, plan₁, rfl⟩ := run₁
      obtain ⟨frame₂, eval₂, plan₂, rfl⟩ := run₂
      obtain ⟨locals, ends, initial, rights, loans, answers⟩ := same
      have localEq : v₁.lokal = v₂.lokal :=
        funext fun d => locals d ⟨0, Nat.zero_lt_succ _⟩ rfl
      rw [← f.evaluate_congr _ localEq, eval₁] at eval₂
      cases eval₂
      rw [(List.cons.inj plan₁).1, (List.cons.inj plan₂).1]
      refine ⟨⟨?_, ends, initial, rights, loans, answers⟩, rfl, rfl⟩
      intro d _ _
      simp only [ExecFrame.advance, localEq]

theorem execFlussLokal (k : Katalog) (op : ExecInstruction) :
    Beobachtung.FlussLokal (execUnit k op) := execProgramFlussLokal k [op]

end Gabbro.Core.Ast.LowLevel
