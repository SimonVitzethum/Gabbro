module

public import Core.Ast.LowLevel.Mem.Proofs.Tabelle.Erhaltung

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

/-! # The table invariant survives releases and reaches every state

`flush` ends a pending token: the completion of a narrowing drops the token and changes no table,
the release of an unmapped range drops the token and changes no entry. All other instructions leave
the spaces and the narrowings untouched. Every reachable state therefore satisfies the invariant. -/

private theorem frei_filter_ausstehend (space : Adressraum) (ausstehend : List Zuruecknahme)
    (wf : space.FreiAusstehend) (sub : ∀ token ∈ ausstehend, token ∈ space.ausstehend) :
    (∀ entry ∈ space.entries, ∀ token ∈ ausstehend, ¬ token.contains entry.1) := by
  intro entry hentry token tmem
  exact wf entry hentry token (sub token tmem)

theorem tabellenGedeckt_flush (target : ZielDaten) (name : Identifier) (s : MemState) (c : Kontext)
    {next : MemFrame} (h : (MemInstruction.flushSpace name).evaluate target s c = some next)
    (inv : (s.lokal c).TabellenGedeckt) : next.TabellenGedeckt := by
  simp only [MemInstruction.evaluate] at h
  cases hm : (s.lokal c).marken.find? (fun p => p.1.val == name.val) with
  | none =>
    simp only [hm, Option.bind_eq_bind, Option.bind_none] at h
    cases h
  | some pair =>
    obtain ⟨nm, token⟩ := pair
    simp only [hm, Option.bind_eq_bind, Option.bind_some] at h
    cases hs : (s.lokal c).spaces[token.raum]? with
    | none =>
      simp only [hs, Option.bind_none] at h
      cases h
    | some space =>
      simp only [hs, Option.bind_some] at h
      by_cases hnr : token.nurRechte = true
      · simp only [hnr, ↓reduceIte] at h
        split at h
        · simp only [Option.pure_def, Option.some.injEq] at h
          subst h
          obtain ⟨hspaces, hnarrow⟩ := inv
          refine ⟨?spaces, ?narrow⟩
          · intro sp space' found
            exact hspaces sp space' found
          · intro tok tmem
            have hold : tok ∈ (s.lokal c).verengt := (List.mem_filter.mp tmem).1
            exact hnarrow tok hold
        · cases h
      · have hnr' : token.nurRechte = false := by
          cases hb : token.nurRechte with
          | false => rfl
          | true => exact (hnr hb).elim
        simp only [hnr', Bool.false_eq_true, ↓reduceIte] at h
        split at h
        · rename_i cond
          simp only [Option.pure_def, Option.some.injEq] at h
          subst h
          obtain ⟨hspaces, hnarrow⟩ := inv
          have hlt : token.raum < (s.lokal c).spaces.length :=
            (List.getElem?_eq_some_iff.mp hs).1
          refine ⟨?spacesRelease, ?narrowRelease⟩
          · intro sp' space' found
            by_cases same : sp' = token.raum
            · subst same
              simp only [List.getElem?_set_self hlt] at found
              have heq : space' = _ := (Option.some.inj found).symm
              subst heq
              have hspace := hspaces token.raum space hs
              obtain ⟨hfrei, hflags, hrights⟩ := hspace
              refine ⟨?frei, ?flags, ?rights⟩
              · exact frei_filter_ausstehend space _ hfrei fun tok t =>
                  (List.mem_filter.mp t).1
              · intro tok tmem
                have hold : tok ∈ space.ausstehend := (List.mem_filter.mp tmem).1
                exact hflags tok hold
              · intro entry hmem
                exact hrights entry hmem
            · have found0 : (s.lokal c).spaces[sp']? = some space' := by
                have : ((s.lokal c).spaces.set token.raum _)[sp']? = some space' := found
                rw [List.getElem?_set_ne (Ne.symm same)] at this
                exact this
              exact hspaces sp' space' found0
          · intro tok mem
            have hmem : tok ∈ (s.lokal c).verengt := mem
            exact hnarrow tok hmem
        · cases h

theorem tabellenGedeckt_tlbFuellen (target : ZielDaten) (core sp page : Nat) (s : MemState)
    (c : Kontext) {next : MemFrame}
    (h : (MemInstruction.tlbFuellen core sp page).evaluate target s c = some next)
    (inv : (s.lokal c).TabellenGedeckt) : next.TabellenGedeckt := by
  simp only [MemInstruction.evaluate] at h
  cases hs : (s.lokal c).spaces[sp]? with
  | none =>
    simp only [hs, Option.bind_eq_bind, Option.bind_none] at h
    cases h
  | some space =>
    simp only [hs, Option.bind_eq_bind, Option.bind_some] at h
    cases hm : space.abbildung page with
    | none =>
      simp only [hm, Option.bind_none] at h
      cases h
    | some entry =>
      simp only [hm, Option.bind_some, Option.pure_def, Option.some.injEq] at h
      subst h
      exact inv.aus_gleich rfl rfl

theorem tabellenGedeckt_tlbVerdraengen (target : ZielDaten) (core sp page : Nat) (s : MemState)
    (c : Kontext) {next : MemFrame}
    (h : (MemInstruction.tlbVerdraengen core sp page).evaluate target s c = some next)
    (inv : (s.lokal c).TabellenGedeckt) : next.TabellenGedeckt := by
  simp only [MemInstruction.evaluate, Option.some.injEq] at h
  subst h
  exact inv.aus_gleich rfl rfl

theorem tabellenGedeckt_ohne_tabellen (target : ZielDaten) (op : MemInstruction) (s : MemState)
    (c : Kontext) {next : MemFrame}
    (keine : ∀ frame : MemFrame, op.evaluate target s c = some frame →
      frame.spaces = (s.lokal c).spaces ∧ frame.verengt = (s.lokal c).verengt)
    (h : op.evaluate target s c = some next) (inv : (s.lokal c).TabellenGedeckt) :
    next.TabellenGedeckt :=
  inv.aus_gleich (keine next h).1 (keine next h).2

theorem tabellenGedeckt_evaluate (target : ZielDaten) (op : MemInstruction) (s : MemState)
    (c : Kontext) {next : MemFrame} (h : op.evaluate target s c = some next)
    (inv : (s.lokal c).TabellenGedeckt) : next.TabellenGedeckt := by
  cases op with
  | splitRegion slot point =>
    have keep := erhaelt_splitRegion target slot point s c next h
    exact inv.aus_gleich keep.2.1 keep.2.2
  | splitPages slot pages =>
    have keep := erhaelt_splitPages target slot pages s c next h
    exact inv.aus_gleich keep.2.1 keep.2.2
  | mergeRegions first second =>
    have keep := erhaelt_mergeRegions target first second s c next h
    exact inv.aus_gleich keep.2.1 keep.2.2
  | newSpace tables => exact tabellenGedeckt_newSpace target tables s c h inv
  | mapSpace space virt frames rights =>
    exact tabellenGedeckt_mapSpace target space virt frames rights s c h inv
  | protectSpace space virt pages rights =>
    exact tabellenGedeckt_protectSpace target space virt pages rights s c h inv
  | unmapSpace space virt pages => exact tabellenGedeckt_unmapSpace target space virt pages s c h inv
  | flushSpace name => exact tabellenGedeckt_flush target name s c h inv
  | activateSpace space =>
    have keep := erhaelt_activateSpace target space s c next h
    exact inv.aus_gleich keep.2.1 keep.2.2
  | bindToken name =>
    have keep := erhaelt_bindToken target name s c next h
    exact inv.aus_gleich keep.2.1 keep.2.2
  | tlbFuellen core space page => exact tabellenGedeckt_tlbFuellen target core space page s c h inv
  | tlbVerdraengen core space page =>
    exact tabellenGedeckt_tlbVerdraengen target core space page s c h inv

/-- Every context's frame of a state satisfies the table invariant. -/
def MemState.TabellenGedeckt (s : MemState) : Prop := ∀ c, (s.lokal c).TabellenGedeckt

theorem MemInstruction.tabellenGedeckt_schritt (target : ZielDaten) (op : MemInstruction)
    (c : Kontext) (s : MemState) (w : PUnit.{1}) (plans : List Plan) (next : MemState)
    (step : op.step target c s w plans next) (inv : s.TabellenGedeckt) :
    next.TabellenGedeckt := by
  obtain ⟨frame, evaluate, _, rfl⟩ := step
  have covered := tabellenGedeckt_evaluate target op s c evaluate (inv c)
  intro d
  by_cases same : d = c
  · rw [same]
    have eq : (frame.advance c s).lokal c = { frame with pc := (s.lokal c).pc + 1 } := by
      simp only [MemFrame.advance, Function.update_self]
    rw [eq]
    exact covered.aus_gleich rfl rfl
  · have eq : (frame.advance c s).lokal d = s.lokal d := by
      simp only [MemFrame.advance, Function.update_of_ne same]
    rw [eq]
    exact inv d

theorem memBoot_tabellenGedeckt (regions : List Strecke) (core : Option Nat) (c : Kontext) :
    ((memBoot regions core).lokal c).TabellenGedeckt := by
  apply MemFrame.TabellenGedeckt.leer
  · unfold memBoot
    by_cases h : c = entryContext
    · simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte]
  · unfold memBoot
    by_cases h : c = entryContext
    · simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte]

/-- **No reachable state of a memory unit holds a table entry outside every reservation.** Every
    instruction keeps the invariant, so every machine state a Mem unit reaches satisfies it. -/
theorem tabellenGedeckt_erreichbar (k : Katalog) (code : List MemInstruction) (start : AussenStart)
    {s : MemState}
    (reach : (memProgram k code).system.IErreichbar (I.start (memProgram k code) start).2 s) :
    s.TabellenGedeckt := by
  induction reach with
  | start => exact fun c => memBoot_tabellenGedeckt start.regions (start.assignment 0) c
  | schritt c w es _ step ih =>
    obtain ⟨op, _, ideal⟩ := step
    exact MemInstruction.tabellenGedeckt_schritt k.plattform.ziel op c _ w es _ ideal ih

end Gabbro.Core.Ast.LowLevel
