module

public import Core.Ast.LowLevel.Mem.Registry

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Text Katalog Maschine Waechter

open Text Katalog Maschine Waechter

theorem protectRealisiert (form : MemForm) : MemRealisiertAussage form := by
  intro k scope tree op hop s c
  simp only [memUnit, memProgram, memHead]
  by_cases hc : c = entryContext
  · subst c
    cases hs : s.status entryContext with
    | laeuft =>
        simp only [if_true, hs, reduceCtorEq, Option.bind_eq_bind, and_true]
        by_cases hp : (s.lokal entryContext).pc = 0
        · rw [hp]
          simp only [List.getElem?_cons_zero, Option.bind_some]
          constructor
          · intro h
            refine ⟨True.intro, True.intro, True.intro, ?_⟩
            by_contra hnot
            rw [if_neg hnot] at h
            cases h
          · intro h
            rw [if_pos h.2.2.2]
        · have hget : [op][(s.lokal entryContext).pc]? = none := by
            simp only [List.getElem?_singleton, hp, if_false]
          simp only [hget, Option.bind_none, hp, hs, false_and, and_false, iff_false]
          intro h
          cases h
    | ruht =>
        simp only [if_true, hs, reduceCtorEq, false_and, iff_self]
    | beendet code =>
        simp only [if_true, hs, reduceCtorEq, false_and, iff_self]
  · simp only [hc, if_false, hc, false_and, and_false, iff_false]
    intro h
    cases h


theorem protectIdeal (form : MemForm) : MemIdealAussage form := by
  intro k scope tree op hop
  intro c s w es es' s1 s2 h1 h2
  simp only [memUnit, memProgram, MemInstruction.rule, MemInstruction.step] at h1 h2
  rcases h1 with ⟨f1, heval1, hes1, hs1⟩
  rcases h2 with ⟨f2, heval2, hes2, hs2⟩
  have hf : f1 = f2 := Option.some.inj (heval1.symm.trans heval2)
  subst f2
  exact ⟨hes1.trans hes2.symm, hs1.trans hs2.symm⟩

theorem protectFortschritt (form : MemForm) : MemFortschrittAussage form := by
  intro k scope tree op hop
  intro s c hhead
  have hcond := (protectRealisiert form k scope tree op hop s c).mp hhead
  rcases hcond with ⟨hstatus, hc, hpc, heval⟩
  subst c
  rcases Option.isSome_iff_exists.mp heval with ⟨frame, hframe⟩
  refine Or.inl ⟨(), [plan], frame.advance entryContext s, ?_⟩
  simp only [memUnit, memProgram, MemInstruction.rule, MemInstruction.step]
  exact ⟨frame, hframe, True.intro, rfl⟩

theorem protectKosten (form : MemForm) : MemKostenAussage form := by
  intro k scope tree op hop t c s w middle next p trace hstep hexec
  rcases hstep with ⟨frame, heval, hplan, hmiddle⟩
  cases hplan
  rw [hmiddle] at hexec
  rcases hexec with ⟨_, _, _, v, hfuehrt, hmem, _⟩
  cases trace with
  | mk memory events =>
      generalize hev : events = outside at hfuehrt hmem ⊢
      cases hfuehrt with
      | intern =>
          simp only [hev, List.append_nil, List.map_nil] at hmem
          have hmemnil : Speicherfolge s.initial (.kontext c) s.graph [] [] s.graph := .nil _
          have hm : memory = [] := (hmem.ausgabe hmemnil rfl).1
          simp only [hm, hev, SchrittSpur.mk.injEq, true_and]
          rfl


theorem protectRegelSicher (form : MemForm) : MemRegelSicherAussage form := by
  intro k scope tree op hop H ρ t c w vor zwischen nach plan spur hhead hstep hexec
  rcases hstep with ⟨frame, heval, hplan, hzwischen⟩
  cases hplan
  rw [hzwischen] at hexec
  rcases hexec with ⟨hrahmen, hreads, sperren, v, hfuehrt, hmem, hnach⟩
  cases spur with
  | mk memory events =>
      generalize hev : events = outside at hfuehrt hmem ⊢
      cases hfuehrt with
      | intern =>
          simp only [List.append_nil, List.map_nil] at hmem
          generalize hg : nach.graph = gfinal at hmem ⊢
          cases hmem with
          | nil =>
              have wirkungen : Sicherheit.NeueWirkungen vor nach (⟨[], []⟩ : SchrittSpur ℕ UInt8) [] := by
                right
                refine ⟨List.not_mem_nil, ?_⟩
                rw [hnach]
                simp only [MemFrame.advance, List.append_nil]
              refine ⟨⟨?_, [], wirkungen, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
              · intro i actor access recorded _
                cases recorded
              · refine ⟨List.nodup_nil, fun _ _ mem => (List.not_mem_nil mem).elim, ?_⟩
                intro _ obj alive lost
                rw [hnach] at lost
                simp only [MemFrame.advance] at lost
                exact nomatch alive.symm.trans lost
              · intro _
                refine ⟨fun _ _ => trivial, ?_⟩
                intro i d declared _
                change ([] : List _)[i]? = some d at declared
                cases declared
              · intro _ l changeOwner
                rw [hnach, hrahmen.sperren] at changeOwner
                exact (changeOwner rfl).elim
              · intro ordered
                rw [hg]
                exact ordered
              · exact ⟨fun _ mem => (List.not_mem_nil mem).elim, [], wirkungen,
                  fun _ mem => (List.not_mem_nil mem).elim⟩
              · exact ⟨fun _ mem => (List.not_mem_nil mem).elim, [], wirkungen,
                  fun _ mem => (List.not_mem_nil mem).elim⟩


theorem protectErhaltung (form : MemForm) : MemErhaltungAussage form := by
  intro k scope tree op hop
  constructor
  · intro hw t c w s u s' i p spur bezug crash bereit head impl aus
    rcases impl with ⟨frame, heval, hplans, hu⟩
    cases hplans
    rcases bezug with ⟨hprot, hlocal⟩
    change s.lokal = i.lokal at hlocal
    change { s with lokal := i.lokal } = i at hprot
    rw [← hlocal] at hprot
    change s = i at hprot
    rw [hprot] at head heval hu bereit
    rw [hprot] at aus
    refine Or.inl ⟨s', ?_, ?_⟩
    · exact .kontext crash bereit ⟨op, head, frame, heval, rfl, hu⟩ aus
    · exact ⟨I.ProtokollBezug.refl _, rfl⟩
  · intro t s c w plans u head memory step
    rcases step with ⟨frame, heval, hplans, hu⟩
    refine ⟨LowLevel.plan, ⟨[], []⟩, u, hplans, ?_⟩
    refine ⟨?_, ?_, [], u, .intern, ?_, rfl⟩
    · rw [hu]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro l hl
      exact (List.not_mem_nil hl).elim
    · simp only [LowLevel.plan, List.append_nil, List.map_nil, List.filter_nil, schreibEreignisse]
      rw [hu]
      exact Speicherfolge.nil _

end Gabbro.Core.Ast.LowLevel
