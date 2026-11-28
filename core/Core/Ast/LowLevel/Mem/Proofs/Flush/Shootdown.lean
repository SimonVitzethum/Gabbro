module

public import Core.Ast.LowLevel.Mem.Proofs.Flush.Flush
public import Core.Ast.LowLevel.Mem.Proofs.Tabelle.Bindung

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

private theorem cache_miss_of_shootdown {cache : TranslationCache} {token : Zuruecknahme}
    (clear : cache.Frei token.raum token.seite token.seiten) (core page : Nat)
    (inside : token.contains page) : cache.sicht core token.raum page = none := by
  unfold TranslationCache.sicht
  have miss : (cache.zellen.find? (fun cell =>
      cell.kern == core && cell.raum == token.raum && cell.seite == page)) = none := by
    apply List.find?_eq_none.mpr
    intro cell member hit
    simp only [Bool.and_eq_true, beq_iff_eq] at hit
    have outside := clear cell member
    simp only [TlbZelle.imBereich, decide_eq_false_iff_not] at outside
    exact outside ⟨hit.1.2, hit.2.symm ▸ inside⟩
  rw [miss]
  rfl

private theorem flush_frame_release {target : ZielDaten} {s : MemState} {c : Kontext}
    {name : Identifier} {token : Zuruecknahme} {frame : MemFrame}
    (bound : (MemInstruction.flushSpace name).abschluss s c = some token)
    (eval : (MemInstruction.flushSpace name).evaluate target s c = some frame)
    (frames : frame.result = some (.frames (token.frames target.seitengranule))) :
    (s.lokal c).tlb.Frei token.raum token.seite token.seiten ∧
    frame.tlb = (s.lokal c).tlb ∧
    ∀ page, token.contains page → frame.tabellenSicht token.raum page = none := by
  cases found : (s.lokal c).marken.find? (fun p => p.1.val == name.val) with
  | none =>
    simp only [MemInstruction.abschluss, found, Option.map_none] at bound
    cases bound
  | some binding =>
    obtain ⟨boundName, selected⟩ := binding
    simp only [MemInstruction.abschluss, found, Option.map_some, Option.some.injEq] at bound
    subst selected
    cases spaceAt : (s.lokal c).spaces[token.raum]? with
    | none =>
      simp only [MemInstruction.evaluate, found, spaceAt, Option.bind_eq_bind,
        Option.bind_some, Option.bind_none] at eval
      cases eval
    | some space =>
      cases kind : token.nurRechte
      · simp only [MemInstruction.evaluate, found, spaceAt, Option.bind_eq_bind, Option.bind_some,
          kind, Bool.false_eq_true, if_false] at eval
        split at eval
        · rename_i done
          simp only [Bool.and_eq_true] at done
          simp only [Option.pure_def, Option.some.injEq] at eval
          subst frame
          refine ⟨TranslationCache.frei_eq_true.mp done.2, rfl, ?_⟩
          intro page inside
          have pos : token.raum < (s.lokal c).spaces.length :=
            (List.getElem?_eq_some_iff.mp spaceAt).1
          have index : page - token.seite < token.seiten := by
            change token.seite ≤ page ∧ page < token.seite + token.seiten at inside
            omega
          have offset : token.seite + (page - token.seite) = page := by
            change token.seite ≤ page ∧ page < token.seite + token.seiten at inside
            omega
          have absent := List.all_eq_true.mp done.1.2 _ (List.mem_range.mpr index)
          rw [offset] at absent
          simp only [MemFrame.tabellenSicht, List.getElem?_set_self pos]
          cases entry : space.abbildung page with
          | none => rfl
          | some entry => simp only [entry, Option.isNone] at absent
        · cases eval
      · simp only [MemInstruction.evaluate, found, spaceAt, Option.bind_eq_bind, Option.bind_some,
          kind, if_true] at eval
        split at eval
        · simp only [Option.pure_def, Option.some.injEq] at eval
          subst frame
          cases frames
        · cases eval

/-- Every checked frame release observes the absence of translations on all cores before returning
    the frames. The released pages remain absent in the successor's bound MMU view. The trace
    identifies the same revocation and epoch as the checked instruction. -/
def MemShootdownAussage : Prop :=
  ∀ {k : Katalog} {code : List MemInstruction} {hw : HwLauf} {t : Nat}
    {s next : MemState} {c : Kontext} {name : Identifier} {token : Zuruecknahme},
    (memProgram k code).system.kopf s c = some (.flushSpace name) →
    ImplSchritt memSetup (memProgram k code).system k hw t s
      (.kontext c (), ⟨[], [.ruecknahmeAbgeschlossen s.epoche token]⟩) next →
    (next.lokal c).result = some (.frames (token.frames k.plattform.ziel.seitengranule)) →
    (MemInstruction.flushSpace name).abschluss s c = some token ∧
    (s.lokal c).tlb.Frei token.raum token.seite token.seiten ∧
    (next.lokal c).tlb = (s.lokal c).tlb ∧
    ∀ core addr right, k.plattform.ziel.virtuell addr →
      token.contains (addr / k.plattform.ziel.seitengranule) →
      uebersetze k.plattform.ziel (next.lokal c).mmuSicht core token.raum addr right =
        .error .absent

theorem mem_shootdown : MemShootdownAussage := by
  intro k code hw t s next c name token head step frames
  obtain ⟨op, frame, chosen, eval, label, rfl⟩ := memKontextSchrittGenau step
  cases Option.some.inj (chosen.symm.trans head)
  obtain ⟨selected, bound, _, _⟩ := MemInstruction.flushToken eval
  have key : (MemInstruction.flushSpace name).abschluss s c = some token := by
    change (MemInstruction.flushSpace name).abschluss s c = some selected at bound
    rw [MemInstruction.schrittSpur, bound] at label
    cases label
    exact bound
  have result : frame.result = _ := by
    simpa only [MemFrame.advance, Function.update_self] using frames
  obtain ⟨clear, cache, table⟩ := flush_frame_release key eval result
  simp only [MemFrame.advance, Function.update_self]
  refine ⟨key, clear, cache, ?_⟩
  intro core addr right virtual inside
  have miss := cache_miss_of_shootdown clear core _ inside
  have absent := table _ inside
  unfold uebersetze MemFrame.mmuSicht
  simp only [virtual, not_true_eq_false, if_false, cache, miss, Option.none_or, absent]

theorem mem_shootdown_erfuellbar :
    ∃ k code hw t s next name token,
      (memProgram k code).system.kopf s entryContext = some (.flushSpace name) ∧
      ImplSchritt memSetup (memProgram k code).system k hw t s
        (.kontext entryContext (), ⟨[], [.ruecknahmeAbgeschlossen s.epoche token]⟩) next ∧
      (next.lokal entryContext).result = some (.frames (token.frames k.plattform.ziel.seitengranule)) := by
  obtain ⟨k, code, _, _, hw, t, s, frame, name, token, _, _, _, _, head, _, frames, step, _⟩ :=
    memFlushFreigabe_erfuellbar
  refine ⟨k, code, hw, t, s, frame.advance entryContext s, name, token, head, step, ?_⟩
  simpa only [MemFrame.advance, Function.update_self] using frames

end Gabbro.Core.Ast.LowLevel
