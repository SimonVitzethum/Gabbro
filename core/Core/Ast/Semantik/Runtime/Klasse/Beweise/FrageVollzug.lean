module

public import Core.Ast.Semantik.Runtime.Atom.Beweise.Komponierbar
public import Core.Ideal.Eigenschaften
public import Core.Maschine.Protokoll

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Aussenfrage

variable {F : Schrittform}

/-- The operand and the authority in the pre-state fix the question plan and the frame transfer.
    The refusal branch keeps the private plan and halts the acting frame. -/
theorem Schrittform.frage_ideal (hk : F.klasse = .frage) {c : Kontext} {s u : Zustand}
    {w : PUnit.{1}} {plans : List Plan} :
    F.ideal c s w plans u ↔
      (¬ F.klasse.befugt (F.operand (s.lokal c)) s c ∧
        plans = [Semantik.plan] ∧ u = F.verweigert c s) ∨
      (F.klasse.befugt (F.operand (s.lokal c)) s c ∧
        plans = [F.plan (s.lokal c) 0] ∧ u = F.zugriffNach c s 0) := by
  rw [Schrittform.ideal, hk]
  simp only [Schrittform.zugriffsschritt, hk, Wirkungsklasse.Lesewert,
    Wirkungsklasse.liest, Bool.false_eq_true, false_or]
  constructor
  · rintro (refused | ⟨owned, v, rfl, same, after⟩)
    · exact Or.inl refused
    · exact Or.inr ⟨owned, same, after⟩
  · rintro (refused | ⟨owned, same, after⟩)
    · exact Or.inl refused
    · exact Or.inr ⟨owned, 0, rfl, same, after⟩

/-- The question rule has a local step in every state, including an explicit refusal when the
    operand cannot be resolved or its authority check fails. -/
theorem Schrittform.frage_fortschritt (hk : F.klasse = .frage) (c : Kontext) (s : Zustand) :
    ∃ plan u, F.ideal c s () [plan] u := by
  by_cases owned : F.klasse.befugt (F.operand (s.lokal c)) s c
  · exact ⟨_, _, (F.frage_ideal hk).2 (Or.inr ⟨owned, rfl, rfl⟩)⟩
  · exact ⟨_, _, (F.frage_ideal hk).2 (Or.inl ⟨owned, rfl, rfl⟩)⟩

/-- The authority check makes the rule deterministic even before the memory choice is fixed. -/
theorem Schrittform.frage_bestimmt (hk : F.klasse = .frage) : Ideal.RegelBestimmt F.regel := by
  intro c s w plans plans' u u' left right
  rcases (F.frage_ideal hk (w := w)).1 left with ⟨denied, rfl, rfl⟩ | ⟨owned, rfl, rfl⟩
  · rcases (F.frage_ideal hk (w := w)).1 right with ⟨_, rfl, rfl⟩ | ⟨owned, _, _⟩
    · exact ⟨rfl, rfl⟩
    · exact (denied owned).elim
  · rcases (F.frage_ideal hk (w := w)).1 right with ⟨denied, _, _⟩ | ⟨_, rfl, rfl⟩
    · exact (denied owned).elim
    · exact ⟨rfl, rfl⟩

/-- Every ideal question step composes with the machine. An authorized operand emits the stamped question
    in the trace and the pending ledger and extends the RC11 graph with its outside label. A refusal
    uses the empty trace and keeps the graph. -/
theorem Schrittform.frage_vollzug (hk : F.klasse = .frage)
    (e : Einrichtung Nat Zelle Int Nat Rahmen PUnit PUnit)
    {t : Nat} {c : Kontext} {s u : Zustand} {w : PUnit.{1}} {p : Plan}
    (gut : s.SpeicherGut) (step : F.ideal c s w [p] u) :
    ∃ spur s', FuehrtSchrittAus e t c s u p spur s' ∧
      ∀ q, p.aktion = .frage q →
        spur.aussen = [.frage (s.stelleFrage t c q)] ∧
          s'.fragen = s.fragen ++ [s.stelleFrage t c q] := by
  have access : F.zugriffsschritt c s [p] u := by
    simpa only [Schrittform.ideal, hk] using step
  have frame := zugriffsschritt_rahmen F c s u access
  have reads := zugriffsschritt_liest F c s u access
  rcases (F.frage_ideal hk).1 step with ⟨_, same, _⟩ | ⟨owned, same, _⟩
  · cases (List.cons.inj same).1
    refine ⟨⟨[], []⟩, { u with graph := s.graph },
      ⟨frame, reads, [], u, FuehrtAus.intern, Speicherfolge.nil _, rfl⟩, ?_⟩
    intro q action
    cases action
  · rw [hk, Wirkungsklasse.befugt] at owned
    obtain ⟨q, operand, _⟩ := owned
    have planEq : p = planMit (.frage q) := by
      simpa only [Schrittform.plan, hk, Wirkungsklasse.plan, Operand.fragePlan, operand, planMit]
        using (List.cons.inj same).1
    subst p
    let event := s.stelleFrage t c q
    let label := aussenEtikett e (.frage event)
    have noRead : ¬ label.art.liest := by
      simp only [label, aussenEtikett, Speicher.Art.liest, not_false_eq_true]
    obtain ⟨g, next⟩ := Speicher.Zustand.schritt_ohne_lesen gut.1 gut.2 (.kontext c) label noRead
    refine ⟨⟨[(.kontext c, label)], [.frage event]⟩, { u.frage event with graph := g },
      ⟨frame, reads, [], u.frage event, FuehrtAus.frage q,
        Speicherfolge.cons (Initialisierung.ohne (Or.inl rfl)) next (Speicherfolge.nil g), rfl⟩, ?_⟩
    intro q' action
    have sameQuestion : q = q' := Aktion.frage.inj action
    subst q'
    exact ⟨rfl, congrArg (fun pending => pending ++ [event]) frame.fragen⟩

/-- The question case for composed ideal determinacy uses the existing graph-choice relation. -/
theorem Schrittform.frage_vollzug_bestimmt (hk : F.klasse = .frage)
    {e : Einrichtung Nat Zelle Int Nat Rahmen PUnit PUnit}
    {t : Nat} {c : Kontext} {s u v s' s'' : Zustand} {w : PUnit.{1}}
    {p p' : Plan} {spur spur' : SchrittSpur Zelle Int}
    (left : F.ideal c s w [p] u) (right : F.ideal c s w [p'] v)
    (run : FuehrtSchrittAus e t c s u p spur s')
    (run' : FuehrtSchrittAus e t c s v p' spur' s'')
    (wahl : SpeicherWahlGleich s'.graph s''.graph) : spur = spur' ∧ s' = s'' := by
  obtain ⟨same, rfl⟩ := F.frage_bestimmt hk c s w [p] [p'] u v left right
  cases (List.cons.inj same).1
  exact run.bestimmt run' wahl

end Gabbro.Core.Ast.Semantik
