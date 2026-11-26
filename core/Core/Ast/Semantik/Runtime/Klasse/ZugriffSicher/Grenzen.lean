/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/ZugriffSicher/Grenzen.lean
  Subject:   THE BOUNDARY OBLIGATIONS OF A CHECKER-ACCEPTED FRAGMENT, made available to the
              pieces of `ZugriffSicherAussage`. `RegelnErfuellbar` keeps its construction of
              `GrenzenSicher` private; the same construction is repeated here so the access proof
              can call the safety induction without changing that module. The loader premise comes
              from `pruefeEinheit_start`, crash recovery from `pruefeEinheit_neustart`, and the
              answer, interrupt and restart boundaries from equal memory content and unchanged
              bookings. Nothing is weakened and no pinned statement is touched.
-/
module

public import Core.Sicherheit.RegelnErfuellbar

@[expose] public section

namespace Gabbro.Core.Sicherheit

open Maschine Katalog Ast Ast.Semantik

/-- The declared part of an invariant table holds at a state whose memory content satisfies
    every declared predicate. -/
private theorem zugriffInvariantenAusPruefung {p : Fragment} (platform : Plattform)
    {ps : List Praedikat}
    (tab : p.klauseln.invariant = ps.map Praedikat.gilt)
    (s : Ast.Semantik.Zustand) (haelt : ∀ q ∈ ps, q.haelt s.initial) :
    InvariantenAmSchnitt (p.sicherheitsEinheit platform) s := by
  refine ⟨fun _ _ => trivial, ?_⟩
  intro i d vorhanden _
  change (p.klauseln.invariant.map (fun gilt => ⟨none, gilt⟩))[i]? = some d at vorhanden
  rw [tab, List.getElem?_map] at vorhanden
  obtain ⟨g, hinner, rfl⟩ := Option.map_eq_some_iff.mp vorhanden
  rw [List.getElem?_map] at hinner
  obtain ⟨q, hsome, rfl⟩ := Option.map_eq_some_iff.mp hinner
  exact haelt q (List.mem_of_getElem? hsome)

/-- Invariants transport across a step that preserves memory content, bookings and running
    contexts. -/
private theorem zugriffInvariantenErhaltenInitial {p : Fragment} (platform : Plattform)
    {ps : List Praedikat}
    (tab : p.klauseln.invariant = ps.map Praedikat.gilt)
    (vor nach : Ast.Semantik.Zustand) (hinit : nach.initial = vor.initial)
    (hbuch : nach.buchung = vor.buchung) (hstatus : nach.status = vor.status)
    (vorSicher : InvariantenAmSchnitt (p.sicherheitsEinheit platform) vor) :
    InvariantenAmSchnitt (p.sicherheitsEinheit platform) nach := by
  obtain ⟨_, deklariert⟩ := vorSicher
  refine ⟨fun _ _ => trivial, ?_⟩
  intro i d vorhanden writersNach
  change (p.klauseln.invariant.map (fun gilt => ⟨none, gilt⟩))[i]? = some d at vorhanden
  rw [tab, List.getElem?_map] at vorhanden
  obtain ⟨g, hinner, rfl⟩ := Option.map_eq_some_iff.mp vorhanden
  rw [List.getElem?_map] at hinner
  obtain ⟨q, hsome, rfl⟩ := Option.map_eq_some_iff.mp hinner
  rw [← tab, ← List.getElem?_map] at vorhanden
  have writersVor : ∀ c, vor.status c = .laeuft → ¬ vor.buchung.schreibt c i := by
    intro c hc hcon
    have hc' : nach.status c = .laeuft := by rw [hstatus]; exact hc
    have hcon' : nach.buchung.schreibt c i := by rw [hbuch]; exact hcon
    exact writersNach c hc' hcon'
  have vorGilt : q.gilt vor := deklariert i _ vorhanden writersVor
  exact Praedikat.gilt_of_initial q vor nach hinit.symm vorGilt

/-- Invariants transport across an interrupt arrival: the fresh handler came to rest. -/
private theorem zugriffInvariantenErhaltenInterrupt {p : Fragment} (platform : Plattform)
    {ps : List Praedikat}
    (tab : p.klauseln.invariant = ps.map Praedikat.gilt)
    (vor nach : Ast.Semantik.Zustand) (c : Kontext)
    (hinit : nach.initial = vor.initial) (hbuch : nach.buchung = vor.buchung)
    (hstatus : ∀ c', c' ≠ c → nach.status c' = vor.status c')
    (hnach : nach.status c = .laeuft)
    (vorSicher : InvariantenAmSchnitt (p.sicherheitsEinheit platform) vor) :
    InvariantenAmSchnitt (p.sicherheitsEinheit platform) nach := by
  obtain ⟨_, deklariert⟩ := vorSicher
  refine ⟨fun _ _ => trivial, ?_⟩
  intro i d vorhanden writersNach
  change (p.klauseln.invariant.map (fun gilt => ⟨none, gilt⟩))[i]? = some d at vorhanden
  rw [tab, List.getElem?_map] at vorhanden
  obtain ⟨g, hinner, rfl⟩ := Option.map_eq_some_iff.mp vorhanden
  rw [List.getElem?_map] at hinner
  obtain ⟨q, hsome, rfl⟩ := Option.map_eq_some_iff.mp hinner
  rw [← tab, ← List.getElem?_map] at vorhanden
  have writersVor : ∀ c', vor.status c' = .laeuft → ¬ vor.buchung.schreibt c' i := by
    intro c' hc' hcon
    by_cases heq : c' = c
    · subst c'
      have hcon' : nach.buchung.schreibt c i := by rw [hbuch]; exact hcon
      exact writersNach c hnach hcon'
    · have hcNach : nach.status c' = .laeuft := by rw [hstatus c' heq]; exact hc'
      have hcon' : nach.buchung.schreibt c' i := by rw [hbuch]; exact hcon
      exact writersNach c' hcNach hcon'
  have vorGilt : q.gilt vor := deklariert i _ vorhanden writersVor
  exact Praedikat.gilt_of_initial q vor nach hinit.symm vorGilt

/-- **The boundary premises of a checker-accepted fragment.** -/
theorem fragmentGrenzen {p : Fragment} (platform : Plattform)
    {ps : List Praedikat}
    (tab : p.klauseln.invariant = ps.map Praedikat.gilt)
    (startOk : ∀ q ∈ ps, q.haelt p.speicher.initial)
    (restartOk : ∀ q ∈ ps, q.haelt (fun _ => 0)) :
    GrenzenSicher (p.sicherheitsEinheit platform) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro H start s _ _ h
    change Ast.Semantik.laden p.eingang p.eintritte p.speicher platform start (H.lade Ast.Semantik.bild) = some s at h
    unfold Ast.Semantik.laden at h
    split at h
    · cases h
      refine ⟨rfl, rfl, rfl, ?_⟩
      exact zugriffInvariantenAusPruefung platform tab _ (fun q hq => startOk q hq)
    · cases h
  · intro hw t a vor spur nach step vorSicher
    obtain ⟨_, _, _, heq⟩ := step
    have hinit : nach.initial = vor.initial := by rw [heq]; try rfl
    have hbuch : nach.buchung = vor.buchung := by rw [heq]; try rfl
    have hstatus : nach.status = vor.status := by rw [heq]; try rfl
    exact zugriffInvariantenErhaltenInitial platform tab vor nach hinit hbuch hstatus vorSicher
  · intro hw t id vor spur nach step vorSicher
    obtain ⟨k, irq, c, nmi, _, _, _, _, _, _, heq⟩ := step
    have hinit : nach.initial = vor.initial := by rw [heq]; try rfl
    have hbuch : nach.buchung = vor.buchung := by rw [heq]; try rfl
    have hstatus : ∀ c', c' ≠ c → nach.status c' = vor.status c' := by
      intro c' hne
      rw [heq]
      try rfl
      exact Function.update_of_ne hne _ _
    have hnach : nach.status c = .laeuft := by
      rw [heq]
      try rfl
      exact Function.update_self c .laeuft vor.status
    exact zugriffInvariantenErhaltenInterrupt platform tab vor nach c hinit hbuch hstatus hnach vorSicher
  · intro hw t vor spur nach step vorSicher
    have hcrash := (AbsturzSchritt.neustart step).2.2.2.1
    have hwieder : (p.sicherheitsEinheit platform).maschine.einrichtung.wiederanlauf.initial =
        (fun _ _ => 0) := rfl
    have hinit : nach.initial = (fun _ => 0) := by rw [hcrash, hwieder]
    exact zugriffInvariantenAusPruefung platform tab nach (fun q hq => by
      rw [hinit]
      exact restartOk q hq)

end Gabbro.Core.Sicherheit
