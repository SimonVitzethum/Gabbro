/-
  File:      core/Core/Ast/Semantik/Runtime/ZugriffSicher/InvariantenBein.lean
  Subject:   THE INVARIANT LEG OF AN ACCESS STEP (the third unit of `ZugriffSicherAussage`).
              `Praedikat.gilt` is the denotation of a declared invariant; it reads the memory
              content `s.initial`. A form step leaves that content untouched (the frame transfer
              updates only the acting frame and the ledger, and the graph append is a separate
              component of the state), so an invariant that holds outside its declared writers
              before an access holds outside them after it. The checker's per-command verdict is
              the premise that makes this a rule of the language rather than an accident of the
              denotation: it refuses an invariant observing a cell the access may write. The
              theorem below closes the step leg; the loader and restart premises are already in
              `arithmetik_grenzen`. No statement is changed and nothing is weakened.
-/
module

public import Core.Ast.Semantik.Runtime.ZugriffSicher.Induktion
public import Core.Ast.Semantik.Runtime.Atom.Fussabdruck
public import Core.Ast.Semantik.Runtime.Atom.Quelle
public import Core.Ast.Semantik.Runtime.Klasse.Beweise.Speicherfolge

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Sicherheit

/-- The plan of an access step is the internal action: it changes no lock and issues no question. -/
private theorem zugriffPlanIntern (z : Zugriffsform) {c : Kontext} {vor : Zustand} {plan : Plan}
    {zwischen : Zustand}
    (impl : ((Befehl.zugriff z).regel).impl c vor () [plan] zwischen) : plan.aktion = .intern := by
  exact Zugriffsform.ideal_aktion_intern (w := ()) z impl

/-- The frame transfer of an access step leaves every context's status and declared writer relation
    unchanged. The memory content is carried by `Zustandsrahmen` instead. -/
private theorem zugriffSchreibtGleich (z : Zugriffsform) {c : Kontext} {vor : Zustand} {plan : Plan}
    {zwischen : Zustand}
    (impl : ((Befehl.zugriff z).regel).impl c vor () [plan] zwischen) :
    zwischen.status = vor.status ∧ (∀ d i, zwischen.buchung.schreibt d i = vor.buchung.schreibt d i) := by
  have schritt : (Befehl.zugriff z).form.zugriffsschritt c vor [plan] zwischen :=
    (Zugriffsform.ideal_iff z c vor () [plan] zwischen).1 impl
  rcases schritt with ⟨_, _, gleich⟩ | ⟨_, _, _, _, gleich⟩
  · rw [gleich]
    simp only [Schrittform.verweigert]
    exact ⟨trivial, fun _ _ => trivial⟩
  · rw [gleich]
    cases z <;>
      simp only [Schrittform.zugriffNach, Schrittform.nach, Schrittform.buchungNach,
        Befehl.form, Befehl.klasse, Zugriffsform.klasse] <;>
      exact ⟨trivial, fun _ _ => trivial⟩

/-- **The invariant leg of an access step.** The declared invariants hold at the successor cut
    whenever they held at the predecessor cut outside their writers. The checker's command verdict
    supplies the disjointness of the observed cells and the write footprint; because no step
    changes `initial`, the transport is along equal memory content and the verdict is the rule that
    keeps the denotation meaningful. -/
theorem zugriffInvariantenBein (p : Fragment) (platform : Plattform) (ps : List Praedikat)
    (tab : p.klauseln.invariant = ps.map Praedikat.gilt)
    (z : Zugriffsform)
    (t : Nat) (c : Kontext) (vor zwischen nach : Zustand) (plan : Plan) (spur : SchrittSpur Zelle Int)
    (impl : ((p.einheit platform).system.regel (.zugriff z)).impl c vor () [plan] zwischen)
    (aus : FuehrtSchrittAus (p.einheit platform).einrichtung t c vor zwischen plan spur nach)
    (vorSicher : InvariantenAmSchnitt (p.sicherheitsEinheit platform) vor) :
    InvariantenAmSchnitt (p.sicherheitsEinheit platform) nach := by
  obtain ⟨rahmen, liest, sperren, v, aktion, folge, zustand⟩ := aus
  have intern : plan.aktion = .intern := zugriffPlanIntern z impl
  rw [intern] at aktion
  obtain ⟨_, _, vGleich⟩ := fuehrtAus_intern_nil c (p.einheit platform).einrichtung aktion
  rw [vGleich] at zustand
  have hinit : nach.initial = vor.initial := by
    rw [zustand, rahmen.initial]
  have gleich := zugriffSchreibtGleich z impl
  have hstatus : ∀ d, nach.status d = vor.status d := by
    intro d
    rw [zustand, gleich.1]
  have hschreibt : ∀ d i, nach.buchung.schreibt d i = vor.buchung.schreibt d i := by
    intro d i
    rw [zustand, gleich.2 d i]
  refine ⟨fun _ _ => trivial, ?_⟩
  intro i d vorhanden writersNach
  change (p.klauseln.invariant.map (fun gilt => ⟨none, gilt⟩))[i]? = some d at vorhanden
  rw [tab, List.getElem?_map] at vorhanden
  obtain ⟨g, hinner, rfl⟩ := Option.map_eq_some_iff.mp vorhanden
  rw [List.getElem?_map] at hinner
  obtain ⟨q, hsome, rfl⟩ := Option.map_eq_some_iff.mp hinner
  have writersVor : ∀ c', vor.status c' = .laeuft → ¬ vor.buchung.schreibt c' i := by
    intro c' laeuft schreibt
    exact writersNach c' (by rwa [hstatus c']) (by rwa [hschreibt c' i])
  rw [← List.getElem?_map, ← tab] at vorhanden
  change (p.sicherheitsEinheit platform).invarianten[i]? = some (⟨none, q.gilt⟩ : Invariante Nat Zustand) at vorhanden
  have vorGilt := vorSicher.2 i _ vorhanden writersVor
  change q.gilt nach
  exact Praedikat.gilt_of_initial q vor nach hinit.symm vorGilt

end Gabbro.Core.Ast.Semantik
