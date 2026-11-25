/-
  File:      core/Core/Ast/Semantik/Runtime/Faden/Beweise/Komponierbar.lean
  Subject:   THE COMPOSABILITY OF THE ACCEPTED STEPS OF A LIFECYCLE INSTRUCTION WITH THE MACHINE FRAME.
             A step of `Befehl.faden` changes only frames, the acting thread's status and the ledger, records
             no memory event and no lock or outside event. The machine frame therefore holds, the read-label
             condition and the memory sequence are empty, and the action of the plan is executed by the
             corresponding constructor of `FuehrtAus` -- the internal action after a refusal, the class
             action when the machine accepts it. This proves the five independent composability statements
             pinned in `Faden/Offen.lean` and their common statement; the progress of a join stays open.
-/
module

public import Core.Ast.Semantik.Runtime.Faden.Offen
public import Core.Ast.Semantik.Runtime.Regeln

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

/-- Every instruction of the thread lifecycle belongs to one of the four lifecycle classes. -/
private theorem fadenform_lebenszyklus (z : Fadenform) :
    (Befehl.faden z).form.Lebenszyklus := by
  cases z <;> simp only [Befehl.form, Befehl.klasse, Fadenform.klasse,
    Schrittform.Lebenszyklus, reduceCtorEq, or_true, true_or, or_false, false_or]

/-- A lifecycle step with no memory events and no protocol events is a machine step: the empty trace
    replays the empty memory sequence, and the state after it is the state the protocol action produced,
    with the graph of the pre-state. -/
private theorem fuehrtSchrittAus_still (e : Einrichtung Nat Zelle Int Nat Rahmen PUnit PUnit)
    (t : Nat) (c : Kontext) (s u : Zustand) (plan : Plan) (v : Zustand)
    (rahmen : Zustandsrahmen s u) (hlesen : plan.lesen = []) (hfuss : plan.fuss = [])
    (haktion : FuehrtAus e t c s u plan.aktion [] [] v) :
    FuehrtSchrittAus e t c s u plan ⟨[], []⟩ { v with graph := s.graph } := by
  refine ⟨rahmen, ?_, [], v, haktion, ?_, rfl⟩
  · intro l hl
    rw [hlesen] at hl
    cases hl
  · rw [hlesen, hfuss]
    change Speicherfolge s.initial (.kontext c) s.graph [] [] s.graph
    exact Speicherfolge.nil _

/-- The facts every ideal step of a lifecycle instruction supplies: the form state stays in the
    machine frame, and the plan records no read and no footprint. -/
private theorem faden_schritt_fakten {z : Fadenform} {c : Kontext} {s u : Zustand} {w : PUnit.{1}}
    {plan : Plan} (step : (Befehl.faden z).ideal c s w [plan] u) :
    Zustandsrahmen s u ∧ plan.lesen = [] ∧ plan.fuss = [] := by
  change (Befehl.faden z).form.ideal c s w [plan] u at step
  obtain ⟨hu, _, hlesen, hfuss⟩ := Schrittform.lebenszyklus_ideal (fadenform_lebenszyklus z) step
  exact ⟨hu.rahmen, hlesen, hfuss⟩

/-- **Composability of the refusal of a lifecycle step** (`FadenVerweigertKomponierbarAussage`).
    The plan of the step is internal, so `FuehrtAus.intern` executes it with the empty trace. -/
theorem fadenVerweigertKomponierbar : FadenVerweigertKomponierbarAussage := by
  intro p platform z t s c w plan u _hkopf hstep hakt
  obtain ⟨rahmen, hlesen, hfuss⟩ := faden_schritt_fakten hstep
  exact ⟨_, _, fuehrtSchrittAus_still (p.einheit platform).einrichtung t c s u plan u
    rahmen hlesen hfuss (by rw [hakt]; exact FuehrtAus.intern)⟩

/-- **Composability of an accepted start** (`StarteKomponierbarAussage`). The resting thread and the
    machine's counter are the premises of `FuehrtAus.starte`; the machine records the acting context as
    the creator of the new thread. -/
theorem starteKomponierbar : StarteKomponierbarAussage := by
  intro p platform z t s c w plan u _hkopf hstep hakt hruht
  obtain ⟨rahmen, hlesen, hfuss⟩ := faden_schritt_fakten hstep
  exact ⟨_, _, fuehrtSchrittAus_still (p.einheit platform).einrichtung t c s u plan
    { u with status := Function.update u.status (.faden s.naechsterFaden) .laeuft,
             naechsterFaden := s.naechsterFaden + 1,
             erzeuger := Function.update u.erzeuger (.faden s.naechsterFaden) (some c) }
    rahmen hlesen hfuss (by rw [hakt]; exact FuehrtAus.starte hruht)⟩

/-- **Composability of an accepted join** (`VerbindeKomponierbarAussage`). The ended status of the
    joined context and the recorded creator are exactly the premises of `FuehrtAus.verbinde`; after the
    join the creator entry is cleared. -/
theorem verbindeKomponierbar : VerbindeKomponierbarAussage := by
  intro p platform z t s c w plan u kind _hkopf hstep hakt hfertig herz
  obtain ⟨rahmen, hlesen, hfuss⟩ := faden_schritt_fakten hstep
  obtain ⟨ausgang, hfertig⟩ := hfertig
  exact ⟨_, _, fuehrtSchrittAus_still (p.einheit platform).einrichtung t c s u plan
    { u with erzeuger := Function.update u.erzeuger kind none }
    rahmen hlesen hfuss (by rw [hakt]; exact FuehrtAus.verbinde hfertig herz)⟩

/-- **Composability of an accepted end** (`BeendeKomponierbarAussage`). The outcome the form sets in
    the acting thread's status is exactly the premise of `FuehrtAus.beende`. -/
theorem beendeKomponierbar : BeendeKomponierbarAussage := by
  intro p platform z t s c w plan u _hkopf hstep hakt hfertig
  obtain ⟨rahmen, hlesen, hfuss⟩ := faden_schritt_fakten hstep
  obtain ⟨ausgang, hfertig⟩ := hfertig
  exact ⟨_, _, fuehrtSchrittAus_still (p.einheit platform).einrichtung t c s u plan u
    rahmen hlesen hfuss (by rw [hakt]; exact FuehrtAus.beende hfertig)⟩

/-- **Composability of an accepted switch** (`WechsleKomponierbarAussage`). The free core, the running
    context on no core and the distinctness from the acting context are the premises of
    `FuehrtAus.wechsle`. -/
theorem wechsleKomponierbar : WechsleKomponierbarAussage := by
  intro p platform z t s c w plan u kern kind _hkopf hstep hakt hfrei
  obtain ⟨rahmen, hlesen, hfuss⟩ := faden_schritt_fakten hstep
  rcases hfrei with ⟨hfrei, hlaeuft, hnirgends, handers⟩
  exact ⟨_, _, fuehrtSchrittAus_still (p.einheit platform).einrichtung t c s u plan
    { u with kerne := Function.update u.kerne kern { u.kerne kern with laeuft := some kind } }
    rahmen hlesen hfuss (by rw [hakt]; exact FuehrtAus.wechsle hfrei hlaeuft hnirgends handers)⟩

/-- Every action the machine accepts is executed by the protocol with the empty trace. The actions
    that are not lifecycle actions carry `False` as their acceptance condition. -/
private theorem ausfuehrbar_fuehrtAus (e : Einrichtung Nat Zelle Int Nat Rahmen PUnit PUnit)
    (t : Nat) (c : Kontext) (s u : Zustand) (a : Aktion Nat PUnit) (h : a.Ausfuehrbar s u c) :
    ∃ v, FuehrtAus e t c s u a [] [] v := by
  cases a with
  | intern => exact ⟨u, FuehrtAus.intern⟩
  | starte => exact ⟨_, FuehrtAus.starte h⟩
  | verbinde kind =>
    obtain ⟨⟨ausgang, hfertig⟩, herz⟩ := h
    exact ⟨_, FuehrtAus.verbinde hfertig herz⟩
  | beende =>
    obtain ⟨ausgang, hfertig⟩ := h
    exact ⟨u, FuehrtAus.beende hfertig⟩
  | wechsle kern kind =>
    rcases h with ⟨hfrei, hlaeuft, hnirgends, handers⟩
    exact ⟨_, FuehrtAus.wechsle hfrei hlaeuft hnirgends handers⟩
  | warte _ => exact False.elim h
  | sperre _ _ => exact False.elim h
  | frage _ => exact False.elim h
  | verbrauche _ => exact False.elim h
  | rueckkehr => exact False.elim h

/-- **Composability of the accepted steps of a lifecycle instruction**
    (`FadenKomponierbarAussage`). The machine's acceptance condition decides which protocol action
    runs; the form supplies the frame, the empty plan and the state the action works on. -/
theorem fadenKomponierbar : FadenKomponierbarAussage := by
  intro p platform z t s c w plan u _hkopf hstep haus
  obtain ⟨rahmen, hlesen, hfuss⟩ := faden_schritt_fakten hstep
  obtain ⟨v, hv⟩ := ausfuehrbar_fuehrtAus (p.einheit platform).einrichtung t c s u
    plan.aktion haus
  exact ⟨_, _, fuehrtSchrittAus_still (p.einheit platform).einrichtung t c s u plan v
    rahmen hlesen hfuss hv⟩

end Gabbro.Core.Ast.Semantik
