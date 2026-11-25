module

public import Core.Ast.LowLevel.DeviceUnit
public import Core.Beobachtung.Nichtinterferenz
public import Core.Beobachtung.Satz

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel (entryContext)
open Gabbro.Core.Ast.LowLevel.Device (Binding Denotation Rule RegisterAccess Frame State Plan)

/-- The loader installs exactly the declared device authority: the declaring
    entry context alone holds the free right, every other object maps to none. -/
theorem geraete_laden_buchung {k : Katalog} {scope : Gabbro.Core.Ast.Scope}
    {locals : Gabbro.Core.Ast.Umgebung scope} {d : Denotation k scope}
    {start : AussenStart} {load : Ladung} {z : State}
    (geladen : (d.unit locals).laden start load = some z) :
    z.buchung.geraet = fun o =>
      if o = d.binding.object then some (entryContext, .frei) else none := by
  unfold Denotation.unit Gabbro.Core.Ast.LowLevel.Device.unit at geladen
  dsimp only at geladen
  split at geladen
  · obtain rfl := Option.some.inj geladen
    rfl
  · cases geladen

/-- The loader installs exactly the declared handle rights: the declaring entry
    context alone holds the binding's handle, every other handle is refused. -/
theorem geraete_laden_aussengriff {k : Katalog} {scope : Gabbro.Core.Ast.Scope}
    {locals : Gabbro.Core.Ast.Umgebung scope} {d : Denotation k scope}
    {start : AussenStart} {load : Ladung} {z : State}
    (geladen : (d.unit locals).laden start load = some z) :
    z.buchung.aussengriff = fun c h right =>
      c = entryContext ∧ h = d.binding.handle ∧ right ∈ h.rights := by
  unfold Denotation.unit Gabbro.Core.Ast.LowLevel.Device.unit at geladen
  dsimp only at geladen
  split at geladen
  · obtain rfl := Option.some.inj geladen
    rfl
  · cases geladen

/-- The loaded frame carries the declared device in `ready` for the declaring
    context; no other context declares a phase. -/
private theorem bootFor_phasen (obj : Objekt) (core : Option Nat) :
    ((Gabbro.Core.Ast.LowLevel.Device.bootFor obj core).lokal entryContext).phases obj =
      some .ready := by
  simp only [Gabbro.Core.Ast.LowLevel.Device.bootFor, if_true]

theorem geraete_laden_phasen {k : Katalog} {scope : Gabbro.Core.Ast.Scope}
    {locals : Gabbro.Core.Ast.Umgebung scope} {d : Denotation k scope}
    {start : AussenStart} {load : Ladung} {z : State}
    (geladen : (d.unit locals).laden start load = some z) :
    (z.lokal entryContext).phases d.binding.object = some .ready := by
  unfold Denotation.unit Gabbro.Core.Ast.LowLevel.Device.unit at geladen
  dsimp only at geladen
  split at geladen
  · obtain rfl := Option.some.inj geladen
    exact bootFor_phasen _ (start.assignment 0)
  · cases geladen

/-- Device steps change only the acting frame: the booking survives issue and reply. -/
theorem geraete_schritt_erhaelt_buchung {k : Katalog} {binding : Binding k}
    {access : RegisterAccess} {required : GeraetePhase} {target : Option GeraetePhase}
    {c : Kontext} {s u : State} {plan : Plan}
    (schritt : Rule binding access required target c s plan u) :
    u.buchung = s.buchung := by
  cases schritt with
  | issue _ _ => rfl
  | consume _ _ _ _ => rfl

/-- With empty labels every question is public: an issue step appends exactly one
    low event, the question itself. -/
private theorem frage_leer {Ort : Type} (q : Frage) :
    (Etiketten.leer (Ort := Ort)).frage q = ∅ := by
  simp only [Etiketten.frage, Etiketten.leer]
  induction q.zugriffe with
  | nil => rfl
  | cons _ _ ih =>
    simp only [List.map_cons, List.foldl_cons, Finset.empty_union] at ih ⊢
    exact ih

theorem geraete_issue_beob {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type}
    [DecidableEq L]
    {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    (leer : E.etiketten = .leer) (e : FrageEreignis) :
    aussenBeob E (.frage e) =
      [.frage e.context e.questionInstance e.question] := by
  have hfrage : E.etiketten.frage e.question = ∅ := leer ▸ frage_leer e.question
  simp only [aussenBeob, hfrage, oeffentlich, decide_true, sichtbar, if_true,
    Option.toList_some]

/-- With empty labels an admitted answer arrival appends two low events: the
    answer and the register address it touches. -/
theorem geraete_antwort_beob {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type}
    [DecidableEq L]
    {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    (leer : E.etiketten = .leer) (e : AntwortEreignis)
    (ok : e.reply.result.isOk = true) {bus : GeratBus} {adresse : Nat}
    (register : registerAdresse E.katalog.plattform e.question = some (bus, adresse)) :
    aussenBeob E (.antwort e) =
      [.antwort e.context e.questionInstance e.question e.reply,
        .register e.question.endpoint bus adresse] := by
  have hfrage : E.etiketten.frage e.question = ∅ := leer ▸ frage_leer e.question
  simp only [aussenBeob, hfrage, oeffentlich, decide_true, sichtbar, if_true,
    ok, register, Option.map_some, Option.toList_some, List.cons_append,
    List.nil_append]

/-- The missing checker duty for device units, in the language of `Satz.lean`:
    protocol steps (answer arrival, interrupt entry, crash) and pauses must keep
    the coupling, exactly as for source fragments. `RegelFluss` alone does not
    force the right run into the same step kind: a consume step is silent while
    an arrival appends two events (`geraete_issue_beob`, `geraete_antwort_beob`
    give lengths one and two), so an arrival-vs-consume interleaving breaks
    prefix-length equality. The full device duty is the conjunction below. -/
def GeraeteProtokollNIAussage : Prop :=
  ∀ (k : Katalog) (scope : Gabbro.Core.Ast.Scope) (locals : Gabbro.Core.Ast.Umgebung scope)
    (d : Denotation k scope),
    ProtokollNIPflicht (d.unit locals) ∧ PausenNIPflicht (d.unit locals)

end Gabbro.Core.Beobachtung
