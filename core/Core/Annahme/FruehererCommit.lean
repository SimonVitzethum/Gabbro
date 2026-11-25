module

public import Core.Annahme.HostedLauf

@[expose] public section

namespace Gabbro.Core.Annahme

open Katalog Maschine
open Sicherheit (AussenCommit Wirkung)
open Hosted

/-- With the selected rows, a context cannot add an unmediated outside commit that touches
    an object the rows do not declare stable. The context cannot rely on an earlier answer
    to supply the stability the catalogue has not granted. -/
theorem unvermittelter_commit_verweigert {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type}
    [DecidableEq L] {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form} {run t s c w spur s'}
    (step : I.Schritt E.einrichtung E.system E.katalog run t s (.kontext c w, spur) s')
    (effect : AussenCommit) {neu : List Wirkung}
    (ledger : s'.buchung.wirkungen = s.buchung.wirkungen ++ neu) (mem : Wirkung.aussen effect ∈ neu)
    (instabil : ¬ Aussen.ReihenStabil E.katalog.plattform effect.frage.handle.origin.object) :
    ¬ Akzeptiert E := by
  intro akzeptiert
  obtain ⟨suffix, record, check⟩ := ((akzeptiert_aussen akzeptiert).1 run t s (.kontext c w) spur s' step).2
  have equal := List.append_cancel_left (ledger.symm.trans record)
  have covers := (check effect (equal ▸ mem)).2.2.2.1
  exact instabil (covers ⟨effect.frage.handle, effect.frage.operation.required⟩ List.mem_cons_self)

/-- An unmediated form uses the earlier reply as its only external evidence. -/
def fruehereEinheit : Modell :=
  let regel : Regel Zustand Plan Unit :=
    let commit := fun c (s : Zustand) (_ : Unit) (plans : List Plan) (u : Zustand) =>
      ∃ a ∈ s.antworten, a.question = frage ∧ a.reply.result.isOk = true ∧
        plans = [bindePlan] ∧
        u = { s with buchung := { s.buchung with wirkungen := s.buchung.wirkungen ++
          [.aussen ⟨c, a.question, Aussen.einzel a.reply.origin⟩] } }
    ⟨commit, commit⟩
  { einheit with system := { einheit.system with regel := fun _ => regel } }

theorem frueherer_commit_erfuellbar :
    ∃ (run : HwLauf) (vor nach : Zustand) (spur : Spur) (vorher : AntwortEreignis) (effect : AussenCommit),
      vorher ∈ vor.antworten ∧ vorher.cut < 3 ∧ vorher.reply.result.isOk = true ∧
      atomar fruehereEinheit.katalog.plattform (run.politik.sicht vorher.cut []) vorher.question =
        .antwort vorher.reply ∧
      AussengriffeEigen vor kontext effect.frage ∧ Aussen.Abgeleitet
        (Aussen.griffAus vorher.reply effect.frage.handle) vorher.reply ∧
      effect.herkunft vorher.reply.origin ∧
      ¬ Aussen.GueltigBeiCommit fruehereEinheit.katalog.plattform (run.politik.sicht 3 vor.verlauf) effect.frage ∧
      I.Schritt fruehereEinheit.einrichtung fruehereEinheit.system fruehereEinheit.katalog
        run 3 vor (.kontext kontext (), spur) nach ∧
      nach.buchung.wirkungen = vor.buchung.wirkungen ++ [.aussen effect] ∧ ¬ Akzeptiert fruehereEinheit := by
  obtain ⟨s, _⟩ := zulStart_erfuellbar (erlaubt []) Sicherheit.Laufkonstruktion.bild_gueltig
  let vorher := angekommen s []
  let gebunden := binde (startZustand s)
  let vor := (gebunden.frage (gestellt s)).antwort vorher
  let effect : AussenCommit := ⟨kontext, frage, Aussen.einzel vorher.reply.origin⟩
  let nach : Zustand := { vor with buchung := { vor.buchung with wirkungen := [.aussen effect] } }
  let run := Umgebung.referenzLauf fruehereEinheit.katalog 1 (fun t h => if t = 3 then .leer else sicht [] t h)
  let spur : Spur := ⟨[], []⟩
  have form : fruehereEinheit.system.ISchritt kontext vor () [bindePlan] nach :=
    ⟨(), rfl, vorher, List.mem_cons_self, rfl, rfl, rfl, rfl⟩
  have rahmen : Zustandsrahmen vor nach := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have aus : FuehrtSchrittAus einrichtung 3 kontext vor nach bindePlan spur nach :=
    ⟨rahmen, fun _ mem => (List.not_mem_nil mem).elim, [], nach, .intern, .nil _, rfl⟩
  have step : I.Schritt fruehereEinheit.einrichtung fruehereEinheit.system fruehereEinheit.katalog
      run 3 vor (.kontext kontext (), spur) nach :=
    .kontext rfl ⟨0, rfl, rfl, rfl⟩ form aus
  refine ⟨run, vor, nach, spur, vorher, effect, List.mem_cons_self, Nat.lt_succ_self _, rfl, rfl,
    eigene_frage _, .griff _ _, rfl, ?_, step, rfl,
    unvermittelter_commit_verweigert step effect rfl List.mem_cons_self
      (Aussen.hosted_nicht_stabil _ _ rfl)⟩
  exact issue_ungueltig [] []

end Gabbro.Core.Annahme
