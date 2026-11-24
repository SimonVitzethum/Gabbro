module

public import Core.Annahme.Annahme
public import Core.Verfeinerung.Simulation

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}

/-- The current acceptance rule checks issuance against every policy, while a context
    transition issuing a request has no premise about the policy. A dead snapshot
    therefore rules out issuance in any accepted ideal context step. -/
theorem akzeptiert_ideal_ohne_frage (akzeptiert : Akzeptiert E) {hw t vor w spur nach}
    (step : I.Schritt E.einrichtung E.system E.katalog hw t vor (w, spur) nach)
    (ev : FrageEreignis) : Ereignis.frage ev ∉ spur.aussen := by
  intro mem
  cases step with
  | kontext normal ready form execute =>
    let tot : HwLauf := { hw with politik := { hw.politik with sicht := fun _ _ => .leer } }
    have transition : I.Schritt E.einrichtung E.system E.katalog tot t vor (.kontext _ _, spur) nach :=
      .kontext normal ready form execute
    have valid := akzeptiert.1.2.2.2 tot t vor _ spur nach transition ev mem
    let zugriff : Zugriff := ⟨ev.question.handle, ev.question.operation.required⟩
    have first : zugriff ∈ ev.question.zugriffe := List.mem_cons_self
    cases valid with
    | frisch alle =>
      have yes := (List.all_eq_true.mp alle) zugriff first
      have no := Aussen.tot_gueltig_falsch AussenSicht.leer ev.question.endpoint zugriff (fun _ => rfl)
      rw [no] at yes
      exact Bool.false_ne_true yes
    | stabil fest => exact Aussen.reihe_instabil _ _ (fest zugriff first)
  | antwort _ arrives =>
    rw [arrives.2.1] at mem
    exact frage_absurd_mem mem (by intro h; cases h)
  | interrupt _ enters =>
    obtain ⟨_, _, _, _, _, _, _, _, spurEq, _, _⟩ := enters
    rw [spurEq] at mem
    exact frage_absurd_mem mem (by intro h; cases h)
  | absturz crash =>
    rw [crash.2.1] at mem
    exact frage_absurd_mem mem (by intro h; cases h)

/-- In a matched implementation run the absence of issued questions also follows.
    A private step has no outside effects, and a matched step preserves its whole event list. -/
theorem akzeptiert_sim_ohne_frage (akzeptiert : Akzeptiert E) {ρ : Lauf E} {η : I.Lauf E}
    (sim : I.Sim E ρ η) {t w spur} (aufgezeichnet : ρ.zeit.spur t = some (w, spur))
    (ev : FrageEreignis) : Ereignis.frage ev ∉ spur.aussen := by
  obtain ⟨_, abgleich, _⟩ := sim
  have abgebildet := abgleich.spur t
  rw [aufgezeichnet] at abgebildet
  generalize idealMark : η.zeit.spur t = ideal at abgebildet
  cases abgebildet with
  | privat _ _ => exact List.not_mem_nil
  | schritt _ =>
    intro mem
    have tick := η.zeit.takt t
    rw [idealMark] at tick
    cases tick with
    | wartet label _ _ => cases label
    | schritt label step =>
      cases label
      exact akzeptiert_ideal_ohne_frage akzeptiert step ev mem

end Gabbro.Core.Beobachtung
