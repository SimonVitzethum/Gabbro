/-
  File:      core/Core/Annahme/DomaeneBeweise/Vakuum.lean
  Subject:   MK-17c item 1 — VACUITY FINDING: no accepted unit satisfies the NI comparison
              premises once the acceptance conjunct is restored.

  Finding. Under the MK-17b checker row (`DomaenenLokal` in `Core/Annahme/Lokal.lean`)
  acceptance demands run isolation under EVERY domain plan: the row quantifies over all
  plans, with no coherence or well-formedness premise. Hence any unit with an admitted
  run that records a question at a context cut is unaccepted: pick the hostile plan that
  puts every context in domain `0` and every device object in domain `1` with no
  channels. The row then forces the recorded cut to respect the domains, while the
  machine fact `frageStelltKontext` shows the recorded question carries the acting
  context's number and is therefore foreign under the hostile plan — contradiction.

  Consequence. `ni_erfuellbar` (in `Core/Beobachtung/NichtinterferenzErfuellbar.lean`)
  cannot be restored WITH its acceptance conjunct: `niVergleich_akzeptiert_unmoeglich`
  proves the negation of the full premise bundle with `Akzeptiert E` added. The accepted
  unit issuing a question over a declared channel that MK-17c asked for does not exist;
  a declared channel in one plan never discharges the row's universal plan
  quantification. The NI statement over elaborated units (`DomaenenNIAussage`) is
  unaffected: its proof never issues a question.

  Proposed diff (meaning change, NOT applied here — needs an explicit decision):
  bind the plan to the unit. Store the domain declaration in the unit (or elaborate it
  from the syntax) and quantify `DomaenenLokal`/`RegelIsolation` only over the unit's
  own table, e.g.
  ```
  def DomaenenLokal (E : ...) : Prop :=
    ∀ (s : Zustand ...) (c : Kontext) (i : ι),
      E.system.kopf s c = some i → RegelIsolation E (E.domaenen) i
  ```
  with `E.domaenen : DomaenenTabelle` (finite tables as in `Tabellen.lean`, so the
  checker still decides coherence). An accepted unit may then issue questions about
  objects of a foreign domain exactly when its own table declares the channel, and
  `ni_erfuellbar` with acceptance becomes attainable again. Alternative: drop the
  `Akzeptiert` conjunct from the NI comparison and compare admitted runs only.
-/
module

public import Core.Annahme.Domaene
public import Core.Annahme.Hosted
public import Core.Beobachtung.Nichtinterferenz

@[expose] public section

namespace Gabbro.Core.Annahme

open Gabbro.Core.Maschine
open Gabbro.Core.Katalog
open Gabbro.Core.Beobachtung

/-- Machine fact: a question recorded in the `aussen` trace of a context implementation
    step carries the acting context's number. Only the `frage` protocol action records a
    question event; every other action (including the thread actions `starte`,
    `verbinde`, `beende` and `wechsle`) records the empty event list. -/
theorem frageStelltKontext [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (t : Nat) (c : Kontext) (s u s' : Zustand L Ort Wert Raum Lok Grund)
    (p : SchrittPlan L Ort Wert Bedingung) (spur : SchrittSpur Ort Wert)
    (q : FrageEreignis)
    (haus : FuehrtSchrittAus E.einrichtung t c s u p spur s')
    (hmem : Ereignis.frage q ∈ spur.aussen) :
    q.context = c.nummer := by
  obtain ⟨_, _, _, _, hF, _, _⟩ := haus
  generalize _hA : p.aktion = a at hF
  generalize _hE : spur.aussen = evs at hF hmem
  cases hF with
  | intern => exact (List.not_mem_nil hmem).elim
  | warte _ => exact (List.not_mem_nil hmem).elim
  | sperre _ _ => exact (List.not_mem_nil hmem).elim
  | frage qq =>
    have heq := List.mem_singleton.mp hmem
    cases heq
    rfl
  | verbrauche _ => exact (List.not_mem_nil hmem).elim
  | rueckkehr _ _ => exact (List.not_mem_nil hmem).elim
  | starte _ => exact (List.not_mem_nil hmem).elim
  | verbinde _ => exact (List.not_mem_nil hmem).elim
  | beende _ => exact (List.not_mem_nil hmem).elim
  | wechsle _ _ _ _ => exact (List.not_mem_nil hmem).elim

/-- Vacuity of the NI comparison with acceptance: an accepted unit has no recorded
    question at any context cut of any run. The hostile plan puts every context in
    domain `0` and every device object in domain `1` with no channels; the checker row
    (from acceptance) forces the recorded cut to respect it, while the recorded
    question is foreign under it. No well-formedness or coherence premise is needed:
    the row quantifies over every plan. -/
theorem akzeptierteFrage_unmoeglich [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (ρ : Lauf E) (t : Nat) (c : Kontext) (w : Wahl)
    (spur : SchrittSpur Ort Wert) (q : FrageEreignis)
    (hakk : Akzeptiert E)
    (hspur : ρ.zeit.spur t = some (.kontext c w, spur))
    (hmem : Ereignis.frage q ∈ spur.aussen) : False := by
  have tick := ρ.zeit.takt t
  rw [hspur] at tick
  generalize vorEq : ρ.zeit.zustand t = vor at tick
  generalize nachEq : ρ.zeit.zustand (t + 1) = nach at tick
  cases tick with
  | schritt label step =>
    cases label
    cases step with
    | schritt impl =>
      cases impl with
      | kontext _ _ regel aus =>
        obtain ⟨i, hkopf, hp⟩ := regel
        let feind : DomaenenPlan :=
          { domaenen := 2
            kontextDomaene := fun _ => 0
            objektDomaene := fun _ => 0
            geraetDomaene := fun _ => 1
            kanaele := [] }
        have hreihe := (akzeptiert_domaenen hakk) feind _ _ _ hkopf
        have hresp := hreihe t c _ _ _ _ _ spur hp aus
        have hkontext : q.context = c.nummer :=
          frageStelltKontext E t c _ _ _ _ _ q aus hmem
        have hnicht := hresp.2 q hmem c hkontext.symm
        have fremd : FremdeFrage feind c q.question := by
          intro h
          unfold DomaenenPlan.erlaubt at h
          rcases h with h | h
          · exact Nat.zero_ne_one h
          · exact List.not_mem_nil h
        exact hnicht fremd
  | wartet label _ _ => cases label

/-- The NI comparison bundle of `ni_erfuellbar` with the acceptance conjunct restored
    is unsatisfiable: any tuple meeting all premises refutes its own acceptance. Only
    the question recorded at the issue cut is used; the low-equivalence, the answers
    and the second run are carried unused. -/
theorem niVergleich_akzeptiert_unmoeglich
    (E : Hosted.Modell) (H₁ H₂ : Umgebung) (ρ₁ : Lauf E) (s₂ : AussenStart)
    (ρ₂ : Lauf E) (tq ta : Nat) (c : Kontext) (q : FrageEreignis)
    (a₁ a₂ : AntwortEreignis) (req resp₁ resp₂ : Hosted.Spur)
    (hakk : Akzeptiert E) (hH₁ : Hardware E.katalog H₁) (hH₂ : Hardware E.katalog H₂)
    (lauf₁ : Laeufe E H₁ ρ₁) (hU : GleicheNiedrigeUmgebung E H₁ H₂)
    (hZ : E.ZulStart H₂ s₂) (hN : NiedrigGleich E ρ₁.start s₂)
    (lauf₂ : Laeufe E H₂ ρ₂) (hS : ρ₂.start = s₂) (hP : GleichePolitik E ρ₁ ρ₂)
    (hs₁ : ρ₁.zeit.spur tq = some (.kontext c (), req))
    (hs₂ : ρ₂.zeit.spur tq = some (.kontext c (), req))
    (hr : req.aussen = [.frage q])
    (ho : oeffentlich (E.etiketten.frage q.question) = false)
    (hlt : tq < ta) (ht₁ : ρ₁.zeit.spur ta = some (.antwort a₁, resp₁))
    (ht₂ : ρ₂.zeit.spur ta = some (.antwort a₂, resp₂))
    (hr₁ : resp₁.aussen = [.antwort a₁]) (hr₂ : resp₂.aussen = [.antwort a₂])
    (hz₁ : a₁.zu q) (hz₂ : a₂.zu q)
    (ho₁ : a₁.reply.result.isOk = true) (ho₂ : a₂.reply.result.isOk = true)
    (hne : a₁.reply.result ≠ a₂.reply.result)
    (hlow : NiedrigAequiv E (NiedrigeBeob E ρ₁) (NiedrigeBeob E ρ₂)) : False := by
  have hmem : Ereignis.frage q ∈ req.aussen := by
    rw [hr]
    exact List.mem_cons_self
  exact akzeptierteFrage_unmoeglich E ρ₁ tq c () req q hakk hs₁ hmem

end Gabbro.Core.Annahme
