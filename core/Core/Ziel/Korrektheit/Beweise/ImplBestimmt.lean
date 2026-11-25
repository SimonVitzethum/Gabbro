/-
  File:      core/Core/Ziel/Korrektheit/Beweise/ImplBestimmt.lean
  Subject:   THE PROOF OF `impl_bestimmt`, the pinned determinacy statement of the implementation machine
             (`Core/Ziel/Korrektheit/Maschine.lean`, `ImplBestimmtAussage`).

  Feeding lemmas (all proved in `Core/Maschine`, none local to one program):
  * `FuehrtSchrittAus.bestimmt` — the context case, from `FuehrtAus.bestimmt`,
    `sperr_bestimmt`, `rueckkehr_kern` and `Speicherfolge.bestimmt`;
  * `AntwortSchritt.bestimmt`, `UnterbrechungsSchritt.bestimmt` — the two outside cases,
    likewise from `Speicherfolge.bestimmt`;
  * `AbsturzSchritt.genau` — the crash case: the trace and the restart state are fixed;
  * the rule premise of the statement (the implementation twin of `Ideal.bestimmt_aus_regeln`)
    fixes form plan and form successor at the head of the context.

  Proof sketch: split the two steps by their shared `SchrittWahl`. The first component of the
  recorded pair is the choice itself, so both steps fall in the same protocol case (context,
  answer, interrupt, crash). In the context case, the form at the head is the same `i` for both
  steps; the rule premise gives one plan and one form successor; the context protocol lemma then
  gives one trace and one machine state. In each outside case the corresponding protocol lemma
  applies directly; the crash case uses `AbsturzSchritt.genau` on both steps. `SpeicherWahlGleich`
  is the stated resolution of the memory order, consumed by the protocol lemmas. No statement is
  changed, and no witness or per-program fact is used.
-/
module

public import Core.Ziel.Korrektheit.Maschine

@[expose] public section

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core
open Gabbro.Core.Maschine

/-- The implementation machine is determinate up to its declared choice points (see the file header). -/
theorem impl_bestimmt : ImplBestimmtAussage := by
  intro L Ort Wert Raum Lok Grund Bedingung Wahl ι inst e Sy regeln
  intro k hw t s w es es' s' s'' step step' wahl
  cases step with
  | kontext _ _ regel aus =>
      cases step' with
      | kontext _ _ regel' aus' =>
          obtain ⟨i, hi, impl⟩ := regel
          obtain ⟨j, hj, impl'⟩ := regel'
          rw [hi] at hj
          cases hj
          have gleich := regeln i _ _ _ _ _ _ _ impl impl'
          cases (List.cons.inj gleich.1).1
          cases gleich.2
          exact aus.bestimmt aus' wahl
  | antwort _ h =>
      cases step' with
      | antwort _ h' => exact h.bestimmt h' wahl
  | interrupt _ h =>
      cases step' with
      | interrupt _ h' => exact h.bestimmt h' wahl
  | absturz h =>
      cases step' with
      | absturz h' =>
          have genau := h.genau
          have genau' := h'.genau
          exact ⟨genau.1.trans genau'.1.symm, genau.2.trans genau'.2.symm⟩

end Gabbro.Core.Ziel.Korrektheit
