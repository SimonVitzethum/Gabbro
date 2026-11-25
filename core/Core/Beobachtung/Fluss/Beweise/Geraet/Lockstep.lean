module

public import Core.Beobachtung.Fluss.Beweise.GeraetKopplung
public import Core.Beobachtung.Fluss.Beweise.GeraetInvariante
public import Core.Beobachtung.Nichtinterferenz
public import Core.Ast.LowLevel.DeviceUnit

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device
open Gabbro.Core.Ast

variable {k : Katalog} {scope : Scope} {locals : Umgebung scope}
variable {d : Denotation k scope}

/- Design note (geraet-ni lockstep): the five `…ErhaltAussage` units below carry
   the strengthened coupling `GeraeteKopplungAussage` across one left tick each,
   distinguished by the left step kind. Together with the start
   (`geraete_start_kopplungAussage`) they give `GeraeteKopplungAlleAussage` by
   induction on `t`, casing the left tick exactly as in `geraete_schnitt_schranke`.
   The pinned `GeraeteProtokollNIAussage` and `GeraeteNIAussage` then follow:
   each duty rebuilds `G` up to `t` from the comparison (`Alle`), applies the
   matching `Erhalt` unit once, and projects `Kopplung` via
   `geraeteKopplung_kopplung`. The coupling premise of each duty is then
   redundant; it is kept only to match the pinned shapes.

   Why the coupling alone does not suffice (measured): `QuellzustandGleich`
   covers the local frames (hence `pending` via `geraete_kopplung_pending`) but
   neither the outside ledgers `fragen`/`verlauf`/`antworten`/`verbraucht` nor the
   booking. An arrival needs a recorded but unmatched question, which only the
   ledgers decide; without them an arrival-vs-consume interleaving cannot be
   ruled out and the prefix-length equality breaks. The three
   `…InvariantAussage` units extend the single-run invariant to the remaining
   step kinds so that the exclusion lemmas (`geraete_issue_schliesst_ankunft_aus`,
   `geraete_consume_schliesst_ankunft_aus`) apply on both runs. -/

/-- Preservation through a left context tick (issue or consume): same pending
    slot on the right (`geraete_kopplung_pending`), transported authority
    (`geraete_befugt_transport`) and opportunity (same core offer, `kerne` and
    `status` from `Kopplung`), then the same elaborated step via
    `geraete_kontext_regel`. Post-states: `QuellzustandGleich` and equal plan
    and output views by `geraeteSchrittNI`; ledgers by `geraete_issue_tick` or
    `geraete_consume_tick` (same fresh question `stelleFrage t c`, same
    counter step); booking unchanged both sides; observations by
    `geraete_issue_beob_tick` (one low event each) or
    `geraete_consume_beob_tick` (silent each), so the prefix relation extends
    and lengths stay equal. -/
def GeraeteKontextErhaltAussage : Prop :=
  ∀ (h₁ h₂ : Umgebung) (ρ₁ ρ₂ : Lauf (d.unit locals))
    (vergleich : Vergleich (d.unit locals) h₁ h₂ ρ₁ ρ₂)
    (predictor : Praediktor) (t : Nat) (c : Kontext) (w : PUnit)
    (spur : SchrittSpur Nat UInt8),
    GeraeteKopplungAussage (d.unit locals) ρ₁ ρ₂ predictor t t →
    ρ₁.zeit.spur t = some ((.kontext c w), spur) →
    GeraeteKopplungAussage (d.unit locals) ρ₁ ρ₂ predictor (t + 1) (t + 1)

/-- Preservation through a left answer arrival: the offer transports to the
    right (`geraete_angeboten_transport` with the ledger and epoch equalities);
    arrival is impossible on an issue- or consume-enabled state
    (`geraete_issue_schliesst_ankunft_aus`,
    `geraete_consume_schliesst_ankunft_aus`), so the right does not take a form
    step instead. Post-states append the same answer to `antworten` and
    `verlauf`; `QuellzustandGleich` is untouched (ledgers are outside it);
    `naechsteAntwort` agreement follows from `geraete_antwort_gleich`.
    Observations: two low events each (answer plus register address,
    `geraete_antwort_beob`), so the prefix relation extends by two on both
    sides. -/
def GeraeteAntwortErhaltAussage : Prop :=
  ∀ (h₁ h₂ : Umgebung) (ρ₁ ρ₂ : Lauf (d.unit locals))
    (vergleich : Vergleich (d.unit locals) h₁ h₂ ρ₁ ρ₂)
    (predictor : Praediktor) (t : Nat) (a : AntwortEreignis)
    (spur : SchrittSpur Nat UInt8),
    GeraeteKopplungAussage (d.unit locals) ρ₁ ρ₂ predictor t t →
    ρ₁.zeit.spur t = some ((.antwort a), spur) →
    GeraeteKopplungAussage (d.unit locals) ρ₁ ρ₂ predictor (t + 1) (t + 1)

/-- Preservation through a left interrupt entry: same interrupt offer on both
    sides (`geraete_angebot_gleich`), transported entry
    (`NimmtUnterbrechung` via `kerne` equality, `status` via `status`
    equality). Post-states: `Zustandseintritt` changes only `kerne`,
    `status` and `geliefert` (same `id` both sides); ledgers, booking and
    epoch stay. No new end is recorded (entry targets `.laeuft`, never
    `.beendet`); the outside part is one interrupt event each. -/
def GeraeteInterruptErhaltAussage : Prop :=
  ∀ (h₁ h₂ : Umgebung) (ρ₁ ρ₂ : Lauf (d.unit locals))
    (vergleich : Vergleich (d.unit locals) h₁ h₂ ρ₁ ρ₂)
    (predictor : Praediktor) (t : Nat) (id : Nat × Nat)
    (spur : SchrittSpur Nat UInt8),
    GeraeteKopplungAussage (d.unit locals) ρ₁ ρ₂ predictor t t →
    ρ₁.zeit.spur t = some ((.interrupt id), spur) →
    GeraeteKopplungAussage (d.unit locals) ρ₁ ρ₂ predictor (t + 1) (t + 1)

/-- Preservation through a left crash: same crash offer
    (`geraete_angebot_gleich`), both sides reset via `wiederanlauf` with the
    same entry data. Post-states: ledgers `fragen`/`antworten`/`verlauf`/
    `verbraucht` carried over equally, `verworfen` recomputed equally from
    equal inputs, `epoche = t + 1` both sides, booking `.leer` both sides
    (`Zustand.start` default), `QuellzustandGleich` from equal entry frames.
    New ends stay equal via `EndeSicht` agreement; every recorded question
    predates the new epoch (`geraete_schnitt_schranke`). -/
def GeraeteAbsturzErhaltAussage : Prop :=
  ∀ (h₁ h₂ : Umgebung) (ρ₁ ρ₂ : Lauf (d.unit locals))
    (vergleich : Vergleich (d.unit locals) h₁ h₂ ρ₁ ρ₂)
    (predictor : Praediktor) (t : Nat) (spur : SchrittSpur Nat UInt8),
    GeraeteKopplungAussage (d.unit locals) ρ₁ ρ₂ predictor t t →
    ρ₁.zeit.spur t = some ((.absturz), spur) →
    GeraeteKopplungAussage (d.unit locals) ρ₁ ρ₂ predictor (t + 1) (t + 1)

/-- Preservation through a left pause: transport every right step kind back to
    a left step and contradict `KeinSchritt` (as in `pauseNI`), using the
    symmetric offer and policy equalities for arrivals. Both states and both
    low prefixes stay, so the coupling is kept. -/
def GeraetePauseErhaltAussage : Prop :=
  ∀ (h₁ h₂ : Umgebung) (ρ₁ ρ₂ : Lauf (d.unit locals))
    (vergleich : Vergleich (d.unit locals) h₁ h₂ ρ₁ ρ₂)
    (predictor : Praediktor) (t : Nat),
    GeraeteKopplungAussage (d.unit locals) ρ₁ ρ₂ predictor t t →
    ρ₁.zeit.spur t = none →
    GeraeteKopplungAussage (d.unit locals) ρ₁ ρ₂ predictor (t + 1) (t + 1)

/-- The strengthened coupling holds at every cut of every compared device run:
    `geraete_start_kopplungAussage` at zero, then the matching `Erhalt` unit
    per left tick kind. This is the induction the three duty proofs share. -/
def GeraeteKopplungAlleAussage : Prop :=
  ∀ (h₁ h₂ : Umgebung) (ρ₁ ρ₂ : Lauf (d.unit locals))
    (vergleich : Vergleich (d.unit locals) h₁ h₂ ρ₁ ρ₂)
    (predictor : Praediktor) (t : Nat),
    GeraeteKopplungAussage (d.unit locals) ρ₁ ρ₂ predictor t t

/-- The single-run invariant survives an answer arrival: in the balanced
    pre-states (idle or consume-ready) no arrival is offered
    (`geraete_issue_schliesst_ankunft_aus`,
    `geraete_consume_schliesst_ankunft_aus`), so only the busy-unmatched shape
    (`fragen = antworten + 1` with one unmatched question) admits one; the
    offered answer is fresh and matches exactly that question, moving the
    ledger to the consume-ready shape. -/
def GeraeteAnkunftInvariantAussage : Prop :=
  ∀ (binding : Binding k) (s : State) (kat : Katalog) (run : HwLauf) (t : Nat)
    (a : AntwortEreignis),
    GeraeteInvariantAussage binding s →
    s.AntwortAngeboten kat run t a →
    GeraeteInvariantAussage binding (s.antwort a)

/-- The single-run invariant survives an interrupt entry: `Zustandseintritt`
    changes only `kerne`, `status` and `geliefert`, none of which the
    invariant constrains. -/
def GeraeteInterruptInvariantAussage : Prop :=
  ∀ (binding : Binding k) (s : State) (kern : Kern) (id : Nat × Nat)
    (c : Kontext) (nmi : Bool) (graph : SpeicherGraph Nat UInt8),
    GeraeteInvariantAussage binding s →
    GeraeteInvariantAussage binding
      { Zustandseintritt s kern id c nmi with graph := graph }

/-- The single-run invariant survives a crash: the post-state takes the
    post-crash branch (booking `.leer` from `Zustand.start`, no pending frame
    from the recovery entry data, every recorded question predating the new
    epoch by the cut bound). -/
def GeraeteAbsturzInvariantAussage : Prop :=
  ∀ (binding : Binding k) (s : State) (w : Wiederanlauf Nat UInt8 PUnit Frame PUnit)
    (t : Nat) (p : PersistZustand),
    GeraeteInvariantAussage binding s →
    (∀ q ∈ s.fragen, q.cut < t) →
    GeraeteInvariantAussage binding (s.wiederanlauf w t p)

end Gabbro.Core.Beobachtung
