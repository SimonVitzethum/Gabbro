/-
  File:      core/Core/Annahme/Waechter.lean
  Subject:   The generated guards of acceptance (PERFECT-MODEL §3.2, §3.4, step M5).

  `WaechterHalten E` says every generated guard holds on every `I` run, no reachable `I`
  cut contains an internal deadlock or a closed waiting set, and every lock held under a
  declared hold bound stays checker-eligible until hand-off. The guards come from the pinned
  table of `I`'s partial operations (`PartielleOperation` with `waechterBedarf`); the unit's
  uses are DATA DETERMINED BY THE UNIT: `WaechterHalten` uses the canonical value
  `kanonischeVerwendung E`, never a supplied instance — there is no free choice of tables.
  Elaboration computes the uses from the reference AST. Deadlock
  freedom is generic over the program's forms through `System.blockiert`: a closed set waits
  only on locks held inside the set and joins of members — outside questions and hardware
  delays are specified outside non-answers, never internal deadlocks.
-/
module

public import Core.Maschine.Start
import Init.Omega

@[expose] public section

namespace Gabbro.Core.Annahme

open Gabbro.Core.Maschine

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type}
/-- The pinned guard for each partial operation. -/
def waechterBedarf : (op : PartielleOperation) → Operanden op → Prop
  | .division, (_, b) => b ≠ 0
  | .modulo, (_, b) => b ≠ 0
  | .index, (i, n) => i < n
  | .shift, (s, w) => s < w
  | .konvertierung, (v, w) => v < 2 ^ w
  | .entpacken, tag => tag = Nat.succ Nat.zero
  | .ganzzahlBereich, (abstand, anzahl) => 0 ≤ abstand ∧ abstand < (anzahl : Int)
  | .teilfolge, (first, last, bytes) => 0 ≤ first ∧ first ≤ last ∧ last ≤ (bytes : Int)

/-- The pinned narrowing row is exactly membership in the declared range. -/
theorem ganzzahlBereich_iff (wert lo hi : Int) :
    waechterBedarf .ganzzahlBereich (ganzzahlBereichOperanden wert lo hi) ↔
      lo ≤ wert ∧ wert ≤ hi := by
  change (0 ≤ wert - lo ∧ wert - lo < ((hi + 1 - lo).toNat : Int)) ↔ _
  omega


/-- **A unit's partial-operation uses**: at each `I` cut, the partial operations the unit
    performs with their operand values. The M6 constructors supply per-program uses in this
    shape when the syntax enters. -/
class GuardVerwendung [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) : Type where
  bedarf : (ρ : I.Lauf E) → I.Schnitt E ρ → (op : PartielleOperation) → Operanden op → Prop

/-- The canonical guard uses are the elaborated table evaluated at the ideal cut. -/
def kanonischeVerwendung [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) :
    GuardVerwendung E :=
  ⟨fun ρ t => E.quelltabellen.guard (ρ.zeit.zustand t.val)⟩

/-- **An internal block reason**: a lock, an `await` (its enabler is unknown at this
    genericity, so conservatively internal), or a join. An outstanding outside question and a
    hardware delay are specified outside non-answers, never internal deadlocks. -/
def InternBlockiert {L Bedingung : Type} (b : Blockade L Bedingung) : Prop :=
  match b with
  | .sperre _ => True
  | .warten _ => True
  | .join _ => True
  | .frage _ => False
  | .verzoegert _ => False

/-- **A closed waiting set in a state** (§3.2, §3.4): a nonempty set of contexts where every
    member is blocked internally, every lock it waits on is held inside the set, and every
    join target lies inside the set. A lone `await` no context can enable is the singleton
    case. -/
def GeschlossenWartend (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (s : Zustand L Ort Wert Raum Lok Grund) (C : Kontext → Prop) : Prop :=
  (∃ c, C c) ∧ ∀ c, C c → ∃ b, E.system.blockiert s c b ∧ InternBlockiert b ∧
    (∀ l, b = Blockade.sperre l → ∃ c', C c' ∧ (s.sperren l).besitzer = some c') ∧
    (∀ k, b = Blockade.join k → C k)

/-- **A lock holder with a declared hold bound stays checker-eligible until hand-off**: the
    holder is live, it is dispatched on some core, and its own rule offers the release step
    for the held lock (with the invariant guard the protocol step would require). This is the
    holder half of the M8 release obligation: eligibility is what the checker carries, so no
    scheduler assumption enters — hardware fairness supplies only the core opportunities.
    Locks without a declared hold bound impose nothing. -/
def SperrHalterBereit [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    (s : Zustand L Ort Wert Raum Lok Grund) (l : L) (h : Kontext) : Prop :=
  E.schranken.halten l ≠ none →
    s.status h = Status.laeuft ∧
    (∃ k, (s.kerne k).laeuft = some h) ∧
    ∃ (w : Wahl) (plan : SchrittPlan L Ort Wert Bedingung)
      (u : Zustand L Ort Wert Raum Lok Grund),
      E.system.ISchritt h s w [plan] u ∧ plan.aktion = .sperre l .geben ∧
      ∀ next : SperrZustand, (s.sperren l).Gibt h next →
        ((s.sperren l).Wechsel next → E.einrichtung.invariant u l)

/-- **The holder row of `WaechterHalten`**: on every `I` run, at every cut, every context that
    holds a lock under a declared hold bound is eligible (`SperrHalterBereit`). Read
    temporally: a holder stays live, dispatched and release-offering until it hands the lock
    off — after the hand-off the premise no longer holds. A crash needs no clause: it wipes
    every lock, so no holder remains. -/
def SperrHalterHalten [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) : Prop :=
  ∀ (ρ : I.Lauf E), I.Laeufe E ρ → ∀ t : I.Schnitt E ρ,
    ∀ (l : L) (h : Kontext), (ρ.zeit.zustand t.val).sperren l |>.besitzer = some h →
      SperrHalterBereit E (ρ.zeit.zustand t.val) l h

/-- **`WaechterHalten E`: every generated guard holds on every `I` run, no reachable `I`
    cut — maximal cuts included — contains an internal deadlock or a closed waiting set, and
    every lock held under a declared hold bound stays eligible until hand-off
    (`SperrHalterHalten`).**
    Nobody writes the guards; the checker proves them. This is what makes "correct logic
    produces an error" impossible. Over the canonical uses determined by the unit, with no
    instance arguments. -/
def WaechterHalten [DecidableEq L] (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) :
    Prop :=
  (∀ (ρ : I.Lauf E), I.Laeufe E ρ → ∀ (t : I.Schnitt E ρ) (op : PartielleOperation)
    (args : Operanden op), (kanonischeVerwendung E).bedarf ρ t op args → waechterBedarf op args) ∧
  (∀ (ρ : I.Lauf E), I.Laeufe E ρ → ∀ t : I.Schnitt E ρ,
    ¬ ∃ C, GeschlossenWartend E (ρ.zeit.zustand t.val) C) ∧
  SperrHalterHalten E

end Gabbro.Core.Annahme
