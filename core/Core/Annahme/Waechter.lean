/-
  File:      core/Core/Annahme/Waechter.lean
  Subject:   The generated guards of acceptance (PERFECT-MODEL §3.2, §3.4, step M5).

  `WaechterHalten E` says every generated guard holds on every `I` run and no reachable `I`
  cut contains an internal deadlock or a closed waiting set. The guards come from the pinned
  table of `I`'s partial operations (`PartielleOperation` with `waechterBedarf`); a unit's uses
  of them are supplied per program by the M6 constructors. Deadlock freedom is generic over the
  program's forms through `System.blockiert`: a closed set waits only on locks held inside the
  set and joins of members — outside questions and hardware delays never count as internal.
-/
module

public import Core.Maschine.Start

@[expose] public section

namespace Gabbro.Core.Annahme

open Gabbro.Core.Maschine

variable {L Ort Wert Raum Lok Grund Bedingung Wahl ι : Type}

/-- **The pinned table of `I`'s partial operations** (§3.2): every partial operation without an
    `else` path that the checker must generate a guard for. -/
inductive PartielleOperation where
  | division
  | modulo
  | index
  | shift
  | konvertierung
  | entpacken
  deriving DecidableEq, Repr

/-- The operands one use of a partial operation carries. -/
def Operanden : PartielleOperation → Type
  | .division => Nat × Nat
  | .modulo => Nat × Nat
  | .index => Nat × Nat
  | .shift => Nat × Nat
  | .konvertierung => Nat × Nat
  | .entpacken => Nat

/-- **The pinned guard of each partial operation** over its operands: what must hold wherever
    the operation is used. Division and modulo need a nonzero divisor; indexing and shifting
    stay inside their bounds; conversion fits its width; unwrapping needs the success tag. -/
def waechterBedarf : (op : PartielleOperation) → Operanden op → Prop
  | .division, (_, b) => b ≠ 0
  | .modulo, (_, b) => b ≠ 0
  | .index, (i, n) => i < n
  | .shift, (s, w) => s < w
  | .konvertierung, (v, w) => v < 2 ^ w
  | .entpacken, tag => tag = Nat.succ Nat.zero

/-- **A unit's partial-operation uses**: at each `I` cut, the partial operations the unit
    performs with their operand values. The M6 constructors supply it per program. -/
class GuardVerwendung [DecidableEq L]
    (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι) : Type where
  bedarf : (ρ : I.Lauf E) → I.Schnitt E ρ → (op : PartielleOperation) → Operanden op → Prop

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

/-- **`WaechterHalten E`: every generated guard holds on every `I` run, and no reachable `I`
    cut — maximal cuts included — contains an internal deadlock or a closed waiting set.**
    Nobody writes the guards; the checker proves them. This is what makes "correct logic
    produces an error" impossible. -/
def WaechterHalten [DecidableEq L] (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl ι)
    [G : GuardVerwendung E] : Prop :=
  (∀ (ρ : I.Lauf E), I.Laeufe E ρ → ∀ (t : I.Schnitt E ρ) (op : PartielleOperation)
    (args : Operanden op), G.bedarf ρ t op args → waechterBedarf op args) ∧
  ∀ (ρ : I.Lauf E), I.Laeufe E ρ → ∀ t : I.Schnitt E ρ,
    ¬ ∃ C, GeschlossenWartend E (ρ.zeit.zustand t.val) C

end Gabbro.Core.Annahme
