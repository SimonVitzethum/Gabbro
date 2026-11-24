module

public import Core.Maschine.Zustand

@[expose] public section

namespace Gabbro.Core.Maschine

open Gabbro.Core.Katalog

variable {L Ort Wert Raum Lok Grund : Type}

/-- The raised interrupt is identified by its hardware cut and its position in that cut's offers.
    It remains pending across masks and cuts until the composition records its delivery. -/
def UnterbrechungAusstehend (s : Zustand L Ort Wert Raum Lok Grund) (run : HwLauf)
    (t kern : Nat) (id : Nat × Nat) (irq : Unterbrechung) : Prop :=
  id.1 ≤ t ∧ (run.angebot id.1).raised[id.2]? = some (kern, irq) ∧ id ∉ s.geliefert

/-- Enter a normal handler or an NMI handler. The same mask translation supplies the pinned
    catalogue row, including the suppression of normal interrupts while an NMI is active. -/
inductive NimmtUnterbrechung (z : KernZustand Raum) (k : Kern) (instanceId : Nat) :
    Unterbrechung → Kontext → Bool → Prop where
  | handler {vector priority} (maske : z.NimmtAn vector)
      (row : unterbrechungen ⟨z.maske vector || z.nmiAktiv, z.untergrenze, z.nmiAktiv, false⟩
        (.maskierbar vector priority) = .handler) :
      NimmtUnterbrechung z k instanceId (.maskierbar vector priority) (.handler k vector instanceId) false
  | nmi (maske : z.NimmtNmiAn)
      (row : unterbrechungen ⟨false, 0, z.nmiAktiv, false⟩ .nmi = .handler) :
      NimmtUnterbrechung z k instanceId .nmi (.nmi k instanceId) true

theorem NimmtUnterbrechung.handler_bei {z : KernZustand Raum} {k i v p}
    (can : z.NimmtAn v) (priority : z.untergrenze ≤ p) :
    NimmtUnterbrechung z k i (.maskierbar v p) (.handler k v i) false :=
  .handler can (by simp only [unterbrechungen, can.1, can.2, Bool.false_or, Nat.not_lt.mpr priority,
    decide_false, Bool.false_eq_true, ite_false])

theorem NimmtUnterbrechung.nmi_bei {z : KernZustand Raum} {k i}
    (can : z.NimmtNmiAn) : NimmtUnterbrechung z k i .nmi (.nmi k i) true :=
  .nmi can (by
    change z.nmiAktiv = false at can
    simp only [unterbrechungen, can, Bool.false_eq_true, ite_false])

/-- Delivery starts a fresh handler on this physical core and records the consumed offer. -/
def Zustandseintritt (s : Zustand L Ort Wert Raum Lok Grund) (k : Kern) (id : Nat × Nat)
    (c : Kontext) (nmi : Bool) : Zustand L Ort Wert Raum Lok Grund :=
  { s with
    kerne := Function.update s.kerne k ((s.kerne k).unterbrechen c nmi)
    status := Function.update s.status c .laeuft
    geliefert := s.geliefert ++ [id] }

/-- A return belongs to the handler currently running on its own core, with a frame to restore. -/
inductive KehrtZurueck (s : Zustand L Ort Wert Raum Lok Grund) :
    Kontext → Kern → Prop where
  | handler {k v i} (aktiv : (s.kerne k).laeuft = some (.handler k v i))
      (frame : (s.kerne k).stapel ≠ []) : KehrtZurueck s (.handler k v i) k
  | nmi {k i} (aktiv : (s.kerne k).laeuft = some (.nmi k i))
      (frame : (s.kerne k).stapel ≠ []) : KehrtZurueck s (.nmi k i) k

def Zustandsrueckkehr (s : Zustand L Ort Wert Raum Lok Grund) (k : Kern) :
    Zustand L Ort Wert Raum Lok Grund :=
  { s with kerne := Function.update s.kerne k (s.kerne k).zurueck }

theorem rueckkehr_setzt_fort (s : Zustand L Ort Wert Raum Lok Grund) (k : Kern)
    (id : Nat × Nat) (c : Kontext) (nmi : Bool) :
    ((Zustandsrueckkehr (Zustandseintritt s k id c nmi) k).kerne k).laeuft = (s.kerne k).laeuft ∧
      ((Zustandsrueckkehr (Zustandseintritt s k id c nmi) k).kerne k).stapel = (s.kerne k).stapel := by
  simp only [Zustandseintritt, Zustandsrueckkehr, Function.update_self]
  exact ⟨rfl, rfl⟩

theorem unterbrechung_erfuellbar (s : Zustand L Ort Wert Raum Lok Grund) (k : Kern) (id : Nat × Nat) :
    let z := { s with
      kerne := Function.update s.kerne k
        { s.kerne k with maske := fun _ => false, untergrenze := 0, nmiAktiv := false } }
    let i := Nat.pair id.1 id.2
    NimmtUnterbrechung (z.kerne k) k i (.maskierbar 0 0) (.handler k 0 i) false ∧
      NimmtUnterbrechung (z.kerne k) k i .nmi (.nmi k i) true ∧
      KehrtZurueck (Zustandseintritt z k id (.nmi k i) true) (.nmi k i) k := by
  dsimp only
  refine ⟨NimmtUnterbrechung.handler_bei ?_ ?_, NimmtUnterbrechung.nmi_bei ?_, .nmi ?_ ?_⟩
  · simp only [Function.update_self, KernZustand.NimmtAn, and_self]
  · simp only [Function.update_self, Nat.le_refl]
  · simp only [KernZustand.NimmtNmiAn, Function.update_self]
  · simp only [Zustandseintritt, Function.update_self, KernZustand.unterbrechen]
  · simp only [Zustandseintritt, Function.update_self, KernZustand.unterbrechen, List.cons_ne_nil]
    exact fun h => nomatch h

end Gabbro.Core.Maschine
