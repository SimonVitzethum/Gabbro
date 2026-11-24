module

public import Core.Beobachtung.Fluss.Fragment

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine

/-- The public offer projection records the IRQ attempt, including its identity. -/
theorem gleiche_interruptwahl {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    [DecidableEq L] {ρ₁ ρ₂ : Lauf E} (politik : GleichePolitik E ρ₁ ρ₂) (t : Nat) :
    (ρ₁.hw.angebot t).interruptAuswahl = (ρ₂.hw.angebot t).interruptAuswahl := by
  have signale : (ρ₁.hw.angebot t).interrupts = (ρ₂.hw.angebot t).interrupts :=
    congrArg (fun p => (p.1 t).2.2.1) politik
  simp only [Gelegenheit.interruptAuswahl, signale]

/-- Two actual deliveries of the same public attempt emit the same event and
    record the same identity, independently of the two pre-states. -/
theorem interruptspur_gleich {e : Einrichtung L Ort Wert Raum Lok Grund Bedingung}
    {hw₁ hw₂ t id₁ id₂ v₁ v₂ spur₁ spur₂ u₁ u₂}
    (angebot : (hw₁.angebot t).interruptAuswahl = (hw₂.angebot t).interruptAuswahl)
    (links : UnterbrechungsSchritt e hw₁ t id₁ v₁ spur₁ u₁)
    (rechts : UnterbrechungsSchritt e hw₂ t id₂ v₂ spur₂ u₂) :
    id₁ = id₂ ∧ spur₁.aussen = spur₂.aussen := by
  obtain ⟨_, _, _, _, _, pending₁, _, _, beob₁, _, _⟩ := links
  obtain ⟨_, _, _, _, _, pending₂, _, _, beob₂, _, _⟩ := rechts
  have gleich := Option.some.inj (pending₁.2.2.2.2.symm.trans (angebot.trans pending₂.2.2.2.2))
  obtain ⟨rfl, rest⟩ := Prod.mk.inj gleich
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
  exact ⟨rfl, beob₁.trans beob₂.symm⟩

/-- At a reserved cut, an enabled delivery is taken with the selected identity.
    The public event is independent of the weak-memory resolution used for the step. -/
theorem interrupt_am_schnitt {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}
    [DecidableEq L] {h : Umgebung} {ρ : Lauf E} {t id v spur u}
    (lauf : Laeufe E h ρ) (vor : ρ.zeit.zustand t = some v)
    (normal : (ρ.hw.angebot t).crash = false)
    (bereit : UnterbrechungsSchritt E.einrichtung ρ.hw t id v spur u) :
    ∃ beob, ρ.zeit.spur t = some (.interrupt id, beob) ∧ beob.aussen = spur.aussen := by
  have details := bereit
  obtain ⟨_, _, _, _, _, pending, _⟩ := details
  obtain ⟨_, keinKern, keineAntwort⟩ := (lauf.2.1.2 t).interrupt_reserviert pending.2.2.2.2
  have tick := ρ.zeit.takt t
  rw [vor] at tick
  generalize ρ.zeit.zustand (t + 1) = danach at tick
  cases tick with
  | wartet _ _ pause => exact (pause _ _ (.schritt (.interrupt normal bereit))).elim
  | schritt label schritt =>
    cases schritt with
    | schritt actual =>
      cases actual with
      | kontext _ dispatch _ _ =>
        obtain ⟨k, angebot, _⟩ := dispatch
        exact (Option.some_ne_none k (angebot.symm.trans keinKern)).elim
      | antwort _ h =>
        have angebot := h.1.2.1.1
        change (ρ.hw.angebot _).delivery _ = true at angebot
        rw [h.1.1, keineAntwort] at angebot
        cases angebot
      | interrupt _ h =>
        obtain ⟨rfl, spurGleich⟩ := interruptspur_gleich rfl h bereit
        exact ⟨_, label, spurGleich⟩
      | absturz h => exact (Bool.false_ne_true (normal.symm.trans h.1.2)).elim

/-- A legal history can raise an IRQ and select that same pending IRQ at a later cut. -/
theorem interrupt_angebot_erfuellbar (k : Katalog) (h : Umgebung) (irq : Unterbrechung)
    (kern : 0 < h.kernzahl) (support : h.ziel.unterstuetzt irq) :
    ∃ hw : HwLauf, hw.konform k h ∧
      (hw.angebot 0).interrupts[0]? = some (.erhoben 0 irq) ∧
      (hw.angebot 1).interruptAuswahl = some (0, (0, 0), irq) := by
  let signale : Nat → List InterruptSignal
    | 0 => [.erhoben 0 irq]
    | 1 => [.zustellen 0 (0, 0) irq]
    | _ + 2 => []
  let hw : HwLauf :=
    ⟨fun t => ⟨none, fun c => decide (c = 0), signale t, fun _ => false, false, false, t⟩, h.politik⟩
  refine ⟨hw, ⟨rfl, fun t => ⟨?_, ?_, ?_, ?_, ?_⟩⟩, rfl, rfl⟩
  · intro _ impossible
    cases impossible
  · intro c offered
    change decide (c = 0) = true at offered
    exact (decide_eq_true_eq.mp offered).symm ▸ kern
  · cases t with
    | zero =>
      intro signal mem
      cases List.mem_singleton.mp mem
      exact ⟨kern, support⟩
    | succ t =>
      cases t with
      | zero =>
        intro signal mem
        cases List.mem_singleton.mp mem
        exact ⟨kern, support, rfl, rfl, ⟨Nat.zero_le _, rfl⟩, rfl, fun _ => rfl⟩
      | succ _ =>
        intro signal mem
        exact (List.not_mem_nil mem).elim
  · intro _ impossible
    exact (Bool.false_ne_true impossible).elim
  · intro impossible
    exact (impossible.elim Bool.false_ne_true Bool.false_ne_true).elim

def InterruptNIAussage : Prop :=
  ProtokollwahlNI fun
    | .interrupt _ => True
    | _ => False

end Gabbro.Core.Beobachtung
