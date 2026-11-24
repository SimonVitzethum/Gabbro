/-
  File:      core/Core/Ideal/Eigenschaften.lean
  Subject:   `I.Bestimmt` AND `I.Fortschritt` OVER THE STATEMENT INTERFACE (PERFECT-MODEL §3.4, step M4), and
             the HARDWARE-DELAY RULE.
             * `IBestimmt`: an `I` step of a context is determined by the state, the context and the
               resolution of its choice points. Proved for the interface (`bestimmt_aus_regeln`) from the
               OBLIGATION `RegelBestimmt` each form discharges when it enters (M6).
             * `IFortschritt`: every context is finished, or has an `I` step, or is blocked with a reason.
               Proved for the interface (`fortschritt_aus_regeln`) from the OBLIGATION `RegelFortschritt`
               each form discharges, and the interface obligation that a context without a form at its
               head is finished.
             * The delay rule (`fortschritt_zur`): at time `t` a context whose core gets no opportunity in
               the exogenous schedule waits in `I` exactly as long; otherwise `IFortschritt` applies.
             NOT covered here (obligations of the forms and of M5/M7): no garbage values (provenance of every
             value), internal-deadlock freedom (`WaechterHalten`), the units' commutation proofs.
-/
module

public import Core.Maschine.Regel

@[expose] public section

namespace Gabbro.Core.Ideal

open Gabbro.Core.Maschine

variable {S Ev Wahl B ι : Type}

/-- **Obligation of a form: its `I` step is determined** by state, context and choice resolution. -/
def RegelBestimmt (r : Regel S Ev Wahl) : Prop :=
  ∀ c s w es es' s1 s2, r.ideal c s w es s1 → r.ideal c s w es' s2 → es = es' ∧ s1 = s2

/-- **`I.Bestimmt`**: deterministic up to the named choice points. -/
def IBestimmt (Sy : System S Ev Wahl B ι) : Prop :=
  ∀ c s w es es' s1 s2, Sy.ISchritt c s w es s1 → Sy.ISchritt c s w es' s2 → es = es' ∧ s1 = s2

/-- **`I.Bestimmt` for the interface**: from the obligation of every form. -/
theorem bestimmt_aus_regeln (Sy : System S Ev Wahl B ι) (h : ∀ i, RegelBestimmt (Sy.regel i)) :
    IBestimmt Sy := by
  intro c s w es es' s1 s2 ⟨i, hi, h1⟩ ⟨j, hj, h2⟩
  rw [hi] at hj
  cases hj
  exact h i c s w es es' s1 s2 h1 h2

/-- **Obligation of a form: progress at its head**: it has an `I` step or blocks with a reason. -/
def RegelFortschritt (Sy : System S Ev Wahl B ι) (i : ι) : Prop :=
  ∀ s c, Sy.kopf s c = some i →
    (∃ w es s', (Sy.regel i).ideal c s w es s') ∨ ∃ b, Sy.blockiert s c b

/-- **`I.Fortschritt`**: every context is finished, steps, or is blocked with a reason. -/
def IFortschritt (Sy : System S Ev Wahl B ι) : Prop :=
  ∀ s c, Sy.fertig s c ∨ (∃ w es s', Sy.ISchritt c s w es s') ∨ ∃ b, Sy.blockiert s c b

/-- **`I.Fortschritt` for the interface**: from the obligation of every form and the interface
    obligation that a context with no form at its head is finished. -/
theorem fortschritt_aus_regeln (Sy : System S Ev Wahl B ι)
    (hk : ∀ s c, Sy.kopf s c = none → Sy.fertig s c) (h : ∀ i, RegelFortschritt Sy i) :
    IFortschritt Sy := by
  intro s c
  cases hc : Sy.kopf s c with
  | none => exact Or.inl (hk s c hc)
  | some i =>
    rcases h i s c hc with ⟨w, es, s', hs⟩ | hb
    · exact Or.inr (Or.inl ⟨w, es, s', i, hc, hs⟩)
    · exact Or.inr (Or.inr hb)

/-- **A step at time `t`**: the context's core has an opportunity in the schedule `g`. -/
def ISchrittZur (Sy : System S Ev Wahl B ι) (g : Nat → Kern → Prop) (kern : S → Kontext → Kern)
    (t : Nat) (c : Kontext) (s : S) (w : Wahl) (es : List Ev) (s' : S) : Prop :=
  g t (kern s c) ∧ Sy.ISchritt c s w es s'

/-- **The hardware-delay rule**: at every time a context is finished, steps, is blocked with a
    reason, or waits because its core has no opportunity -- exactly as long as the hardware withholds
    it. -/
theorem fortschritt_zur (Sy : System S Ev Wahl B ι) (hF : IFortschritt Sy)
    (g : Nat → Kern → Prop) (kern : S → Kontext → Kern) (t : Nat) (s : S) (c : Kontext) :
    Sy.fertig s c ∨ (∃ w es s', ISchrittZur Sy g kern t c s w es s') ∨
      (∃ b, Sy.blockiert s c b) ∨ ((∃ w es s', Sy.ISchritt c s w es s') ∧ ¬ g t (kern s c)) := by
  rcases hF s c with hf | ⟨w, es, s', hs⟩ | hb
  · exact Or.inl hf
  · by_cases hg : g t (kern s c)
    · exact Or.inr (Or.inl ⟨w, es, s', hg, hs⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨⟨w, es, s', hs⟩, hg⟩))
  · exact Or.inr (Or.inr (Or.inl hb))

/-- Satisfiability of the interface obligations: a system of one form that always steps
    deterministically meets both, so `I.Bestimmt` and `I.Fortschritt` hold for it. -/
theorem schnittstelle_erfuellbar :
    let Sy : System Unit Unit Unit Unit Unit :=
      ⟨fun _ => ⟨fun _ _ _ _ _ => True, fun _ _ _ es _ => es = []⟩, fun _ _ => some (), fun _ _ => False,
        fun _ _ _ => False⟩
    IBestimmt Sy ∧ IFortschritt Sy :=
  ⟨bestimmt_aus_regeln _ fun _ _ _ _ _ _ _ _ h1 h2 => ⟨h1.trans h2.symm, rfl⟩,
    fortschritt_aus_regeln _ (fun _ _ h => (Option.some_ne_none () h).elim)
      fun _ _ _ _ => Or.inl ⟨(), [], (), rfl⟩⟩

end Gabbro.Core.Ideal
