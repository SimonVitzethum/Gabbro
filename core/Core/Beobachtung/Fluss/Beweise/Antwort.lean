module

public import Core.Beobachtung.Fluss.Fragment

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Fragment Rahmen)

/-- The current source fragment has no outside question instruction. Its runs
    cannot receive an answer, even if the hardware offers delivery. -/
def AntwortNIAussage : Prop :=
  ∀ (p : Fragment) (plattform : Plattform) (h : Umgebung) (ρ : Lauf (p.einheit plattform)),
    Laeufe (p.einheit plattform) h ρ → ∀ t a spur,
      ρ.zeit.spur t ≠ some (.antwort a, spur)

abbrev AntwortZustand := Ast.Semantik.Zustand
abbrev AntwortPlan := Ast.Semantik.Plan
abbrev AntwortSpur := SchrittWahl PUnit × SchrittSpur Ast.Semantik.Zelle Int

/-- The action of every context step of a canonical fragment is internal:
    a `Befehl` never issues a question. -/
theorem antwort_kontext_intern {p : Fragment} (plattform : Plattform)
    {c : Kontext} {s u : AntwortZustand} {w : PUnit} {plan : AntwortPlan}
    (regel : (p.einheit plattform).system.ImplSchritt c s w [plan] u) :
    plan.aktion = .intern := by
  obtain ⟨i, _, impl⟩ := regel
  exact i.impl_aktion_intern impl

/-- A form action other than a question leaves the pending-question ledger unchanged. -/
theorem antwort_fuehrt_aus_fragen_leer {p : Fragment} (plattform : Plattform)
    {t : Nat} {c : Kontext} {s u v : AntwortZustand}
    {aktion : Aktion Nat PUnit} {sperren : List (Speicher.Etikett Ast.Semantik.Zelle Int)}
    {aussen : List Ereignis}
    (aktionStep : FuehrtAus (p.einheit plattform).einrichtung t c s u aktion sperren aussen v)
    (uLeer : u.fragen = []) (keinFrage : ∀ q, aktion ≠ .frage q) : v.fragen = [] := by
  cases aktionStep with
  | frage q => exact (keinFrage q rfl).elim
  | intern | warte _ | sperre _ _ | verbrauche _ | rueckkehr _ _ =>
      change u.fragen = []
      exact uLeer

/-- A machine step from a canonical fragment never creates a pending question. -/
theorem antwort_schritt_fragen {p : Fragment} (plattform : Plattform)
    {hw : HwLauf} {t : Nat} {s s' : AntwortZustand} {spur : AntwortSpur}
    (step : ImplSchritt (p.einheit plattform).einrichtung (p.einheit plattform).system
                        (p.einheit plattform).katalog hw t s spur s')
    (leer : s.fragen = []) : s'.fragen = [] := by
  cases step with
  | kontext _ _ regel aus =>
      obtain ⟨i, _, impl⟩ := regel
      have intern := i.impl_aktion_intern impl
      obtain ⟨frame, _, _, _, aktion, _, s'Eq⟩ := aus
      have vLeer := antwort_fuehrt_aus_fragen_leer plattform aktion
        (frame.fragen.trans leer) (fun q h => by rw [intern] at h; cases h)
      rw [s'Eq]
      exact vLeer
  | antwort _ arrives =>
      obtain ⟨_, _, _, stateEq⟩ := arrives
      rw [stateEq]
      change s.fragen = []
      exact leer
  | interrupt _ enters =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, stateEq⟩ := enters
      rw [stateEq]
      change s.fragen = []
      exact leer
  | absturz crash =>
      obtain ⟨_, _, _, _, stateEq⟩ := crash
      rw [stateEq]
      change s.fragen = []
      exact leer

/-- By induction over the cuts, a canonical-fragment run has no pending question at any cut
    whose implementation state is loaded. -/
theorem antwort_fragen_leer (p : Fragment) (plattform : Plattform)
    {h : Umgebung} {ρ : Lauf (p.einheit plattform)}
    (lauf : Laeufe (p.einheit plattform) h ρ) :
    ∀ t, ρ.zeit.zustand t = none ∨ ∃ z, ρ.zeit.zustand t = some z ∧ z.fragen = [] := by
  intro t
  induction t with
  | zero =>
      rw [lauf.2.2.2]
      have ladenEq : (p.einheit plattform).laden =
          Gabbro.Core.Ast.Semantik.laden p.eingang p.eintritte p.speicher plattform := rfl
      rw [ladenEq]
      unfold Gabbro.Core.Ast.Semantik.laden
      split
      · right
        refine ⟨_, rfl, ?_⟩
        rfl
      · left
        rfl
  | succ t ih =>
      cases ih with
      | inl noneq =>
          have tick := ρ.zeit.takt t
          rw [noneq] at tick
          cases tick with
          | schritt _ step =>
              cases step
          | wartet _ eq _ =>
              exact Or.inl eq
      | inr gefunden =>
          obtain ⟨z, atZ, fragenLeer⟩ := gefunden
          have tick := ρ.zeit.takt t
          rw [atZ] at tick
          cases tick with
          | schritt _ step =>
              cases after : ρ.zeit.zustand (t + 1) with
              | none =>
                  rw [after] at step
                  cases step
              | some next =>
                  right
                  refine ⟨next, rfl, ?_⟩
                  rw [after] at step
                  cases step with
                  | schritt impl =>
                      exact antwort_schritt_fragen plattform impl fragenLeer
          | wartet _ eq _ =>
              right
              exact ⟨z, eq, fragenLeer⟩

theorem antwort_fragen_leer_an (p : Fragment) (plattform : Plattform)
    {h : Umgebung} {ρ : Lauf (p.einheit plattform)}
    (lauf : Laeufe (p.einheit plattform) h ρ)
    (t : Nat) {z : AntwortZustand} (atZ : ρ.zeit.zustand t = some z) :
    z.fragen = [] := by
  have alle := antwort_fragen_leer p plattform lauf t
  cases alle with
  | inl noneq =>
      cases (atZ.symm.trans noneq)
  | inr gefunden =>
      obtain ⟨z', eq, leer⟩ := gefunden
      have zz : z = z' := Option.some.inj (atZ.symm.trans eq)
      cases zz
      exact leer

/-- A canonical fragment never records an answer: an answer requires an already pending
    question, and the induction over the cuts shows none is ever issued. -/
theorem antwortNI : AntwortNIAussage := by
  intro p plattform h ρ lauf t a spur gleich
  have tick := ρ.zeit.takt t
  rw [gleich] at tick
  cases tick with
  | wartet label _ _ =>
      cases label
  | schritt label step =>
      rename_i event
      have evEq := Option.some.inj label
      rw [← evEq] at step
      cases before : ρ.zeit.zustand t with
      | none =>
          rw [before] at step
          cases step
      | some z =>
          cases after : ρ.zeit.zustand (t + 1) with
          | none =>
              rw [before] at step
              rw [after] at step
              cases step
          | some next =>
              rw [before] at step
              rw [after] at step
              cases step with
              | schritt impl =>
                  cases impl with
                  | antwort _ arrives =>
                      obtain ⟨angebot, _, _, _⟩ := arrives
                      have zLeer := antwort_fragen_leer_an p plattform lauf t before
                      obtain ⟨q, qmem, _⟩ := angebot.2.2.2.1
                      rw [zLeer] at qmem
                      cases qmem

end Gabbro.Core.Beobachtung
