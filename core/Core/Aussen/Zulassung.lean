/-
  File:      core/Core/Aussen/Zulassung.lean
  Subject:   THE CATALOGUE ADMISSION RULE (PERFECT-MODEL §4, step M10): a catalogue interface
             is admitted only if every query goes through a handle the program owns, every
             precondition is checked in the same question with a failure channel, and name
             resolution happens only in operations that return a handle. The concrete M2 rows
             satisfy the rule (`zulassung_m2`, proved structurally).
-/
module

public import Core.Katalog.Erfuellbar

@[expose] public section

namespace Gabbro.Core.Aussen

open Gabbro.Core.Katalog

/-- **The catalogue admission rule** for interfaces: every query goes through an owned
    handle (the same-event channel binding), every precondition is checked in the same
    question with a failure channel, and only handle-returning operations resolve names. -/
structure ZulassungsRegel (p : Plattform) : Prop where
  griffbindung : ∀ (s : AussenSicht) (q : Frage) (a : Antwort),
    atomar p s q = .antwort a → a.result.isOk = true →
    (s.gueltig q.endpoint ⟨q.handle, q.operation.required⟩) = true
  fehlerkanal : ∀ (s : AussenSicht) (q : Frage), p.operationAngeboten q = true →
    q.zugriffe.all (s.gueltig q.endpoint) = false →
    ∃ a, atomar p s q = .antwort a ∧ a.result.isOk = false
  namen_nur_griff : ∀ (s : AussenSicht) (q : Frage) (h : Handle),
    s.erfolg p q = .ok (.handle h) → ∃ name, q.operation = .resolve name

/-- A successful answer establishes the same-event ownership of the primary handle. -/
theorem griffbindung_gilt (s : AussenSicht) (p : Plattform) (q : Frage) (a : Antwort)
    (antwort : atomar p s q = .antwort a) (erfolg : a.result.isOk = true) :
    (s.gueltig q.endpoint ⟨q.handle, q.operation.required⟩) = true := by
  cases hv : a.result with
  | ok v => exact (atomar_aktuell antwort hv).2.2 _ List.mem_cons_self
  | error e =>
    rw [hv] at erfolg
    simp only [Except.isOk] at erfolg
    exact Bool.false_ne_true erfolg

/-- A failed same-event precondition answers through the failure channel. -/
theorem fehlerkanal_gilt (s : AussenSicht) (p : Plattform) (q : Frage)
    (offered : p.operationAngeboten q = true)
    (denied : q.zugriffe.all (s.gueltig q.endpoint) = false) :
    ∃ a, atomar p s q = .antwort a ∧ a.result.isOk = false :=
  ⟨_, atomar_ungueltig offered denied, rfl⟩

/-- Only `resolve` answers with a handle. -/
theorem namen_nur_griff_gilt (s : AussenSicht) (p : Plattform) (q : Frage) (h : Handle)
    (erf : s.erfolg p q = .ok (.handle h)) :
    ∃ name, q.operation = .resolve name := by
  cases q with
  | mk endpoint handle other operation =>
    cases operation with
    | resolve name => exact ⟨name, rfl⟩
    | read => simp only [AussenSicht.erfolg] at erf; cases erf
    | write bytes => simp only [AussenSicht.erfolg] at erf; cases erf
    | firmware service bytes => simp only [AussenSicht.erfolg] at erf; cases erf
    | exchange bytes => simp only [AussenSicht.erfolg] at erf; cases erf
    | registerRead offset => simp only [AussenSicht.erfolg] at erf; cases erf
    | registerWrite offset value => simp only [AussenSicht.erfolg] at erf; cases erf
    | waitRegister offset expected => simp only [AussenSicht.erfolg] at erf; cases erf

/-- **The concrete M2 rows satisfy the admission rule**, proved structurally over the
    row definitions: same-event ownership from the atomic answer, the failure channel
    from the explicit refusal, handle answers only from `resolve`. -/
theorem zulassung_m2 (p : Plattform) : ZulassungsRegel p where
  griffbindung := griffbindung_gilt
  fehlerkanal := fehlerkanal_gilt
  namen_nur_griff := namen_nur_griff_gilt

/-- Satisfiability: the admission rule holds on every platform. -/
theorem zulassung_erfuellbar : ∃ p, ZulassungsRegel p :=
  ⟨.x86_64, zulassung_m2 _⟩

end Gabbro.Core.Aussen
