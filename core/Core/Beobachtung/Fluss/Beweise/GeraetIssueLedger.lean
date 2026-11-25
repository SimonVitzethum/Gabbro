module

public import Core.Beobachtung.Fluss.Beweise.GeraetInvariante

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device
open Gabbro.Core.Ast.LowLevel (entryContext)

-- Single-run preservation is stated with the concrete device rule so that
-- `stelleFrage` instance and context are available without extra hypotheses.

theorem geraete_issue_ledger {k : Katalog} {binding : Binding k} {access : RegisterAccess}
    {required : GeraetePhase} {target : Option GeraetePhase} {c : Kontext}
    {s : State} {t : Nat}
    (owned : Befugt binding required access s c)
    (idle : (s.lokal c).pending = none) :
    let e := s.stelleFrage t c (binding.question access)
    let u := setFrame s c { s.lokal c with pending := some (binding.question access) }
    let v := u.frage e
    v.fragen = s.fragen ++ [e] ∧ v.verlauf = s.verlauf ++ [(e.cut, .frage e.question)] ∧
      v.antworten = s.antworten ∧ v.verbraucht = s.verbraucht ∧ v.buchung = s.buchung ∧
      v.epoche = s.epoche ∧ v.verworfen = s.verworfen ∧ v.geliefert = s.geliefert ∧
      v.kerne = s.kerne ∧ v.status = s.status ∧ e.questionInstance = s.fragen.length ∧
      e.context = c.nummer ∧ e.cut = t ∧ e.question = binding.question access := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Gabbro.Core.Beobachtung
