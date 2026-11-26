module

public import Core.Beobachtung.Fluss.Beweise.GeraetIssueKontext
public import Core.Beobachtung.Fluss.Beweise.GeraetIssueLedger

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device
open Gabbro.Core.Ast.LowLevel (entryContext)

/-- Fresh issue instance equals the prior ledger length. -/
theorem geraete_issue_frisch {s : State} {t : Nat} {c : Kontext} {q : Frage}
    (e : FrageEreignis) (neu : e = s.stelleFrage t c q) :
    e.questionInstance = s.fragen.length := by
  simp only [neu, Zustand.stelleFrage]

end Gabbro.Core.Beobachtung
