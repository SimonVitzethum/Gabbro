module

public import Core.Beobachtung.Fluss.Beweise.GeraetIssueLedger
public import Core.Beobachtung.Fluss.Beweise.GeraetInvariante

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Gabbro.Core.Ast.LowLevel.Device
open Gabbro.Core.Ast.LowLevel (entryContext)

/-- Acting issue context must be the entry context while the initial booking
    holds: the start booking grants the free device right only to the entry. -/
theorem geraete_issue_kontext {k : Katalog} {binding : Binding k} {access : RegisterAccess}
    {required : GeraetePhase} {target : Option GeraetePhase} {c : Kontext} {s : State}
    (buchung : s.buchung.geraet = (startBuchung binding.object binding.handle).geraet)
    (befugt : Befugt binding required access s c) :
    c = entryContext := by
  have hobj : s.buchung.geraet binding.object = some (entryContext, .frei) := by
    simp only [buchung, startBuchung, if_true]
  have hbefugt : s.buchung.geraet binding.object = some (c, .frei) := befugt.1
  have heq : (c, Aussen.Vollmacht.frei) = (entryContext, Aussen.Vollmacht.frei) :=
    Option.some.inj (hbefugt.symm.trans hobj)
  exact (Prod.mk.inj heq).1

end Gabbro.Core.Beobachtung
