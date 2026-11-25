module

public import Core.Ast.Semantik.Kernregister
public import Core.Ast.Semantik.Elaborierung
public import Core.Ast.Semantik.Runtime.Sicherheit
public import Core.Ast.Program.KernelPremises

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Waechter Sicherheit
open Lean (Name)

/-- The pinned program-instruction safety statement follows from the generic command duty:
    a command with a program constructor is frame-only, and a fragment without declared
    invariants passes the empty predicate table. It needs no registry entry and no premise
    that the constructor is registered. -/
public theorem programKernSicherheit (constructor : Name) :
    ProgramKernSicherheitsAussage constructor := by
  intro p platform b form invariant
  exact Befehl.sicherheitsPflichten p platform [] (tabLeer _ invariant) (fun _ _ => rfl) b
    (Befehl.privat_von_programConstructor form)

end Gabbro.Core.Ast.Semantik
