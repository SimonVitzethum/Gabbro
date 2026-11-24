module

public import Core.Beobachtung.Unentscheidbar.Simulation.KodierBefehlBeweis

namespace Scratch

example : Encodable (Befehl) := inferInstance
example : Encodable (List Befehl) := inferInstance

end Scratch
