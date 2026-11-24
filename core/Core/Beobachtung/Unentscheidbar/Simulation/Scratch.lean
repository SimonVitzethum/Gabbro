module

public import Core.Beobachtung.Unentscheidbar.Modell

@[expose] public section

namespace Scratch

example (z : Int) : Equiv.intEquivNat.symm (Encodable.encode z) = z := by
  simpa [Encodable.encode, Encodable.decode] using (Encodable.encodek z)

example (z : Int) : (Encodable.decode (Encodable.encode z) : Option Int) = some z := by
  exact Encodable.encodek z

end Scratch
