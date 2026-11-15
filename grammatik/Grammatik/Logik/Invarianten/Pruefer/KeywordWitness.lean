module

public import Grammatik.Logik.Invarianten.Pruefer.Program

public section

namespace Gabbro.Grammatik.Invarianten.Pruefer.KeywordWitness

/-- Importing the checker must leave ordinary Lean identifiers available. -/
theorem alias_is_identifier_zeuge (alias : Nat) : alias = alias := rfl

end Gabbro.Grammatik.Invarianten.Pruefer.KeywordWitness
