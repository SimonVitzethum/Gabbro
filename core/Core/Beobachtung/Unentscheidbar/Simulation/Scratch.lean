module

public import Core.Beobachtung.Unentscheidbar.Modell

namespace Scratch

example (xs : List Nat) :
    (do let fs ← some xs; match fs with | [a] => some a | _ => none) =
      (match xs with | [a] => some a | _ => none) := by
  simp only [Option.bind_some]

end Scratch
