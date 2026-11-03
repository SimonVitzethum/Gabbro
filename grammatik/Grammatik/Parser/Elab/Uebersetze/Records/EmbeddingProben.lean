module

import Grammatik.Parser.Elab.Uebersetze.Records.Embedding

namespace Gabbro.Grammatik.Parser.Uebersetze

private def declarations : List SItemTief :=
  [.typeT [] "Pos" [] [] (some (.raw "{ x: i32, y: i32 }")),
   .typeT [] "Body" [] [] (some (.raw "{ ..Pos, mass: f64 }")),
   .typeT [] "Collision" [] [] (some (.raw "{ ..Pos, x: i32 }")),
   .typeT [] "Number" [] [] (some (.atom "i32")),
   .typeT [] "Bad" [] [] (some (.raw "{ ..Number }")),
   .typeT [] "Cycle" [] [] (some (.raw "{ ..Cycle }"))]

theorem flat_expansion_zeuge :
    (expandRecord 7 declarations [] "Body").map (fun fields => fields.map (·.fname)) =
      .ok ["x", "y", "mass"] := rfl

theorem embedding_collision_zeuge :
    expandRecord 7 declarations [] "Collision" = .error "record embedding: duplicate field" := rfl

theorem embedding_nonrecord_zeuge :
    expandRecord 7 declarations [] "Bad" = .error "record embedding: non-record target" := rfl

theorem embedding_recursive_zeuge :
    expandRecord 7 declarations [] "Cycle" = .error "record embedding: recursive embedding" := rfl

end Gabbro.Grammatik.Parser.Uebersetze
