module
public import Grammatik.Parser.Elab.Konst.Scopes.Correctness
public import Stage0.Frontend.Functions
@[expose] public section


namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

theorem normalizeAliases_sound_zeuge :
    Normalization [.typeT [] "Small" [] [] (some (.atom "u8")),
      .typeT [] "Count" [] [] (some (.atom "Small")),
      .constT "N" (.atom "Count") (.one (.bin "+" (.lit 40) (.lit 2)))]
    (normalizeAliases [.typeT [] "Small" [] [] (some (.atom "u8")),
      .typeT [] "Count" [] [] (some (.atom "Small")),
      .constT "N" (.atom "Count") (.one (.bin "+" (.lit 40) (.lit 2)))]) :=
  normalizeAliases_sound _

end Gabbro.Stage0.Frontend
