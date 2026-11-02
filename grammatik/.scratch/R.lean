import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuhe.Teil2
open Lean in
#eval show CoreM _ from do return (← findModuleOf? `Gabbro.Grammatik.Deklaration.mitRuhe)
