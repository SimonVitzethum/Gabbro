import Stage0.Profil
namespace Gabbro.Stage0.Profil
open Gabbro.Grammatik.Parser
example : (parseOptions ["--target", "metal", "--arch", "x86_64"] {}).toOption.map (·.target) =
    some (some "metal") := by decide
example : (parseOptions ["--target"] {}).isOk = false := by decide
example : (prepareItems ⟨"aarch64", none⟩ []).isOk = false := by decide
example : (prepareItems {} [.goalT "linux" none]).isOk = true := by decide
example : (prepareItems {} [.modT "m" [.gateT (.varT "gate")]]).isOk = false := by decide
example : (prepareItems {} [.profT false []]).isOk = false := by decide
#print axioms prepareItems_preserves
#print axioms prepareItems_arch
end Gabbro.Stage0.Profil
