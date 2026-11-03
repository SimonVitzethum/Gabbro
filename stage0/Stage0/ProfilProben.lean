module
public import Stage0.Profil
@[expose] public section

namespace Gabbro.Stage0.Profil
open Gabbro.Grammatik.Parser
example : (parseOptions ["--target", "metal", "--arch", "x86_64"] {}).toOption.map (·.target) =
    some (some "metal") := by decide
example : (parseOptions ["--target"] {}).isOk = false := by decide
example : (prepareItems { arch := "aarch64", target := none } []).isOk = false := by decide
example : (prepareItems {} [.goalT "linux" none]).isOk = true := by decide
example : (prepareItems {} [.modT "m" [.gateT (.varT "gate")]]).isOk = true := by decide
example : (prepareItems {} [.profT false []]).isOk = true := by decide
/-- An uncovered requirement block is refused at the binding gate. -/
example : (prepareItems {} [.profT true [.mode "arch" "x86_64"]]).isOk = false := by decide
/-- A requirement block covered by the admitted profile passes the binding gate. -/
example : (prepareItems {} [.profT false [.mode "arch" "x86_64"],
    .profT true [.mode "arch" "x86_64"]]).isOk = true := by decide
#print axioms prepareItems_preserves
#print axioms prepareItems_arch
end Gabbro.Stage0.Profil
