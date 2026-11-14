/- A real image containing one scoped lock, for both admitted source profiles.
   No parser or large source fixture is evaluated by this module. -/
module
public import Stage0.Senke.Sperre.Bindung.Zeuge
@[expose] public section

namespace Gabbro.Stage0.Senke.WaitBindingWitness
open Gabbro.Grammatik Runner.IR

abbrev entry : WartenProbe.D.Fn := ⟨0, by decide⟩
abbrev lock : WartenProbe.D.Lock := ⟨0, by decide⟩

def body : Endblock WartenProbe.D (vertragVon WartenProbe.D entry) false [] [] :=
  .cons (.locks lock (fun _ h => (List.not_mem_nil h).elim) .nil)
    (.ret .empty (.refl []))

def program : Programm WartenProbe.D where
  invariante _ := .tru
  requires _ := .tru
  ensures _ := .tru
  rumpf f := by
    have same : f = entry := Fin.ext (by have := f.isLt; change f.val < 1 at this; omega)
    subst f
    exact body

/-- The production image builder receives the selected profile binding. -/
def image (environment : String) : Except String (Bild WartenProbe.D) :=
  bild 1 program
    (layU (lockWait := (layout environment).lockWait) WartenProbe.unit (fun _ => none))
    [entry] Fin.val (fun _ => "main") entry .nil [] 1024 0

set_option maxRecDepth 100000 in
/-- Both actual images build, contain the nonempty scoped-lock function, and
    retain the selected binding after relocation. The complete Linux image has
    exactly four more syscall instructions: one wait and three scoped release
    paths. Startup syscalls occur equally in both images. -/
theorem image_binding_zeuge :
    (image "freestanding").isOk = true ∧ (image "linux").isOk = true ∧
    ((image "freestanding").toOption.map fun b =>
      b.Y.lockWait == .spin && decide (86 < b.code.length) &&
      ((nimmT b.Y (b.Y.lk lock) 4 ++ gibT b.Y (b.Y.lk lock) 4).all fun i => i.o != 23)) = some true ∧
    ((image "linux").toOption.map fun b =>
      b.Y.lockWait == .futex && decide (86 < b.code.length) &&
      decide ((nimmT b.Y (b.Y.lk lock) 4)[26]?.map (·.o) = some 23) &&
      decide ((gibT b.Y (b.Y.lk lock) 4)[15]?.map (·.o) = some 23)) = some true ∧
    ((image "linux").toOption.map fun b => (b.code.filter fun i => i.o == 23).length) =
      ((image "freestanding").toOption.map fun b => (b.code.filter fun i => i.o == 23).length + 4) := by
  decide

end Gabbro.Stage0.Senke.WaitBindingWitness
