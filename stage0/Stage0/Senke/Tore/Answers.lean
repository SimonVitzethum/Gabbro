/- Joint Boolean and provider capability witnesses for actual foreign lowering. -/
module
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.AxiomElseProbes
public import Stage0.Senke.Ausdruck.Referenz.Proben
import Grammatik.Kern.Taktik.KernelRfl
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [RootNativeFloat.Hardware] {D : Deklaration}

end Gabbro.Stage0.Senke

namespace Gabbro.Stage0.Senke.ForeignAnswers
variable [RootNativeFloat.Hardware]
open Gabbro.Grammatik Runner.IR
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

abbrev result : Option Ty := some .bool
abbrev D := AxiomElseProbe.D result
abbrev entry : D.Fn := AxiomElseProbe.entry result
abbrev gate : D.Ax := AxiomElseProbe.gate result

def admission : RufPasst D (vertragVon D entry) (D.asignatur gate) [] where
  hw t := Fin.elim0 t
  hg g := Fin.elim0 g
  hk := ⟨[], List.Perm.refl _, List.Sublist.refl _⟩
  hh l := Fin.elim0 l

/-- A single declared reason needs no constructor dispatch: its live error arm returns 9.
    The separate statement probes retain reason-dispatch lowering coverage. -/
def reasonHandler {Γ : Ctx} : Endblock D (vertragVon D entry) false (.why 1 :: Γ) [] :=
  AxiomElseProbe.retN result 9 (by decide) (by decide)

def success : Endblock D (vertragVon D entry) false [.bool] [] :=
  .ite (.var .here) (AxiomElseProbe.retN result 17 (by decide) (by decide))
    (AxiomElseProbe.retN result 19 (by decide) (by decide))

def bindEnd (optional : Bool) : Endblock D (vertragVon D entry) false [] [] :=
  if optional then
    .bindAxiomOptElse result gate .nil rfl admission
      (fun t => Fin.elim0 t) (fun g => Fin.elim0 g) (by decide)
      (reasonHandler) success
  else
    .bindAxiomElse gate .nil rfl (by decide)
      (fun t => Fin.elim0 t) (fun g => Fin.elim0 g)
      (fun t => Fin.elim0 t) (fun g => Fin.elim0 g)
      (reasonHandler) success

def successBlock : Block D (vertragVon D entry) false [.bool] [] [] :=
  .cons (.ite (.var .here)
    (.cons (.ret (.val (.widen (by decide) (by decide) (.lit 17))) (.refl [])) .nil)
    (.cons (.ret (.val (.widen (by decide) (by decide) (.lit 19))) (.refl [])) .nil)) .nil

def bindBlock (optional : Bool) : Block D (vertragVon D entry) false [] [] [] :=
  if optional then
    .bindAxiomOptElse result gate .nil rfl admission
      (fun t => Fin.elim0 t) (fun g => Fin.elim0 g) (by decide)
      (reasonHandler) successBlock
  else
    .bindAxiomElse gate .nil rfl (by decide)
      (fun t => Fin.elim0 t) (fun g => Fin.elim0 g)
      (fun t => Fin.elim0 t) (fun g => Fin.elim0 g)
      (reasonHandler) successBlock

def body (optional nested : Bool) : Endblock D (vertragVon D entry) false [] [] :=
  if nested then .cons (.ite .tru (bindBlock optional) .nil)
    (AxiomElseProbe.retN result 99 (by decide) (by decide))
  else bindEnd optional

def program (optional nested : Bool) : Programm D where
  invariante _ := .tru
  requires _ := .tru
  ensures _ := .tru
  rumpf f := by
    obtain ⟨f, hf⟩ := f
    have zero : f = 0 := by change f < 1 at hf; omega
    subst f
    exact body optional nested

def image (optional nested : Bool) : Except String (List Runner.B) := do
  let emitted ← bild 1 (program optional nested)
    (layU (AxiomElseProbe.u result) (fun _ => some AxiomElseProbe.binding))
    [entry] Fin.val (fun _ => "main") entry .nil [] 1024 0
  pure emitted.bytes

def oracle (raw : Runner.W) : Orakel D where
  wirktL _ σ _ := ({ σ with spur := [] }, rohW AxiomElseProbe.binding 1 raw)
  regLiesL r := Fin.elim0 r
  regSchreib r := Fin.elim0 r
  sichtbarL _ _ := true

def observed (optional nested : Bool) (raw : Runner.W) : Int :=
  match execEnd (oracle raw) 1 (AxiomElseProbe.calls result)
      (body optional nested) (AxiomElseProbe.initial result) .nil with
  | .zurueck _ value => value.n
  | _ => -1

namespace Region
open Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

def unit : UProg := { ControlProbe.u with
  tabs := [{name := "Bytes", count := 4, cols := [("byte", (0, 255))]}]
  axs := [{name := "region", params := [], kinds := [],
           res := some (.ptr (.table 0 (false, true)))}] }
abbrev D := declOf unit
abbrev entry : D.Fn := ⟨0, by decide⟩
abbrev gate : D.Ax := ⟨0, by decide⟩

/-- The capability belongs to a real nominal table, and the continuation copies
    its canonical word through an ordinary local binding before returning. -/
def body : Endblock D (vertragVon D entry) false [] [] :=
  .bindAxiom gate .nil rfl (fun _ h => nomatch h) (fun g => Fin.elim0 g)
    (fun _ h => nomatch h) (fun g => Fin.elim0 g)
    (.bind (.var .here) (.ret (.val (.widen (by decide) (by decide) (.lit 17))) (.refl [])))

def program : Programm D where
  invariante _ := .tru
  requires _ := .tru
  ensures _ := .tru
  rumpf f := by
    obtain ⟨f, hf⟩ := f
    have zero : f = 0 := by change f < 1 at hf; omega
    subst f
    exact body

def image : Except String (List Runner.B) := do
  let emitted ← bild 1 program (layU unit (fun _ => some ⟨39, regsIn 0, [], none⟩))
    [entry] Fin.val (fun _ => "main") entry .nil [] 1024 0
  pure emitted.bytes

end Region

end Gabbro.Stage0.Senke.ForeignAnswers
