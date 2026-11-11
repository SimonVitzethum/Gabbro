module
public import Stage0.IRBild
import all Stage0.IRBild
import all Stage0.Senke.Images.Bild

@[expose] public section
namespace Gabbro.Stage0.ImagePhases
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
set_option maxRecDepth 2000
set_option maxHeartbeats 100000

-- Complete geometry follows from the accepted builder, without reducing a
-- byte payload or recomputing source/compile/get graphs for each projection.
theorem geometry {src : String} {K : Nat} {options : Profil.Options}
    (image : Emitted src K options) :
    0 < image.image.code.length ∧ Runner.Prog.IMG + image.bytes.length < 2 ^ 64 := by
  have positions : ∀ g : (declOf image.compiled.unit).Fn,
      (List.finRange image.compiled.unit.fns.length)[g.val]? = some g := by
    intro g
    simp only [List.finRange, List.getElem?_ofFn, g.isLt, ↓reduceDIte]
    congr 1
  obtain ⟨cs, body, sp, layout, code, _, _, _⟩ :=
    Senke.bild_lage image.emission positions
      (fun base bound => Senke.layU_in image.compiled.unit image.tor base bound)
      (fun base => Senke.layU_dis image.compiled.unit image.tor base)
      (fun base => by simp only [Senke.layU]; omega)
      (fun base => Senke.layU_sync image.compiled.unit image.tor base)
  have codeLength : image.image.code.length =
      Senke.headLen (image.starts.map (·.1)).length + body.length := by
    rw [code, List.length_append, layout.head]
    rfl
  have length := Senke.bild_initialized_length_u image.initialValid image.emission positions
  change image.bytes.length = 16 + 16 * image.image.code.length + 8 * image.image.K at length
  have frame := layout.hfp
  have fits := layout.hfit
  change image.image.fp0 = Senke.codeBase +
    16 * (Senke.headLen (image.starts.map (·.1)).length + body.length) at frame
  simp only [Senke.codeBase] at frame
  have headPositive : 0 < Senke.headLen (image.starts.map (·.1)).length := by
    simp only [Senke.headLen, Senke.startLen]
    omega
  constructor
  · omega
  · have power : (2 : Nat) ^ 31 < 2 ^ 64 := by decide
    omega

end Gabbro.Stage0.ImagePhases
