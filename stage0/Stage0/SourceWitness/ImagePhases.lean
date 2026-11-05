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

/-- A real compiler refusal is the same emitter refusal, with its exact diagnostic. -/
theorem emit_compile_error {src : String} {K : Nat} {options : Profil.Options} {error : String}
    (failed : compile src options = .error error) : emit src K options = .error error := by
  unfold emit
  rw [failed]
  rfl

/-- Replay the existing emitter for an AX-free unit. The supplied Emitted fields
    certify initial validity, the complete main environment and actual bild;
    compilation, target/binding selection and ordered starts remain mandatory.
    This equation neither supplies an image nor assumes emit's final outcome. -/
theorem emit_eq {src : String} {K : Nat} {options : Profil.Options}
    (result : Emitted src K options)
    (compiled : compile src options = .ok result.compiled)
    (target : validateTargetFor options.arch options.target
      (uMembers (pre108 result.compiled.source.items)) = .ok ())
    (gates : List Tor)
    (bindings : toreVonFor options.arch options.target
      (uMembers (pre108 result.compiled.source.items)) = .ok gates)
    (foreigns : result.compiled.unit.axs = [])
    (gateMap : (fun a => (gates.find? (·.name == (uaxAt result.compiled.unit a).name)).map
      (fun gate => (⟨gate.nummer, gate.regs, gate.fehler, gate.resultArea⟩ : Senke.TorB))) = result.tor)
    (starts : StartArgument.plan result.compiled.unit
      (uMembers (pre108 result.compiled.source.prepared.elaborierbar)) result.compiled.main =
        .ok result.startPlan) :
    emit src K options = .ok result := by
  unfold emit
  rw [compiled]
  dsimp only [bind, Except.bind]
  rw [target, bindings]
  dsimp only [bind, Except.bind]
  simp only [foreigns, List.forIn_nil]
  dsimp only [bind, Except.bind, pure, Except.pure]
  erw [gateMap, starts]
  dsimp only [bind, Except.bind]
  split
  · split
    · rename_i missing
      cases missing.symm.trans result.pointers
    · rename_i args selected
      have same : args = result.args := Option.some.inj (selected.symm.trans result.pointers)
      subst args
      split
      · rename_i error rejected
        cases rejected.symm.trans result.emission
      · rename_i image selected
        have same : image = result.image := Except.ok.inj (selected.symm.trans result.emission)
        subst image
        cases result
        rfl
  · rename_i rejected
    exact False.elim (rejected result.initialValid)

/-- Whole canonical constructor equality from actual phase results. The AX-free
    certificate discharges the original foreign-result-area loop, not a bypass.
    Consumers can project this same constructor's exact compiled/image/layout
    fields without choosing a fresh image after an existential success. -/
theorem emit_from_phases {src : String} {K : Nat} {options : Profil.Options}
    (compiled : Compiled src options) (compilation : compile src options = .ok compiled)
    (target : validateTargetFor options.arch options.target
      (uMembers (pre108 compiled.source.items)) = .ok ())
    (gates : List Tor)
    (bindings : toreVonFor options.arch options.target
      (uMembers (pre108 compiled.source.items)) = .ok gates)
    (foreigns : compiled.unit.axs = [])
    (tor : (declOf compiled.unit).Ax → Option Senke.TorB)
    (gateMap : (fun a => (gates.find? (·.name == (uaxAt compiled.unit a).name)).map
      (fun gate => (⟨gate.nummer, gate.regs, gate.fehler, gate.resultArea⟩ : Senke.TorB))) = tor)
    (plan : StartArgument.Plan compiled.unit
      (uMembers (pre108 compiled.source.prepared.elaborierbar)) compiled.main)
    (starts : StartArgument.plan compiled.unit
      (uMembers (pre108 compiled.source.prepared.elaborierbar)) compiled.main = .ok plan)
    (valid : GabbroV.sp0OkB compiled.unit = true)
    (args : Env (declOf compiled.unit) ((declOf compiled.unit).params compiled.main))
    (pointers : Senke.mainEnv ((declOf compiled.unit).params compiled.main) = some args)
    (image : Senke.Bild (declOf compiled.unit))
    (emission : Senke.bild irDurchlaeufe compiled.program (Senke.layU compiled.unit tor)
      (List.finRange compiled.unit.fns.length) Fin.val
      (fun g => (compiled.unit.fns[g.val]?.map (·.name)).getD "?") compiled.main args
      (plan.starts (Senke.initialWorld compiled.unit valid)) K
      (Senke.bodenAusrichtung compiled.unit) = .ok image) :
    emit src K options = .ok ({
      compiled := compiled
      tor := tor
      startPlan := plan
      initialValid := valid
      args := args
      pointers := pointers
      image := image
      emission := emission } : Emitted src K options) :=
  emit_eq _ compilation target gates bindings foreigns gateMap starts

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
