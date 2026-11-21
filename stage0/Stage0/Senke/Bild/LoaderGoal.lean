module

public import Stage0.Senke.Bild.ImageGoal
public import Runner.Beweis.Lader
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Stage0.Senke Runner Runner.IR Runner.Beweis

variable {src : String} {K : Nat} {options : Profil.Options}

/-- The frame word consumed by the real runner loader is taken from the
    production payload and names the certified image's initial frame. -/
theorem Emitted.loader_frame [Kern] (output : Emitted src K options) {m : Mem}
    (loaded : BytesAt m Runner.Prog.IMG output.bytes) :
    m.rd64 (BitVec.ofNat 64 Runner.Prog.IMG) = some (BitVec.ofNat 64 output.image.fp0) := by
  obtain ⟨_, _, _, _, _, _, header, _, _⟩ :=
    bild_initialized_loaded_u output.initialValid output.emission output.funktionen_voll loaded
  obtain ⟨_, _, _, placed, _⟩ := bild_lage output.emission output.funktionen_voll
    (fun base bound => layU_in output.compiled.unit output.tor base bound)
    (fun base => layU_dis output.compiled.unit output.tor base)
    (fun base => by simp only [layU]; omega)
    (fun base => layU_sync output.compiled.unit output.tor base)
  have fits := placed.hfit
  exact rd64_leN header (by omega)

/-- After mapping the actual CLI payload, the runner's real header request
    can read it under TSO and resumes at the image's certified entry.
    The reading thread has no pending writes to forward. -/
theorem irBild_loader_dispatch [Kern] {output : Emitted src K options} {bytes : List Runner.B}
    (built : emit src K options = .ok output) (payload : irBild src K options = .ok bytes)
    {s : (TSO L0).St} {thread : Nat} (empty : s.1.buf thread = [])
    (loaded : BytesAt s.1.m Runner.Prog.IMG bytes) :
    ∃ resume : Ans → Res T,
      t4 = .ask (.rd 8 (BitVec.ofNat 64 Runner.Prog.IMG)) resume ∧
      (TSO L0).ans s thread (.rd 8 (BitVec.ofNat 64 Runner.Prog.IMG))
        (some (BitVec.ofNat 64 output.image.fp0, 0)) s ∧
      resume (some (BitVec.ofNat 64 output.image.fp0, 0)) =
        .next ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 output.image.fp0⟩ := by
  have frame := output.loader_frame ((irBild_eq_output built payload).symm ▸ loaded)
  refine ⟨fun answer => opt answer fun pair => .next ⟨BitVec.ofNat 64 Runner.Prog.IMG + 16, pair.1⟩,
    rfl, ⟨rfl, 0, ?_⟩, rfl⟩
  simpa only [TSt.view, empty, List.foldl_nil, rdN, frame, Option.map_some]

/-- Every TSO answer to the loaded header read returns the same entry
    frame. The extra answer word has no effect on the loader. -/
theorem irBild_loader_dispatch_all [Kern] {output : Emitted src K options} {bytes : List Runner.B}
    (built : emit src K options = .ok output) (payload : irBild src K options = .ok bytes)
    {s s' : (TSO L0).St} {thread : Nat} {answer : Ans} (empty : s.1.buf thread = [])
    (loaded : BytesAt s.1.m Runner.Prog.IMG bytes)
    (answered : (TSO L0).ans s thread (.rd 8 (BitVec.ofNat 64 Runner.Prog.IMG)) answer s') :
    s' = s ∧
      ∀ resume, t4 = .ask (.rd 8 (BitVec.ofNat 64 Runner.Prog.IMG)) resume →
        resume answer = .next ⟨BitVec.ofNat 64 codeBase, BitVec.ofNat 64 output.image.fp0⟩ := by
  have frame := output.loader_frame ((irBild_eq_output built payload).symm ▸ loaded)
  obtain ⟨same, extra, actual⟩ := answered
  refine ⟨same, ?_⟩
  intro resume read
  have exactAnswer : answer = some (BitVec.ofNat 64 output.image.fp0, extra) := by
    simpa only [TSt.view, empty, List.foldl_nil, rdN, frame, Option.map_some] using actual
  rw [exactAnswer]
  have equalResume := (Res.ask.inj read).2
  rw [← equalResume]
  rfl

end Gabbro.Stage0
