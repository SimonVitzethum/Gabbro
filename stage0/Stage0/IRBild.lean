/-
  File:      stage0/Stage0/IRBild.lean
  Subject:   `stage0 --ir PROGRAM.gab IMAGE`: the program checked by the goal theorem's checker Bool, lowered to G
             (`lowerAllg`), every function lowered to `S0IR` (`Senke/`), laid out as an image the runner loads.
-/
module
public import Stage0.Bindung
public import Stage0.Compiler
public import Grammatik.Parser.Elab.UebersetzePipeline
public import Grammatik.GabbroV.Start.GvStartPflicht
public import Stage0.Senke.Images.Bild
public import Stage0.Senke.Images.InitialExecution
public import Stage0.Senke.Welt.Anordnung
public import Stage0.Senke.Welt.GlobalAlignment
public import Stage0.Senke.Welt.MainEnv
public import Stage0.Senke.Welt.Initial
public import Stage0.Senke.Images.SourceStarts
@[expose] public section


namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2 Gabbro.Grammatik.GabbroV
  Gabbro.Grammatik.Parser.Cover.Differenz

/-- The stack of an image, in slots (4 MiB); the world lies above it (`Senke.layU`). -/
def irStapel : Nat := 2 ^ 19

/-- Per-loop environment fuel compiled into the image; independent of call depth. -/
def irDurchlaeufe : Nat := 2 ^ 20

/-- The actual image together with the exact source program and successful canonical IR emission. -/
structure Emitted (text : String) (K : Nat) (options : Profil.Options := {}) where
  compiled : Compiled text options
  tor : (declOf compiled.unit).Ax → Option Senke.TorB
  /-- Starts recovered from the selected original source, before names could erase arguments. -/
  startPlan : StartArgument.Plan compiled.unit
    (uMembers (pre108 compiled.source.prepared.elaborierbar)) compiled.main
  initialValid : sp0OkB compiled.unit = true
  /-- the environment `main` starts with: the pointer to the table each parameter's type names -/
  args : Env (declOf compiled.unit) ((declOf compiled.unit).params compiled.main)
  pointers : Senke.mainEnv ((declOf compiled.unit).params compiled.main) = some args
  image : Senke.Bild (declOf compiled.unit)
  emission : Senke.bild irDurchlaeufe compiled.program (Senke.layU compiled.unit tor)
    (List.finRange compiled.unit.fns.length) Fin.val
    (fun g => (compiled.unit.fns[g.val]?.map (·.name)).getD "?") compiled.main args
    (startPlan.starts (Senke.initialWorld compiled.unit initialValid)) K
    (Senke.bodenAusrichtung compiled.unit) = .ok image

/-- One source-to-image path; no separate unchecked emitter is retained. -/
def emit (src : String) (K : Nat := irStapel) (options : Profil.Options := {}) : Except String (Emitted src K options) := do
  let compiled ← compile src options
  let items := compiled.source.items
  let u := compiled.unit
  let P := compiled.program
  let main := compiled.main
  let members := uMembers (pre108 items)
  validateTargetFor options.arch options.target members
  let tore ← toreVonFor options.arch options.target members
  for foreign in u.axs do
    match foreign.res with
    | some type =>
      if 1 < Senke.valueWords type then
        let area := (tore.find? (·.name == foreign.name)).bind (·.resultArea)
        if area.isNone then
          throw s!"gate {foreign.name}: multiword result requires result area REGISTER in the selected profile"
    | none => pure ()
  let tor : (declOf u).Ax → Option Senke.TorB := fun a =>
    (tore.find? (·.name == (uaxAt u a).name)).map fun t => ⟨t.nummer, t.regs, t.fehler, t.resultArea⟩
  let startPlan ← StartArgument.plan u (uMembers (pre108 compiled.source.prepared.elaborierbar)) main
  if initialValid : sp0OkB u = true then
    match hp : Senke.mainEnv ((declOf u).params main) with
    | none => throw "ir: main takes a parameter that is not a table pointer: no start-argument form"
    | some args =>
      match he : Senke.bild irDurchlaeufe P (Senke.layU u tor) (List.finRange u.fns.length) Fin.val
          (fun g => (u.fns[g.val]?.map (·.name)).getD "?") main args
          (startPlan.starts (Senke.initialWorld u initialValid)) K
          (Senke.bodenAusrichtung u) with
      | .error e => throw e
      | .ok image => pure ⟨compiled, tor, startPlan, initialValid, args, hp, image, he⟩
  else throw "ir: canonical initial memory is outside its declared types"

/-- The exact typed occurrences supplied to the image constructor. -/
def Emitted.starts {src : String} {K : Nat} {options : Profil.Options} (output : Emitted src K options) :
    List (Σ f : (declOf output.compiled.unit).Fn, Env (declOf output.compiled.unit) ((declOf output.compiled.unit).params f)) :=
  output.startPlan.starts (Senke.initialWorld output.compiled.unit output.initialValid)

/-- The sole emitted payload, including the canonical world and all typed start frames. -/
def Emitted.bytes {src : String} {K : Nat} {options : Profil.Options}
    (output : Emitted src K options) : List Runner.B :=
  output.image.initializedBytes output.compiled.unit output.initialValid

def irBild (src : String) (K : Nat := irStapel) (options : Profil.Options := {}) : Except String (List Runner.B) :=
  (emit src K options).map (fun output => output.bytes)

/-- Every actual returned byte list comes from this same certified source/program/image path. -/
theorem irBild_emitted (src : String) (K : Nat) (bytes : List Runner.B) {options : Profil.Options}
    (h : irBild src K options = .ok bytes) :
    ∃ output : Emitted src K options, emit src K options = .ok output ∧ output.bytes = bytes := by
  unfold irBild at h
  cases he : emit src K options with
  | error e => simp only [he] at h; contradiction
  | ok output =>
    refine ⟨output, rfl, ?_⟩
    simp only [he] at h
    exact Except.ok.inj h

/-- The inherited IR execution conclusion for this exact emitted program and entry state; `main` runs with the
    environment whose words the image carries. -/
def Emitted.Simulates [Runner.IR.Kern] {src : String} {K : Nat} {options : Profil.Options}
    (output : Emitted src K options) (O : Orakel (declOf output.compiled.unit))
    (m : Runner.Mem) (σ : World (declOf output.compiled.unit)) : Prop :=
    match rufAt output.compiled.program O output.image.passes output.image.depth output.compiled.main σ output.args with
    | .ok _ v => ∃ t' m' q,
        Runner.IR.Star ⟨BitVec.ofNat 64 Senke.codeBase, BitVec.ofNat 64 output.image.fp0⟩ m t' m' ∧
        Runner.IR.StopAt t' m' q ∧ q.nr = 231 ∧
        Senke.ExitErg output.image.Y ((declOf output.compiled.unit).erg output.compiled.main) v q.a1
    | .logik e => Senke.Stops ⟨BitVec.ofNat 64 Senke.codeBase, BitVec.ofNat 64 output.image.fp0⟩ m
        (Senke.logikCode e)
    | .hardware h => Senke.Stops ⟨BitVec.ofNat 64 Senke.codeBase, BitVec.ofNat 64 output.image.fp0⟩ m
        (Senke.hwCode h)
    | _ => False

/-- A root occurrence runs with its own original typed environment on stack `j + 1`.
    This is the existing individual-thread theorem, with no simultaneous GX claim. -/
def Emitted.RootSimulates [Runner.IR.Kern] {src : String} {K : Nat} {options : Profil.Options}
    (output : Emitted src K options) (O : Orakel (declOf output.compiled.unit))
    (m : Runner.Mem) (σ : World (declOf output.compiled.unit))
    (j : Nat) (hj : j < output.starts.length) : Prop :=
  let root := output.starts[j]
  let entry : Runner.IR.T :=
    ⟨BitVec.ofNat 64 (Senke.codeBase + 16 * (3 * output.starts.length + Senke.startLen + Senke.startLen * j)),
      BitVec.ofNat 64 (output.image.fp0 + 8 * (output.image.Ks * (j + 1)))⟩
  match rufAt output.compiled.program O output.image.passes output.image.depth root.1 σ root.2 with
  | .ok _ _ => ∃ t' m' q, Runner.IR.Star entry m t' m' ∧ Runner.IR.StopAt t' m' q ∧ q.nr = 60
  | .logik e => Senke.Stops entry m (Senke.logikCode e)
  | .hardware h => Senke.Stops entry m (Senke.hwCode h)
  | _ => False

/-- Loading the sole production payload establishes the canonical source world.
    Layout, initialized storage, locks and stack bounds come from the accepted builder. -/
theorem Emitted.loaded_initial_world [Runner.IR.Kern]
    {src : String} {K : Nat} {options : Profil.Options} (output : Emitted src K options)
    {m : Runner.Mem} (loaded : Senke.BytesAt m Runner.Prog.IMG output.bytes) :
    Senke.WeltAt m output.image.Y (Senke.initialWorld output.compiled.unit output.initialValid) := by
  have positions : ∀ g : (declOf output.compiled.unit).Fn,
      (List.finRange output.compiled.unit.fns.length)[g.val]? = some g := by
    intro g
    simp only [List.finRange, List.getElem?_ofFn, g.isLt, ↓reduceDIte]
    congr 1
  exact (Senke.bild_initialized_loaded_u output.initialValid output.emission positions loaded).1

/-- Original-source canonical elaboration and execution of that identical program
    in every compatible world under the inherited image contracts. Ordered roots
    retain their source environments; their individual simulations make no
    simultaneous GX execution claim. -/
def Emitted.Correct [Runner.IR.Kern] {src : String} {K : Nat} {options : Profil.Options} (output : Emitted src K options) : Prop :=
  CanonicalSourceProgram output.compiled ∧
  ∀ (O : Orakel (declOf output.compiled.unit)) (m : Runner.Mem)
    (σ : World (declOf output.compiled.unit)),
    Senke.BytesAt m Runner.Prog.IMG output.bytes →
    Senke.WeltAt m output.image.Y σ → Senke.TorOK output.image.Y O → Senke.SichtOK O →
    output.Simulates O m σ ∧ ∀ j (hj : j < output.starts.length), output.RootSimulates O m σ j hj

theorem Emitted.correct [Runner.IR.Kern] [Senke.CloneOK] {src : String} {K : Nat} {options : Profil.Options}
    (output : Emitted src K options) : output.Correct := by
  refine ⟨compile_source_program _ output.compiled, ?_⟩
  intro O m σ hm hWa hT hV
  have hfs : ∀ g : (declOf output.compiled.unit).Fn,
      (List.finRange output.compiled.unit.fns.length)[g.val]? = some g := by
    intro g
    simp only [List.finRange, List.getElem?_ofFn, g.isLt, ↓reduceDIte]
    congr 1
  constructor
  · unfold Emitted.Simulates
    have hr := Senke.bild_initialized_ok_u output.initialValid output.emission hfs hm σ
      (fun τ x => Senke.mainEnv_valid output.image.Y _ output.args output.pointers τ x) hWa hT hV
    generalize rufAt output.compiled.program O output.image.passes output.image.depth
      output.compiled.main σ output.args = outcome at hr ⊢
    cases outcome <;> exact hr
  · intro j hj
    have hr := Senke.bild_initialized_wurzel_ok_u output.initialValid output.emission hfs hm j hj σ
      (output.startPlan.starts_valid _ output.image.Y output.starts[j] (List.getElem_mem hj)) hWa hT hV
    dsimp only [Emitted.RootSimulates, Emitted.starts] at hr ⊢
    generalize rufAt (D := declOf output.compiled.unit) output.compiled.program O
      output.image.passes output.image.depth
      ((output.startPlan.starts (Senke.initialWorld output.compiled.unit output.initialValid))[j]'hj).1 σ
      ((output.startPlan.starts (Senke.initialWorld output.compiled.unit output.initialValid))[j]'hj).2 =
        outcome at hr ⊢
    cases outcome <;> exact hr

/-- Canonical source startup is an instance of the all-compatible-world theorem.
    The actual initialized payload establishes its world relation internally; no
    independent initial world or source execution is supplied by the caller. -/
theorem Emitted.source_correct [Runner.IR.Kern] [Senke.CloneOK]
    {src : String} {K : Nat} {options : Profil.Options} (output : Emitted src K options) :
    CanonicalSourceProgram output.compiled ∧
    ∀ (O : Orakel (declOf output.compiled.unit)) (m : Runner.Mem),
      Senke.BytesAt m Runner.Prog.IMG output.bytes →
      Senke.TorOK output.image.Y O → Senke.SichtOK O →
      output.Simulates O m (Senke.initialWorld output.compiled.unit output.initialValid) ∧
        ∀ j (hj : j < output.starts.length),
          output.RootSimulates O m (Senke.initialWorld output.compiled.unit output.initialValid) j hj := by
  have generic := output.correct
  refine ⟨generic.1, ?_⟩
  intro O m loaded gates view
  exact generic.2 O m (Senke.initialWorld output.compiled.unit output.initialValid)
    loaded (output.loaded_initial_world loaded) gates view

/-- The emitted root prefix preserves every original concurrent member, including duplicate names. -/
theorem Emitted.starts_source {src : String} {K : Nat} {options : Profil.Options}
    (output : Emitted src K options) :
    output.startPlan.concurrent.map (fun start => (start.path, start.sourceArgs)) =
      StartArgument.sourceIdentities (uMembers (pre108 output.compiled.source.prepared.elaborierbar)) :=
  output.startPlan.source_identity

/-- The image is built for exactly the profile the program was checked against:
    the checked binding travels from `Prepared` into the canonical program. -/
theorem Emitted.profile_binding {src : String} {K : Nat} {options : Profil.Options}
    (output : Emitted src K options) :
    Gabbro.Grammatik.Parser.ProfilBindung.bindungB output.compiled.source.prepared.bindung = true :=
  output.compiled.profile_binding

/-- The built image has no named sections: the flat runner image carries no
    section relocation. -/
theorem Emitted.sections_free {src : String} {K : Nat} {options : Profil.Options}
    (output : Emitted src K options) :
    Profil.abschnittFehler output.compiled.source.prepared.selected = none :=
  output.compiled.sections_free

/-- Every placed global's absolute address meets its declared alignment: the image builder
    aligned the world base up to the required base alignment (`bodenAusrichtung`), which every
    combined grid divides (`boden_teilt`), so no loader base-placement duty remains. -/
def Emitted.Placed {src : String} {K : Nat} {options : Profil.Options}
    (output : Emitted src K options) : Prop :=
  ∀ g : Fin output.compiled.unit.globs.length,
    0 < Senke.globAlign output.compiled.unit g →
    Senke.globAlign output.compiled.unit g ∣ output.image.Y.ga g ∧
      8 ∣ output.image.Y.ga g

theorem Emitted.placed {src : String} {K : Nat} {options : Profil.Options}
    (output : Emitted src K options) : output.Placed := by
  intro g hpos
  have hreq : 0 < Senke.bodenAusrichtung output.compiled.unit := Senke.boden_pos _
  have hdvd : Nat.lcm 8 (Senke.globAlign output.compiled.unit g) ∣
      Senke.bodenAusrichtung output.compiled.unit :=
    Senke.boden_teilt _ _ hpos
  have hb := output.emission
  generalize hgen : output.image = bimg at hb ⊢
  simp only [Senke.bild] at hb
  split at hb
  · cases hb
  · next cs0 h0 =>
    split at hb
    · cases hb
    · next cs h1 =>
      split at hb
      · next hg =>
        simp only [Except.ok.injEq] at hb
        have hbase : Nat.lcm 8 (Senke.globAlign output.compiled.unit g) ∣ bimg.Y.lo := by
          rw [← hb]
          exact Nat.dvd_trans hdvd (Senke.alignUp_dvd _ _ hreq)
        subst hb
        dsimp only at hbase ⊢
        exact ⟨Senke.layU_ga_aligned _ _ _ _ hpos hbase,
          Senke.layU_ga_word_aligned _ _ _ _ hpos hbase⟩
      · exfalso
        revert hb
        repeat' split
        all_goals intro hb; cases hb

/-- The actual CLI payload retains the original canonical source, initialized main/root
    execution certificate and alignment guarantees under the inherited runner contracts. -/
theorem irBild_correct [Runner.IR.Kern] [Senke.CloneOK] (src : String) (K : Nat) (bytes : List Runner.B) {options : Profil.Options}
    (h : irBild src K options = .ok bytes) :
    ∃ output : Emitted src K options, emit src K options = .ok output ∧ output.bytes = bytes ∧ output.Correct ∧ output.Placed := by
  obtain ⟨output, he, hb⟩ := irBild_emitted src K bytes h
  exact ⟨output, he, hb, output.correct, output.placed⟩

/-- The exact bytes returned by the CLI also realize canonical source startup.
    The general compatible-world certificate remains available for the same image. -/
theorem irBild_source_correct [Runner.IR.Kern] [Senke.CloneOK]
    (src : String) (K : Nat) (bytes : List Runner.B) {options : Profil.Options}
    (h : irBild src K options = .ok bytes) :
    ∃ output : Emitted src K options,
      emit src K options = .ok output ∧ output.bytes = bytes ∧ output.Correct ∧ output.Placed ∧
      ∀ (O : Orakel (declOf output.compiled.unit)) (m : Runner.Mem),
        Senke.BytesAt m Runner.Prog.IMG bytes →
        Senke.TorOK output.image.Y O → Senke.SichtOK O →
        output.Simulates O m (Senke.initialWorld output.compiled.unit output.initialValid) ∧
          ∀ j (hj : j < output.starts.length),
            output.RootSimulates O m (Senke.initialWorld output.compiled.unit output.initialValid) j hj := by
  obtain ⟨output, emitted, payload, generic, placed⟩ := irBild_correct src K bytes h
  refine ⟨output, emitted, payload, generic, placed, ?_⟩
  rw [← payload]
  exact output.source_correct.2

end Gabbro.Stage0
