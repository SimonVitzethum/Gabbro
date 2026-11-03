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
public import Stage0.Senke.Welt.Anordnung
public import Stage0.Senke.Welt.GlobalAlignment
public import Stage0.Senke.Welt.MainEnv
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
  roots : List (declOf compiled.unit).Fn
  /-- the environment `main` starts with: the pointer to the table each parameter's type names -/
  args : Env (declOf compiled.unit) ((declOf compiled.unit).params compiled.main)
  pointers : Senke.mainEnv ((declOf compiled.unit).params compiled.main) = some args
  image : Senke.Bild (declOf compiled.unit)
  emission : Senke.bild irDurchlaeufe compiled.program (Senke.layU compiled.unit tor)
    (List.finRange compiled.unit.fns.length) Fin.val
    (fun g => (compiled.unit.fns[g.val]?.map (·.name)).getD "?") compiled.main args roots K = .ok image

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
  let tor : (declOf u).Ax → Option Senke.TorB := fun a =>
    (tore.find? (·.name == (uaxAt u a).name)).map fun t => ⟨t.nummer, t.regs, t.fehler⟩
  let rs ← (uOhneDoppelte (u.roots ++ u.gestartet)).mapM (fnIdx u.fns)
  let roots := rs.filter (· != main)
  match hp : Senke.mainEnv ((declOf u).params main) with
  | none => throw "ir: main takes a parameter that is not a table pointer: no start-argument form"
  | some args =>
    match he : Senke.bild irDurchlaeufe P (Senke.layU u tor) (List.finRange u.fns.length) Fin.val
        (fun g => (u.fns[g.val]?.map (·.name)).getD "?") main args roots K with
    | .error e => throw e
    | .ok image => pure ⟨compiled, tor, roots, args, hp, image, he⟩

def irBild (src : String) (K : Nat := irStapel) (options : Profil.Options := {}) : Except String (List Runner.B) :=
  (emit src K options).map (fun output => output.image.bytes)

/-- Every actual returned byte list comes from this same certified source/program/image path. -/
theorem irBild_emitted (src : String) (K : Nat) (bytes : List Runner.B) {options : Profil.Options}
    (h : irBild src K options = .ok bytes) :
    ∃ output : Emitted src K options, emit src K options = .ok output ∧ output.image.bytes = bytes := by
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

/-- Original-source canonical elaboration, exact invariant carriers/read bounds, and execution\n    of that identical program (including ordered normal-return restoration) by this image,
    under the existing image theorem's gate/view and initial-memory contracts. -/
def Emitted.Correct [Runner.IR.Kern] {src : String} {K : Nat} {options : Profil.Options} (output : Emitted src K options) : Prop :=
  CanonicalSourceProgram output.compiled ∧
  ∀ (O : Orakel (declOf output.compiled.unit)) (m : Runner.Mem)
    (σ : World (declOf output.compiled.unit)),
    Senke.BytesAt m Runner.Prog.IMG output.image.bytes →
    Senke.WeltAt m output.image.Y σ → Senke.TorOK output.image.Y O → Senke.SichtOK O →
    output.Simulates O m σ

theorem Emitted.correct [Runner.IR.Kern] [Senke.CloneOK] {src : String} {K : Nat} {options : Profil.Options}
    (output : Emitted src K options) : output.Correct := by
  refine ⟨compile_source_program _ output.compiled, ?_⟩
  intro O m σ hm hWa hT hV
  have hfs : ∀ g : (declOf output.compiled.unit).Fn,
      (List.finRange output.compiled.unit.fns.length)[g.val]? = some g := by
    intro g
    simp only [List.finRange, List.getElem?_ofFn, g.isLt, ↓reduceDIte]
    congr 1
  unfold Emitted.Simulates
  have hr := Senke.bild_ok_u output.emission hfs hm σ
    (fun τ x => Senke.mainEnv_valid output.image.Y _ output.args output.pointers τ x) hWa hT hV
  generalize rufAt output.compiled.program O output.image.passes output.image.depth
    output.compiled.main σ output.args = outcome at hr ⊢
  cases outcome <;> exact hr

/-- The actual successful CLI byte result realizes its original source's canonical program.
    This includes C05 through `compile_source_program` and the generic return epilogue theorem.\n    Reason exits keep the original program and its separate `InvGutGrundA` user duty.\n    This is conditional on successful compilation and inherited runner contracts, not total coverage. -/
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

/-- Every placed global's absolute address meets its declared alignment, once the
    image base lies on the combined grid (the loader base-placement duty). -/
def Emitted.Placed {src : String} {K : Nat} {options : Profil.Options}
    (output : Emitted src K options) : Prop :=
  ∀ g : Fin (declOf output.compiled.unit).globs.length,
    0 < Senke.globAlign output.compiled.unit g →
    Nat.lcm 8 (Senke.globAlign output.compiled.unit g) ∣ output.image.Y.lo →
    Senke.globAlign output.compiled.unit g ∣ output.image.Y.ga g ∧
      8 ∣ output.image.Y.ga g

theorem Emitted.placed {src : String} {K : Nat} {options : Profil.Options}
    (output : Emitted src K options) : output.Placed := by
  intro g hpos hbase
  have hb := output.emission
  generalize hgen : output.image = bimg at hb hbase ⊢
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
        subst hb
        dsimp only at hbase ⊢
        exact ⟨Senke.layU_ga_aligned _ _ _ _ hpos hbase,
          Senke.layU_ga_word_aligned _ _ _ _ hpos hbase⟩
      · exfalso
        revert hb
        repeat' split
        all_goals intro hb; cases hb

theorem irBild_correct [Runner.IR.Kern] [Senke.CloneOK] (src : String) (K : Nat) (bytes : List Runner.B) {options : Profil.Options}
    (h : irBild src K options = .ok bytes) :
    ∃ output : Emitted src K options, emit src K options = .ok output ∧ output.image.bytes = bytes ∧ output.Correct ∧ output.Placed := by
  obtain ⟨output, he, hb⟩ := irBild_emitted src K bytes h
  exact ⟨output, he, hb, output.correct, output.placed⟩

end Gabbro.Stage0
