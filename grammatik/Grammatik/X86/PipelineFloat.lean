/-
  File:      Grammatik/X86/PipelineFloat.lean
  Subject:   Pipeline: IEEE float expressions (source `gleit` block nodes to
              accepted scalar SSE2 forms).

  Lane 1161: lower the source IEEE model (`Gleitkomma`, `gleitRechne`,
  `gleitAusInt`, `gleitRoh`, `gleitLt`/`gleitLe`) to the ACCEPTED scalar
  SSE2 forms (`ScalarFloat.fpSchritt`/`fpRechne`, `ScalarFloatCodec`,
  `ScalarFloat32HardwareForms`, `FpControlHardwareForms`) under the MXCSR
  control-state premise (round-to-nearest, no fast-math, no contraction).

  Reused, not duplicated:
    - machine words: `Gleitprofil.muster64`/`bites64`/`fadd64`/…,
      `mxcsrGueltig`, `kontextReset`;
    - target steps: `ScalarFloat.fpSchritt` with its `fpSchritt_*`
      equations, `fpRechne_gleitRechne`, `fpRechne_klasse`,
      `ucomiFlags_*`, `cvtsiErg`, `cvttPaket_gleicht_gleitRoh`;
    - source observations: `FloatSourceObservations.eval_fllt_ist_gleitLt`;
    - joint state: `fpZeugeT`/`fpZeugeT1`/`fpZeugeT2` and their step
      lemmas for the `_zeuge`.
  No second source interpreter, no new IEEE model, no optimiser edit.
-/
import Grammatik.X86.ScalarFloat

namespace Gabbro.Grammatik.X86.PipelineFloat

open Gabbro.Grammatik
open Gabbro.Grammatik.X86

/-- Lower one source float op to its accepted scalar SSE2 register form:
    one source op = one machine op (no contraction, no fast-math). -/
def senkGleitOp : GleitOp → XmmReg → XmmReg → FpBefehl
  | .add, dst, src => .addsdRR dst src
  | .sub, dst, src => .subsdRR dst src
  | .mul, dst, src => .mulsdRR dst src
  | .div, dst, src => .divsdRR dst src

/-- Run a decoded scalar-FP list; `none` is an explicit refusal. -/
def laufFp : List FpDecodiert → FpZustand → Option FpZustand
  | [], t => some t
  | d :: ds, t =>
    match fpSchritt d t with
    | none => none
    | some t' => laufFp ds t'

/-- The empty run reaches its start state. -/
theorem laufFp_nil (t : FpZustand) : laufFp [] t = some t := rfl

/-- One run step unfolds to the head step plus the tail run. -/
theorem laufFp_cons (d : FpDecodiert) (ds : List FpDecodiert) (t : FpZustand) :
    laufFp (d :: ds) t
      = match fpSchritt d t with | none => none | some t' => laufFp ds t' := rfl

/-! ## 1. Validator: MXCSR profile and decode length.

  The pipeline admits a float sequence only under the checked control
  word (round-to-nearest, no FTZ/DAZ, all masks set: `mxcsrGueltig`)
  and checked decode lengths (`laengeOk`). Anything else is refused,
  never executed. -/

/-- The decided admission check of one float lowering. -/
def floatPipeOk (k : FPKontext) (len : Nat) : Bool :=
  mxcsrGueltig k.mxcsr && laengeOk len

/-- The reset context with a 4-byte form is admitted. -/
theorem floatPipeOk_reset : floatPipeOk kontextReset 4 = true := by
  decide

/-- A refused MXCSR word refuses every length. -/
theorem floatPipeOk_profil_verweigert (k : FPKontext)
    (h : mxcsrGueltig k.mxcsr = false) (len : Nat) :
    floatPipeOk k len = false := by
  unfold floatPipeOk
  simp [h]

/-- A bad decode length refuses every control word. -/
theorem floatPipeOk_laenge_verweigert (k : FPKontext) (len : Nat)
    (h : laengeOk len = false) :
    floatPipeOk k len = false := by
  unfold floatPipeOk
  simp [h]

/-! ## 2. Arithmetic sequences: source `gleitRechne`, bit for bit.

  `movsd dst, a` then the lowered op against `b` computes the source
  model op on the injected operand words, projected back as a word
  (`fpRechne_gleitRechne`). `b ≠ dst` keeps the move from clobbering
  the second operand. Stated with an existential successor in the style
  of `Pipeline.pipeline_correct`: the run, the RIP past both 4-byte
  forms, the model word in `dst`, the untouched control word. -/

/-- THE FLOAT SEQUENCE: the lowered two-step run reaches a successor
    whose `dst` holds the exact source model result bit for bit. -/
theorem pipelineFloat_seq (op : GleitOp) (dst a b : XmmReg) (t : FpZustand)
    (hne : b ≠ dst)
    (hok : laengeOk 4 = true)
    (hfp : fpEintritt t.fp = true) :
    ∃ t' : FpZustand,
      laufFp [⟨.movsdRR dst a, 4⟩, ⟨senkGleitOp op dst b, 4⟩] t = some t'
      ∧ t'.kern.rip = ripNach (ripNach t.kern.rip 4) 4
      ∧ xmmTief t'.xmm dst
          = muster64 (gleitRechne op (bites64 (xmmTief t.xmm a)) (bites64 (xmmTief t.xmm b)))
      ∧ t'.fp = t.fp := by
  have hmov : fpSchritt (⟨.movsdRR dst a, 4⟩ : FpDecodiert) t =
      some { t with kern := { t.kern with rip := ripNach t.kern.rip 4 }, xmm := xmmSchreibeTief t.xmm dst (xmmTief t.xmm a) } :=
    fpSchritt_movsdRR _ _ dst a hok hfp rfl
  have hfp0 : fpEintritt ({ t with kern := { t.kern with rip := ripNach t.kern.rip 4 }, xmm := xmmSchreibeTief t.xmm dst (xmmTief t.xmm a) } : FpZustand).fp = true := hfp
  have hdst : xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst =
      xmmTief t.xmm a :=
    xmmSchreibeTief_tief _ _ _
  have hsrc : xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) b =
      xmmTief t.xmm b := by
    unfold xmmTief
    rw [xmmSchreibeTief_fremd _ _ _ _ hne]
  cases op with
  | add =>
    have h2 := fpSchritt_addsdRR (⟨senkGleitOp .add dst b, 4⟩ : FpDecodiert)
      { t with kern := { t.kern with rip := ripNach t.kern.rip 4 }, xmm := xmmSchreibeTief t.xmm dst (xmmTief t.xmm a) }
      dst b hok hfp0 rfl
    have h2f : fpSchritt (⟨senkGleitOp .add dst b, 4⟩ : FpDecodiert) { t with kern := { t.kern with rip := ripNach t.kern.rip 4 }, xmm := xmmSchreibeTief t.xmm dst (xmmTief t.xmm a) } = some { kern := { register := t.kern.register, flags := t.kern.flags, rip := ripNach (ripNach t.kern.rip 4) 4, speicher := t.kern.speicher }, xmm := xmmSchreibeTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst (fpRechne .add (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst) (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) b)), fp := t.fp } := h2
    have hrun : laufFp [⟨.movsdRR dst a, 4⟩, ⟨senkGleitOp .add dst b, 4⟩] t = some { kern := { register := t.kern.register, flags := t.kern.flags, rip := ripNach (ripNach t.kern.rip 4) 4, speicher := t.kern.speicher }, xmm := xmmSchreibeTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst (fpRechne .add (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst) (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) b)), fp := t.fp } := by
      simp only [laufFp_cons, laufFp_nil, hmov, h2f]
    refine ⟨_, hrun, rfl,
      by simp only [xmmSchreibeTief_tief, hdst, hsrc, fpRechne_gleitRechne], rfl⟩
  | sub =>
    have h2 := fpSchritt_subsdRR (⟨senkGleitOp .sub dst b, 4⟩ : FpDecodiert)
      { t with kern := { t.kern with rip := ripNach t.kern.rip 4 }, xmm := xmmSchreibeTief t.xmm dst (xmmTief t.xmm a) }
      dst b hok hfp0 rfl
    have h2f : fpSchritt (⟨senkGleitOp .sub dst b, 4⟩ : FpDecodiert) { t with kern := { t.kern with rip := ripNach t.kern.rip 4 }, xmm := xmmSchreibeTief t.xmm dst (xmmTief t.xmm a) } = some { kern := { register := t.kern.register, flags := t.kern.flags, rip := ripNach (ripNach t.kern.rip 4) 4, speicher := t.kern.speicher }, xmm := xmmSchreibeTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst (fpRechne .sub (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst) (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) b)), fp := t.fp } := h2
    have hrun : laufFp [⟨.movsdRR dst a, 4⟩, ⟨senkGleitOp .sub dst b, 4⟩] t = some { kern := { register := t.kern.register, flags := t.kern.flags, rip := ripNach (ripNach t.kern.rip 4) 4, speicher := t.kern.speicher }, xmm := xmmSchreibeTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst (fpRechne .sub (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst) (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) b)), fp := t.fp } := by
      simp only [laufFp_cons, laufFp_nil, hmov, h2f]
    refine ⟨_, hrun, rfl,
      by simp only [xmmSchreibeTief_tief, hdst, hsrc, fpRechne_gleitRechne], rfl⟩
  | mul =>
    have h2 := fpSchritt_mulsdRR (⟨senkGleitOp .mul dst b, 4⟩ : FpDecodiert)
      { t with kern := { t.kern with rip := ripNach t.kern.rip 4 }, xmm := xmmSchreibeTief t.xmm dst (xmmTief t.xmm a) }
      dst b hok hfp0 rfl
    have h2f : fpSchritt (⟨senkGleitOp .mul dst b, 4⟩ : FpDecodiert) { t with kern := { t.kern with rip := ripNach t.kern.rip 4 }, xmm := xmmSchreibeTief t.xmm dst (xmmTief t.xmm a) } = some { kern := { register := t.kern.register, flags := t.kern.flags, rip := ripNach (ripNach t.kern.rip 4) 4, speicher := t.kern.speicher }, xmm := xmmSchreibeTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst (fpRechne .mul (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst) (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) b)), fp := t.fp } := h2
    have hrun : laufFp [⟨.movsdRR dst a, 4⟩, ⟨senkGleitOp .mul dst b, 4⟩] t = some { kern := { register := t.kern.register, flags := t.kern.flags, rip := ripNach (ripNach t.kern.rip 4) 4, speicher := t.kern.speicher }, xmm := xmmSchreibeTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst (fpRechne .mul (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst) (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) b)), fp := t.fp } := by
      simp only [laufFp_cons, laufFp_nil, hmov, h2f]
    refine ⟨_, hrun, rfl,
      by simp only [xmmSchreibeTief_tief, hdst, hsrc, fpRechne_gleitRechne], rfl⟩
  | div =>
    have h2 := fpSchritt_divsdRR (⟨senkGleitOp .div dst b, 4⟩ : FpDecodiert)
      { t with kern := { t.kern with rip := ripNach t.kern.rip 4 }, xmm := xmmSchreibeTief t.xmm dst (xmmTief t.xmm a) }
      dst b hok hfp0 rfl
    have h2f : fpSchritt (⟨senkGleitOp .div dst b, 4⟩ : FpDecodiert) { t with kern := { t.kern with rip := ripNach t.kern.rip 4 }, xmm := xmmSchreibeTief t.xmm dst (xmmTief t.xmm a) } = some { kern := { register := t.kern.register, flags := t.kern.flags, rip := ripNach (ripNach t.kern.rip 4) 4, speicher := t.kern.speicher }, xmm := xmmSchreibeTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst (fpRechne .div (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst) (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) b)), fp := t.fp } := h2
    have hrun : laufFp [⟨.movsdRR dst a, 4⟩, ⟨senkGleitOp .div dst b, 4⟩] t = some { kern := { register := t.kern.register, flags := t.kern.flags, rip := ripNach (ripNach t.kern.rip 4) 4, speicher := t.kern.speicher }, xmm := xmmSchreibeTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst (fpRechne .div (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst) (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) b)), fp := t.fp } := by
      simp only [laufFp_cons, laufFp_nil, hmov, h2f]
    refine ⟨_, hrun, rfl,
      by simp only [xmmSchreibeTief_tief, hdst, hsrc, fpRechne_gleitRechne], rfl⟩

end Gabbro.Grammatik.X86.PipelineFloat
