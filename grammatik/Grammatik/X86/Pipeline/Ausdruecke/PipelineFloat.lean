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
import Grammatik.X86.Befehle.Gleitkomma.ScalarFloat
import Grammatik.Logik.Vertraege.EinpassenVoll
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
      ∧ t'.fp = t.fp
      ∧ t'.kern.speicher = t.kern.speicher
      ∧ t'.kern.register = t.kern.register := by
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
      by simp only [xmmSchreibeTief_tief, hdst, hsrc, fpRechne_gleitRechne], rfl, rfl, rfl⟩
  | sub =>
    have h2 := fpSchritt_subsdRR (⟨senkGleitOp .sub dst b, 4⟩ : FpDecodiert)
      { t with kern := { t.kern with rip := ripNach t.kern.rip 4 }, xmm := xmmSchreibeTief t.xmm dst (xmmTief t.xmm a) }
      dst b hok hfp0 rfl
    have h2f : fpSchritt (⟨senkGleitOp .sub dst b, 4⟩ : FpDecodiert) { t with kern := { t.kern with rip := ripNach t.kern.rip 4 }, xmm := xmmSchreibeTief t.xmm dst (xmmTief t.xmm a) } = some { kern := { register := t.kern.register, flags := t.kern.flags, rip := ripNach (ripNach t.kern.rip 4) 4, speicher := t.kern.speicher }, xmm := xmmSchreibeTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst (fpRechne .sub (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst) (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) b)), fp := t.fp } := h2
    have hrun : laufFp [⟨.movsdRR dst a, 4⟩, ⟨senkGleitOp .sub dst b, 4⟩] t = some { kern := { register := t.kern.register, flags := t.kern.flags, rip := ripNach (ripNach t.kern.rip 4) 4, speicher := t.kern.speicher }, xmm := xmmSchreibeTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst (fpRechne .sub (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst) (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) b)), fp := t.fp } := by
      simp only [laufFp_cons, laufFp_nil, hmov, h2f]
    refine ⟨_, hrun, rfl,
      by simp only [xmmSchreibeTief_tief, hdst, hsrc, fpRechne_gleitRechne], rfl, rfl, rfl⟩
  | mul =>
    have h2 := fpSchritt_mulsdRR (⟨senkGleitOp .mul dst b, 4⟩ : FpDecodiert)
      { t with kern := { t.kern with rip := ripNach t.kern.rip 4 }, xmm := xmmSchreibeTief t.xmm dst (xmmTief t.xmm a) }
      dst b hok hfp0 rfl
    have h2f : fpSchritt (⟨senkGleitOp .mul dst b, 4⟩ : FpDecodiert) { t with kern := { t.kern with rip := ripNach t.kern.rip 4 }, xmm := xmmSchreibeTief t.xmm dst (xmmTief t.xmm a) } = some { kern := { register := t.kern.register, flags := t.kern.flags, rip := ripNach (ripNach t.kern.rip 4) 4, speicher := t.kern.speicher }, xmm := xmmSchreibeTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst (fpRechne .mul (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst) (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) b)), fp := t.fp } := h2
    have hrun : laufFp [⟨.movsdRR dst a, 4⟩, ⟨senkGleitOp .mul dst b, 4⟩] t = some { kern := { register := t.kern.register, flags := t.kern.flags, rip := ripNach (ripNach t.kern.rip 4) 4, speicher := t.kern.speicher }, xmm := xmmSchreibeTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst (fpRechne .mul (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst) (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) b)), fp := t.fp } := by
      simp only [laufFp_cons, laufFp_nil, hmov, h2f]
    refine ⟨_, hrun, rfl,
      by simp only [xmmSchreibeTief_tief, hdst, hsrc, fpRechne_gleitRechne], rfl, rfl, rfl⟩
  | div =>
    have h2 := fpSchritt_divsdRR (⟨senkGleitOp .div dst b, 4⟩ : FpDecodiert)
      { t with kern := { t.kern with rip := ripNach t.kern.rip 4 }, xmm := xmmSchreibeTief t.xmm dst (xmmTief t.xmm a) }
      dst b hok hfp0 rfl
    have h2f : fpSchritt (⟨senkGleitOp .div dst b, 4⟩ : FpDecodiert) { t with kern := { t.kern with rip := ripNach t.kern.rip 4 }, xmm := xmmSchreibeTief t.xmm dst (xmmTief t.xmm a) } = some { kern := { register := t.kern.register, flags := t.kern.flags, rip := ripNach (ripNach t.kern.rip 4) 4, speicher := t.kern.speicher }, xmm := xmmSchreibeTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst (fpRechne .div (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst) (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) b)), fp := t.fp } := h2
    have hrun : laufFp [⟨.movsdRR dst a, 4⟩, ⟨senkGleitOp .div dst b, 4⟩] t = some { kern := { register := t.kern.register, flags := t.kern.flags, rip := ripNach (ripNach t.kern.rip 4) 4, speicher := t.kern.speicher }, xmm := xmmSchreibeTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst (fpRechne .div (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) dst) (xmmTief (xmmSchreibeTief t.xmm dst (xmmTief t.xmm a)) b)), fp := t.fp } := by
      simp only [laufFp_cons, laufFp_nil, hmov, h2f]
    refine ⟨_, hrun, rfl,
      by simp only [xmmSchreibeTief_tief, hdst, hsrc, fpRechne_gleitRechne], rfl, rfl, rfl⟩

/-! ## 3. Comparisons: `ucomisd` with the unordered case.

  Source `fllt`/`flle` evaluate to `gleitLt`/`gleitLe`
  (`FloatSourceObservations.eval_fllt_ist_gleitLt`); the lowered
  `ucomisd` sets exactly the `ucomiFlags` of the injected operand
  words. NaN on either side takes the unordered row (ZF, PF, CF set);
  off the NaN rows the flags are the two model comparisons
  (`ucomiFlags_nichtNan`), and `<=` is the negated reverse `<`
  (`fle_flt`). -/

/-- Which source float comparison is lowered (both read the same
    `ucomisd` flags; `lt` is the CF row, `le` the CF-or-ZF row). -/
inductive FloatCmp where
  | lt | le
  deriving DecidableEq, Repr

/-- Lower a source float comparison to the accepted unordered compare:
    one source comparison = one `ucomisd`. -/
def senkGleitCmp : FloatCmp → XmmReg → XmmReg → FpBefehl
  | .lt, lhs, rhs => .ucomisdRR lhs rhs
  | .le, lhs, rhs => .ucomisdRR lhs rhs

/-- THE COMPARE STEP: the lowered comparison sets exactly the
    architectural flags of the injected operand words. -/
theorem pipelineFloat_cmp_schritt (c : FloatCmp) (lhs rhs : XmmReg) (d : FpDecodiert)
    (t : FpZustand)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = senkGleitCmp c lhs rhs) :
    fpSchritt d t = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge, flags := ucomiFlags (bites64 (xmmTief t.xmm lhs)) (bites64 (xmmTief t.xmm rhs)) } } := by
  cases c with
  | lt => exact fpSchritt_ucomisdRR d t lhs rhs hok hfp h
  | le => exact fpSchritt_ucomisdRR d t lhs rhs hok hfp h

/-- UNORDERED WITNESS: `0.0 / 0.0` is NaN, so comparing it against
    `1.0` sets ZF, PF and CF. -/
theorem pipelineFloat_cmp_ungeordnet :
    ucomiFlags (Gleitkomma.div Gleitkomma.f64 (Gleitkomma.ofInt Gleitkomma.f64 0) (Gleitkomma.ofInt Gleitkomma.f64 0)) (Gleitkomma.ofInt Gleitkomma.f64 1) = ⟨true, true, some false, true, false, false⟩ := by
  exact ucomiFlags_ungeordnet_links _ _ Gleitkomma.zeuge_nullDurchNull

/-- ORDERED LESS: a true source `fllt` (`gleitLt`) is exactly the CF row. -/
theorem pipelineFloat_cmp_lt (a b : GFloat)
    (ha : Gleitkomma.klasse Gleitkomma.f64 a ≠ .nan)
    (hb : Gleitkomma.klasse Gleitkomma.f64 b ≠ .nan)
    (hlt : gleitLt a b = true) :
    ucomiFlags a b = ⟨true, false, some false, false, false, false⟩ := by
  have h : Gleitkomma.flt Gleitkomma.f64 a b = true := hlt
  exact ucomiFlags_kleiner a b h ha hb

/-- ORDERED LESS-OR-EQUAL: a true source `flle` (`gleitLe`) is the CF
    row or the ZF row, never the unordered row. -/
theorem pipelineFloat_cmp_le (a b : GFloat)
    (ha : Gleitkomma.klasse Gleitkomma.f64 a ≠ .nan)
    (hb : Gleitkomma.klasse Gleitkomma.f64 b ≠ .nan)
    (hle : gleitLe a b = true) :
    (ucomiFlags a b).cf = true ∨ (ucomiFlags a b).zf = true := by
  have hfle : Gleitkomma.fle Gleitkomma.f64 a b = true := hle
  rw [fle_flt ha hb] at hfle
  have hba : Gleitkomma.flt Gleitkomma.f64 b a = false := by
    cases h : Gleitkomma.flt Gleitkomma.f64 b a with
    | true => simp_all
    | false => rfl
  cases h : Gleitkomma.flt Gleitkomma.f64 a b with
  | true =>
    rw [ucomiFlags_kleiner a b h ha hb]
    exact Or.inl rfl
  | false =>
    rw [ucomiFlags_gleich a b h hba ha hb]
    exact Or.inr rfl

/-! ## 4. Conversions: only where the accepted codec exists.

  `cvtsi2sd` (64-bit GPR to binary64) IS the source `gleitAusInt`
  at the machine, and the `cvttsd2si` wrapper IS the source
  `gleitRoh` on every word (`cvttPaket_gleicht_gleitRoh`). Any other
  width has no accepted form and is refused (`konvBreiteOk`).
  Literals travel as correctly rounded words (`bruch`/`muster64`). -/

/-- Lower an integer register to a float register: the accepted
    64-bit conversion only. -/
def senkGleitVon : Register → XmmReg → FpBefehl
  | src, dst => .cvtsi2sd dst src

/-- Lower a float register to an integer register: the accepted
    truncating 64-bit conversion only. -/
def senkGleitNach : XmmReg → Register → FpBefehl
  | src, dst => .cvttsd2si dst src

/-- Lower a source literal to its correctly rounded word. -/
def senkGleitLit (q : Int × Int) : Wort := muster64 (bruch q)

/-- The decided conversion-width check: 64 bits only. -/
def konvBreiteOk (w : Nat) : Bool := decide (w = 64)

/-- 64-bit conversions are admitted. -/
theorem konvBreiteOk_64 : konvBreiteOk 64 = true := by decide

/-- 32-bit conversions are refused: no accepted form. -/
theorem konvBreiteOk_32 : konvBreiteOk 32 = false := by decide

/-- Any non-64 width is refused. -/
theorem konvBreiteOk_nur64 (w : Nat) (h : w ≠ 64) : konvBreiteOk w = false := by
  unfold konvBreiteOk
  cases h' : decide (w = 64) with
  | true => exact absurd (of_decide_eq_true h') h
  | false => rfl

/-- INT TO FLOAT: the lowered conversion holds exactly the source
    `gleitAusInt` of the register value, bit for bit. -/
theorem pipelineFloat_von (src : Register) (dst : XmmReg) (d : FpDecodiert)
    (t : FpZustand)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = senkGleitVon src dst) :
    fpSchritt d t = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSchreibeTief t.xmm dst (muster64 (gleitAusInt (t.kern.register src).toInt)) } :=
  fpSchritt_cvtsi2sd d t dst src hok hfp h

/-- FLOAT TO INT: the lowered conversion holds exactly the source
    `gleitRoh` (truncation toward zero, saturated) of the operand. -/
theorem pipelineFloat_nach (src : XmmReg) (dst : Register) (d : FpDecodiert)
    (t : FpZustand)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = senkGleitNach src dst) :
    fpSchritt d t = some { t with kern := { t.kern with register := regSet t.kern.register dst (intWort (gleitRoh (bites64 (xmmTief t.xmm src)))), rip := ripNach t.kern.rip d.laenge } } := by
  have hstep := fpSchritt_cvttsd2si d t dst src hok hfp h
  rw [cvttPaket_gleicht_gleitRoh] at hstep
  exact hstep

/-- LITERALS ROUND-TRIP: injecting the lowered word gives back a
    well-formed source literal. -/
theorem pipelineFloat_lit_rund (q : Int × Int)
    (hwf : Gleitkomma.wf Gleitkomma.f64 (bruch q)) :
    bites64 (senkGleitLit q) = bruch q :=
  bites64_muster64 _ hwf

/-! ## 5. Refusals: unsupported shapes never execute.

  A refused MXCSR profile, a bad decode length, an unreadable memory
  source, or a non-64 conversion width refuses the step (`none`).
  `pipelineFloat_refuses_validator` ties both `floatPipeOk` legs to
  the step refusal. -/

/-- A refused profile refuses every lowered form. -/
theorem pipelineFloat_refuses_profil (d : FpDecodiert) (t : FpZustand)
    (hok : laengeOk d.laenge = true)
    (h : fpEintritt t.fp = false) :
    fpSchritt d t = none :=
  fpSchritt_profil_verweigert d t hok h

/-- A bad decode length refuses every lowered form. -/
theorem pipelineFloat_refuses_laenge (d : FpDecodiert) (t : FpZustand)
    (h : laengeOk d.laenge = false) :
    fpSchritt d t = none :=
  fpSchritt_laenge_verweigert d t h

/-- A failed validator refuses: either `floatPipeOk` leg stops the run. -/
theorem pipelineFloat_refuses_validator (d : FpDecodiert) (t : FpZustand)
    (h : floatPipeOk t.fp d.laenge = false) :
    fpSchritt d t = none := by
  unfold floatPipeOk at h
  cases hl : laengeOk d.laenge with
  | false => exact fpSchritt_laenge_verweigert d t hl
  | true =>
    cases hm : mxcsrGueltig t.fp.mxcsr with
    | false =>
      have hf : fpEintritt t.fp = false := hm
      exact fpSchritt_profil_verweigert d t hl hf
    | true => simp_all

/-- An unreadable memory source refuses the load. -/
theorem pipelineFloat_refuses_lade (d : FpDecodiert) (t : FpZustand) (dst : XmmReg)
    (base : Register) (disp : BitVec 32)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .movsdLade dst base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = none) :
    fpSchritt d t = none :=
  fpSchritt_movsdLade_verweigert d t dst base disp hok hfp h hrd

/-- POISON PROBE (profile): under flush-to-zero the admitted divide refuses. -/
theorem pipelineFloat_probe_profil :
    fpSchritt ⟨.addsdRR XmmReg.xmm0 XmmReg.xmm1, 4⟩ { fpZeugeT with fp := ⟨0x9F80⟩ } = none := by
  have hf : fpEintritt ((⟨0x9F80⟩ : FPKontext)) = false := mxcsr_ftz_verweigert
  exact fpSchritt_profil_verweigert _ _ fpZeuge_laenge hf

/-- POISON PROBE (length): a 16-byte form refuses. -/
theorem pipelineFloat_probe_laenge :
    fpSchritt ⟨.addsdRR XmmReg.xmm0 XmmReg.xmm1, 16⟩ fpZeugeT = none := by
  have hl : laengeOk 16 = false := by decide
  exact fpSchritt_laenge_verweigert _ _ hl

/-! ## 6. Signed-zero and conversion witnesses, joint `_zeuge`.

  `+0.0 + -0.0` is `+0.0` at the source model, bit for bit; `42`
  converts to the `42.0` pattern. The joint witness instantiates
  every premise of `pipelineFloat_seq` (`div`, `xmm0`, `xmm1`, the
  witness state, `xmm1 ≠ xmm0`, checked length, admitted profile)
  and extends the reached run with a memory-changing store: the
  computed `+∞` lands at 8192 and reads back, with one observably
  changed byte. -/

/-- SIGNED-ZERO WITNESS: `+0.0 + -0.0` is `+0.0` in the source model,
    bit for bit. -/
theorem pipelineFloat_nullzeichen :
    muster64 (gleitRechne .add (bites64 0) (bites64 0x8000000000000000)) = 0 := by
  rw [← fpRechne_gleitRechne]
  exact add_plusnull_minusnull

/-- CONVERSION WITNESS: `42` converts to the `42.0` pattern. -/
theorem pipelineFloat_konv_zeuge :
    muster64 (gleitAusInt (42 : Wort).toInt) = 0x4045000000000000 :=
  cvtsiErg_42

/-- JOINT WITNESS: the lowered divide sequence computes `1.0 / +0.0`
    on the witness state, and the stored `+∞` observably changes
    memory -- two reached steps under the admitted profile. -/
theorem pipelineFloat_zeuge :
    ∃ t' t'' : FpZustand,
      laufFp [⟨.movsdRR XmmReg.xmm0 XmmReg.xmm0, 4⟩, ⟨senkGleitOp .div XmmReg.xmm0 XmmReg.xmm1, 4⟩] fpZeugeT = some t'
      ∧ fpSchritt ⟨.movsdSpeichere Register.rax XmmReg.xmm0 0, 4⟩ t' = some t''
      ∧ read64 t''.kern.speicher (BitVec.ofNat 64 8192) = some 0x7FF0000000000000
      ∧ fpZeugeT.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) ≠ t''.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) := by
  have hne : XmmReg.xmm1 ≠ XmmReg.xmm0 := by decide
  obtain ⟨t', hrun, hrip, hval, hfp', hmem0, hreg0⟩ :=
    pipelineFloat_seq GleitOp.div XmmReg.xmm0 XmmReg.xmm0 XmmReg.xmm1 fpZeugeT hne fpZeuge_laenge fpZeuge_fp
  have hvalinf : xmmTief t'.xmm XmmReg.xmm0 = 0x7FF0000000000000 := by
    rw [fpZeuge_tief0, fpZeuge_tief1] at hval
    have hinf : muster64 (gleitRechne .div (bites64 0x3FF0000000000000) (bites64 0)) = 0x7FF0000000000000 := by
      rw [← fpRechne_gleitRechne]
      exact div_eins_durch_null
    rw [hinf] at hval
    exact hval
  have hmem : t'.kern.speicher = zeugenSpeicher := hmem0.trans rfl
  have hrax : t'.kern.register Register.rax = fpZeugeT.kern.register Register.rax :=
    congrArg (· Register.rax) hreg0
  have heff : effAddr t'.kern Register.rax 0 = BitVec.ofNat 64 8192 := by
    unfold effAddr
    rw [hrax]
    exact fpZeuge_effAddr
  have hwr : write64 t'.kern.speicher (effAddr t'.kern Register.rax 0) (xmmTief t'.xmm XmmReg.xmm0) = some fpZeugeSpeicherNach := by
    rw [hmem, heff, hvalinf]
    unfold write64
    have hc : schreibbar8 zeugenSpeicher (BitVec.ofNat 64 8192) = true := rfl
    rw [if_pos hc]
    rfl
  have hfp2 : fpEintritt t'.fp = true := by
    rw [hfp']
    exact fpZeuge_fp
  have hstep2 := fpSchritt_movsdSpeichere_erfolg ⟨.movsdSpeichere Register.rax XmmReg.xmm0 0, 4⟩ t' Register.rax XmmReg.xmm0 0 fpZeugeSpeicherNach fpZeuge_laenge hfp2 rfl hwr
  have hliest : read64 fpZeugeSpeicherNach (BitVec.ofNat 64 8192) = some 0x7FF0000000000000 :=
    fpZeuge_liest
  refine ⟨t', _, hrun, hstep2, hliest, fpZeuge_speicher_aendert⟩

/- CUTS: what is not proved here.
  - No loaded image, no byte fetch, no relocation: `laufFp` runs
    constructed `FpDecodiert` values through `fpSchritt`, never bytes
    through a decoder. The byte connection is owned by
    `ScalarFloatCodec` (MOVSD/ADDSD subset) and the full
    source-to-final-loaded-byte closing theorem stays open.
  - No TSO/concurrency claim: `fpSchritt`/`laufFp` are sequential over
    one `Speicher`; the per-access target-to-W/GX bridge stays with
    the TSO-bridge lane.
  - No f32 lowering: `Ty.fl` is widthless binary64 in the source model
    (the named cut of GLEITKOMMA.md section 7), so a genuine binary32
    op has no source semantics to meet here; `konvBreiteOk` admits
    64-bit conversions only. NaN agreement is class-level
    (`fpRechne_klasse`); payload-bit equality of computed NaNs is
    never concluded.
  - No reassociation, contraction, fast-math, value-range propagation
    or cross-op rewrite is admitted: one source op is one machine op
    (`senkGleitOp`), one source comparison one `ucomisd`
    (`senkGleitCmp`). Sticky MXCSR flags, SNaN, costs and timing stay
    open (see the CUTS of `ScalarFloat` and `Gleitprofil`).
  - No second source interpreter and no optimiser change: the source
    side is named only through the accepted `gleitRechne`,
    `gleitAusInt`, `gleitRoh`, `gleitLt`/`gleitLe`, `bruch` and the
    `eval_fllt_ist_gleitLt` observation.
  - Rule 13 (inhabitation): no theorem here quantifies over the listed
    source-syntax types (`Vertrag`, `Stmt`, `Endblock`, `ErgExpr`,
    `Expr`, `Args`); `GleitOp`/`FloatCmp` range over the model op and
    the joint non-degenerate witness with a real memory change is
    `pipelineFloat_zeuge`.
-/

#print axioms pipelineFloat_seq
#print axioms pipelineFloat_cmp_schritt
#print axioms pipelineFloat_cmp_ungeordnet
#print axioms pipelineFloat_cmp_lt
#print axioms pipelineFloat_cmp_le
#print axioms pipelineFloat_von
#print axioms pipelineFloat_nach
#print axioms pipelineFloat_lit_rund
#print axioms konvBreiteOk_nur64
#print axioms pipelineFloat_refuses_profil
#print axioms pipelineFloat_refuses_laenge
#print axioms pipelineFloat_refuses_validator
#print axioms pipelineFloat_refuses_lade
#print axioms pipelineFloat_nullzeichen
#print axioms pipelineFloat_konv_zeuge
#print axioms pipelineFloat_zeuge

end Gabbro.Grammatik.X86.PipelineFloat
