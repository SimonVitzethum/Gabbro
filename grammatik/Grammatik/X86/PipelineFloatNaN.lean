/-
  File:      Grammatik/X86/PipelineFloatNaN.lean
  Subject:   Pipeline float: NaN payload and bit-exact agreement.

  Lane 1201: follow-up of lane 1161 (`PipelineFloat.lean`), whose NaN
  agreement is class-level only (`fpRechne_klasse`; payload equality
  never concluded). This file states and proves bit-exact agreement
  of the source IEEE result (`gleitRechne`) and the SSE2 result
  (`fpRechne`) INCLUDING NaN payload propagation and quiet/signalling
  behaviour AS THE ACCEPTED CODECS DEFINE THEM (`Gleitkomma*.lean`,
  `ScalarFloat.lean`): the model propagates a NaN operand verbatim
  (`Gleitkomma.add/mul/div`: first NaN wins; `sub` via `neg`), with a
  single `.nan` class and no quiet-bit discipline. Where silicon
  leaves the two-NaN operand-order choice open, it is a NAMED
  hardware assumption (`HwZweiNanWahl`), never proved.

  Reused, not duplicated:
    - model ops: `Gleitkomma.add/sub/mul/div/neg`, `klasse_neg`,
      `nanQ`;
    - target steps: `fpRechne`/`fpRechne_gleitRechne`, `fpSchritt`
      with its `fpSchritt_*` equations, `muster64`/`bites64`,
      `muster64_bites64`, `ucomiFlags_ungeordnet_links`;
    - pipeline: `senkGleitOp`, `laufFp`, `floatPipeOk`,
      `pipelineFloat_seq` and the witness vocabulary (`fpZeugeT`,
      `read64_nach_write64`, `zeugenSpeicher`).
  No second source interpreter, no new IEEE model, no optimiser edit.
-/
import Grammatik.X86.PipelineFloat

namespace Gabbro.Grammatik.X86.PipelineFloatNaN

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.PipelineFloat

/-- Lower one float op as the admitted two-step NaN-carrying sequence:
    `movsd dst, a` then the accepted scalar SSE2 form against `b`. -/
def senkNanSeq (op : GleitOp) (dst a b : XmmReg) : List FpDecodiert :=
  [⟨.movsdRR dst a, 4⟩, ⟨senkGleitOp op dst b, 4⟩]

/-- The decided admission check of a NaN-carrying lowering: the accepted
    profile and decode length (`floatPipeOk`, reused unchanged). -/
def nanPipeOk (k : FPKontext) (len : Nat) : Bool :=
  floatPipeOk k len

/-- The reset context with a 4-byte form is admitted. -/
theorem nanPipeOk_reset : nanPipeOk kontextReset 4 = true :=
  floatPipeOk_reset

/-- LEFT NaN through `add`: the left operand wins bit-exactly. -/
theorem nanAdd_links (a b : GFloat)
    (ha : Gleitkomma.klasse Gleitkomma.f64 a = .nan) :
    Gleitkomma.add Gleitkomma.f64 a b = a := by
  unfold Gleitkomma.add
  rw [ha]

/-- RIGHT NaN through `add` (non-NaN left): the right operand wins. -/
theorem nanAdd_rechts (a b : GFloat)
    (hb : Gleitkomma.klasse Gleitkomma.f64 b = .nan)
    (ha : Gleitkomma.klasse Gleitkomma.f64 a ≠ .nan) :
    Gleitkomma.add Gleitkomma.f64 a b = b := by
  unfold Gleitkomma.add
  rw [hb]
  cases hka : Gleitkomma.klasse Gleitkomma.f64 a with
  | nan => exact absurd hka ha
  | unendlich => rfl
  | null => rfl
  | subnormal => rfl
  | normal => rfl

/-- LEFT NaN through `mul`: the left operand wins bit-exactly. -/
theorem nanMul_links (a b : GFloat)
    (ha : Gleitkomma.klasse Gleitkomma.f64 a = .nan) :
    Gleitkomma.mul Gleitkomma.f64 a b = a := by
  unfold Gleitkomma.mul
  rw [ha]

/-- RIGHT NaN through `mul` (non-NaN left): the right operand wins. -/
theorem nanMul_rechts (a b : GFloat)
    (hb : Gleitkomma.klasse Gleitkomma.f64 b = .nan)
    (ha : Gleitkomma.klasse Gleitkomma.f64 a ≠ .nan) :
    Gleitkomma.mul Gleitkomma.f64 a b = b := by
  unfold Gleitkomma.mul
  rw [hb]
  cases hka : Gleitkomma.klasse Gleitkomma.f64 a with
  | nan => exact absurd hka ha
  | unendlich => rfl
  | null => rfl
  | subnormal => rfl
  | normal => rfl

/-- LEFT NaN through `div`: the left operand wins bit-exactly. -/
theorem nanDiv_links (a b : GFloat)
    (ha : Gleitkomma.klasse Gleitkomma.f64 a = .nan) :
    Gleitkomma.div Gleitkomma.f64 a b = a := by
  unfold Gleitkomma.div
  rw [ha]

/-- RIGHT NaN through `div` (non-NaN left): the right operand wins. -/
theorem nanDiv_rechts (a b : GFloat)
    (hb : Gleitkomma.klasse Gleitkomma.f64 b = .nan)
    (ha : Gleitkomma.klasse Gleitkomma.f64 a ≠ .nan) :
    Gleitkomma.div Gleitkomma.f64 a b = b := by
  unfold Gleitkomma.div
  rw [hb]
  cases hka : Gleitkomma.klasse Gleitkomma.f64 a with
  | nan => exact absurd hka ha
  | unendlich => rfl
  | null => rfl
  | subnormal => rfl
  | normal => rfl

/-- LEFT NaN through `sub`: negation keeps the class, `add` takes left. -/
theorem nanSub_links (a b : GFloat)
    (ha : Gleitkomma.klasse Gleitkomma.f64 a = .nan) :
    Gleitkomma.sub Gleitkomma.f64 a b = a := by
  unfold Gleitkomma.sub
  exact nanAdd_links a _ ha

/-- RIGHT NaN through `sub` (non-NaN left): the negated right operand
    (sign flipped, payload intact -- see `nanNeg_nutzlast`). -/
theorem nanSub_rechts (a b : GFloat)
    (hb : Gleitkomma.klasse Gleitkomma.f64 b = .nan)
    (ha : Gleitkomma.klasse Gleitkomma.f64 a ≠ .nan) :
    Gleitkomma.sub Gleitkomma.f64 a b = Gleitkomma.neg Gleitkomma.f64 b := by
  unfold Gleitkomma.sub
  exact nanAdd_rechts a _ (by rw [Gleitkomma.klasse_neg]; exact hb) ha

/-- Negation keeps exponent and payload: only the sign flips. -/
theorem nanNeg_nutzlast (b : GFloat) :
    (Gleitkomma.neg Gleitkomma.f64 b).frac = b.frac ∧
      (Gleitkomma.neg Gleitkomma.f64 b).bexp = b.bexp := by
  unfold Gleitkomma.neg
  exact ⟨rfl, rfl⟩

/-! ## 2. Word-level bit-exact agreement: the SSE2 word IS the source word.

  `fpRechne_gleitRechne` already ties every word op to the source
  model op; here the NaN cases resolve to the operand WORD itself:
  payload, quiet bit and sign travel bit-exactly (`add`/`mul`/`div`
  on both sides, `sub` on the left; `sub` on the right flips only
  the sign, `nanNeg_nutzlast`). -/

/-- BIT-EXACT LEFT: with a NaN left word every lowered op returns the
    left word unchanged. -/
theorem fpRechne_nan_links (op : GleitOp) (a b : Wort)
    (ha : Gleitkomma.klasse Gleitkomma.f64 (bites64 a) = .nan) :
    fpRechne op a b = a := by
  cases op with
  | add =>
    show muster64 (Gleitkomma.add Gleitkomma.f64 (bites64 a) (bites64 b)) = a
    rw [nanAdd_links _ _ ha, muster64_bites64]
  | sub =>
    show muster64 (Gleitkomma.sub Gleitkomma.f64 (bites64 a) (bites64 b)) = a
    rw [nanSub_links _ _ ha, muster64_bites64]
  | mul =>
    show muster64 (Gleitkomma.mul Gleitkomma.f64 (bites64 a) (bites64 b)) = a
    rw [nanMul_links _ _ ha, muster64_bites64]
  | div =>
    show muster64 (Gleitkomma.div Gleitkomma.f64 (bites64 a) (bites64 b)) = a
    rw [nanDiv_links _ _ ha, muster64_bites64]

/-- BIT-EXACT RIGHT (`add`): a NaN right word comes back unchanged. -/
theorem fpRechne_add_nan_rechts (a b : Wort)
    (hb : Gleitkomma.klasse Gleitkomma.f64 (bites64 b) = .nan)
    (ha : Gleitkomma.klasse Gleitkomma.f64 (bites64 a) ≠ .nan) :
    fpRechne .add a b = b := by
  show muster64 (Gleitkomma.add Gleitkomma.f64 (bites64 a) (bites64 b)) = b
  rw [nanAdd_rechts _ _ hb ha, muster64_bites64]

/-- BIT-EXACT RIGHT (`mul`): a NaN right word comes back unchanged. -/
theorem fpRechne_mul_nan_rechts (a b : Wort)
    (hb : Gleitkomma.klasse Gleitkomma.f64 (bites64 b) = .nan)
    (ha : Gleitkomma.klasse Gleitkomma.f64 (bites64 a) ≠ .nan) :
    fpRechne .mul a b = b := by
  show muster64 (Gleitkomma.mul Gleitkomma.f64 (bites64 a) (bites64 b)) = b
  rw [nanMul_rechts _ _ hb ha, muster64_bites64]

/-- BIT-EXACT RIGHT (`div`): a NaN right word comes back unchanged. -/
theorem fpRechne_div_nan_rechts (a b : Wort)
    (hb : Gleitkomma.klasse Gleitkomma.f64 (bites64 b) = .nan)
    (ha : Gleitkomma.klasse Gleitkomma.f64 (bites64 a) ≠ .nan) :
    fpRechne .div a b = b := by
  show muster64 (Gleitkomma.div Gleitkomma.f64 (bites64 a) (bites64 b)) = b
  rw [nanDiv_rechts _ _ hb ha, muster64_bites64]

/-- SUB RIGHT: the SSE2 word is the injected sign-flipped right
    operand (payload intact by `nanNeg_nutzlast`). -/
theorem fpRechne_sub_nan_rechts (a b : Wort)
    (hb : Gleitkomma.klasse Gleitkomma.f64 (bites64 b) = .nan)
    (ha : Gleitkomma.klasse Gleitkomma.f64 (bites64 a) ≠ .nan) :
    fpRechne .sub a b
      = muster64 (Gleitkomma.neg Gleitkomma.f64 (bites64 b)) := by
  show muster64 (Gleitkomma.sub Gleitkomma.f64 (bites64 a) (bites64 b)) = _
  rw [nanSub_rechts _ _ hb ha]

/-! ## 3. Quiet and signalling as the accepted codecs define them.

  The codecs define NO distinction: `Klasse` carries a single `.nan`,
  propagation is verbatim whatever the quiet bit says, and UCOMISD
  takes the unordered row for every NaN-class operand (ScalarFloat
  §5: "quiet or signalling -- the model has a single `.nan`, so no
  signalling bit is observed anywhere"). The quiet bit (bit 51, the
  MSB of the 52-bit payload field) is named here only to state what
  is IGNORED: a signalling-like word (quiet bit clear) passes
  through unquieted -- silicon quieting under a masked invalid
  exception is NOT modelled and NOT claimed (see CUTS and §4). -/

/-- The quiet bit of a binary64 word: bit 51, MSB of the payload field. -/
def nanStill (w : Wort) : Bool := w.toNat.testBit 51

/-- The canonical quiet NaN word carries its quiet bit. -/
theorem nanStill_quiet : nanStill 0x7FF8000000000001 = true := by
  decide

/-- The signalling-like NaN word clears it. -/
theorem nanStill_signalisierend : nanStill 0x7FF4000000000001 = false := by
  decide

/-- The quiet payload word classifies as NaN. -/
theorem nanKlasse_quiet :
    Gleitkomma.klasse Gleitkomma.f64 (bites64 0x7FF8000000000001) = .nan := by
  decide

/-- The signalling-like word classifies as NaN too: the class ignores
    the quiet bit. -/
theorem nanKlasse_signalisierend :
    Gleitkomma.klasse Gleitkomma.f64 (bites64 0x7FF4000000000001) = .nan := by
  decide

/-- A second payload classifies as NaN (right-side witness below). -/
theorem nanKlasse_nutzlast2 :
    Gleitkomma.klasse Gleitkomma.f64 (bites64 0x7FF8000000000002) = .nan := by
  decide

/-- `1.0` is not NaN (the non-NaN side of the witnesses). -/
theorem nanKlasse_eins :
    Gleitkomma.klasse Gleitkomma.f64 (bites64 0x3FF0000000000000) ≠ .nan := by
  decide

/-- QUIET PAYLOAD WITNESS: the payload word comes back bit-exact. -/
theorem nanNutzlast_quiet_add :
    fpRechne .add 0x7FF8000000000001 0x3FF0000000000000
      = 0x7FF8000000000001 :=
  fpRechne_nan_links .add _ _ nanKlasse_quiet

/-- SIGNALLING-LIKE WITNESS: no quieting in the model -- the word
    passes through with its quiet bit still clear. -/
theorem nanNutzlast_signalisierend_add :
    fpRechne .add 0x7FF4000000000001 0x3FF0000000000000
      = 0x7FF4000000000001 :=
  fpRechne_nan_links .add _ _ nanKlasse_signalisierend

/-- RIGHT-SIDE PAYLOAD WITNESS: the right payload wins bit-exact. -/
theorem nanNutzlast_rechts_mul :
    fpRechne .mul 0x3FF0000000000000 0x7FF8000000000002
      = 0x7FF8000000000002 :=
  fpRechne_mul_nan_rechts _ _ nanKlasse_nutzlast2 nanKlasse_eins

/-- UCOMISD is unordered for the signalling-like word too: the quiet
    bit is observed by nothing. -/
theorem nanUcomi_signalisierend :
    ucomiFlags (bites64 0x7FF4000000000001) (bites64 0x3FF0000000000000)
      = ⟨true, true, some false, true, false, false⟩ :=
  ucomiFlags_ungeordnet_links _ _ nanKlasse_signalisierend

/-! ## 4. Named hardware assumption: the two-NaN operand-order choice.

  The model resolves two NaN operands deterministically (first wins,
  §1). Silicon leaves the choice open: with two NaN inputs the
  answer is one of the two input words, but WHICH one is
  implementation-defined. This is stated as the named assumption
  `HwZweiNanWahl` over an abstract silicon function and USED (the
  two-NaN answer still classifies NaN), never proved: no theorem
  here concludes the assumption itself. -/

/-- NAMED HARDWARE ASSUMPTION (never proved here): with two NaN
    operands silicon answers one of the two input words. -/
def HwZweiNanWahl (silizium : GleitOp → Wort → Wort → Wort) : Prop :=
  ∀ op a b,
    Gleitkomma.klasse Gleitkomma.f64 (bites64 a) = .nan →
      Gleitkomma.klasse Gleitkomma.f64 (bites64 b) = .nan →
        silizium op a b = a ∨ silizium op a b = b

/-- Under the assumption a two-NaN silicon answer still classifies
    NaN, whichever operand silicon picks. -/
theorem silizium_zweiNan_bleibtNan
    (silizium : GleitOp → Wort → Wort → Wort)
    (hHw : HwZweiNanWahl silizium) (op : GleitOp) (a b : Wort)
    (ha : Gleitkomma.klasse Gleitkomma.f64 (bites64 a) = .nan)
    (hb : Gleitkomma.klasse Gleitkomma.f64 (bites64 b) = .nan) :
    Gleitkomma.klasse Gleitkomma.f64 (bites64 (silizium op a b)) = .nan := by
  rcases hHw op a b ha hb with h | h
  · rw [h]; exact ha
  · rw [h]; exact hb

/-! ## 5. Pipeline sequence: the lowered NaN run computes the source word.

  `senkNanSeq` is the accepted two-step sequence; `pipelineNaN_seq`
  ties its run to the source model result bit for bit (in the style
  of `pipeline_correct_entry`: source `execBlock`-level value related
  to the run on the lowered forms). The payload corollaries resolve
  the conclusion to the operand WORD: a NaN in `a` lands in `dst`
  for every op; a NaN in `b` (healthy `a`) lands in `dst` for `add`
  (the word level §2 covers `mul`/`div`, `sub` flips only the sign).
  NaN operands are never a refusal reason: the sequence reaches
  `some` under the admitted profile. -/

/-- The NaN sequence IS the accepted two-step float sequence. -/
theorem senkNanSeq_klingt (op : GleitOp) (dst a b : XmmReg) :
    senkNanSeq op dst a b
      = [⟨.movsdRR dst a, 4⟩, ⟨senkGleitOp op dst b, 4⟩] :=
  rfl

/-- The NaN admission check unpacks to the profile and the length. -/
theorem nanPipeOk_zulaessig (k : FPKontext) (len : Nat)
    (h : nanPipeOk k len = true) :
    mxcsrGueltig k.mxcsr = true ∧ laengeOk len = true := by
  unfold nanPipeOk floatPipeOk at h
  cases hm : mxcsrGueltig k.mxcsr with
  | false => simp [hm] at h
  | true =>
    cases hl : laengeOk len with
    | false => simp [hl] at h
    | true => exact ⟨rfl, rfl⟩

/-- THE NaN SEQUENCE: the lowered two-step run reaches a successor
    whose `dst` holds the exact source model result bit for bit. -/
theorem pipelineNaN_seq (op : GleitOp) (dst a b : XmmReg) (t : FpZustand)
    (hne : b ≠ dst)
    (hok : laengeOk 4 = true)
    (hfp : fpEintritt t.fp = true) :
    ∃ t' : FpZustand,
      laufFp (senkNanSeq op dst a b) t = some t'
      ∧ t'.kern.rip = ripNach (ripNach t.kern.rip 4) 4
      ∧ xmmTief t'.xmm dst
          = muster64 (gleitRechne op (bites64 (xmmTief t.xmm a))
              (bites64 (xmmTief t.xmm b)))
      ∧ t'.fp = t.fp
      ∧ t'.kern.speicher = t.kern.speicher
      ∧ t'.kern.register = t.kern.register := by
  rw [senkNanSeq_klingt]
  exact pipelineFloat_seq op dst a b t hne hok hfp

/-- PIPELINE PAYLOAD LEFT: with a NaN in `a` the run lands `a`'s word
    in `dst`, for every op. -/
theorem pipelineNaN_nutzlast_links (op : GleitOp) (dst a b : XmmReg)
    (t : FpZustand)
    (hne : b ≠ dst)
    (hok : laengeOk 4 = true)
    (hfp : fpEintritt t.fp = true)
    (ha : Gleitkomma.klasse Gleitkomma.f64 (bites64 (xmmTief t.xmm a))
      = .nan) :
    ∃ t' : FpZustand,
      laufFp (senkNanSeq op dst a b) t = some t'
      ∧ xmmTief t'.xmm dst = xmmTief t.xmm a := by
  obtain ⟨t', hrun, -, hval, -, -, -⟩ :=
    pipelineNaN_seq op dst a b t hne hok hfp
  refine ⟨t', hrun, ?_⟩
  rw [hval, ← fpRechne_gleitRechne, fpRechne_nan_links _ _ _ ha]

/-- PIPELINE PAYLOAD RIGHT (`add`): with a NaN in `b` and a healthy
    `a` the run lands `b`'s word in `dst`. -/
theorem pipelineNaN_nutzlast_rechts_add (dst a b : XmmReg) (t : FpZustand)
    (hne : b ≠ dst)
    (hok : laengeOk 4 = true)
    (hfp : fpEintritt t.fp = true)
    (hb : Gleitkomma.klasse Gleitkomma.f64 (bites64 (xmmTief t.xmm b))
      = .nan)
    (ha : Gleitkomma.klasse Gleitkomma.f64 (bites64 (xmmTief t.xmm a))
      ≠ .nan) :
    ∃ t' : FpZustand,
      laufFp (senkNanSeq .add dst a b) t = some t'
      ∧ xmmTief t'.xmm dst = xmmTief t.xmm b := by
  obtain ⟨t', hrun, -, hval, -, -, -⟩ :=
    pipelineNaN_seq .add dst a b t hne hok hfp
  refine ⟨t', hrun, ?_⟩
  rw [hval, ← fpRechne_gleitRechne, fpRechne_add_nan_rechts _ _ hb ha]

/- CUTS: what is not proved here (filled as the file grows). -/

#print axioms nanPipeOk_reset

end Gabbro.Grammatik.X86.PipelineFloatNaN
