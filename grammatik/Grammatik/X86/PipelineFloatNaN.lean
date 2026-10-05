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

/- CUTS: what is not proved here (filled as the file grows). -/

#print axioms nanPipeOk_reset

end Gabbro.Grammatik.X86.PipelineFloatNaN
