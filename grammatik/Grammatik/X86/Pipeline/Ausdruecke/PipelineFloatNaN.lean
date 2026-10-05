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
import Grammatik.X86.Pipeline.Ausdruecke.PipelineFloat

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

/-! ## 6. Refusals: a NaN never saves a refused run.

  What this pipeline does NOT cover refuses explicitly: a refused
  MXCSR profile or a bad decode length stops the NaN sequence with
  `none`. Unsupported shapes are REFUSED, never guessed; NaN
  operands change nothing about admission. -/

/-- A refused profile refuses the NaN sequence at the first step. -/
theorem pipelineNaN_refuses_profil (op : GleitOp) (dst a b : XmmReg)
    (t : FpZustand)
    (hok : laengeOk 4 = true)
    (h : fpEintritt t.fp = false) :
    laufFp (senkNanSeq op dst a b) t = none := by
  have h1 : fpSchritt (⟨.movsdRR dst a, 4⟩ : FpDecodiert) t = none :=
    fpSchritt_profil_verweigert _ t hok h
  rw [senkNanSeq_klingt, laufFp_cons, h1]

/-- A bad decode length refuses the NaN sequence at the first step. -/
theorem pipelineNaN_refuses_laenge (op : GleitOp) (dst a b : XmmReg)
    (t : FpZustand)
    (h : laengeOk 4 = false) :
    laufFp (senkNanSeq op dst a b) t = none := by
  have h1 : fpSchritt (⟨.movsdRR dst a, 4⟩ : FpDecodiert) t = none :=
    fpSchritt_laenge_verweigert _ t h
  rw [senkNanSeq_klingt, laufFp_cons, h1]

/-- POISON PROBE (profile): the NaN sequence under flush-to-zero
    refuses -- the payload does not admit the run. -/
theorem pipelineNaN_probe_profil :
    laufFp (senkNanSeq .add XmmReg.xmm0 XmmReg.xmm0 XmmReg.xmm1)
      { fpZeugeT with fp := ⟨0x9F80⟩ } = none := by
  have hf : fpEintritt ((⟨0x9F80⟩ : FPKontext)) = false :=
    mxcsr_ftz_verweigert
  exact pipelineNaN_refuses_profil .add _ _ _ _ fpZeuge_laenge hf

/-- POISON PROBE (length): a 16-byte divide form refuses. -/
theorem pipelineNaN_probe_laenge :
    fpSchritt ⟨.divsdRR XmmReg.xmm0 XmmReg.xmm1, 16⟩ fpZeugeT = none := by
  have hl : laengeOk 16 = false := by decide
  exact fpSchritt_laenge_verweigert _ _ hl

/-! ## 7. Joint witness: a payload NaN computed, stored, read back.

  `xmm0` holds the quiet payload word `0x7FF8000000000001`, `xmm1`
  holds `1.0`; `rax` points at 8192 under the admitted profile. The
  lowered add sequence lands the payload word in `xmm0` verbatim
  (`pipelineNaN_nutzlast_links` via `pipelineNaN_seq`), the store
  writes it at 8192, it reads back, and one memory byte observably
  changed: a reached run with a real memory-changing step
  (non-degenerate: the payload word is nonzero and the footprint top
  byte moves `0x00` to `0x7F`). -/

/-- Witness XMM file: `xmm0` holds the payload NaN, `xmm1` holds `1.0`. -/
def nanZeugeXmm : XmmDatei :=
  fun q => if q = XmmReg.xmm0 then vecJoin 0x7FF8000000000001 0
    else if q = XmmReg.xmm1 then vecJoin 0x3FF0000000000000 0
    else vecJoin 0 0

/-- Witness state: `rax` at 8192, admitted profile. -/
def nanZeugeT : FpZustand := ⟨fpZeugeKern, nanZeugeXmm, kontextReset⟩

/-- The witness `xmm0` holds the payload NaN word. -/
theorem nanZeuge_tief0 :
    xmmTief nanZeugeT.xmm XmmReg.xmm0 = 0x7FF8000000000001 := by
  decide

/-- The witness `xmm1` holds `1.0`. -/
theorem nanZeuge_tief1 :
    xmmTief nanZeugeT.xmm XmmReg.xmm1 = 0x3FF0000000000000 := by
  decide

/-- Admitted profile on the witness state. -/
theorem nanZeuge_fp : fpEintritt nanZeugeT.fp = true := by
  decide

/-- Witness memory after the store: the payload word at 8192. -/
def nanZeugeSpeicherNach : Speicher :=
  { zeugenSpeicher with bytes := writeBytes zeugenSpeicher (BitVec.ofNat 64 8192) 0x7FF8000000000001 }

/-- The stored payload word reads back. -/
theorem nanZeuge_liest :
    read64 nanZeugeSpeicherNach (BitVec.ofNat 64 8192)
      = some 0x7FF8000000000001 := by
  have hrd : lesbar8 zeugenSpeicher (BitVec.ofNat 64 8192) = true := rfl
  have hwr0 : write64 zeugenSpeicher (BitVec.ofNat 64 8192)
      0x7FF8000000000001 = some nanZeugeSpeicherNach := by
    unfold write64
    have hc : schreibbar8 zeugenSpeicher (BitVec.ofNat 64 8192) = true := rfl
    rw [if_pos hc]
    rfl
  exact read64_nach_write64 _ _ _ _ hwr0 hrd

/-- The store observably changed memory (footprint top byte). -/
theorem nanZeuge_speicher_aendert :
    nanZeugeT.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) ≠
      nanZeugeSpeicherNach.bytes (addrOff (BitVec.ofNat 64 8192) 7) := by
  decide

/-- JOINT WITNESS: the lowered add sequence computes the payload NaN
    into `xmm0`, the store writes it at 8192, it reads back, and one
    memory byte observably changed -- a reached run with a real
    memory-changing step under the admitted profile. -/
theorem pipelineNaN_zeuge :
    ∃ t' t'' : FpZustand,
      laufFp (senkNanSeq .add XmmReg.xmm0 XmmReg.xmm0 XmmReg.xmm1)
          nanZeugeT = some t'
      ∧ fpSchritt ⟨.movsdSpeichere Register.rax XmmReg.xmm0 0, 4⟩ t'
          = some t''
      ∧ read64 t''.kern.speicher (BitVec.ofNat 64 8192)
          = some 0x7FF8000000000001
      ∧ nanZeugeT.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) ≠
          t''.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) := by
  have hne : XmmReg.xmm1 ≠ XmmReg.xmm0 := by decide
  obtain ⟨t', hrun, -, hval, hfp', hmem0, hreg0⟩ :=
    pipelineNaN_seq GleitOp.add XmmReg.xmm0 XmmReg.xmm0 XmmReg.xmm1
      nanZeugeT hne fpZeuge_laenge nanZeuge_fp
  have hvalnan : xmmTief t'.xmm XmmReg.xmm0 = 0x7FF8000000000001 := by
    rw [nanZeuge_tief0, nanZeuge_tief1] at hval
    have hprop : muster64 (gleitRechne GleitOp.add
        (bites64 0x7FF8000000000001) (bites64 0x3FF0000000000000))
        = 0x7FF8000000000001 := by
      show muster64 (Gleitkomma.add Gleitkomma.f64 _ _) = _
      rw [nanAdd_links _ _ nanKlasse_quiet, muster64_bites64]
    rw [hprop] at hval
    exact hval
  have hmem : t'.kern.speicher = zeugenSpeicher := hmem0.trans rfl
  have hrax : t'.kern.register Register.rax =
      nanZeugeT.kern.register Register.rax :=
    congrArg (· Register.rax) hreg0
  have heff : effAddr t'.kern Register.rax 0 = BitVec.ofNat 64 8192 := by
    unfold effAddr
    rw [hrax]
    exact fpZeuge_effAddr
  have hwr : write64 t'.kern.speicher (effAddr t'.kern Register.rax 0)
      (xmmTief t'.xmm XmmReg.xmm0) = some nanZeugeSpeicherNach := by
    rw [hmem, heff, hvalnan]
    unfold write64
    have hc : schreibbar8 zeugenSpeicher (BitVec.ofNat 64 8192) = true := rfl
    rw [if_pos hc]
    rfl
  have hfp2 : fpEintritt t'.fp = true := by
    rw [hfp']
    exact nanZeuge_fp
  have hstep2 := fpSchritt_movsdSpeichere_erfolg
    ⟨.movsdSpeichere Register.rax XmmReg.xmm0 0, 4⟩ t'
    Register.rax XmmReg.xmm0 0 nanZeugeSpeicherNach
    fpZeuge_laenge hfp2 rfl hwr
  refine ⟨t', _, hrun, hstep2, ?_, ?_⟩
  · exact nanZeuge_liest
  · exact nanZeuge_speicher_aendert

/- CUTS: what is not proved here.
  - No loaded image, no byte fetch, no relocation: runs go through
    `laufFp` over constructed `FpDecodiert` values, never bytes
    through a decoder. The byte connection stays owned by
    `ScalarFloatCodec` and the source-to-final-loaded-byte closing
    theorem stays open (same cut as lane 1161).
  - No TSO/concurrency claim: `fpSchritt`/`laufFp` are sequential
    over one `Speicher`; the per-access target-to-W/GX bridge stays
    with the TSO-bridge lane.
  - No f32 lowering: `Ty.fl` is widthless binary64 in the source
    model, so there is no binary32 node to admit here.
  - Silicon scope: the bit-exact agreement proved here is
    source-model (`gleitRechne`) against SSE2-model (`fpRechne`) --
    the SAME accepted model function on both sides, so payload
    propagation is verbatim by construction (§1-§2). Silicon SNaN
    quieting under a masked invalid exception is NOT modelled and
    NOT claimed (the accepted codecs define no quiet-bit
    discipline); the two-NaN operand-order choice is the named
    assumption `HwZweiNanWahl`, used by
    `silizium_zweiNan_bleibtNan` and never proved.
  - `sub` with a right NaN flips only the sign: the payload travels
    in `Gleitkomma.neg` (`nanNeg_nutzlast`), stated at model level
    and as `muster64 (neg …)` at word level -- no bare-word
    equation is claimed for it.
  - Pipeline right-side payload is proved for `add`
    (`pipelineNaN_nutzlast_rechts_add`); `mul`/`div`/`sub` right
    sides live at word level (§2) through the same rewrite.
  - No reassociation, contraction, fast-math or cross-op rewrite is
    admitted: one source op is one machine form (`senkGleitOp`,
    reused unchanged). Sticky MXCSR flags, SNaN traps, costs and
    timing stay open (see the CUTS of `ScalarFloat`/`Gleitprofil`).
  - No second source interpreter and no optimiser change: the source
    side is named only through the accepted `gleitRechne`.
  - Rule 13 (inhabitation): no theorem here quantifies over the
    listed source-syntax types (`Vertrag`, `Stmt`, `Endblock`,
    `ErgExpr`, `Expr`, `Args`); `GleitOp`/`FpBefehl` range over the
    model op and the target form. The joint non-degenerate witness
    with a real memory-changing step is `pipelineNaN_zeuge`
    (payload NaN computed, stored at 8192, read back, one
    observably changed byte).
-/

#print axioms nanPipeOk_reset
#print axioms nanAdd_links
#print axioms nanAdd_rechts
#print axioms nanMul_links
#print axioms nanMul_rechts
#print axioms nanDiv_links
#print axioms nanDiv_rechts
#print axioms nanSub_links
#print axioms nanSub_rechts
#print axioms nanNeg_nutzlast
#print axioms fpRechne_nan_links
#print axioms fpRechne_add_nan_rechts
#print axioms fpRechne_mul_nan_rechts
#print axioms fpRechne_div_nan_rechts
#print axioms fpRechne_sub_nan_rechts
#print axioms nanStill_quiet
#print axioms nanStill_signalisierend
#print axioms nanKlasse_quiet
#print axioms nanKlasse_signalisierend
#print axioms nanKlasse_nutzlast2
#print axioms nanKlasse_eins
#print axioms nanNutzlast_quiet_add
#print axioms nanNutzlast_signalisierend_add
#print axioms nanNutzlast_rechts_mul
#print axioms nanUcomi_signalisierend
#print axioms silizium_zweiNan_bleibtNan
#print axioms senkNanSeq_klingt
#print axioms nanPipeOk_zulaessig
#print axioms pipelineNaN_seq
#print axioms pipelineNaN_nutzlast_links
#print axioms pipelineNaN_nutzlast_rechts_add
#print axioms pipelineNaN_refuses_profil
#print axioms pipelineNaN_refuses_laenge
#print axioms pipelineNaN_probe_profil
#print axioms pipelineNaN_probe_laenge
#print axioms nanZeuge_tief0
#print axioms nanZeuge_tief1
#print axioms nanZeuge_fp
#print axioms nanZeuge_liest
#print axioms nanZeuge_speicher_aendert
#print axioms pipelineNaN_zeuge

#print axioms nanPipeOk_reset

end Gabbro.Grammatik.X86.PipelineFloatNaN
