/-
  File:      Grammatik/X86/ScalarFloat.lean
  Subject:   Scalar SSE2 double-precision forms over the canonical x86 vocabulary.

  Lane 340 (wave A6): scalar SSE2 DOUBLE forms only
  (ADDSD/SUBSD/MULSD/DIVSD/UCOMISD/CVTSI2SD/CVTTSD2SI+wrapper/MOVSD) over the
  SAME canonical vocabulary (`Typen`: `Zustand`/`Register`/`Flags`;
  `Speicher`: `read64`/`write64`; `Vektor`: `vLo`/`vHi`/`vecJoin`;
  `Gleitprofil`: `mxcsrGueltig`/`muster64`/`bites64`/f64 arithmetic;
  `Ausfuehrung`: `ripNach`/`laengeOk`/`effAddr`), with the checked
  `mxcsrGueltig` premise on every step. No `Befehl` constructor is added or
  changed; the existing 14-form `schritt` is never redefined (extension
  interface in §1 lifts it onto the extended state instead).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Vektor
import Grammatik.X86.Gleitprofil
import Grammatik.X86.Ausfuehrung
import Grammatik.Syntax
import Grammatik.Semantik

namespace Gabbro.Grammatik.X86

/-- The sixteen scalar FP registers. Scalar DOUBLE forms compute on the low
    64 bits (`vLo`); the high 64 bits (`vHi`) are preserved (legacy SSE
    semantics -- VEX zeroing does not exist here, AVX is deferred). -/
inductive XmmReg where
  | xmm0 | xmm1 | xmm2 | xmm3 | xmm4 | xmm5 | xmm6 | xmm7
  | xmm8 | xmm9 | xmm10 | xmm11 | xmm12 | xmm13 | xmm14 | xmm15
  deriving DecidableEq, Repr, Inhabited

/-- Scalar FP register file: each entry is a full 128-bit word. -/
abbrev XmmDatei := XmmReg → Vektor

/-! ## 1. XMM file helpers and the extension interface.

  The one target semantics (`Ausfuehrung.schritt` over the 14 pilot `Befehl`
  constructors) is extended WITHOUT redefining it: `FpZustand` pairs the
  canonical `Zustand` with the XMM file and the per-context FP control word,
  and `laufAlt` runs the OLD step on the `kern` half, leaving XMM and MXCSR
  untouched. New scalar FP forms live in `fpSchritt` (§3) on a SEPARATE
  instruction type -- there is no second evaluator of the 14 old forms. -/

/-- XMM register-file update: `dst` holds `v`, every other register kept. -/
def xmmSet (f : XmmDatei) (dst : XmmReg) (v : Vektor) : XmmDatei :=
  fun q => if q = dst then v else f q

/-- The updated XMM register answers `v` at `dst`. -/
theorem xmmSet_gleich (f : XmmDatei) (dst : XmmReg) (v : Vektor) :
    xmmSet f dst v dst = v := by
  simp [xmmSet]

/-- Every other XMM register keeps its value. -/
theorem xmmSet_fremd (f : XmmDatei) (dst q : XmmReg) (v : Vektor)
    (h : q ≠ dst) : xmmSet f dst v q = f q := by
  unfold xmmSet
  rw [if_neg h]

/-- The scalar double a register carries: the low 64 bits as a word. -/
def xmmTief (f : XmmDatei) (r : XmmReg) : Wort := vLo (f r)

/-- The preserved upper half of a register. -/
def xmmHoch (f : XmmDatei) (r : XmmReg) : Wort := vHi (f r)

/-- Scalar write: the low 64 bits become `w`, the high 64 bits are kept
    (legacy SSE `xmm,xmm` and arithmetic behaviour; loads zero the high
    half explicitly at their own site, §3). -/
def xmmSchreibeTief (f : XmmDatei) (dst : XmmReg) (w : Wort) : XmmDatei :=
  xmmSet f dst (vecJoin w (xmmHoch f dst))

/-- Splitting a joined word recovers the low half. -/
theorem vLo_vecJoin (lo hi : Wort) : vLo (vecJoin lo hi) = lo := by
  apply BitVec.eq_of_toNat_eq
  unfold vLo vecJoin
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hlo := lo.isLt
  have hhi := hi.isLt
  have hbound : lo.toNat + hi.toNat * 2 ^ 64 < 2 ^ 128 := by
    have h128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by rw [← Nat.pow_add]
    have h1 : hi.toNat * 2 ^ 64 < 2 ^ 64 * 2 ^ 64 :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by decide : 0 < 2 ^ 64)
    omega
  rw [Nat.mod_eq_of_lt hbound, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hlo]

/-- Splitting a joined word recovers the high half. -/
theorem vHi_vecJoin (lo hi : Wort) : vHi (vecJoin lo hi) = hi := by
  apply BitVec.eq_of_toNat_eq
  unfold vHi vecJoin
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hlo := lo.isLt
  have hhi := hi.isLt
  have hbound : lo.toNat + hi.toNat * 2 ^ 64 < 2 ^ 128 := by
    have h128 : (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by rw [← Nat.pow_add]
    have h1 : hi.toNat * 2 ^ 64 < 2 ^ 64 * 2 ^ 64 :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by decide : 0 < 2 ^ 64)
    omega
  rw [Nat.mod_eq_of_lt hbound,
    Nat.add_mul_div_right _ _ (by decide : 0 < 2 ^ 64),
    Nat.div_eq_of_lt hlo, Nat.zero_add,
    Nat.mod_eq_of_lt hhi]

/-- A scalar write installs `w` in the low half. -/
theorem xmmSchreibeTief_tief (f : XmmDatei) (dst : XmmReg) (w : Wort) :
    xmmTief (xmmSchreibeTief f dst w) dst = w := by
  unfold xmmTief xmmSchreibeTief xmmHoch
  rw [xmmSet_gleich, vLo_vecJoin]

/-- A scalar write keeps the high half. -/
theorem xmmSchreibeTief_hoch (f : XmmDatei) (dst : XmmReg) (w : Wort) :
    xmmHoch (xmmSchreibeTief f dst w) dst = xmmHoch f dst := by
  unfold xmmHoch xmmSchreibeTief
  rw [xmmSet_gleich, vHi_vecJoin]
  rfl

/-- A scalar write keeps every other register whole. -/
theorem xmmSchreibeTief_fremd (f : XmmDatei) (dst q : XmmReg) (w : Wort)
    (h : q ≠ dst) : (xmmSchreibeTief f dst w) q = f q := by
  unfold xmmSchreibeTief
  exact xmmSet_fremd f dst q _ h

/-- The extended target state: the canonical core plus the XMM file and the
    per-context FP control word. `Zustand` itself is never changed. -/
structure FpZustand where
  kern : Zustand
  xmm : XmmDatei
  fp : FPKontext

/-- Lift a canonical state into the extended state. -/
def hebeHoch (s : Zustand) (f : XmmDatei) (k : FPKontext) : FpZustand :=
  ⟨s, f, k⟩

/-- The old step on the extended state: `schritt` runs on `kern`, XMM and
    MXCSR are untouched. This is how the one target semantics is extended;
    old forms keep exactly their old meaning. -/
def laufAlt (d : Decodiert) (t : FpZustand) : Option FpZustand :=
  match schritt d t.kern with
  | some s' => some { t with kern := s' }
  | none => none

/-- The lifted old step changes no XMM register. -/
theorem laufAlt_xmm (d : Decodiert) (t : FpZustand) (s' : Zustand)
    (h : schritt d t.kern = some s') (q : XmmReg) :
    (laufAlt d t).map (fun u => u.xmm q) = some (t.xmm q) := by
  unfold laufAlt
  rw [h]
  rfl

/-- The lifted old step keeps the FP control word. -/
theorem laufAlt_fp (d : Decodiert) (t : FpZustand) (s' : Zustand)
    (h : schritt d t.kern = some s') :
    (laufAlt d t).map (fun u => u.fp) = some t.fp := by
  unfold laufAlt
  rw [h]
  rfl

/-- The lifted old step reaches the old successor on `kern`. -/
theorem laufAlt_kern (d : Decodiert) (t : FpZustand) (s' : Zustand)
    (h : schritt d t.kern = some s') :
    (laufAlt d t).map (fun u => u.kern) = some s' := by
  unfold laufAlt
  rw [h]
  rfl

/-! ## 2. Scalar SSE2 DOUBLE instruction forms (admission data).

  Register operands are XMM; memory operands reuse the canonical
  base-plus-displacement addressing (`effAddr`) over the GPR file, with
  actual (unaligned-tolerant) `read64`/`write64` behaviour -- MOVSD imposes
  no alignment requirement, matching silicon. Only DOUBLE (`SD`) forms
  exist here; every other encoding is a `FpVerweigert` (§5). -/

/-- Scalar DOUBLE forms: four arithmetic (register and memory source),
    unordered compare (register and memory source), the two conversions,
    and the three MOVSD moves. -/
inductive FpBefehl where
  | addsdRR (dst src : XmmReg)
  | subsdRR (dst src : XmmReg)
  | mulsdRR (dst src : XmmReg)
  | divsdRR (dst src : XmmReg)
  | addsdRM (dst : XmmReg) (base : Register) (disp : BitVec 32)
  | subsdRM (dst : XmmReg) (base : Register) (disp : BitVec 32)
  | mulsdRM (dst : XmmReg) (base : Register) (disp : BitVec 32)
  | divsdRM (dst : XmmReg) (base : Register) (disp : BitVec 32)
  | ucomisdRR (lhs rhs : XmmReg)
  | ucomisdRM (lhs : XmmReg) (base : Register) (disp : BitVec 32)
  | cvtsi2sd (dst : XmmReg) (src : Register)
  | cvttsd2si (dst : Register) (src : XmmReg)
  | movsdRR (dst src : XmmReg)
  | movsdLade (dst : XmmReg) (base : Register) (disp : BitVec 32)
  | movsdSpeichere (base : Register) (src : XmmReg) (disp : BitVec 32)
  deriving DecidableEq, Repr

/-- A decoded scalar FP instruction: the form plus its decode length
    (checked `1..15` data, exactly as the pilot `Decodiert`). -/
structure FpDecodiert where
  befehl : FpBefehl
  laenge : Nat
  deriving DecidableEq, Repr

/-- Profile admission at the control word: the checked `mxcsrGueltig`
    premise. `false` is a VALIDATOR refusal (the image is not admitted
    under the ESSENTIAL f64 profile), never a hardware fault: actual
    silicon with a deviating MXCSR computes something this file does
    not model. -/
def fpEintritt (k : FPKontext) : Bool := mxcsrGueltig k.mxcsr

/-- The reset control word is admitted. -/
theorem fpEintritt_reset : fpEintritt kontextReset = true := by
  unfold fpEintritt
  exact kontextReset_gueltig

/-- One machine DOUBLE op: the model op at binary64, back as a word.
    Each `GleitOp` names exactly one model op (policy: one source op =
    one machine op; §4 proves this is `gleitRechne`). -/
def fpRechne : Gabbro.Grammatik.GleitOp → Wort → Wort → Wort
  | .add, a, b => muster64 (fadd64 (bites64 a) (bites64 b))
  | .sub, a, b => muster64 (fsub64 (bites64 a) (bites64 b))
  | .mul, a, b => muster64 (fmul64 (bites64 a) (bites64 b))
  | .div, a, b => muster64 (fdiv64 (bites64 a) (bites64 b))

/-- UCOMISD flag result over two model doubles: ZF/PF/CF per the
    architecture (unordered NaN operand: all three set; greater: none;
    less: CF; equal: ZF). OF/SF/AF are cleared -- AF as `some false`
    (defined zero, unlike XOR's undefined `none`). -/
def ucomiFlags (a b : Gleitkomma.GBits Gleitkomma.f64) : Flags :=
  match Gleitkomma.klasse Gleitkomma.f64 a, Gleitkomma.klasse Gleitkomma.f64 b with
  | .nan, _ => ⟨true, true, some false, true, false, false⟩
  | _, .nan => ⟨true, true, some false, true, false, false⟩
  | _, _ =>
    if Gleitkomma.flt Gleitkomma.f64 a b then ⟨true, false, some false, false, false, false⟩
    else if Gleitkomma.flt Gleitkomma.f64 b a then ⟨false, false, some false, false, false, false⟩
    else ⟨false, false, some false, true, false, false⟩

/-- CVTSI2SD result: the signed 64-bit GPR value as a binary64 model
    value (the source `gleitAusInt` at the machine; §4 proves the link). -/
def cvtsiErg (w : Wort) : Gleitkomma.GBits Gleitkomma.f64 :=
  Gleitkomma.ofInt Gleitkomma.f64 w.toInt

/-- A wrapped integer as a word: two's complement modulo `2^64`. -/
def intWort (n : Int) : Wort := BitVec.ofNat 64 (n % (2 ^ 64 : Int)).toNat

/-- CVTTSD2SI wrapper at `Int` level: hardware-invalid (NaN, infinity)
    is decided from the CLASS first -- the silicon "integer indefinite"
    case -- then truncation toward zero with saturation, exactly the
    shape of the source `gleitRoh` (§4 proves the equality). -/
def cvttPaket (w : Wort) : Int :=
  let x := bites64 w
  match Gleitkomma.klasse Gleitkomma.f64 x with
  | .nan => 0
  | .unendlich => 0
  | _ =>
    match Gleitkomma.wertExakt Gleitkomma.f64 x with
    | Option.none => 0
    | Option.some v =>
      let t : Int := if 0 ≤ v.zweierExp then v.zaehler * ((2 ^ v.zweierExp.toNat : Nat) : Int)
        else v.zaehler.tdiv ((2 ^ (-v.zweierExp).toNat : Nat) : Int)
      if t < -(2 ^ 63 : Int) then -(2 ^ 63 : Int)
      else if (2 ^ 63 - 1 : Int) < t then 2 ^ 63 - 1 else t

/-! ## 3. Scalar FP step semantics.

  `fpSchritt` steps ONLY the §2 forms on the extended state. Guards, in
  order: decode length (`laengeOk`, checked data), profile admission
  (`fpEintritt`, validator refusal), memory permission (`read64`/`write64`
  `none`). Arithmetic writes the low half and keeps the high half;
  UCOMISD writes only flags (OF/SF/AF cleared); MOVSD preserves flags;
  loads zero the high half; RIP advances past the decode length. -/

/-- Single scalar FP step; `none` is an explicit refusal (bad length,
    refused profile, or failed memory access). -/
def fpSchritt (d : FpDecodiert) (t : FpZustand) : Option FpZustand :=
  match laengeOk d.laenge with
  | false => none
  | true =>
    match fpEintritt t.fp with
    | false => none
    | true =>
      let nach := ripNach t.kern.rip d.laenge
      match d.befehl with
      | .addsdRR dst src =>
        let w := fpRechne .add (xmmTief t.xmm dst) (xmmTief t.xmm src)
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSchreibeTief t.xmm dst w }
      | .subsdRR dst src =>
        let w := fpRechne .sub (xmmTief t.xmm dst) (xmmTief t.xmm src)
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSchreibeTief t.xmm dst w }
      | .mulsdRR dst src =>
        let w := fpRechne .mul (xmmTief t.xmm dst) (xmmTief t.xmm src)
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSchreibeTief t.xmm dst w }
      | .divsdRR dst src =>
        let w := fpRechne .div (xmmTief t.xmm dst) (xmmTief t.xmm src)
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSchreibeTief t.xmm dst w }
      | .addsdRM dst base disp =>
        match read64 t.kern.speicher (effAddr t.kern base disp) with
        | some v =>
          let w := fpRechne .add (xmmTief t.xmm dst) v
          some { t with kern := { t.kern with rip := nach }, xmm := xmmSchreibeTief t.xmm dst w }
        | none => none
      | .subsdRM dst base disp =>
        match read64 t.kern.speicher (effAddr t.kern base disp) with
        | some v =>
          let w := fpRechne .sub (xmmTief t.xmm dst) v
          some { t with kern := { t.kern with rip := nach }, xmm := xmmSchreibeTief t.xmm dst w }
        | none => none
      | .mulsdRM dst base disp =>
        match read64 t.kern.speicher (effAddr t.kern base disp) with
        | some v =>
          let w := fpRechne .mul (xmmTief t.xmm dst) v
          some { t with kern := { t.kern with rip := nach }, xmm := xmmSchreibeTief t.xmm dst w }
        | none => none
      | .divsdRM dst base disp =>
        match read64 t.kern.speicher (effAddr t.kern base disp) with
        | some v =>
          let w := fpRechne .div (xmmTief t.xmm dst) v
          some { t with kern := { t.kern with rip := nach }, xmm := xmmSchreibeTief t.xmm dst w }
        | none => none
      | .ucomisdRR lhs rhs =>
        let f := ucomiFlags (bites64 (xmmTief t.xmm lhs)) (bites64 (xmmTief t.xmm rhs))
        some { t with kern := { t.kern with rip := nach, flags := f } }
      | .ucomisdRM lhs base disp =>
        match read64 t.kern.speicher (effAddr t.kern base disp) with
        | some v =>
          let f := ucomiFlags (bites64 (xmmTief t.xmm lhs)) (bites64 v)
          some { t with kern := { t.kern with rip := nach, flags := f } }
        | none => none
      | .cvtsi2sd dst src =>
        let w := muster64 (cvtsiErg (t.kern.register src))
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSchreibeTief t.xmm dst w }
      | .cvttsd2si dst src =>
        let w := intWort (cvttPaket (xmmTief t.xmm src))
        some { t with kern := { t.kern with register := regSet t.kern.register dst w, rip := nach } }
      | .movsdRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSchreibeTief t.xmm dst (xmmTief t.xmm src) }
      | .movsdLade dst base disp =>
        match read64 t.kern.speicher (effAddr t.kern base disp) with
        | some v =>
          some { t with kern := { t.kern with rip := nach }, xmm := xmmSet t.xmm dst (vecJoin v 0) }
        | none => none
      | .movsdSpeichere base src disp =>
        match write64 t.kern.speicher (effAddr t.kern base disp) (xmmTief t.xmm src) with
        | some m => some { t with kern := { t.kern with speicher := m, rip := nach } }
        | none => none

/-! ## Step equations: guards, arithmetic, and their frames.

  Each equation pins the full successor; every premise is used. -/

/-- A bad decode length refuses every scalar FP form. -/
theorem fpSchritt_laenge_verweigert (d : FpDecodiert) (t : FpZustand)
    (h : laengeOk d.laenge = false) : fpSchritt d t = none := by
  unfold fpSchritt
  simp [h]

/-- A refused profile refuses every scalar FP form (validator admission,
    not a hardware fault). -/
theorem fpSchritt_profil_verweigert (d : FpDecodiert) (t : FpZustand)
    (hok : laengeOk d.laenge = true) (h : fpEintritt t.fp = false) :
    fpSchritt d t = none := by
  unfold fpSchritt
  simp [hok, h]

/-- `addsd` (register): the low half holds the model sum. -/
theorem fpSchritt_addsdRR (d : FpDecodiert) (t : FpZustand)
    (dst src : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .addsdRR dst src) :
    fpSchritt d t =
      some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSchreibeTief t.xmm dst (fpRechne .add (xmmTief t.xmm dst) (xmmTief t.xmm src)) } := by
  unfold fpSchritt
  simp [hok, hfp, h]

/-- `subsd` (register): the low half holds the model difference. -/
theorem fpSchritt_subsdRR (d : FpDecodiert) (t : FpZustand)
    (dst src : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .subsdRR dst src) :
    fpSchritt d t =
      some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSchreibeTief t.xmm dst (fpRechne .sub (xmmTief t.xmm dst) (xmmTief t.xmm src)) } := by
  unfold fpSchritt
  simp [hok, hfp, h]

/-- `mulsd` (register): the low half holds the model product. -/
theorem fpSchritt_mulsdRR (d : FpDecodiert) (t : FpZustand)
    (dst src : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .mulsdRR dst src) :
    fpSchritt d t =
      some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSchreibeTief t.xmm dst (fpRechne .mul (xmmTief t.xmm dst) (xmmTief t.xmm src)) } := by
  unfold fpSchritt
  simp [hok, hfp, h]

/-- `divsd` (register): the low half holds the model quotient. -/
theorem fpSchritt_divsdRR (d : FpDecodiert) (t : FpZustand)
    (dst src : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .divsdRR dst src) :
    fpSchritt d t =
      some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSchreibeTief t.xmm dst (fpRechne .div (xmmTief t.xmm dst) (xmmTief t.xmm src)) } := by
  unfold fpSchritt
  simp [hok, hfp, h]

/-- `addsd` (memory source) success: the word at base plus displacement
    is the second model operand. -/
theorem fpSchritt_addsdRM_erfolg (d : FpDecodiert) (t : FpZustand)
    (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .addsdRM dst base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = some v) :
    fpSchritt d t =
      some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSchreibeTief t.xmm dst (fpRechne .add (xmmTief t.xmm dst) v) } := by
  unfold fpSchritt
  simp [hok, hfp, h, hrd]

/-- `addsd` (memory source) refusal: a failed read is explicit. -/
theorem fpSchritt_addsdRM_verweigert (d : FpDecodiert) (t : FpZustand)
    (dst : XmmReg) (base : Register) (disp : BitVec 32)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .addsdRM dst base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = none) :
    fpSchritt d t = none := by
  unfold fpSchritt
  simp [hok, hfp, h, hrd]

/-- `subsd` (memory source) success. -/
theorem fpSchritt_subsdRM_erfolg (d : FpDecodiert) (t : FpZustand)
    (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .subsdRM dst base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = some v) :
    fpSchritt d t =
      some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSchreibeTief t.xmm dst (fpRechne .sub (xmmTief t.xmm dst) v) } := by
  unfold fpSchritt
  simp [hok, hfp, h, hrd]

/-- `subsd` (memory source) refusal. -/
theorem fpSchritt_subsdRM_verweigert (d : FpDecodiert) (t : FpZustand)
    (dst : XmmReg) (base : Register) (disp : BitVec 32)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .subsdRM dst base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = none) :
    fpSchritt d t = none := by
  unfold fpSchritt
  simp [hok, hfp, h, hrd]

/-- `mulsd` (memory source) success. -/
theorem fpSchritt_mulsdRM_erfolg (d : FpDecodiert) (t : FpZustand)
    (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .mulsdRM dst base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = some v) :
    fpSchritt d t =
      some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSchreibeTief t.xmm dst (fpRechne .mul (xmmTief t.xmm dst) v) } := by
  unfold fpSchritt
  simp [hok, hfp, h, hrd]

/-- `mulsd` (memory source) refusal. -/
theorem fpSchritt_mulsdRM_verweigert (d : FpDecodiert) (t : FpZustand)
    (dst : XmmReg) (base : Register) (disp : BitVec 32)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .mulsdRM dst base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = none) :
    fpSchritt d t = none := by
  unfold fpSchritt
  simp [hok, hfp, h, hrd]

/-- `divsd` (memory source) success. -/
theorem fpSchritt_divsdRM_erfolg (d : FpDecodiert) (t : FpZustand)
    (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .divsdRM dst base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = some v) :
    fpSchritt d t =
      some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSchreibeTief t.xmm dst (fpRechne .div (xmmTief t.xmm dst) v) } := by
  unfold fpSchritt
  simp [hok, hfp, h, hrd]

/-- `divsd` (memory source) refusal. -/
theorem fpSchritt_divsdRM_verweigert (d : FpDecodiert) (t : FpZustand)
    (dst : XmmReg) (base : Register) (disp : BitVec 32)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .divsdRM dst base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = none) :
    fpSchritt d t = none := by
  unfold fpSchritt
  simp [hok, hfp, h, hrd]

/-! ## Arithmetic frames: flags, memory, upper halves, GPRs.

  Scalar DOUBLE arithmetic never touches rFLAGS, never changes a memory
  byte, keeps every GPR, and keeps the destination's high half. One triple
  per form; every premise is used. -/

/-- `addsd` (register) preserves the flags. -/
theorem fpSchritt_addsdRR_flags (d : FpDecodiert) (t t' : FpZustand)
    (dst src : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .addsdRR dst src) (hstep : fpSchritt d t = some t') :
    t'.kern.flags = t.kern.flags := by
  rw [fpSchritt_addsdRR d t dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- `addsd` (register) changes no memory byte. -/
theorem fpSchritt_addsdRR_speicher (d : FpDecodiert) (t t' : FpZustand)
    (dst src : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .addsdRR dst src) (hstep : fpSchritt d t = some t') :
    t'.kern.speicher = t.kern.speicher := by
  rw [fpSchritt_addsdRR d t dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- `addsd` (register) keeps the destination's high half. -/
theorem fpSchritt_addsdRR_hoch (d : FpDecodiert) (t t' : FpZustand)
    (dst src : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .addsdRR dst src) (hstep : fpSchritt d t = some t') :
    xmmHoch t'.xmm dst = xmmHoch t.xmm dst := by
  rw [fpSchritt_addsdRR d t dst src hok hfp h] at hstep
  cases hstep
  exact xmmSchreibeTief_hoch _ _ _

/-- `addsd` (register) keeps every GPR. -/
theorem fpSchritt_addsdRR_gpr (d : FpDecodiert) (t t' : FpZustand)
    (dst src : XmmReg) (q : Register)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .addsdRR dst src) (hstep : fpSchritt d t = some t') :
    t'.kern.register q = t.kern.register q := by
  rw [fpSchritt_addsdRR d t dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- `subsd` (register) preserves the flags. -/
theorem fpSchritt_subsdRR_flags (d : FpDecodiert) (t t' : FpZustand)
    (dst src : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .subsdRR dst src) (hstep : fpSchritt d t = some t') :
    t'.kern.flags = t.kern.flags := by
  rw [fpSchritt_subsdRR d t dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- `subsd` (register) changes no memory byte. -/
theorem fpSchritt_subsdRR_speicher (d : FpDecodiert) (t t' : FpZustand)
    (dst src : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .subsdRR dst src) (hstep : fpSchritt d t = some t') :
    t'.kern.speicher = t.kern.speicher := by
  rw [fpSchritt_subsdRR d t dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- `subsd` (register) keeps the destination's high half. -/
theorem fpSchritt_subsdRR_hoch (d : FpDecodiert) (t t' : FpZustand)
    (dst src : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .subsdRR dst src) (hstep : fpSchritt d t = some t') :
    xmmHoch t'.xmm dst = xmmHoch t.xmm dst := by
  rw [fpSchritt_subsdRR d t dst src hok hfp h] at hstep
  cases hstep
  exact xmmSchreibeTief_hoch _ _ _

/-- `mulsd` (register) preserves the flags. -/
theorem fpSchritt_mulsdRR_flags (d : FpDecodiert) (t t' : FpZustand)
    (dst src : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .mulsdRR dst src) (hstep : fpSchritt d t = some t') :
    t'.kern.flags = t.kern.flags := by
  rw [fpSchritt_mulsdRR d t dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- `mulsd` (register) changes no memory byte. -/
theorem fpSchritt_mulsdRR_speicher (d : FpDecodiert) (t t' : FpZustand)
    (dst src : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .mulsdRR dst src) (hstep : fpSchritt d t = some t') :
    t'.kern.speicher = t.kern.speicher := by
  rw [fpSchritt_mulsdRR d t dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- `mulsd` (register) keeps the destination's high half. -/
theorem fpSchritt_mulsdRR_hoch (d : FpDecodiert) (t t' : FpZustand)
    (dst src : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .mulsdRR dst src) (hstep : fpSchritt d t = some t') :
    xmmHoch t'.xmm dst = xmmHoch t.xmm dst := by
  rw [fpSchritt_mulsdRR d t dst src hok hfp h] at hstep
  cases hstep
  exact xmmSchreibeTief_hoch _ _ _

/-- `divsd` (register) preserves the flags. -/
theorem fpSchritt_divsdRR_flags (d : FpDecodiert) (t t' : FpZustand)
    (dst src : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .divsdRR dst src) (hstep : fpSchritt d t = some t') :
    t'.kern.flags = t.kern.flags := by
  rw [fpSchritt_divsdRR d t dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- `divsd` (register) changes no memory byte. -/
theorem fpSchritt_divsdRR_speicher (d : FpDecodiert) (t t' : FpZustand)
    (dst src : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .divsdRR dst src) (hstep : fpSchritt d t = some t') :
    t'.kern.speicher = t.kern.speicher := by
  rw [fpSchritt_divsdRR d t dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- `divsd` (register) keeps the destination's high half. -/
theorem fpSchritt_divsdRR_hoch (d : FpDecodiert) (t t' : FpZustand)
    (dst src : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .divsdRR dst src) (hstep : fpSchritt d t = some t') :
    xmmHoch t'.xmm dst = xmmHoch t.xmm dst := by
  rw [fpSchritt_divsdRR d t dst src hok hfp h] at hstep
  cases hstep
  exact xmmSchreibeTief_hoch _ _ _

/-- `addsd` (memory source) preserves the flags. -/
theorem fpSchritt_addsdRM_flags (d : FpDecodiert) (t t' : FpZustand)
    (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .addsdRM dst base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = some v)
    (hstep : fpSchritt d t = some t') :
    t'.kern.flags = t.kern.flags := by
  rw [fpSchritt_addsdRM_erfolg d t dst base disp v hok hfp h hrd] at hstep
  cases hstep
  rfl

/-- `addsd` (memory source) changes no memory byte. -/
theorem fpSchritt_addsdRM_speicher (d : FpDecodiert) (t t' : FpZustand)
    (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .addsdRM dst base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = some v)
    (hstep : fpSchritt d t = some t') :
    t'.kern.speicher = t.kern.speicher := by
  rw [fpSchritt_addsdRM_erfolg d t dst base disp v hok hfp h hrd] at hstep
  cases hstep
  rfl

/-- `addsd` (memory source) keeps the destination's high half. -/
theorem fpSchritt_addsdRM_hoch (d : FpDecodiert) (t t' : FpZustand)
    (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .addsdRM dst base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = some v)
    (hstep : fpSchritt d t = some t') :
    xmmHoch t'.xmm dst = xmmHoch t.xmm dst := by
  rw [fpSchritt_addsdRM_erfolg d t dst base disp v hok hfp h hrd] at hstep
  cases hstep
  exact xmmSchreibeTief_hoch _ _ _

/-- `subsd` (memory source) preserves the flags. -/
theorem fpSchritt_subsdRM_flags (d : FpDecodiert) (t t' : FpZustand)
    (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .subsdRM dst base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = some v)
    (hstep : fpSchritt d t = some t') :
    t'.kern.flags = t.kern.flags := by
  rw [fpSchritt_subsdRM_erfolg d t dst base disp v hok hfp h hrd] at hstep
  cases hstep
  rfl

/-- `subsd` (memory source) changes no memory byte. -/
theorem fpSchritt_subsdRM_speicher (d : FpDecodiert) (t t' : FpZustand)
    (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .subsdRM dst base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = some v)
    (hstep : fpSchritt d t = some t') :
    t'.kern.speicher = t.kern.speicher := by
  rw [fpSchritt_subsdRM_erfolg d t dst base disp v hok hfp h hrd] at hstep
  cases hstep
  rfl

/-- `mulsd` (memory source) preserves the flags. -/
theorem fpSchritt_mulsdRM_flags (d : FpDecodiert) (t t' : FpZustand)
    (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .mulsdRM dst base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = some v)
    (hstep : fpSchritt d t = some t') :
    t'.kern.flags = t.kern.flags := by
  rw [fpSchritt_mulsdRM_erfolg d t dst base disp v hok hfp h hrd] at hstep
  cases hstep
  rfl

/-- `mulsd` (memory source) changes no memory byte. -/
theorem fpSchritt_mulsdRM_speicher (d : FpDecodiert) (t t' : FpZustand)
    (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .mulsdRM dst base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = some v)
    (hstep : fpSchritt d t = some t') :
    t'.kern.speicher = t.kern.speicher := by
  rw [fpSchritt_mulsdRM_erfolg d t dst base disp v hok hfp h hrd] at hstep
  cases hstep
  rfl

/-- `divsd` (memory source) preserves the flags. -/
theorem fpSchritt_divsdRM_flags (d : FpDecodiert) (t t' : FpZustand)
    (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .divsdRM dst base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = some v)
    (hstep : fpSchritt d t = some t') :
    t'.kern.flags = t.kern.flags := by
  rw [fpSchritt_divsdRM_erfolg d t dst base disp v hok hfp h hrd] at hstep
  cases hstep
  rfl

/-- `divsd` (memory source) changes no memory byte. -/
theorem fpSchritt_divsdRM_speicher (d : FpDecodiert) (t t' : FpZustand)
    (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .divsdRM dst base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = some v)
    (hstep : fpSchritt d t = some t') :
    t'.kern.speicher = t.kern.speicher := by
  rw [fpSchritt_divsdRM_erfolg d t dst base disp v hok hfp h hrd] at hstep
  cases hstep
  rfl

/-! ## Compare, convert and move steps.

  UCOMISD writes only flags (OF/SF/AF cleared); conversions and MOVSD
  preserve flags; loads zero the high half; only the store changes memory. -/

/-- `ucomisd` (register): flags carry the unordered comparison. -/
theorem fpSchritt_ucomisdRR (d : FpDecodiert) (t : FpZustand)
    (lhs rhs : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .ucomisdRR lhs rhs) :
    fpSchritt d t = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge, flags := ucomiFlags (bites64 (xmmTief t.xmm lhs)) (bites64 (xmmTief t.xmm rhs)) } } := by
  unfold fpSchritt
  simp [hok, hfp, h]

/-- `ucomisd` (register) changes no XMM register. -/
theorem fpSchritt_ucomisdRR_xmm (d : FpDecodiert) (t t' : FpZustand)
    (lhs rhs : XmmReg) (q : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .ucomisdRR lhs rhs) (hstep : fpSchritt d t = some t') :
    t'.xmm q = t.xmm q := by
  rw [fpSchritt_ucomisdRR d t lhs rhs hok hfp h] at hstep
  cases hstep
  rfl

/-- `ucomisd` (register) changes no memory byte. -/
theorem fpSchritt_ucomisdRR_speicher (d : FpDecodiert) (t t' : FpZustand)
    (lhs rhs : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .ucomisdRR lhs rhs) (hstep : fpSchritt d t = some t') :
    t'.kern.speicher = t.kern.speicher := by
  rw [fpSchritt_ucomisdRR d t lhs rhs hok hfp h] at hstep
  cases hstep
  rfl

/-- `ucomisd` (memory source) success. -/
theorem fpSchritt_ucomisdRM_erfolg (d : FpDecodiert) (t : FpZustand)
    (lhs : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .ucomisdRM lhs base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = some v) :
    fpSchritt d t = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge, flags := ucomiFlags (bites64 (xmmTief t.xmm lhs)) (bites64 v) } } := by
  unfold fpSchritt
  simp [hok, hfp, h, hrd]

/-- `ucomisd` (memory source) refusal. -/
theorem fpSchritt_ucomisdRM_verweigert (d : FpDecodiert) (t : FpZustand)
    (lhs : XmmReg) (base : Register) (disp : BitVec 32)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .ucomisdRM lhs base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = none) :
    fpSchritt d t = none := by
  unfold fpSchritt
  simp [hok, hfp, h, hrd]

/-- `ucomisd` (memory source) changes no XMM register. -/
theorem fpSchritt_ucomisdRM_xmm (d : FpDecodiert) (t t' : FpZustand)
    (lhs : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort)
    (q : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .ucomisdRM lhs base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = some v)
    (hstep : fpSchritt d t = some t') :
    t'.xmm q = t.xmm q := by
  rw [fpSchritt_ucomisdRM_erfolg d t lhs base disp v hok hfp h hrd] at hstep
  cases hstep
  rfl

/-- `cvtsi2sd`: the low half holds the converted GPR value. -/
theorem fpSchritt_cvtsi2sd (d : FpDecodiert) (t : FpZustand)
    (dst : XmmReg) (src : Register)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .cvtsi2sd dst src) :
    fpSchritt d t = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSchreibeTief t.xmm dst (muster64 (cvtsiErg (t.kern.register src))) } := by
  unfold fpSchritt
  simp [hok, hfp, h]

/-- `cvtsi2sd` preserves the flags. -/
theorem fpSchritt_cvtsi2sd_flags (d : FpDecodiert) (t t' : FpZustand)
    (dst : XmmReg) (src : Register)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .cvtsi2sd dst src) (hstep : fpSchritt d t = some t') :
    t'.kern.flags = t.kern.flags := by
  rw [fpSchritt_cvtsi2sd d t dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- `cvtsi2sd` changes no memory byte. -/
theorem fpSchritt_cvtsi2sd_speicher (d : FpDecodiert) (t t' : FpZustand)
    (dst : XmmReg) (src : Register)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .cvtsi2sd dst src) (hstep : fpSchritt d t = some t') :
    t'.kern.speicher = t.kern.speicher := by
  rw [fpSchritt_cvtsi2sd d t dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- `cvtsi2sd` keeps the destination's high half. -/
theorem fpSchritt_cvtsi2sd_hoch (d : FpDecodiert) (t t' : FpZustand)
    (dst : XmmReg) (src : Register)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .cvtsi2sd dst src) (hstep : fpSchritt d t = some t') :
    xmmHoch t'.xmm dst = xmmHoch t.xmm dst := by
  rw [fpSchritt_cvtsi2sd d t dst src hok hfp h] at hstep
  cases hstep
  exact xmmSchreibeTief_hoch _ _ _

/-- `cvttsd2si`: the GPR holds the wrapped conversion. -/
theorem fpSchritt_cvttsd2si (d : FpDecodiert) (t : FpZustand)
    (dst : Register) (src : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .cvttsd2si dst src) :
    fpSchritt d t = some { t with kern := { t.kern with register := regSet t.kern.register dst (intWort (cvttPaket (xmmTief t.xmm src))), rip := ripNach t.kern.rip d.laenge } } := by
  unfold fpSchritt
  simp [hok, hfp, h]

/-- `cvttsd2si` preserves the flags. -/
theorem fpSchritt_cvttsd2si_flags (d : FpDecodiert) (t t' : FpZustand)
    (dst : Register) (src : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .cvttsd2si dst src) (hstep : fpSchritt d t = some t') :
    t'.kern.flags = t.kern.flags := by
  rw [fpSchritt_cvttsd2si d t dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- `cvttsd2si` changes no memory byte. -/
theorem fpSchritt_cvttsd2si_speicher (d : FpDecodiert) (t t' : FpZustand)
    (dst : Register) (src : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .cvttsd2si dst src) (hstep : fpSchritt d t = some t') :
    t'.kern.speicher = t.kern.speicher := by
  rw [fpSchritt_cvttsd2si d t dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- `cvttsd2si` changes no XMM register. -/
theorem fpSchritt_cvttsd2si_xmm (d : FpDecodiert) (t t' : FpZustand)
    (dst : Register) (src q : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .cvttsd2si dst src) (hstep : fpSchritt d t = some t') :
    t'.xmm q = t.xmm q := by
  rw [fpSchritt_cvttsd2si d t dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- `movsd` (register): the low half moves, the destination high stays. -/
theorem fpSchritt_movsdRR (d : FpDecodiert) (t : FpZustand)
    (dst src : XmmReg)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .movsdRR dst src) :
    fpSchritt d t = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSchreibeTief t.xmm dst (xmmTief t.xmm src) } := by
  unfold fpSchritt
  simp [hok, hfp, h]

/-- `movsd` (register) preserves the flags. -/
theorem fpSchritt_movsdRR_flags (d : FpDecodiert) (t t' : FpZustand)
    (dst src : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .movsdRR dst src) (hstep : fpSchritt d t = some t') :
    t'.kern.flags = t.kern.flags := by
  rw [fpSchritt_movsdRR d t dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- `movsd` load success: the word lands low, the high half is zeroed. -/
theorem fpSchritt_movsdLade_erfolg (d : FpDecodiert) (t : FpZustand)
    (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .movsdLade dst base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = some v) :
    fpSchritt d t = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSet t.xmm dst (vecJoin v 0) } := by
  unfold fpSchritt
  simp [hok, hfp, h, hrd]

/-- `movsd` load refusal. -/
theorem fpSchritt_movsdLade_verweigert (d : FpDecodiert) (t : FpZustand)
    (dst : XmmReg) (base : Register) (disp : BitVec 32)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .movsdLade dst base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = none) :
    fpSchritt d t = none := by
  unfold fpSchritt
  simp [hok, hfp, h, hrd]

/-- `movsd` load zeroes the destination high half. -/
theorem fpSchritt_movsdLade_hochNull (d : FpDecodiert) (t t' : FpZustand)
    (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .movsdLade dst base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = some v)
    (hstep : fpSchritt d t = some t') :
    xmmHoch t'.xmm dst = 0 := by
  rw [fpSchritt_movsdLade_erfolg d t dst base disp v hok hfp h hrd] at hstep
  cases hstep
  show xmmHoch (xmmSet t.xmm dst (vecJoin v 0)) dst = 0
  unfold xmmHoch
  rw [xmmSet_gleich, vHi_vecJoin]

/-- `movsd` load preserves the flags. -/
theorem fpSchritt_movsdLade_flags (d : FpDecodiert) (t t' : FpZustand)
    (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .movsdLade dst base disp)
    (hrd : read64 t.kern.speicher (effAddr t.kern base disp) = some v)
    (hstep : fpSchritt d t = some t') :
    t'.kern.flags = t.kern.flags := by
  rw [fpSchritt_movsdLade_erfolg d t dst base disp v hok hfp h hrd] at hstep
  cases hstep
  rfl

/-- `movsd` store success: the low half lands in memory. -/
theorem fpSchritt_movsdSpeichere_erfolg (d : FpDecodiert) (t : FpZustand)
    (base : Register) (src : XmmReg) (disp : BitVec 32) (m : Speicher)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .movsdSpeichere base src disp)
    (hwr : write64 t.kern.speicher (effAddr t.kern base disp) (xmmTief t.xmm src) = some m) :
    fpSchritt d t = some { t with kern := { t.kern with speicher := m, rip := ripNach t.kern.rip d.laenge } } := by
  unfold fpSchritt
  simp [hok, hfp, h, hwr]

/-- `movsd` store refusal. -/
theorem fpSchritt_movsdSpeichere_verweigert (d : FpDecodiert) (t : FpZustand)
    (base : Register) (src : XmmReg) (disp : BitVec 32)
    (hok : laengeOk d.laenge = true)
    (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .movsdSpeichere base src disp)
    (hwr : write64 t.kern.speicher (effAddr t.kern base disp) (xmmTief t.xmm src) = none) :
    fpSchritt d t = none := by
  unfold fpSchritt
  simp [hok, hfp, h, hwr]

/-- `movsd` store preserves the flags. -/
theorem fpSchritt_movsdSpeichere_flags (d : FpDecodiert) (t t' : FpZustand)
    (base : Register) (src : XmmReg) (disp : BitVec 32) (m : Speicher)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .movsdSpeichere base src disp)
    (hwr : write64 t.kern.speicher (effAddr t.kern base disp) (xmmTief t.xmm src) = some m)
    (hstep : fpSchritt d t = some t') :
    t'.kern.flags = t.kern.flags := by
  rw [fpSchritt_movsdSpeichere_erfolg d t base src disp m hok hfp h hwr] at hstep
  cases hstep
  rfl

/-- `movsd` store keeps every permission: only bytes change. -/
theorem fpSchritt_movsdSpeichere_berechtigungen (d : FpDecodiert)
    (t t' : FpZustand)
    (base : Register) (src : XmmReg) (disp : BitVec 32) (m : Speicher)
    (hok : laengeOk d.laenge = true) (hfp : fpEintritt t.fp = true)
    (h : d.befehl = .movsdSpeichere base src disp)
    (hwr : write64 t.kern.speicher (effAddr t.kern base disp) (xmmTief t.xmm src) = some m)
    (hstep : fpSchritt d t = some t') :
    t'.kern.speicher.lesbar = t.kern.speicher.lesbar ∧ t'.kern.speicher.schreibbar = t.kern.speicher.schreibbar ∧ t'.kern.speicher.ausfuehrbar = t.kern.speicher.ausfuehrbar := by
  rw [fpSchritt_movsdSpeichere_erfolg d t base src disp m hok hfp h hwr] at hstep
  cases hstep
  exact write64_erhaelt_berechtigungen t.kern.speicher (effAddr t.kern base disp) (xmmTief t.xmm src) m hwr

/-! ## 4. Source bridge: one source op = one machine op, class-level.

  `fpRechne` IS the source `gleitRechne` at binary64, transported through
  words (`muster64`/`bites64`). NaN agreement is class-level only:
  payload equality is never concluded (OPEN, §6). -/

/-- The machine word op is the source model op on injected words. -/
theorem fpRechne_gleitRechne (op : Gabbro.Grammatik.GleitOp) (a b : Wort) :
    fpRechne op a b =
      muster64 (Gabbro.Grammatik.gleitRechne op (bites64 a) (bites64 b)) := by
  cases op <;> rfl

/-- Class-level agreement: the computed word classifies exactly as the
    source model result (NaN payloads excluded -- OPEN, §6). -/
theorem fpRechne_klasse (op : Gabbro.Grammatik.GleitOp) (a b : Wort) :
    Gleitkomma.klasse Gleitkomma.f64 (bites64 (fpRechne op a b)) =
      Gleitkomma.klasse Gleitkomma.f64
        (Gabbro.Grammatik.gleitRechne op (bites64 a) (bites64 b)) := by
  rw [fpRechne_gleitRechne]
  have hwf : ∀ x : Wort, Gleitkomma.wf Gleitkomma.f64 (bites64 x) :=
    fun x => ausBits_wf Gleitkomma.f64 Gleitkomma.f64_dicht x.toNat
  have hw : Gleitkomma.wf Gleitkomma.f64
      (Gabbro.Grammatik.gleitRechne op (bites64 a) (bites64 b)) := by
    cases op with
    | add => exact Gleitkomma.add_wf _ Gleitkomma.f64_p _ _ (hwf a) (hwf b)
    | sub => exact Gleitkomma.sub_wf _ Gleitkomma.f64_p _ _ (hwf a) (hwf b)
    | mul => exact Gleitkomma.mul_wf _ Gleitkomma.f64_p _ _ (hwf a) (hwf b)
    | div => exact Gleitkomma.div_wf _ Gleitkomma.f64_p _ _ (hwf a) (hwf b)
  rw [bites64_muster64 _ hw]

/-- Model `flt` answers `false` on a left NaN. -/
theorem flt_nan_links (a b : Gleitkomma.GBits Gleitkomma.f64)
    (h : Gleitkomma.klasse Gleitkomma.f64 a = .nan) :
    Gleitkomma.flt Gleitkomma.f64 a b = false := by
  unfold Gleitkomma.flt
  rw [h]

/-- Model `flt` answers `false` on a right NaN. -/
theorem flt_nan_rechts (a b : Gleitkomma.GBits Gleitkomma.f64)
    (h : Gleitkomma.klasse Gleitkomma.f64 b = .nan) :
    Gleitkomma.flt Gleitkomma.f64 a b = false := by
  unfold Gleitkomma.flt
  cases ka : Gleitkomma.klasse Gleitkomma.f64 a with
  | nan => rfl
  | unendlich => rw [h]
  | null => rw [h]
  | subnormal => rw [h]
  | normal => rw [h]

/-- Model `fle` answers `false` on a left NaN. -/
theorem fle_nan_links (a b : Gleitkomma.GBits Gleitkomma.f64)
    (h : Gleitkomma.klasse Gleitkomma.f64 a = .nan) :
    Gleitkomma.fle Gleitkomma.f64 a b = false := by
  unfold Gleitkomma.fle
  rw [h]

/-- Model `fle` answers `false` on a right NaN. -/
theorem fle_nan_rechts (a b : Gleitkomma.GBits Gleitkomma.f64)
    (h : Gleitkomma.klasse Gleitkomma.f64 b = .nan) :
    Gleitkomma.fle Gleitkomma.f64 a b = false := by
  unfold Gleitkomma.fle
  cases ka : Gleitkomma.klasse Gleitkomma.f64 a with
  | nan => rfl
  | unendlich => rw [h]
  | null => rw [h]
  | subnormal => rw [h]
  | normal => rw [h]

/-- UCOMISD unordered row, left NaN: ZF, PF, CF set. -/
theorem ucomiFlags_ungeordnet_links (a b : Gleitkomma.GBits Gleitkomma.f64)
    (h : Gleitkomma.klasse Gleitkomma.f64 a = .nan) :
    ucomiFlags a b = ⟨true, true, some false, true, false, false⟩ := by
  unfold ucomiFlags
  rw [h]

/-- UCOMISD unordered row, right NaN: ZF, PF, CF set. -/
theorem ucomiFlags_ungeordnet_rechts (a b : Gleitkomma.GBits Gleitkomma.f64)
    (h : Gleitkomma.klasse Gleitkomma.f64 b = .nan) :
    ucomiFlags a b = ⟨true, true, some false, true, false, false⟩ := by
  unfold ucomiFlags
  cases ka : Gleitkomma.klasse Gleitkomma.f64 a with
  | nan => rfl
  | unendlich => rw [h]
  | null => rw [h]
  | subnormal => rw [h]
  | normal => rw [h]

/-- Off the NaN rows, the flag table is the two model comparisons. -/
theorem ucomiFlags_nichtNan (a b : Gleitkomma.GBits Gleitkomma.f64)
    (ha : Gleitkomma.klasse Gleitkomma.f64 a ≠ .nan)
    (hb : Gleitkomma.klasse Gleitkomma.f64 b ≠ .nan) :
    ucomiFlags a b =
      (if Gleitkomma.flt Gleitkomma.f64 a b then (⟨true, false, some false, false, false, false⟩ : Flags)
       else if Gleitkomma.flt Gleitkomma.f64 b a then (⟨false, false, some false, false, false, false⟩ : Flags)
       else (⟨false, false, some false, true, false, false⟩ : Flags)) := by
  unfold ucomiFlags
  cases ka : Gleitkomma.klasse Gleitkomma.f64 a with
  | nan => exact absurd ka ha
  | unendlich =>
    cases kb : Gleitkomma.klasse Gleitkomma.f64 b with
    | nan => exact absurd kb hb
    | unendlich => rfl
    | null => rfl
    | subnormal => rfl
    | normal => rfl
  | null =>
    cases kb : Gleitkomma.klasse Gleitkomma.f64 b with
    | nan => exact absurd kb hb
    | unendlich => rfl
    | null => rfl
    | subnormal => rfl
    | normal => rfl
  | subnormal =>
    cases kb : Gleitkomma.klasse Gleitkomma.f64 b with
    | nan => exact absurd kb hb
    | unendlich => rfl
    | null => rfl
    | subnormal => rfl
    | normal => rfl
  | normal =>
    cases kb : Gleitkomma.klasse Gleitkomma.f64 b with
    | nan => exact absurd kb hb
    | unendlich => rfl
    | null => rfl
    | subnormal => rfl
    | normal => rfl

/-- UCOMISD less row: only CF set. -/
theorem ucomiFlags_kleiner (a b : Gleitkomma.GBits Gleitkomma.f64)
    (hlt : Gleitkomma.flt Gleitkomma.f64 a b = true)
    (ha : Gleitkomma.klasse Gleitkomma.f64 a ≠ .nan)
    (hb : Gleitkomma.klasse Gleitkomma.f64 b ≠ .nan) :
    ucomiFlags a b = ⟨true, false, some false, false, false, false⟩ := by
  rw [ucomiFlags_nichtNan a b ha hb]
  simp [hlt]

/-- UCOMISD greater row: no flag set. -/
theorem ucomiFlags_groesser (a b : Gleitkomma.GBits Gleitkomma.f64)
    (h1 : Gleitkomma.flt Gleitkomma.f64 a b = false)
    (h2 : Gleitkomma.flt Gleitkomma.f64 b a = true)
    (ha : Gleitkomma.klasse Gleitkomma.f64 a ≠ .nan)
    (hb : Gleitkomma.klasse Gleitkomma.f64 b ≠ .nan) :
    ucomiFlags a b = ⟨false, false, some false, false, false, false⟩ := by
  rw [ucomiFlags_nichtNan a b ha hb]
  simp [h1, h2]

/-- UCOMISD equal row: only ZF set. -/
theorem ucomiFlags_gleich (a b : Gleitkomma.GBits Gleitkomma.f64)
    (h1 : Gleitkomma.flt Gleitkomma.f64 a b = false)
    (h2 : Gleitkomma.flt Gleitkomma.f64 b a = false)
    (ha : Gleitkomma.klasse Gleitkomma.f64 a ≠ .nan)
    (hb : Gleitkomma.klasse Gleitkomma.f64 b ≠ .nan) :
    ucomiFlags a b = ⟨false, false, some false, true, false, false⟩ := by
  rw [ucomiFlags_nichtNan a b ha hb]
  simp [h1, h2]

/-! ## Conversion bridge: CVTSI2SD and the CVTTSD2SI wrapper.

  `cvtsiErg` is the source `gleitAusInt` at the machine (definitionally:
  `gleitAusInt z = ofInt f64 z`; the link is the definition, proved
  well-formed and computed here, not restated as a vacuous equation).
  `cvttPaket` decides hardware-invalid from the CLASS first and is proved
  equal to the source `gleitRoh` on every word. -/

/-- CVTSI2SD always lands well-formed. -/
theorem cvtsiErg_wf (w : Wort) :
    Gleitkomma.wf Gleitkomma.f64 (cvtsiErg w) :=
  Gleitkomma.ofInt_wf _ Gleitkomma.f64_p _

/-- CVTSI2SD computes: `42` becomes the `42.0` pattern. -/
theorem cvtsiErg_42 : muster64 (cvtsiErg 42) = 0x4045000000000000 := by
  decide

/-- The CVTTSD2SI wrapper agrees with the source `gleitRoh` on every word:
    NaN and infinity give `0`, finite values truncate toward zero with
    saturation. -/
theorem cvttPaket_gleicht_gleitRoh (w : Wort) :
    cvttPaket w = Gabbro.Grammatik.gleitRoh (bites64 w) := by
  cases hk : Gleitkomma.klasse Gleitkomma.f64 (bites64 w) with
  | nan =>
    have hcv : cvttPaket w = 0 := by
      unfold cvttPaket
      simp [hk]
    have hgl : Gabbro.Grammatik.gleitRoh (bites64 w) = 0 := by
      unfold Gabbro.Grammatik.gleitRoh
      have hw : Gleitkomma.wertExakt Gleitkomma.f64 (bites64 w) = none := by
        unfold Gleitkomma.wertExakt
        rw [hk]
      simp [hw]
    rw [hcv, hgl]
  | unendlich =>
    have hcv : cvttPaket w = 0 := by
      unfold cvttPaket
      simp [hk]
    have hgl : Gabbro.Grammatik.gleitRoh (bites64 w) = 0 := by
      unfold Gabbro.Grammatik.gleitRoh
      have hw : Gleitkomma.wertExakt Gleitkomma.f64 (bites64 w) = none := by
        unfold Gleitkomma.wertExakt
        rw [hk]
      simp [hw]
    rw [hcv, hgl]
  | null =>
    have hw : Gleitkomma.wertExakt Gleitkomma.f64 (bites64 w)
        = some ⟨0, 0⟩ := by
      unfold Gleitkomma.wertExakt
      rw [hk]
    unfold Gabbro.Grammatik.gleitRoh
    rw [hw]
    unfold cvttPaket
    simp [hk, hw]
  | subnormal =>
    obtain ⟨v, hv⟩ :
        ∃ v, Gleitkomma.wertExakt Gleitkomma.f64 (bites64 w) = some v := by
      unfold Gleitkomma.wertExakt
      rw [hk]
      exact ⟨_, rfl⟩
    unfold Gabbro.Grammatik.gleitRoh
    rw [hv]
    unfold cvttPaket
    simp [hk, hv]
  | normal =>
    obtain ⟨v, hv⟩ :
        ∃ v, Gleitkomma.wertExakt Gleitkomma.f64 (bites64 w) = some v := by
      unfold Gleitkomma.wertExakt
      rw [hk]
      exact ⟨_, rfl⟩
    unfold Gabbro.Grammatik.gleitRoh
    rw [hv]
    unfold cvttPaket
    simp [hk, hv]

/-! ## 5. Profile refusal: arity, width, and the SNaN position.

  Every `FpBefehl` takes at most two XMM operands (three-operand FMA has
  no constructor here; packed lanes have none either -- `Vektor` lanes
  are owned by the deferred SIMD profile, never read by `fpSchritt`).
  The word bridge is binary64 only: source `Ty.fl` carries no width and
  the model computes every source float in binary64 (`Typen.lean`), so
  there is no f32 node to admit and no double-rounding paragraph to
  write -- the f32-vs-f64 counterexample stays owned by lane 286
  (`Gleitprofil`), never duplicated here. `Klasse` has a single `.nan`
  (no SNaN/QNaN distinction in the model): every NaN-class operand
  takes the unordered UCOMISD row whatever its payload or signalling
  bit, and OF/SF/AF are reserved (cleared) on every compare. -/

/-- XMM operand count per form: at most two (register-register and
    register-register moves take two, memory and conversion forms one). -/
def fpXmmZahl : FpBefehl → Nat
  | .addsdRR _ _ => 2
  | .subsdRR _ _ => 2
  | .mulsdRR _ _ => 2
  | .divsdRR _ _ => 2
  | .addsdRM _ _ _ => 1
  | .subsdRM _ _ _ => 1
  | .mulsdRM _ _ _ => 1
  | .divsdRM _ _ _ => 1
  | .ucomisdRR _ _ => 2
  | .ucomisdRM _ _ _ => 1
  | .cvtsi2sd _ _ => 1
  | .cvttsd2si _ _ => 1
  | .movsdRR _ _ => 2
  | .movsdLade _ _ _ => 1
  | .movsdSpeichere _ _ _ => 1

/-- No three-operand (FMA) or lane-indexed (packed) form exists: every
    scalar DOUBLE form takes at most two XMM operands. -/
theorem fpXmmZahl_le_zwei (b : FpBefehl) : fpXmmZahl b ≤ 2 := by
  cases b <;> simp only [fpXmmZahl] <;> omega

/-- The bridge admits binary64 only: every word reads as a well-formed
    f64 model value. There is no f32 entry point in this file. -/
theorem bites64_wf (w : Wort) :
    Gleitkomma.wf Gleitkomma.f64 (bites64 w) :=
  ausBits_wf Gleitkomma.f64 Gleitkomma.f64_dicht w.toNat

/-- The `∀ GleitOp` bridge equation at one joint instance: divide. -/
theorem fpRechne_gleitRechne_zeuge :
    fpRechne .div 0x3FF0000000000000 0 =
      muster64 (Gabbro.Grammatik.gleitRechne .div
        (bites64 0x3FF0000000000000) (bites64 0)) :=
  fpRechne_gleitRechne .div _ _

/-- The class-level agreement at one joint instance: divide. -/
theorem fpRechne_klasse_zeuge :
    Gleitkomma.klasse Gleitkomma.f64
        (bites64 (fpRechne .div 0x3FF0000000000000 0)) =
      Gleitkomma.klasse Gleitkomma.f64
        (Gabbro.Grammatik.gleitRechne .div
          (bites64 0x3FF0000000000000) (bites64 0)) :=
  fpRechne_klasse .div _ _

/-- UCOMISD reserves OF/SF/AF on every row: both cleared, AF defined
    zero (`some false`, unlike XOR's undefined `none`). -/
theorem ucomiFlags_reserviert (a b : GFloat) :
    (ucomiFlags a b).of = false ∧ (ucomiFlags a b).sf = false ∧
      (ucomiFlags a b).af = some false := by
  by_cases ha : Gleitkomma.klasse Gleitkomma.f64 a = .nan
  · rw [ucomiFlags_ungeordnet_links a b ha]
    exact ⟨rfl, rfl, rfl⟩
  · by_cases hb : Gleitkomma.klasse Gleitkomma.f64 b = .nan
    · rw [ucomiFlags_ungeordnet_rechts a b hb]
      exact ⟨rfl, rfl, rfl⟩
    · rw [ucomiFlags_nichtNan a b ha hb]
      by_cases h1 : Gleitkomma.flt Gleitkomma.f64 a b = true <;>
        by_cases h2 : Gleitkomma.flt Gleitkomma.f64 b a = true <;>
        simp [h1, h2]

/-- Joint NaN/flag reservation: a NaN-class operand (quiet or
    signalling -- the model has a single `.nan`, so no signalling bit
    is observed anywhere) forces the unordered row with reserved flags. -/
theorem ucomiFlags_nan_klasse_nur (a b : GFloat)
    (h : Gleitkomma.klasse Gleitkomma.f64 a = .nan) :
    ucomiFlags a b = ⟨true, true, some false, true, false, false⟩ ∧
      (ucomiFlags a b).of = false :=
  ⟨ucomiFlags_ungeordnet_links a b h, (ucomiFlags_reserviert a b).1⟩

/-! ## 6. Joint witness: divide special case stored to memory.

  `xmm0` holds `1.0`, `xmm1` holds `+0.0`; `divsd xmm0, xmm1` computes
  the divide special case `1.0 / +0.0 = +∞`, and `movsd [rax], xmm0`
  stores it at 8192. The word reads back and one memory byte observably
  changed (footprint top: `0x00` becomes `0x7F`). Two reached steps,
  real memory change, admitted profile throughout. -/

/-- Witness XMM file: `xmm0` holds `1.0`, every other register `+0.0`
    (high halves zero). -/
def fpZeugeXmm : XmmDatei :=
  fun q => if q = XmmReg.xmm0 then vecJoin 0x3FF0000000000000 0 else vecJoin 0 0

/-- Witness core: `rax` points at 8192, fully permissive zeroed memory. -/
def fpZeugeKern : Zustand :=
  { register := fun q => if q = Register.rax then BitVec.ofNat 64 8192 else BitVec.ofNat 64 0
    flags := ⟨false, true, some false, false, false, false⟩
    rip := BitVec.ofNat 64 4096
    speicher := zeugenSpeicher }

/-- Witness extended state: reset FP control word (admitted profile). -/
def fpZeugeT : FpZustand := ⟨fpZeugeKern, fpZeugeXmm, kontextReset⟩

/-- The witness `xmm0` holds `1.0`. -/
theorem fpZeuge_tief0 :
    xmmTief fpZeugeT.xmm XmmReg.xmm0 = 0x3FF0000000000000 := by
  decide

/-- The witness `xmm1` holds `+0.0`. -/
theorem fpZeuge_tief1 : xmmTief fpZeugeT.xmm XmmReg.xmm1 = 0 := by
  decide

/-- The witness store address: `rax + 0` is 8192. -/
theorem fpZeuge_effAddr :
    effAddr fpZeugeT.kern Register.rax 0 = BitVec.ofNat 64 8192 := by
  decide

/-- Admitted profile on the witness state. -/
theorem fpZeuge_fp : fpEintritt fpZeugeT.fp = true := by
  decide

/-- Witness decode lengths are checked data. -/
theorem fpZeuge_laenge : laengeOk 4 = true := by
  decide

/-- Divide special case: `1.0 / +0.0` is `+∞`. -/
theorem div_eins_durch_null :
    fpRechne .div 0x3FF0000000000000 0 = 0x7FF0000000000000 := by
  decide

/-- Signed-zero special case: `+0.0 + -0.0` is `+0.0`. -/
theorem add_plusnull_minusnull :
    fpRechne .add 0 0x8000000000000000 = 0 := by
  decide

/-- Witness state after the divide: `xmm0` holds `+∞`. -/
def fpZeugeT1 : FpZustand :=
  { fpZeugeT with kern := { fpZeugeT.kern with rip := ripNach fpZeugeT.kern.rip 4 }, xmm := xmmSchreibeTief fpZeugeT.xmm XmmReg.xmm0 0x7FF0000000000000 }

/-- Witness memory after the store: `+∞` at 8192. -/
def fpZeugeSpeicherNach : Speicher :=
  { zeugenSpeicher with bytes := writeBytes zeugenSpeicher (BitVec.ofNat 64 8192) 0x7FF0000000000000 }

/-- Witness state after the store. -/
def fpZeugeT2 : FpZustand :=
  { fpZeugeT1 with kern := { fpZeugeT1.kern with speicher := fpZeugeSpeicherNach, rip := ripNach fpZeugeT1.kern.rip 4 } }

/-- First reached step: the divide computes `+∞` into `xmm0`. -/
theorem fpZeuge_schritt1 :
    fpSchritt ⟨.divsdRR XmmReg.xmm0 XmmReg.xmm1, 4⟩ fpZeugeT = some fpZeugeT1 := by
  have h := fpSchritt_divsdRR ⟨.divsdRR XmmReg.xmm0 XmmReg.xmm1, 4⟩ fpZeugeT
    XmmReg.xmm0 XmmReg.xmm1 fpZeuge_laenge fpZeuge_fp rfl
  rw [fpZeuge_tief0, fpZeuge_tief1, div_eins_durch_null] at h
  exact h

/-- After the divide, `xmm0` holds `+∞`. -/
theorem fpZeugeT1_tief0 :
    xmmTief fpZeugeT1.xmm XmmReg.xmm0 = 0x7FF0000000000000 := by
  decide

/-- The divide changes no memory byte. -/
theorem fpZeugeT1_speicher : fpZeugeT1.kern.speicher = zeugenSpeicher :=
  rfl

/-- The store address is still 8192 after the divide. -/
theorem fpZeugeT1_effAddr :
    effAddr fpZeugeT1.kern Register.rax 0 = BitVec.ofNat 64 8192 := by
  decide

/-- The store goes through: `+∞` lands at 8192. -/
theorem fpZeuge_schreib :
    write64 fpZeugeT1.kern.speicher (effAddr fpZeugeT1.kern Register.rax 0)
      (xmmTief fpZeugeT1.xmm XmmReg.xmm0) = some fpZeugeSpeicherNach := by
  rw [fpZeugeT1_speicher, fpZeugeT1_effAddr, fpZeugeT1_tief0]
  unfold write64
  have hc : schreibbar8 zeugenSpeicher (BitVec.ofNat 64 8192) = true := rfl
  rw [if_pos hc]
  rfl

/-- Second reached step: the store writes `xmm0` to `[rax]`. -/
theorem fpZeuge_schritt2 :
    fpSchritt ⟨.movsdSpeichere Register.rax XmmReg.xmm0 0, 4⟩ fpZeugeT1 =
      some fpZeugeT2 := by
  exact fpSchritt_movsdSpeichere_erfolg
    ⟨.movsdSpeichere Register.rax XmmReg.xmm0 0, 4⟩ fpZeugeT1
    Register.rax XmmReg.xmm0 0 fpZeugeSpeicherNach
    fpZeuge_laenge fpZeuge_fp rfl fpZeuge_schreib

/-- The stored word reads back: `+∞` at 8192. -/
theorem fpZeuge_liest :
    read64 fpZeugeT2.kern.speicher (BitVec.ofNat 64 8192) =
      some 0x7FF0000000000000 := by
  have hrd : lesbar8 zeugenSpeicher (BitVec.ofNat 64 8192) = true := rfl
  exact read64_nach_write64 _ _ _ _ fpZeuge_schreib hrd

/-- The store observably changed memory (footprint top byte). -/
theorem fpZeuge_speicher_aendert :
    fpZeugeT.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) ≠
      fpZeugeT2.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) := by
  decide

/-- Joint witness: divide special case computed, stored, read back, with
    real memory change -- two reached steps under the admitted profile. -/
theorem fpZeuge_div_unendlich_speichert :
    ∃ (t' t'' : FpZustand),
      fpSchritt ⟨.divsdRR XmmReg.xmm0 XmmReg.xmm1, 4⟩ fpZeugeT = some t'
      ∧ fpSchritt ⟨.movsdSpeichere Register.rax XmmReg.xmm0 0, 4⟩ t' = some t''
      ∧ read64 t''.kern.speicher (BitVec.ofNat 64 8192) = some 0x7FF0000000000000
      ∧ fpZeugeT.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) ≠
          t''.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) :=
  ⟨fpZeugeT1, fpZeugeT2, fpZeuge_schritt1, fpZeuge_schritt2, fpZeuge_liest,
    fpZeuge_speicher_aendert⟩

/- CUTS:
   - NaN relation is class-level only: payload equality of computed NaN
     results is never concluded (Gleitprofil §7 owns the explicit gap).
     The non-observability lemma (no consumer distinguishes two NaN
     payloads through any program-observable channel) is OPEN.
   - SNaN has no model form: `Klasse` carries a single `.nan`, so quiet
     versus signalling inputs are indistinguishable by construction, and
     no SNaN exception/trap behaviour is modelled (MXCSR masks are
     admission-checked, never semantically executed).
   - Sticky MXCSR flags (bits 0-5) are unchecked and unmodelled
     (Gleitprofil §2); flag accumulation across steps stays open.
   - No encoder/decoder: `FpDecodiert.laenge` is checked input data
     (1..15) and `FpBefehl` values arrive constructed, never decoded
     from bytes. x87, FMA and packed/AVX encodings have no constructor:
     syntactically absent, not dynamically refused.
   - No source `float` (f32) node exists (`Ty.fl` is widthless binary64,
     `Typen.lean`): the bridge is f64-only by type. Double rounding and
     the f32-vs-f64 counterexample stay owned by lane 286, never
     duplicated here.
   - One source op = one machine op is proved for the four arithmetic
     forms (`fpRechne_gleitRechne`); reassociation, FMA contraction,
     value-range propagation and any cross-op rewrite are NOT admitted
     and have no theorem here.
   - No TSO/concurrency claim: `fpSchritt` is sequential over one
     `Speicher`; aligned multi-byte atomicity, tearing, and the GX
     refinement stay with the TSO-bridge lane. `laufAlt` lifts the old
     14-form step unchanged (XMM/MXCSR untouched); no interleaving of
     old and new forms is modelled.
   - No cost/timing claim: per-instruction latency, CAS retry bounds and
     budget transfer are open.
   - Rule 13 (inhabitation): no theorem here quantifies over the listed
     source-syntax types (`Vertrag`, `Stmt`, `Endblock`, `ErgExpr`,
     `Expr`, `Args`); `FpBefehl` is target syntax and `GleitOp` range
     over the model op, whose joint divide instance is proved
     (`fpRechne_gleitRechne_zeuge`, `fpRechne_klasse_zeuge`). The joint
     non-degenerate witness is `fpZeuge_div_unendlich_speichert`: two
     reached steps with a real memory change.
-/

#print axioms fpRechne_gleitRechne
#print axioms fpRechne_klasse
#print axioms cvttPaket_gleicht_gleitRoh
#print axioms fpXmmZahl_le_zwei
#print axioms bites64_wf
#print axioms ucomiFlags_reserviert
#print axioms ucomiFlags_nan_klasse_nur
#print axioms div_eins_durch_null
#print axioms add_plusnull_minusnull
#print axioms fpZeuge_div_unendlich_speichert

end Gabbro.Grammatik.X86
