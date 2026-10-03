/-
  File:      Grammatik/X86/ScalarFloat32FetchedSteps.lean
  Subject:   Fetched binary32 steps with a lifting API for the FP consumer.

  Lane 1108: fetched execution for the accepted S32Op rows (ADDSS/SUBSS/
  MULSS/DIVSS register shapes) on per-core FP state (`FpZustand`) over the
  shared memory (`Speicher`, `read32`/`write32`), reusing the accepted
  binary32 kernel routing (`s32Rechne` via `Gleitprofil.fadd32/fsub32/
  fmul32/fdiv32`) and 724-style control inputs (silicon bit, OS XMM state,
  MXCSR profiles from lane 682, raw MXCSR control, XMM upper-lane
  preservation). The CVTSD2SS narrowing witness reuses the 702
  f32-vs-f64 counterexample pattern (`s32_stallt_bei_2hoch24`), never a
  new interpreter. Sticky-flag accumulation, NaN payloads and silicon
  correspondence stay OPEN (CUTS). The lifting interface is explicit
  named definitions with exact signatures; consumer 724 is never
  imported. No source, checker, emitter or goal claim.

  Manual provenance (local snapshot `.tmp/HARDWARE-REFERENCES/`):
  Intel SDM combined Vols 1-4, edition 325462-093US September 2026,
  Vol. 1 Chap. 5 §5.5.1.2 (scalar single arithmetic), Chap. 10
  §10.4.1.2 (low-doubleword semantics) and §10.2.3 (MXCSR layout).
-/
import Grammatik.X86.ScalarFloat32HardwareForms
import Grammatik.X86.FpControlHardwareForms

namespace Gabbro.Grammatik.X86

/-- Lane marker: the fetched binary32 step layer over the accepted S32 rows. -/
def s32FetchedSchicht : Nat := 32

/-- The layer marker is binary32. -/
theorem s32FetchedSchicht_ist_f32 : s32FetchedSchicht = 32 := rfl

/-! ## 1. Fetched control inputs (724-style): silicon, OS state, 682 profile.

  The fetched binary32 layer runs under an explicit control bundle: the
  silicon support bit (`S32Hw`), the OS vector state (`osXmm`), and the
  lane-682 MXCSR hardware profile (`MxcsrProfil`). Admission is the
  conjunction of the accepted silicon/OS/profile gate (`s32Zugelassen`,
  which carries the shared raw-MXCSR check `s32Eintritt`) and the 682
  architectural load check (`ldmxcsrArchOk`) on the RAW control word:
  the word is read, never rewritten, by any step below. -/

/-- Fetched binary32 control bundle: silicon support, OS vector state,
    and the 682 MXCSR hardware profile. Consumer 724 supplies all three;
    no default is assumed. -/
structure S32FetchedKontrolle where
  hw : S32Hw
  osXmm : Bool
  profil : MxcsrProfil
  deriving DecidableEq, Repr

/-- Admission: silicon AND OS state AND the shared MXCSR profile AND the
    682 architectural load check on the raw control word. `false` is a
    validator refusal, never a hardware fault. -/
def s32FetchedZugelassen (k : S32FetchedKontrolle) (fp : FPKontext) : Bool :=
  s32Zugelassen k.hw k.osXmm fp && ldmxcsrArchOk k.profil fp.mxcsr

/-- The reset control word is admitted under the modern profile. -/
theorem s32FetchedZugelassen_reset :
    s32FetchedZugelassen ⟨⟨true⟩, true, mxcsrProfilModern⟩ kontextReset = true := by
  have h1 : s32Zugelassen (⟨true⟩ : S32Hw) true kontextReset = true := by
    simp [s32Zugelassen, s32Eintritt_reset]
  have h2 : ldmxcsrArchOk mxcsrProfilModern kontextReset.mxcsr = true :=
    ldmxcsrArchOk_reset_modern
  unfold s32FetchedZugelassen
  simp [h1, h2]

/-- Admission projects to the silicon/OS/profile gate and the 682 check:
    both conjuncts hold wherever admission holds. -/
theorem s32FetchedZugelassen_profil (k : S32FetchedKontrolle) (fp : FPKontext)
    (h : s32FetchedZugelassen k fp = true) :
    s32Zugelassen k.hw k.osXmm fp = true
      ∧ ldmxcsrArchOk k.profil fp.mxcsr = true := by
  unfold s32FetchedZugelassen at h
  simp only [Bool.and_eq_true] at h
  exact h

/-- Without silicon support nothing is admitted. -/
theorem s32FetchedZugelassen_ohne_silizium (osXmm : Bool)
    (p : MxcsrProfil) (fp : FPKontext) :
    s32FetchedZugelassen ⟨⟨false⟩, osXmm, p⟩ fp = false := by
  unfold s32FetchedZugelassen s32Zugelassen
  simp

/-- Without OS vector state nothing is admitted (silicon present). -/
theorem s32FetchedZugelassen_ohne_os (fp : FPKontext) (p : MxcsrProfil) :
    s32FetchedZugelassen ⟨⟨true⟩, false, p⟩ fp = false := by
  unfold s32FetchedZugelassen s32Zugelassen
  simp

/-- A refused control word admits nothing (validator refusal, not a fault). -/
theorem s32FetchedZugelassen_ohne_profil (k : S32FetchedKontrolle)
    (fp : FPKontext) (h : s32Eintritt fp = false) :
    s32FetchedZugelassen k fp = false := by
  unfold s32FetchedZugelassen s32Zugelassen
  simp [h]

/-- A 682-architecturally refused word admits nothing. -/
theorem s32FetchedZugelassen_arch_verweigert (k : S32FetchedKontrolle)
    (fp : FPKontext) (h : ldmxcsrArchOk k.profil fp.mxcsr = false) :
    s32FetchedZugelassen k fp = false := by
  unfold s32FetchedZugelassen
  simp [h]

/-! ## 2. Fetched step agreement per S32Op row.

  Every arithmetic op denotes one fetched register form (`s32OpForm`).
  The fetched step agrees with the accepted `s32Schritt` row equation:
  the low single is the kernel value (`s32Rechne`, hence
  `Gleitprofil.fadd32/fsub32/fmul32/fdiv32` via `muster32`/`bites32`),
  the upper 96 bits survive, the raw MXCSR control word passes through
  untouched (no sticky accumulation exists here), and RIP advances past
  the decode length. Shared buffered memory (`Speicher`) is threaded by
  the reused `read32`/`write32`; TSO/store-buffer tearing of the
  four-byte accesses stays OPEN (CUTS). -/

/-- The fetched register form denoting an arithmetic op: one
    constructor per accepted kernel op. Consumer 724 matches on exactly
    these constructors; a new row is a loud addition here, not a silent
    admission there. -/
def s32OpForm : S32Op → XmmReg → XmmReg → S32Befehl
  | .add, dst, src => .addssRR dst src
  | .sub, dst, src => .subssRR dst src
  | .mul, dst, src => .mulssRR dst src
  | .div, dst, src => .divssRR dst src

/-- Fetched arithmetic frame: a fetched step through a low-single write
    delivers the written value, keeps the upper 96 bits and the raw
    control word, and advances RIP past the decode length. Every
    premise is fetch/step evidence. -/
theorem s32Fetched_rahmen_arith (dst : XmmReg) (t t1 : FpZustand)
    (d : S32Decodiert) (rest : List Byte) (w : BitVec 32)
    (hf : s32FetchDekodiert t = some (d, rest))
    (hstep : s32Schritt d t = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSchreibeTief32 t.xmm dst w })
    (hout : s32Byteschritt t = .weiter t1) :
    xmmTief32 t1.xmm dst = w
    ∧ (t1.xmm dst).toNat / 2 ^ 32 = (t.xmm dst).toNat / 2 ^ 32
    ∧ t1.fp = t.fp
    ∧ t1.kern.rip = ripNach t.kern.rip d.laenge := by
  have hbyte := s32Byteschritt_weiter t _ d rest hf hstep
  rw [hout] at hbyte
  cases hbyte
  refine ⟨?_, ?_, rfl, rfl⟩
  · exact xmmSchreibeTief32_tief _ _ _
  · exact xmmSchreibeTief32_hoch96 _ _ _

/-- Fetched step agreement per S32Op row: under admitted control, the
    fetched register form of each op computes the kernel value with the
    upper lanes, the raw control word and RIP framed as above. -/
theorem s32Fetched_schritt (k : S32FetchedKontrolle) (op : S32Op)
    (dst src : XmmReg) (t t1 : FpZustand) (d : S32Decodiert)
    (rest : List Byte)
    (hz : s32FetchedZugelassen k t.fp = true)
    (hok : laengeOk d.laenge = true)
    (hf : s32FetchDekodiert t = some (d, rest))
    (hform : d.befehl = s32OpForm op dst src)
    (hout : s32Byteschritt t = .weiter t1) :
    xmmTief32 t1.xmm dst = s32Rechne op (xmmTief32 t.xmm dst) (xmmTief32 t.xmm src)
    ∧ (t1.xmm dst).toNat / 2 ^ 32 = (t.xmm dst).toNat / 2 ^ 32
    ∧ t1.fp = t.fp
    ∧ t1.kern.rip = ripNach t.kern.rip d.laenge := by
  have hz1 := (s32FetchedZugelassen_profil k t.fp hz).1
  simp only [s32Zugelassen, Bool.and_eq_true] at hz1
  obtain ⟨⟨_, _⟩, hfp⟩ := hz1
  cases op with
  | add =>
    have hform' : d.befehl = .addssRR dst src := hform
    have hstep := s32Schritt_addssRR d t dst src hok hfp hform'
    exact s32Fetched_rahmen_arith dst t t1 d rest
      (s32Rechne .add (xmmTief32 t.xmm dst) (xmmTief32 t.xmm src))
      hf hstep hout
  | sub =>
    have hform' : d.befehl = .subssRR dst src := hform
    have hstep := s32Schritt_subssRR d t dst src hok hfp hform'
    exact s32Fetched_rahmen_arith dst t t1 d rest
      (s32Rechne .sub (xmmTief32 t.xmm dst) (xmmTief32 t.xmm src))
      hf hstep hout
  | mul =>
    have hform' : d.befehl = .mulssRR dst src := hform
    have hstep := s32Schritt_mulssRR d t dst src hok hfp hform'
    exact s32Fetched_rahmen_arith dst t t1 d rest
      (s32Rechne .mul (xmmTief32 t.xmm dst) (xmmTief32 t.xmm src))
      hf hstep hout
  | div =>
    have hform' : d.befehl = .divssRR dst src := hform
    have hstep := s32Schritt_divssRR d t dst src hok hfp hform'
    exact s32Fetched_rahmen_arith dst t t1 d rest
      (s32Rechne .div (xmmTief32 t.xmm dst) (xmmTief32 t.xmm src))
      hf hstep hout

/-! ## 3. CVTSD2SS narrowing witness: f32 versus f64.

  The narrowing computation below is evaluated once, here, through the
  accepted kernel (`cvtSD2SS`, hence `rundeExakt` RNE). The f32-vs-f64
  DISTINCTION reuses the accepted 702 counterexample pattern instead of
  re-proving it: binary32 stalls at `2^24` (`s32_stallt_bei_2hoch24`)
  while binary64 advances (`s32_f64_steigt_weiter`). The narrowed value
  here IS the stalled f32 value. -/

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2048 in
/-- Narrowing `2^24 + 1` (exact in f64 as `0x4170000010000000`) rounds
    back to `2^24` (`0x4B800000`) in f32: the kernel round, RNE
    ties-to-even, never a truncation. -/
theorem s32Narrowing_2hoch24plus1 :
    muster32 (cvtSD2SS (bites64 0x4170000010000000)) = 0x4B800000 := by
  decide

/-- Fetched CVTSD2SS narrowing: under admitted control, the fetched
    conversion of the exact f64 `2^24 + 1` writes the stalled f32
    `2^24`, while the f64 lane advances; upper lanes and raw control
    framed as in §2. -/
theorem s32Fetched_narrowing (k : S32FetchedKontrolle)
    (dst src : XmmReg) (t t1 : FpZustand) (d : S32Decodiert)
    (rest : List Byte)
    (hz : s32FetchedZugelassen k t.fp = true)
    (hok : laengeOk d.laenge = true)
    (hf : s32FetchDekodiert t = some (d, rest))
    (hform : d.befehl = .cvtsd2ssRR dst src)
    (hx : xmmTief t.xmm src = 0x4170000010000000)
    (hout : s32Byteschritt t = .weiter t1) :
    xmmTief32 t1.xmm dst = 0x4B800000
    ∧ xmmTief32 t1.xmm dst = s32Rechne .add 0x4B800000 0x3F800000
    ∧ muster64 (fadd64 (bites64 0x4330000000000000)
        (bites64 0x3FF0000000000000)) ≠ 0x4330000000000000
    ∧ (t1.xmm dst).toNat / 2 ^ 32 = (t.xmm dst).toNat / 2 ^ 32
    ∧ t1.fp = t.fp := by
  have hz1 := (s32FetchedZugelassen_profil k t.fp hz).1
  simp only [s32Zugelassen, Bool.and_eq_true] at hz1
  obtain ⟨⟨_, _⟩, hfp⟩ := hz1
  have hstep := s32Schritt_cvtsd2ssRR d t dst src hok hfp hform
  rw [hx, s32Narrowing_2hoch24plus1] at hstep
  have h := s32Fetched_rahmen_arith dst t t1 d rest 0x4B800000 hf hstep hout
  refine ⟨h.1, ?_, s32_f64_steigt_weiter, h.2.1, h.2.2.1⟩
  rw [h.1]
  exact s32_stallt_bei_2hoch24.symm

/-! ## 4. Lifting interface for consumer 724.

  SMALL explicit interface, named definitions with exact signatures.
  Consumer 724 imports exactly these names once this module is
  accepted; each signature carries its contract, so a shape mismatch
  with 724 is a loud type error, not silent drift. The 724 module
  itself is never imported here.

  Contracts:
  - `S32FetchedKontrolle`: the control input. 724 supplies the silicon
    bit, the OS vector state and the 682 profile; admission is
    `s32FetchedZugelassen` (§1), fail-closed.
  - `s32LiftForm`: the fetched register form denoting an op. 724 must
    match on exactly the four constructors below; agreement with
    `s32OpForm` is proved (`s32LiftForm_stimmt`), so a fifth row is a
    loud addition here, never a silent admission there.
  - `s32LiftWert`: the value the lifted step must compute. It routes to
    the accepted kernel (`s32LiftWert_routen`, via `muster32`/`bites32`
    to `fadd32/fsub32/fmul32/fdiv32`); NaN payloads stay class-only.
  - `s32LiftSchritt`: the lifted fetched step. It runs the fetched
    form only under admission AND only where the fetched bytes decode
    to the lifted form; agreement with the byte step is proved
    (`s32LiftSchritt_stimmt`). -/

/-- Lifted form: the fetched register form denoting an op (see §4
    contract). -/
def s32LiftForm : S32Op → XmmReg → XmmReg → S32Befehl
  | .add, dst, src => .addssRR dst src
  | .sub, dst, src => .subssRR dst src
  | .mul, dst, src => .mulssRR dst src
  | .div, dst, src => .divssRR dst src

/-- Lifted value: the kernel value the lifted step computes (see §4
    contract). -/
def s32LiftWert : S32Op → BitVec 32 → BitVec 32 → BitVec 32
  | .add, a, b => s32Rechne .add a b
  | .sub, a, b => s32Rechne .sub a b
  | .mul, a, b => s32Rechne .mul a b
  | .div, a, b => s32Rechne .div a b

/-- Lifted fetched step: admission, then the fetched bytes, then the
    lifted form check, then the accepted step (see §4 contract). Takes
    only control, op, registers and state: no caller-supplied decoded
    value ever becomes trusted fetch. -/
def s32LiftSchritt (k : S32FetchedKontrolle) (op : S32Op)
    (dst src : XmmReg) (t : FpZustand) : S32Ausgang :=
  match s32FetchedZugelassen k t.fp with
  | false => .verweigert
  | true =>
    match s32FetchDekodiert t with
    | none => .verweigert
    | some (d, _) =>
      if d.befehl = s32LiftForm op dst src then
        match s32Schritt d t with
        | none => .verweigert
        | some t' => .weiter t'
      else .verweigert

/-- The lifted form agrees with the fetched row map on every op. -/
theorem s32LiftForm_stimmt (op : S32Op) (dst src : XmmReg) :
    s32LiftForm op dst src = s32OpForm op dst src := by
  cases op <;> rfl

/-- The lifted value routes to the accepted kernel on every op. -/
theorem s32LiftWert_routen (a b : BitVec 32) :
    s32LiftWert .add a b = muster32 (fadd32 (bites32 a) (bites32 b))
    ∧ s32LiftWert .sub a b = muster32 (fsub32 (bites32 a) (bites32 b))
    ∧ s32LiftWert .mul a b = muster32 (fmul32 (bites32 a) (bites32 b))
    ∧ s32LiftWert .div a b = muster32 (fdiv32 (bites32 a) (bites32 b)) := by
  have h := s32Rechne_routen a b
  exact h

/-- The lifted step runs the fetched form: admission, fetch, form
    check and step together continue exactly where the step leads. -/
theorem s32LiftSchritt_stimmt (k : S32FetchedKontrolle) (op : S32Op)
    (dst src : XmmReg) (t t1 : FpZustand) (d : S32Decodiert)
    (rest : List Byte)
    (hz : s32FetchedZugelassen k t.fp = true)
    (hf : s32FetchDekodiert t = some (d, rest))
    (hform : d.befehl = s32LiftForm op dst src)
    (hstep : s32Schritt d t = some t1) :
    s32LiftSchritt k op dst src t = .weiter t1 := by
  unfold s32LiftSchritt
  simp [hz, hf, hform, hstep]

/-- Interface inhabitation: every lifting signature has a proved
    provider -- the form map agrees with `s32OpForm`, the value map
    routes to the kernel, and the lifted step runs the fetched form. -/
theorem s32Fetched_lift_schnittstelle :
    (∀ op dst src, s32LiftForm op dst src = s32OpForm op dst src)
    ∧ (∀ a b, s32LiftWert .add a b = muster32 (fadd32 (bites32 a) (bites32 b))
      ∧ s32LiftWert .sub a b = muster32 (fsub32 (bites32 a) (bites32 b))
      ∧ s32LiftWert .mul a b = muster32 (fmul32 (bites32 a) (bites32 b))
      ∧ s32LiftWert .div a b = muster32 (fdiv32 (bites32 a) (bites32 b)))
    ∧ (∀ k op dst src t t1 d rest,
      s32FetchedZugelassen k t.fp = true →
      s32FetchDekodiert t = some (d, rest) →
      d.befehl = s32LiftForm op dst src → s32Schritt d t = some t1 →
      s32LiftSchritt k op dst src t = .weiter t1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro op dst src
    exact s32LiftForm_stimmt op dst src
  · intro a b
    exact s32LiftWert_routen a b
  · intro k op dst src t t1 d rest hz hf hform hstep
    exact s32LiftSchritt_stimmt k op dst src t t1 d rest hz hf hform hstep

/-! ## 5. Joint witness: arithmetic row, store, and narrowing row.

  The arithmetic half reuses the accepted 702 fetched run
  (`s32ZeugeT`: fetched ADDSS `1.0f + 2.0f = 3.0f`, then a fetched
  MOVSS store changing real RAM). The conversion half runs on a new
  witness below: fetched CVTSD2SS (`F2 0F 5A C0`) narrowing the exact
  f64 `2^24 + 1` to the stalled f32 `2^24`. Non-degeneracy follows the
  accepted X86 precedent: reached fetched runs with a real memory
  change plus register changes, never an empty run. (There is no
  Gabbro source table in scope at the X86 level; see the report.) -/

/-- Witness code bytes: CVTSD2SS xmm0, xmm0 (`F2 0F 5A C0`) at `0x3000`. -/
def s32FetchedEngBytes : Adresse → Byte :=
  fun a =>
    if a = BitVec.ofNat 64 0x3000 then natByte 242
    else if a = BitVec.ofNat 64 0x3001 then natByte 15
    else if a = BitVec.ofNat 64 0x3002 then natByte 90
    else if a = BitVec.ofNat 64 0x3003 then natByte 192
    else natByte 0

/-- Witness memory: the conversion above executable over
    `0x3000..0x3004`, everything readable and writable. -/
def s32FetchedEngMem : Speicher :=
  { bytes := s32FetchedEngBytes, lesbar := fun _ => true,
    schreibbar := fun _ => true,
    ausfuehrbar := fun a => 0x3000 ≤ a.toNat && a.toNat < 0x3004 }

/-- Witness XMM file: xmm0 holds the exact f64 `2^24 + 1` in its low
    double (`0x4170000010000000`). -/
def s32FetchedEngXmm : XmmDatei :=
  fun _ => BitVec.ofNat 128 0x4170000010000000

/-- Witness core: rip at the conversion, registers zero. -/
def s32FetchedEngKern : Zustand :=
  { register := fun _ => 0,
    flags := ⟨false, false, some false, false, false, false⟩,
    rip := BitVec.ofNat 64 0x3000, speicher := s32FetchedEngMem }

/-- Witness start state. -/
def s32FetchedEngT : FpZustand :=
  ⟨s32FetchedEngKern, s32FetchedEngXmm, kontextReset⟩

/-- Witness state after the narrowing: xmm0 holds `2^24` in its low
    single. -/
def s32FetchedEngT1 : FpZustand :=
  { s32FetchedEngT with
    kern := { s32FetchedEngT.kern with
      rip := ripNach (BitVec.ofNat 64 0x3000) 4 },
    xmm := xmmSchreibeTief32 s32FetchedEngXmm .xmm0 (0x4B800000 : BitVec 32) }

/-- The witness source holds the exact f64 `2^24 + 1`. -/
theorem s32FetchedEng_tief :
    xmmTief s32FetchedEngT.xmm .xmm0 = 0x4170000010000000 := by
  decide

/-- The witness control word is admitted. -/
theorem s32FetchedEng_fp : s32Eintritt s32FetchedEngT.fp = true := by
  unfold s32Eintritt
  exact kontextReset_gueltig

/-- FETCH: the actual code bytes decode to the narrowing form. -/
theorem s32FetchedEng_fetch :
    s32FetchDekodiert s32FetchedEngT =
      some (⟨.cvtsd2ssRR .xmm0 .xmm0, 4⟩, []) := by
  decide

/-- STEP: the narrowing computes `2^24` into xmm0. -/
theorem s32FetchedEng_schritt :
    s32Schritt ⟨.cvtsd2ssRR .xmm0 .xmm0, 4⟩ s32FetchedEngT
      = some s32FetchedEngT1 := by
  have heq := s32Schritt_cvtsd2ssRR ⟨.cvtsd2ssRR .xmm0 .xmm0, 4⟩
    s32FetchedEngT .xmm0 .xmm0 s32Zeuge_laenge4 s32FetchedEng_fp rfl
  rw [s32FetchedEng_tief, s32Narrowing_2hoch24plus1] at heq
  exact heq

/-- The narrowed witness value reads back in the low single. -/
theorem s32FetchedEng_tief32 :
    xmmTief32 s32FetchedEngT1.xmm .xmm0 = 0x4B800000 :=
  xmmSchreibeTief32_tief _ _ _

/-- Joint witness: every premise of all three targets, instantiated
    together -- admitted control, the fetched arithmetic row with its
    memory-changing store (real RAM change from the accepted 702 run),
    and the fetched narrowing row with the f32-vs-f64 value
    distinction. -/
theorem s32Fetched_gelenk_zeuge :
    ∃ (k : S32FetchedKontrolle) (dA : S32Decodiert) (restA : List Byte)
      (tA1 tA2 : FpZustand) (dE : S32Decodiert) (restE : List Byte)
      (tE1 : FpZustand),
      s32FetchedZugelassen k s32ZeugeT.fp = true
      ∧ laengeOk dA.laenge = true
      ∧ s32FetchDekodiert s32ZeugeT = some (dA, restA)
      ∧ dA.befehl = s32OpForm .add .xmm0 .xmm1
      ∧ s32Byteschritt s32ZeugeT = .weiter tA1
      ∧ s32Schritt dA s32ZeugeT = some tA1
      ∧ s32Byteschritt tA1 = .weiter tA2
      ∧ read32 tA2.kern.speicher (BitVec.ofNat 64 0x2000)
          = some (BitVec.ofNat 64 0x40400000)
      ∧ tA2.kern.speicher.bytes (BitVec.ofNat 64 0x2002)
          ≠ s32ZeugeMem.bytes (BitVec.ofNat 64 0x2002)
      ∧ s32FetchedZugelassen k s32FetchedEngT.fp = true
      ∧ laengeOk dE.laenge = true
      ∧ s32FetchDekodiert s32FetchedEngT = some (dE, restE)
      ∧ dE.befehl = .cvtsd2ssRR .xmm0 .xmm0
      ∧ xmmTief s32FetchedEngT.xmm .xmm0 = 0x4170000010000000
      ∧ s32Byteschritt s32FetchedEngT = .weiter tE1
      ∧ s32Schritt dE s32FetchedEngT = some tE1
      ∧ xmmTief32 tE1.xmm .xmm0 = 0x4B800000
      ∧ xmmTief32 tE1.xmm .xmm0
          = s32Rechne .add 0x4B800000 0x3F800000 := by
  obtain ⟨u1, u2, hb1, hb2, hrd, hdiff⟩ := s32Zeuge_fetched_lauf
  have hb1' : s32Byteschritt s32ZeugeT = .weiter s32ZeugeT1 :=
    s32Byteschritt_weiter _ _ _ _ s32Zeuge_fetch1 s32Zeuge_schritt1
  rw [hb1'] at hb1
  cases hb1
  have houtE : s32Byteschritt s32FetchedEngT = .weiter s32FetchedEngT1 :=
    s32Byteschritt_weiter _ _ _ _ s32FetchedEng_fetch s32FetchedEng_schritt
  have hE2 : xmmTief32 s32FetchedEngT1.xmm .xmm0
      = s32Rechne .add 0x4B800000 0x3F800000 := by
    rw [s32FetchedEng_tief32]
    exact s32_stallt_bei_2hoch24.symm
  refine ⟨⟨⟨true⟩, true, mxcsrProfilModern⟩, ⟨.addssRR .xmm0 .xmm1, 4⟩,
    [natByte 243, natByte 15, natByte 17, natByte 128, natByte 0,
      natByte 0, natByte 0, natByte 0],
    s32ZeugeT1, u2, ⟨.cvtsd2ssRR .xmm0 .xmm0, 4⟩, [], s32FetchedEngT1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · exact s32FetchedZugelassen_reset
  · exact s32Zeuge_laenge4
  · exact s32Zeuge_fetch1
  · rfl
  · exact hb1'
  · exact s32Zeuge_schritt1
  · exact hb2
  · exact hrd
  · exact hdiff
  · exact s32FetchedZugelassen_reset
  · exact s32Zeuge_laenge4
  · exact s32FetchedEng_fetch
  · rfl
  · exact s32FetchedEng_tief
  · exact houtE
  · exact s32FetchedEng_schritt
  · exact s32FetchedEng_tief32
  · exact hE2

/-! ## 6. Target witnesses: one companion per target.

  Each `ZEUGE` companion instantiates ALL premises of its target
  jointly from §5, with the target conclusion proved alongside. -/

/-- Witness for the fetched-step target: all its premises together on
    the arithmetic run, with the kernel value, upper lanes, raw
    control and RIP concluded. -/
theorem s32Fetched_schritt_zeuge :
    ∃ (k : S32FetchedKontrolle) (d : S32Decodiert) (rest : List Byte)
      (t1 : FpZustand),
      s32FetchedZugelassen k s32ZeugeT.fp = true
      ∧ laengeOk d.laenge = true
      ∧ s32FetchDekodiert s32ZeugeT = some (d, rest)
      ∧ d.befehl = s32OpForm .add .xmm0 .xmm1
      ∧ s32Byteschritt s32ZeugeT = .weiter t1
      ∧ xmmTief32 t1.xmm .xmm0
          = s32Rechne .add (xmmTief32 s32ZeugeT.xmm .xmm0)
              (xmmTief32 s32ZeugeT.xmm .xmm1)
      ∧ (t1.xmm .xmm0).toNat / 2 ^ 32
          = (s32ZeugeT.xmm .xmm0).toNat / 2 ^ 32
      ∧ t1.fp = s32ZeugeT.fp
      ∧ t1.kern.rip = ripNach s32ZeugeT.kern.rip d.laenge := by
  obtain ⟨k, dA, restA, tA1, tA2, dE, restE, tE1, hzA, hokA, hfA, hformA,
    houtA, hsA, houtA2, hrd, hdiff, hzE, hokE, hfE, hformE, hxE, houtE,
    hsE, hE1, hE2⟩ := s32Fetched_gelenk_zeuge
  have h := s32Fetched_schritt k .add .xmm0 .xmm1 s32ZeugeT tA1 dA
    restA hzA hokA hfA hformA houtA
  exact ⟨k, dA, restA, tA1, hzA, hokA, hfA, hformA, houtA, h.1, h.2.1,
    h.2.2.1, h.2.2.2⟩

/-- Witness for the narrowing target: all its premises together on
    the conversion run, with the stalled value and the f32-vs-f64
    distinction concluded. -/
theorem s32Fetched_narrowing_zeuge :
    ∃ (k : S32FetchedKontrolle) (d : S32Decodiert) (rest : List Byte)
      (t1 : FpZustand),
      s32FetchedZugelassen k s32FetchedEngT.fp = true
      ∧ laengeOk d.laenge = true
      ∧ s32FetchDekodiert s32FetchedEngT = some (d, rest)
      ∧ d.befehl = .cvtsd2ssRR .xmm0 .xmm0
      ∧ xmmTief s32FetchedEngT.xmm .xmm0 = 0x4170000010000000
      ∧ s32Byteschritt s32FetchedEngT = .weiter t1
      ∧ xmmTief32 t1.xmm .xmm0 = 0x4B800000
      ∧ xmmTief32 t1.xmm .xmm0 = s32Rechne .add 0x4B800000 0x3F800000
      ∧ muster64 (fadd64 (bites64 0x4330000000000000)
          (bites64 0x3FF0000000000000)) ≠ 0x4330000000000000 := by
  obtain ⟨k, dA, restA, tA1, tA2, dE, restE, tE1, hzA, hokA, hfA, hformA,
    houtA, hsA, houtA2, hrd, hdiff, hzE, hokE, hfE, hformE, hxE, houtE,
    hsE, hE1, hE2⟩ := s32Fetched_gelenk_zeuge
  have h := s32Fetched_narrowing k .xmm0 .xmm0 s32FetchedEngT tE1 dE
    restE hzE hokE hfE hformE hxE houtE
  exact ⟨k, dE, restE, tE1, hzE, hokE, hfE, hformE, hxE, houtE, h.1,
    h.2.1, h.2.2.1⟩

/-- Witness for the interface target: every lifting signature with a
    proved provider on the arithmetic run -- the form map, the kernel
    value at the witness patterns, and the lifted step continuing. -/
theorem s32Fetched_lift_schnittstelle_zeuge :
    ∃ (k : S32FetchedKontrolle) (d : S32Decodiert) (rest : List Byte)
      (t1 : FpZustand),
      s32LiftForm .add .xmm0 .xmm1 = s32OpForm .add .xmm0 .xmm1
      ∧ s32LiftWert .add 0x3F800000 0x40000000 = 0x40400000
      ∧ s32FetchedZugelassen k s32ZeugeT.fp = true
      ∧ s32FetchDekodiert s32ZeugeT = some (d, rest)
      ∧ d.befehl = s32LiftForm .add .xmm0 .xmm1
      ∧ s32Schritt d s32ZeugeT = some t1
      ∧ s32LiftSchritt k .add .xmm0 .xmm1 s32ZeugeT
          = .weiter t1 := by
  obtain ⟨k, dA, restA, tA1, tA2, dE, restE, tE1, hzA, hokA, hfA, hformA,
    houtA, hsA, houtA2, hrd, hdiff, hzE, hokE, hfE, hformE, hxE, houtE,
    hsE, hE1, hE2⟩ := s32Fetched_gelenk_zeuge
  have hformL : dA.befehl = s32LiftForm .add .xmm0 .xmm1 := by
    rw [s32LiftForm_stimmt]
    exact hformA
  have hwert : s32LiftWert .add 0x3F800000 0x40000000 = 0x40400000 :=
    s32_eins_plus_zwei
  have hlift := s32LiftSchritt_stimmt k .add .xmm0 .xmm1 s32ZeugeT tA1
    dA restA hzA hfA hformL hsA
  exact ⟨k, dA, restA, tA1, s32LiftForm_stimmt .add .xmm0 .xmm1, hwert,
    hzA, hfA, hformL, hsA, hlift⟩

/-! ## 7. Planted probes: refused claims.

  Three negative probes pin the boundary: a narrowing claimed without
  length evidence refuses, a sticky-flag accumulation claim is refused
  by raw control passthrough, and an XMM-upper clobber is refused by
  preservation -- generally and on a nonzero-upper instance. -/

/-- NARROWING WITHOUT EVIDENCE REFUSED: a conversion claim with no
    decode length refuses explicitly. -/
theorem s32Sonde_engung_ohne_laenge (t : FpZustand) :
    s32Schritt ⟨.cvtsd2ssRR .xmm0 .xmm0, 0⟩ t = none :=
  s32Schritt_laenge_verweigert _ t (by decide)

/-- STICKY ACCUMULATION REFUSED: an arithmetic step passes the control
    word through raw -- no sticky flag is set, cleared or
    accumulated. -/
theorem s32Sonde_klebrig_verweigert (d : S32Decodiert) (t t' : FpZustand)
    (dst src : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true)
    (h : d.befehl = .addssRR dst src)
    (hstep : s32Schritt d t = some t') :
    t'.fp.mxcsr = t.fp.mxcsr := by
  rw [s32Schritt_addssRR d t dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- UPPER CLOBBER REFUSED: an arithmetic step preserves the upper 96
    bits at its destination -- any clearing claim is false. -/
theorem s32Sonde_obere_xmm_verweigert (d : S32Decodiert) (t t' : FpZustand)
    (dst src : XmmReg)
    (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true)
    (h : d.befehl = .addssRR dst src)
    (hstep : s32Schritt d t = some t') :
    (t'.xmm dst).toNat / 2 ^ 32 = (t.xmm dst).toNat / 2 ^ 32 :=
  s32Schritt_addssRR_hoch d t t' dst src hok hfp h hstep

/-- UPPER CLOBBER REFUSED, concrete nonzero instance: a write into a
    nonzero upper half keeps it nonzero. -/
theorem s32Sonde_obere_xmm_konkret :
    (setzeTief32 0x123456789ABCDEF00A0B0C0D3F800000 0x40400000).toNat
      / 2 ^ 32 ≠ 0 := by
  decide

/- CUTS:
   Proved here (all over the REUSED accepted vocabulary -- no new
   machine, no new decoder row, no new evaluator, no new IEEE
   arithmetic, no source/checker/goal claim):
   - fetched control (§1): silicon/OS/682-profile bundle with
     fail-closed admission, the reset word admitted, per-conjunct
     refusals and projection to both gates;
   - fetched step agreement per S32Op row (§2): register ADDSS/SUBSS/
     MULSS/DIVSS through the accepted kernel routing, with upper-96,
     raw-MXCSR and RIP frames;
   - CVTSD2SS narrowing (§3): the exact f64 `2^24 + 1` narrows to the
     stalled f32 `2^24`, reusing the accepted 702 f32-vs-f64 pattern
     (`s32_stallt_bei_2hoch24`, `s32_f64_steigt_weiter`) for the
     distinction instead of re-proving it;
   - lifting interface (§4): form/value/step signatures with proved
     providers for consumer 724 (724 never imported here);
   - joint witness (§5) with one companion per target (§6): all
     premises together on the accepted 702 arithmetic-plus-store run
     and the new narrowing run, with real RAM change;
   - planted probes (§7): narrowing without length, sticky
     accumulation, and upper clobber -- all refused.
   OPEN (essential, never claimed): sticky-flag accumulation across
   steps (control passes through raw; `Gleitprofil` §7 owns the gap);
   NaN payload/quiet-bit discipline of computed and narrowed results
   (class only); SNaN versus QNaN; DAZ/FTZ execution (admission
   refuses them); denormal inputs to narrowing; memory-source
   arithmetic rows (no fetched RM agreement here -- RR rows only);
   integer conversion rows (no fetched CVTSI2SS/CVTTSS2SI agreement);
   compare/move rows (no fetched UCOMISS/MOVSS agreement -- the store
   runs only inside the reused witness); TSO/store-buffer tearing of
   the four-byte accesses and the GX bridge; faults beyond explicit
   refusal (no #XM/#GP/#PF delivery is modelled); timing/budget
   transfer; silicon correspondence of any byte row; integration into
   `decodeExt`/`stepExt` and consumer 724 (awaits their owners); the
   umbrella `Grammatik.lean` import (this lane owns only its module
   and report, so the integration owner adds it).
-/

#print axioms s32FetchedZugelassen_reset
#print axioms s32FetchedZugelassen_profil
#print axioms s32Fetched_schritt
#print axioms s32Narrowing_2hoch24plus1
#print axioms s32Fetched_narrowing
#print axioms s32LiftForm_stimmt
#print axioms s32LiftWert_routen
#print axioms s32LiftSchritt_stimmt
#print axioms s32Fetched_lift_schnittstelle
#print axioms s32Fetched_gelenk_zeuge
#print axioms s32Fetched_schritt_zeuge
#print axioms s32Fetched_narrowing_zeuge
#print axioms s32Fetched_lift_schnittstelle_zeuge
#print axioms s32Sonde_engung_ohne_laenge
#print axioms s32Sonde_klebrig_verweigert
#print axioms s32Sonde_obere_xmm_verweigert

end Gabbro.Grammatik.X86
