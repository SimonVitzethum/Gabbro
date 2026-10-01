/-
  File:      Grammatik/X86/FloatEntryState.lean
  Subject:   Entry control-state admission for admitted scalar FP execution.

  Lane 626: connects the actual `ScalarFloat` extended state
  (`FpZustand`/`fpEintritt` over the `mxcsrGueltig` profile), the
  `EntryState` entry control-state discipline (`mxcsrOk` over the
  per-entry `EintrittZustand` word) and the `FeatureProfile`
  silicon/readiness admission (`bereit`/`merkmalZugelassen`).
  Proves MXCSR word validity decomposition and preservation across
  actual admitted FP steps, and refuses FTZ/DAZ, non-nearest rounding
  and unsupported exception/control encodings at the entry predicate.
  No new executor, no second decoder, no source/checker/emitter change.
-/
import Grammatik.X86.ScalarFloat
import Grammatik.X86.EntryState
import Grammatik.X86.FeatureProfile
import Grammatik.X86.ContractSites

namespace Gabbro.Grammatik.X86

/-- The entry's FP context: the entry state's own MXCSR word as the
    per-context control word (software establishment is ordinary data
    movement of this word; no OS/hardware switch semantics claimed). -/
def eintrittFp (z : EintrittZustand) : FPKontext := ⟨z.mxcsr⟩

/-- Entry admission at the control word IS the FP profile admission:
    the entry word as a context meets `fpEintritt` exactly when the
    word is profile-valid. -/
theorem eintrittFp_profil (z : EintrittZustand) :
    fpEintritt (eintrittFp z) = mxcsrGueltig z.mxcsr := rfl

/-! ## 1. MXCSR word validity, decomposed.

  `mxcsrGueltig` is one conjunction; every admitted word meets each
  leg (round-to-nearest-even, no flush-to-zero, no denormals-are-zero,
  every exception mask set). Sticky flags (bits 0-5) stay unchecked
  by construction (Gleitprofil §2 owns the gap). -/

/-- An admitted word meets every leg of the profile: nearest-even
    rounding, FTZ off, DAZ off, all six masks set. -/
theorem mxcsrGueltig_zerlegt (m : MXCSR) (h : mxcsrGueltig m = true) :
    mxcsrRundungRNE m = true ∧ mxcsrBit m 15 = false ∧
      mxcsrBit m 6 = false ∧ mxcsrMaskenAlle m = true := by
  unfold mxcsrGueltig at h
  simp only [Bool.and_eq_true_iff] at h
  obtain ⟨⟨⟨hrne, hftz⟩, hdaz⟩, hmask⟩ := h
  unfold mxcsrRundungRNE at hrne
  simp only [Bool.and_eq_true_iff] at hrne
  refine ⟨?_, ?_, ?_, hmask⟩
  · unfold mxcsrRundungRNE
    simp [hrne.1, hrne.2]
  · cases hb : mxcsrBit m 15 <;> simp_all
  · cases hb : mxcsrBit m 6 <;> simp_all

/-- Round-to-nearest-even survives the decomposition on the reset word. -/
theorem mxcsrReset_rne : mxcsrRundungRNE (0x1F80 : MXCSR) = true := by
  decide

/-- Round-up (RC = 10) is refused: non-nearest rounding admits nothing. -/
theorem mxcsr_runde_hoch_verweigert :
    mxcsrGueltig (0x5F80 : MXCSR) = false := by
  decide

/-- Round-toward-zero (RC = 11) is refused. -/
theorem mxcsr_runde_schnitt_verweigert :
    mxcsrGueltig (0x7F80 : MXCSR) = false := by
  decide

/-- A trap-on-exception word (invalid-operation mask clear) is refused:
    unmasked exception encodings are unsupported, never executed. -/
theorem mxcsr_falle_verweigert :
    mxcsrGueltig (0x1F00 : MXCSR) = false := by
  decide

/-- A cleared zero-divide mask is refused (second unsupported mask row). -/
theorem mxcsr_maske_null_verweigert :
    mxcsrGueltig (0x1D80 : MXCSR) = false := by
  decide

/-! ## 2. Entry control state admits FP execution.

  The `EntryState` discipline (`mxcsrOk`: touching XMM needs a
  validated save and a profile-valid word) transfers to the actual FP
  admission (`fpEintritt`) and to the silicon/readiness admission
  (`bereit` at `.sseDoppel` with vector state on). The
  `FeatureProfile` admission transfers back: an admitted
  scalar-double feature carries a profile-valid word. -/

/-- An entry that touches XMM under the discipline admits FP
    execution: the entry word as a context meets `fpEintritt`. -/
theorem eintritt_mxcsr_gibt_fpEintritt (z : EintrittZustand)
    (ht : z.xmmBeruehrt = true) (h : mxcsrOk z = true) :
    fpEintritt (eintrittFp z) = true := by
  have hg : mxcsrGueltig z.mxcsr = true := by
    unfold mxcsrOk at h
    rw [ht] at h
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true_iff] at h
    exact h.2
  rw [eintrittFp_profil]
  exact hg

/-- The full entry predicate with XMM touched admits FP execution:
    the control-state leg of `eintrittOk` is the FP admission. -/
theorem eintrittOk_gibt_fpEintritt (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand)
    (ht : z.xmmBeruehrt = true)
    (h : eintrittOk p bild bias art z = true) :
    fpEintritt (eintrittFp z) = true := by
  unfold eintrittOk at h
  simp only [Bool.and_eq_true_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, hmx⟩, _⟩ := h
  exact eintritt_mxcsr_gibt_fpEintritt z ht hmx

/-- The disciplined entry word readies the scalar-double feature:
    with OS vector state on, `bereit` holds at `.sseDoppel`. -/
theorem eintritt_gibt_bereit (z : EintrittZustand)
    (ht : z.xmmBeruehrt = true) (h : mxcsrOk z = true) :
    bereit ⟨z.mxcsr, true⟩ .sseDoppel = true := by
  have hg : mxcsrGueltig z.mxcsr = true := by
    unfold mxcsrOk at h
    rw [ht] at h
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true_iff] at h
    exact h.2
  unfold bereit
  simp [hg]

/-- An admitted scalar-double feature carries a profile-valid word:
    feature admission implies the FP step admission. -/
theorem sse_zugelassen_gibt_fpEintritt (hw : HwProfil) (b : BereitProfil)
    (h : merkmalZugelassen hw b .sseDoppel = true) :
    fpEintritt ⟨b.mxcsr⟩ = true := by
  unfold merkmalZugelassen at h
  simp only [Bool.and_eq_true_iff] at h
  obtain ⟨_, hber⟩ := h
  unfold bereit at hber
  simp only [Bool.and_eq_true_iff] at hber
  unfold fpEintritt
  exact hber.1

/-! ## 3. Preservation across admitted FP steps.

  No admitted scalar FP step touches the control word: every
  `fpSchritt` successor keeps `t.fp` (all fifteen forms write only
  `kern`/`xmm`). Hence admission is preserved, and every reached step
  ran under a checked decode length and a valid profile. No admitted
  step can install a new control word -- control-word load/store has no
  accepted byte form (see CUTS). -/

/-- Every admitted FP step keeps the FP control word. -/
theorem fpSchritt_erhaelt_fp (d : FpDecodiert) (t t' : FpZustand)
    (hstep : fpSchritt d t = some t') : t'.fp = t.fp := by
  cases hok : laengeOk d.laenge with
  | false =>
    rw [fpSchritt_laenge_verweigert d t hok] at hstep
    cases hstep
  | true =>
    cases hfp : fpEintritt t.fp with
    | false =>
      rw [fpSchritt_profil_verweigert d t hok hfp] at hstep
      cases hstep
    | true =>
      cases hbef : d.befehl
      case addsdRR dst src =>
        rw [fpSchritt_addsdRR d t dst src hok hfp hbef] at hstep
        cases hstep
        rfl
      case subsdRR dst src =>
        rw [fpSchritt_subsdRR d t dst src hok hfp hbef] at hstep
        cases hstep
        rfl
      case mulsdRR dst src =>
        rw [fpSchritt_mulsdRR d t dst src hok hfp hbef] at hstep
        cases hstep
        rfl
      case divsdRR dst src =>
        rw [fpSchritt_divsdRR d t dst src hok hfp hbef] at hstep
        cases hstep
        rfl
      case addsdRM dst base disp =>
        cases hrd : read64 t.kern.speicher (effAddr t.kern base disp) with
        | none =>
          rw [fpSchritt_addsdRM_verweigert d t dst base disp hok hfp hbef hrd] at hstep
          cases hstep
        | some v =>
          rw [fpSchritt_addsdRM_erfolg d t dst base disp v hok hfp hbef hrd] at hstep
          cases hstep
          rfl
      case subsdRM dst base disp =>
        cases hrd : read64 t.kern.speicher (effAddr t.kern base disp) with
        | none =>
          rw [fpSchritt_subsdRM_verweigert d t dst base disp hok hfp hbef hrd] at hstep
          cases hstep
        | some v =>
          rw [fpSchritt_subsdRM_erfolg d t dst base disp v hok hfp hbef hrd] at hstep
          cases hstep
          rfl
      case mulsdRM dst base disp =>
        cases hrd : read64 t.kern.speicher (effAddr t.kern base disp) with
        | none =>
          rw [fpSchritt_mulsdRM_verweigert d t dst base disp hok hfp hbef hrd] at hstep
          cases hstep
        | some v =>
          rw [fpSchritt_mulsdRM_erfolg d t dst base disp v hok hfp hbef hrd] at hstep
          cases hstep
          rfl
      case divsdRM dst base disp =>
        cases hrd : read64 t.kern.speicher (effAddr t.kern base disp) with
        | none =>
          rw [fpSchritt_divsdRM_verweigert d t dst base disp hok hfp hbef hrd] at hstep
          cases hstep
        | some v =>
          rw [fpSchritt_divsdRM_erfolg d t dst base disp v hok hfp hbef hrd] at hstep
          cases hstep
          rfl
      case ucomisdRR lhs rhs =>
        rw [fpSchritt_ucomisdRR d t lhs rhs hok hfp hbef] at hstep
        cases hstep
        rfl
      case ucomisdRM lhs base disp =>
        cases hrd : read64 t.kern.speicher (effAddr t.kern base disp) with
        | none =>
          rw [fpSchritt_ucomisdRM_verweigert d t lhs base disp hok hfp hbef hrd] at hstep
          cases hstep
        | some v =>
          rw [fpSchritt_ucomisdRM_erfolg d t lhs base disp v hok hfp hbef hrd] at hstep
          cases hstep
          rfl
      case cvtsi2sd dst src =>
        rw [fpSchritt_cvtsi2sd d t dst src hok hfp hbef] at hstep
        cases hstep
        rfl
      case cvttsd2si dst src =>
        rw [fpSchritt_cvttsd2si d t dst src hok hfp hbef] at hstep
        cases hstep
        rfl
      case movsdRR dst src =>
        rw [fpSchritt_movsdRR d t dst src hok hfp hbef] at hstep
        cases hstep
        rfl
      case movsdLade dst base disp =>
        cases hrd : read64 t.kern.speicher (effAddr t.kern base disp) with
        | none =>
          rw [fpSchritt_movsdLade_verweigert d t dst base disp hok hfp hbef hrd] at hstep
          cases hstep
        | some v =>
          rw [fpSchritt_movsdLade_erfolg d t dst base disp v hok hfp hbef hrd] at hstep
          cases hstep
          rfl
      case movsdSpeichere base src disp =>
        cases hwr : write64 t.kern.speicher (effAddr t.kern base disp) (xmmTief t.xmm src) with
        | none =>
          rw [fpSchritt_movsdSpeichere_verweigert d t base src disp hok hfp hbef hwr] at hstep
          cases hstep
        | some m =>
          rw [fpSchritt_movsdSpeichere_erfolg d t base src disp m hok hfp hbef hwr] at hstep
          cases hstep
          rfl

/-- Admission is preserved: the successor meets the same profile. -/
theorem fpSchritt_erhaelt_fpEintritt (d : FpDecodiert) (t t' : FpZustand)
    (hstep : fpSchritt d t = some t') :
    fpEintritt t'.fp = fpEintritt t.fp := by
  rw [fpSchritt_erhaelt_fp d t t' hstep]

/-- An admitted step from an admitted state stays admitted. -/
theorem zugelassener_schritt_bleibt (d : FpDecodiert) (t t' : FpZustand)
    (hstep : fpSchritt d t = some t')
    (h : fpEintritt t.fp = true) :
    fpEintritt t'.fp = true := by
  rw [fpSchritt_erhaelt_fp d t t' hstep]
  exact h

/-- BOUNDED ADMISSION: every reached step ran under a checked decode
    length and a valid profile -- length and admission are not assumed,
    they are read off the step. -/
theorem fpSchritt_zugelassen_heisst (d : FpDecodiert) (t t' : FpZustand)
    (hstep : fpSchritt d t = some t') :
    laengeOk d.laenge = true ∧ fpEintritt t.fp = true := by
  constructor
  · cases hok : laengeOk d.laenge with
    | false =>
      rw [fpSchritt_laenge_verweigert d t hok] at hstep
      cases hstep
    | true => rfl
  · cases hfp : fpEintritt t.fp with
    | false =>
      cases hok : laengeOk d.laenge with
      | false =>
        rw [fpSchritt_laenge_verweigert d t hok] at hstep
        cases hstep
      | true =>
        rw [fpSchritt_profil_verweigert d t hok hfp] at hstep
        cases hstep
    | true => rfl

/-- No admitted step installs a control word: a word absent before the
    step is absent after it. Establishment comes only from the entry,
    never from an admitted FP byte. -/
theorem kein_fpSchritt_installiert (d : FpDecodiert) (t t' : FpZustand)
    (w : MXCSR) (hstep : fpSchritt d t = some t')
    (hne : t.fp.mxcsr ≠ w) : t'.fp.mxcsr ≠ w := by
  have hfp : t'.fp = t.fp := fpSchritt_erhaelt_fp d t t' hstep
  rw [hfp]
  exact hne

/-! ## 4. Entry-level refusals and generic hosted/freestanding admission.

  The word refusals of §1 lift to the entry predicate: an entry that
  touches XMM under a validated save still admits nothing when its
  word carries FTZ, DAZ, non-nearest rounding or an unmasked
  exception encoding. Hosted and freestanding entries share the same
  control-state discipline (generic profiles: no libc/Linux content
  anywhere -- the IF/guard legs stay with `EntryState`). -/

/-- A profile-invalid word admits no entry, however disciplined the
    save: the generic entry-level refusal. -/
theorem mxcsrOk_verweigert_ungueltig (z : EintrittZustand)
    (ht : z.xmmBeruehrt = true) (hs : z.mxcsrGesichert = true)
    (h : mxcsrGueltig z.mxcsr = false) : mxcsrOk z = false := by
  unfold mxcsrOk
  simp [ht, hs, h]

/-- FTZ at the entry is refused. -/
theorem mxcsrOk_verweigert_ftz (z : EintrittZustand)
    (ht : z.xmmBeruehrt = true) (hs : z.mxcsrGesichert = true)
    (hw : z.mxcsr = 0x9F80) : mxcsrOk z = false := by
  have h : mxcsrGueltig z.mxcsr = false := by
    rw [hw]
    exact mxcsr_ftz_verweigert
  exact mxcsrOk_verweigert_ungueltig z ht hs h

/-- DAZ at the entry is refused. -/
theorem mxcsrOk_verweigert_daz (z : EintrittZustand)
    (ht : z.xmmBeruehrt = true) (hs : z.mxcsrGesichert = true)
    (hw : z.mxcsr = 0x1FC0) : mxcsrOk z = false := by
  have h : mxcsrGueltig z.mxcsr = false := by
    rw [hw]
    exact mxcsr_daz_verweigert
  exact mxcsrOk_verweigert_ungueltig z ht hs h

/-- Round-down at the entry is refused. -/
theorem mxcsrOk_verweigert_runde_unten (z : EintrittZustand)
    (ht : z.xmmBeruehrt = true) (hs : z.mxcsrGesichert = true)
    (hw : z.mxcsr = 0x3F80) : mxcsrOk z = false := by
  have h : mxcsrGueltig z.mxcsr = false := by
    rw [hw]
    exact mxcsr_runde_unten_verweigert
  exact mxcsrOk_verweigert_ungueltig z ht hs h

/-- Round-up at the entry is refused. -/
theorem mxcsrOk_verweigert_runde_hoch (z : EintrittZustand)
    (ht : z.xmmBeruehrt = true) (hs : z.mxcsrGesichert = true)
    (hw : z.mxcsr = 0x5F80) : mxcsrOk z = false := by
  have h : mxcsrGueltig z.mxcsr = false := by
    rw [hw]
    exact mxcsr_runde_hoch_verweigert
  exact mxcsrOk_verweigert_ungueltig z ht hs h

/-- Round-toward-zero at the entry is refused. -/
theorem mxcsrOk_verweigert_runde_schnitt (z : EintrittZustand)
    (ht : z.xmmBeruehrt = true) (hs : z.mxcsrGesichert = true)
    (hw : z.mxcsr = 0x7F80) : mxcsrOk z = false := by
  have h : mxcsrGueltig z.mxcsr = false := by
    rw [hw]
    exact mxcsr_runde_schnitt_verweigert
  exact mxcsrOk_verweigert_ungueltig z ht hs h

/-- A trap-on-exception word at the entry is refused. -/
theorem mxcsrOk_verweigert_falle (z : EintrittZustand)
    (ht : z.xmmBeruehrt = true) (hs : z.mxcsrGesichert = true)
    (hw : z.mxcsr = 0x1F00) : mxcsrOk z = false := by
  have h : mxcsrGueltig z.mxcsr = false := by
    rw [hw]
    exact mxcsr_falle_verweigert
  exact mxcsrOk_verweigert_ungueltig z ht hs h

/-- Hosted entry control state: XMM touched, save validated, reset
    word, interrupts enabled. -/
def zeugenEintrittFpHosted : EintrittZustand :=
  { zustand := fpZeugeKern
    mxcsr := 0x1F80
    xmmBeruehrt := true
    mxcsrGesichert := true
    ifBit := true
    guardOk := true }

/-- Freestanding entry control state: same control-state discipline,
    interrupts disabled, no guard owed -- generic profile, no OS
    content. -/
def zeugenEintrittFpMetall : EintrittZustand :=
  { zustand := fpZeugeKern
    mxcsr := 0x1F80
    xmmBeruehrt := true
    mxcsrGesichert := true
    ifBit := false
    guardOk := false }

/-- ACCEPTANCE: the hosted control state is admitted. -/
theorem zeugenEintrittFpHosted_ok :
    mxcsrOk zeugenEintrittFpHosted = true := by
  decide

/-- ACCEPTANCE: the freestanding control state is admitted. -/
theorem zeugenEintrittFpMetall_ok :
    mxcsrOk zeugenEintrittFpMetall = true := by
  decide

/-- The hosted word admits FP execution. -/
theorem zeugenEintrittFpHosted_fp :
    fpEintritt (eintrittFp zeugenEintrittFpHosted) = true := by
  decide

/-- The freestanding word admits FP execution. -/
theorem zeugenEintrittFpMetall_fp :
    fpEintritt (eintrittFp zeugenEintrittFpMetall) = true := by
  decide

/-- Both profiles ready the scalar-double feature. -/
theorem zeugenEintrittFp_bereit :
    bereit ⟨zeugenEintrittFpHosted.mxcsr, true⟩ .sseDoppel = true ∧
      bereit ⟨zeugenEintrittFpMetall.mxcsr, true⟩ .sseDoppel = true := by
  decide

/-- THREE-WAY REFUSAL: the FTZ word is refused at the entry
    predicate, at feature admission (whatever the silicon), and at
    the FP step admission -- one bad word, three closed doors. -/
theorem ftz_dreiWege_verweigert (hw : HwProfil)
    (hh : hat hw .sseDoppel = true) :
    mxcsrOk { zeugenEintrittFpHosted with mxcsr := 0x9F80 } = false ∧
      merkmalZugelassen hw ⟨0x9F80, true⟩ .sseDoppel = false ∧
      fpEintritt (⟨0x9F80⟩ : FPKontext) = false := by
  refine ⟨by decide,
    sse_verweigert_ohne_profil hw ⟨0x9F80, true⟩ hh
      mxcsr_ftz_verweigert, ?_⟩
  unfold fpEintritt
  exact mxcsr_ftz_verweigert

/-! ## 5. Joint witness: admitted FP run beside a reached source run.

  The hosted entry word IS the witness FP context; under it the
  actual divide special case (`1.0 / +0.0 = +∞`) computes, stores to
  memory and reads back with an observable byte change -- two reached
  admitted steps. Beside it, the certified source fixture contributes
  a reached run whose table some function writes (`0` at the start,
  `5` at the entry contract's place) plus a real eight-byte memory
  change. Neither side is derived from the other; no lowering between
  them is claimed. -/

/-- The hosted entry word IS the witness FP context: the entry
    establishes exactly the control word the admitted run executes. -/
theorem zeugenEintrittFpHosted_kontext :
    eintrittFp zeugenEintrittFpHosted = fpZeugeT.fp := rfl

/-- JOINT WITNESS (admitted FP execution + reached source run): the
    hosted entry is control-state admitted, establishes the witness
    FP context, two admitted FP steps compute and store `+∞` with a
    real memory change, and on a reached non-degenerate source run
    (a table-writing call, `0 -> 5` at the entry contract's place)
    the entry contract holds at its actual place. -/
theorem floatEintritt_zeuge :
    ∃ (z : EintrittZustand) (t' t'' : FpZustand)
      (M : RufMaschineG eD) (rhoP : Env eD (eD.params ePruefe))
      (wP : World eD),
      mxcsrOk z = true ∧
      eintrittFp z = fpZeugeT.fp ∧
      fpSchritt ⟨.divsdRR XmmReg.xmm0 XmmReg.xmm1, 4⟩ fpZeugeT = some t' ∧
      fpSchritt ⟨.movsdSpeichere Register.rax XmmReg.xmm0 0, 4⟩ t' = some t'' ∧
      read64 t''.kern.speicher (BitVec.ofNat 64 8192) =
        some 0x7FF0000000000000 ∧
      fpZeugeT.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) ≠
        t''.kern.speicher.bytes (addrOff (BitVec.ofNat 64 8192) 7) ∧
      RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M ∧
      ReqAmEintritt eP ePruefe wP rhoP ∧
      (eSp.slots () 0 ()).n = 0 ∧
      (wP.slots () 0 ()).n = 5 ∧
      (∃ (m m' : Speicher) (a : Adresse) (v : Wort),
        v ≠ 0 ∧ write64 m a v = some m' ∧ read64 m' a = some v ∧
          m.bytes a ≠ m'.bytes a) := by
  obtain ⟨M, hr, hsl0, _, rhoP, wP, _, _, _, _, _, _, _, _, hsl5, hreq, _⟩ :=
    vertragStandort_lauf_zeuge
  exact ⟨zeugenEintrittFpHosted, fpZeugeT1, fpZeugeT2, M, rhoP, wP,
    zeugenEintrittFpHosted_ok, zeugenEintrittFpHosted_kontext,
    fpZeuge_schritt1, fpZeuge_schritt2, fpZeuge_liest,
    fpZeuge_speicher_aendert, hr, hreq, hsl0, hsl5, write_read_zeuge⟩

/- CUTS: what is not proved here.
   - No FP decoder: `FpDecodiert.laenge` is checked data (`1..15`)
     and `FpBefehl` values arrive constructed, never decoded from
     bytes (inherited cut of ScalarFloat). Control-word load/store
     (LDMXCSR/STMXCSR) has no accepted byte form at all: the checked
     claims are admission (`fpEintritt`), preservation
     (`fpSchritt_erhaelt_fp`) and no-installation
     (`kein_fpSchritt_installiert`); establishment of the word from
     entry bytes is OPEN.
   - x87/FPCR, further rounding modes beyond refusal, contraction and
     fast-math are out of scope; sticky MXCSR flags (bits 0-5) are
     unchecked and unmodelled (inherited gap of Gleitprofil §2); NaN
     conclusions are class-level only, never payload equality.
   - The image/stack/guard/IF legs of the full `eintrittOk` are not
     re-proved here (owned by EntryState/EntryExecution); this module
     owns the control-state leg (`mxcsrOk`) and its transfer to
     `fpEintritt`/`bereit`. Entry establishment is the entry word as
     data (`eintrittFp`); no OS/hardware context-switch semantics and
     no x87/OS runtime semantics is claimed anywhere.
   - No lowering between the witness sides: the joint witness pairs an
     admitted target run with a reached source run side by side; no
     claim is made that the executed bytes are the emitted form of
     that source program. Full source-to-final-loaded-bytes remains
     OPEN until a generic closing proof is derived.
   - No concurrency claim: `fpSchritt` is sequential over one
     `Speicher`; per-access TSO granularity, tearing and the GX
     refinement stay with the TSO-bridge work. No cost, timing or
     budget transfer.
   - Rule 13 (inhabitation): no theorem here takes a premise
     universally quantifying over source syntax (`Vertrag`, `Stmt`,
     `Endblock`, `ErgExpr`, `Expr`, `Args`); contracts appear only at
     actual values (`ReqAmEintritt eP ePruefe wP rhoP`). The joint
     non-degenerate witness is `floatEintritt_zeuge`: an admitted
     two-step FP execution with a real memory change beside a reached
     source run with a table-writing call.
-/

#print axioms eintrittFp
#print axioms eintrittFp_profil
#print axioms mxcsrGueltig_zerlegt
#print axioms mxcsrReset_rne
#print axioms mxcsr_runde_hoch_verweigert
#print axioms mxcsr_runde_schnitt_verweigert
#print axioms mxcsr_falle_verweigert
#print axioms mxcsr_maske_null_verweigert
#print axioms eintritt_mxcsr_gibt_fpEintritt
#print axioms eintrittOk_gibt_fpEintritt
#print axioms eintritt_gibt_bereit
#print axioms sse_zugelassen_gibt_fpEintritt
#print axioms fpSchritt_erhaelt_fp
#print axioms fpSchritt_erhaelt_fpEintritt
#print axioms zugelassener_schritt_bleibt
#print axioms fpSchritt_zugelassen_heisst
#print axioms kein_fpSchritt_installiert
#print axioms mxcsrOk_verweigert_ungueltig
#print axioms mxcsrOk_verweigert_ftz
#print axioms mxcsrOk_verweigert_daz
#print axioms mxcsrOk_verweigert_runde_unten
#print axioms mxcsrOk_verweigert_runde_hoch
#print axioms mxcsrOk_verweigert_runde_schnitt
#print axioms mxcsrOk_verweigert_falle
#print axioms zeugenEintrittFpHosted_ok
#print axioms zeugenEintrittFpMetall_ok
#print axioms zeugenEintrittFpHosted_fp
#print axioms zeugenEintrittFpMetall_fp
#print axioms zeugenEintrittFp_bereit
#print axioms zeugenEintrittFpHosted_kontext
#print axioms ftz_dreiWege_verweigert
#print axioms floatEintritt_zeuge

end Gabbro.Grammatik.X86
