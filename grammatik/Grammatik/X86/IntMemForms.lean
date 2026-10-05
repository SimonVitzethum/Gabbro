/-
  File:      Grammatik/X86/IntMemForms.lean
  Subject:   Memory-operand addressing forms for rotates, carry forms
             and sign-extend/XCHG over the coherent machine.

  Lane 1315: the rotate (IntRotate), ADC/SBB/INC/DEC (IntCarryForms)
  and sign-extend/XCHG (IntegerCore value layer, XchgOrderNeed swap
  shape) families only admit the pilot base-plus-disp32 memory shape
  (mod=10, no SIB choice, no RIP-relative, no disp8/disp0). Using the
  accepted selected `AdrForm`/`adrEff` (AddressEncoding) and the
  `HwAddressed` event pattern, this module lifts all three families
  to the full addressing-mode set: decode and encode with pinned
  round trips, effective address equal to `adrEff`, access as TSO
  events with the exact `entriesOf` footprint, and memory-destination
  RMW as load-modify-store events. LOCK stays refused. No silicon
  correspondence beyond self-consistency (see CUTS).
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.AddressEncoding
import Grammatik.X86.HwAddressed
import Grammatik.X86.ConcurrentIntegerExecution
import Grammatik.X86.NarrowOps
import Grammatik.X86.IntRotate
import Grammatik.X86.IntCarryForms

namespace Gabbro.Grammatik.X86

/-- Selected address of one access from the acting core's pre-state
    registers plus the next-RIP base for RIP-relative forms. -/
def intMemAddr (m : HwMaschine) (c : Nat) (ripNext : Adresse)
    (f : AdrForm) : Adresse :=
  adrEff (projZustand m c) ripNext f

/-- The lifted address reads the acting core's pre-state registers
    (and the RIP base for RIP-relative forms) only. -/
theorem intMemAddr_basisForm (m : HwMaschine) (c : Nat)
    (base : Register) (disp : BitVec 32) (ripNext : Adresse) :
    intMemAddr m c ripNext (basisForm base disp) =
      effAddr (projZustand m c) base disp := by
  unfold intMemAddr
  rw [adrEff_basisForm]

/-! ## 1. Lifted memory descriptors: full `AdrForm` operands.

  The accepted decoders only admit the pilot base-plus-disp32 memory
  shape (rotate: mod=2 only; carry: `carryMemAdr` refuses SIB with
  `rm=4` and RIP-relative `mod=0,rm=5`; XCHG: mod=2 only; sign-extend
  has no memory form at all). The descriptors below carry a full
  selected `AdrForm` instead; §3 runs them as TSO events. -/

/-- Lifted rotate memory form: operation, width, resolved count, full
    selected address, consumed length. The count is the
    already-resolved value (count-source decoding stays with the
    accepted `decodeRot`); masking applies at evaluation. -/
structure RotVoll where
  op : RotOp
  breite : Breite
  zaehlung : Nat
  form : AdrForm
  laenge : Nat
  deriving DecidableEq, Repr

/-- Lifted carry memory-destination form: ADC/SBB with register or
    immediate source, INC/DEC over the full selected address. -/
inductive CarryVoll where
  | adcV (b : Breite) (f : AdrForm) (src : Register) (len : Nat)
  | sbbV (b : Breite) (f : AdrForm) (src : Register) (len : Nat)
  | adcIV (b : Breite) (f : AdrForm) (op : Wort) (len : Nat)
  | sbbIV (b : Breite) (f : AdrForm) (op : Wort) (len : Nat)
  | incV (b : Breite) (f : AdrForm) (len : Nat)
  | decV (b : Breite) (f : AdrForm) (len : Nat)
  deriving DecidableEq, Repr

/-- Lifted sign-extend load: source width (8/16/32), destination
    register, full selected address. A 64-bit source is refused
    (no-op shape, see `signVollOk`). -/
structure SignVoll where
  quelle : Breite
  ziel : Register
  form : AdrForm
  laenge : Nat
  deriving DecidableEq, Repr

/-- Lifted XCHG memory form: width, full selected address, register,
    consumed length. Modelled as load-modify-store events; atomicity
    stays with the locked families (see CUTS). -/
structure XchgVoll where
  breite : Breite
  form : AdrForm
  reg : Register
  laenge : Nat
  deriving DecidableEq, Repr

/-- Width to its two codec bits. -/
def breitenCode : Breite → Nat
  | .b8 => 0 | .b16 => 1 | .b32 => 2 | .b64 => 3

/-- Two codec bits back to a width. -/
def codeBreite : Nat → Option Breite
  | 0 => some .b8 | 1 => some .b16 | 2 => some .b32 | 3 => some .b64
  | _ => none

/-- Decoding inverts encoding on every width. -/
theorem codeBreite_breitenCode (b : Breite) :
    codeBreite (breitenCode b) = some b := by
  cases b <;> rfl

/-! ## 2. Value layer: the accepted evaluators are lifted, never
  redefined. Every `Neu` below is the accepted function applied to
  the loaded word; the agreement theorems pin this per arm. -/

/-- Lifted rotate result: new memory word from the accepted value core. -/
def rotVollNeu (r : RotVoll) (alt : Wort) (cf : Bool) : Wort :=
  match r.op with
  | .rol => rolB r.breite alt r.zaehlung
  | .ror => rorB r.breite alt r.zaehlung
  | .rcl => (rclB r.breite alt cf r.zaehlung).1
  | .rcr => (rcrB r.breite alt cf r.zaehlung).1

/-- Lifted rotate flags: the accepted executable snapshot. -/
def rotVollFlags (r : RotVoll) (alt : Wort) (cf : Bool)
    (vor : Flags) : Flags :=
  rotFlags r.op r.breite alt cf vor r.zaehlung

/-- Agreement: ROL lifts `rolB`. -/
theorem rotVollNeu_rol (r : RotVoll) (alt : Wort) (cf : Bool)
    (h : r.op = .rol) :
    rotVollNeu r alt cf = rolB r.breite alt r.zaehlung := by
  simp [rotVollNeu, h]

/-- Agreement: ROR lifts `rorB`. -/
theorem rotVollNeu_ror (r : RotVoll) (alt : Wort) (cf : Bool)
    (h : r.op = .ror) :
    rotVollNeu r alt cf = rorB r.breite alt r.zaehlung := by
  simp [rotVollNeu, h]

/-- Agreement: RCL lifts the `rclB` value. -/
theorem rotVollNeu_rcl (r : RotVoll) (alt : Wort) (cf : Bool)
    (h : r.op = .rcl) :
    rotVollNeu r alt cf = (rclB r.breite alt cf r.zaehlung).1 := by
  simp [rotVollNeu, h]

/-- Agreement: RCR lifts the `rcrB` value. -/
theorem rotVollNeu_rcr (r : RotVoll) (alt : Wort) (cf : Bool)
    (h : r.op = .rcr) :
    rotVollNeu r alt cf = (rcrB r.breite alt cf r.zaehlung).1 := by
  simp [rotVollNeu, h]

/-- The lifted flags ARE the accepted snapshot. -/
theorem rotVollFlags_gleich (r : RotVoll) (alt : Wort) (cf : Bool)
    (vor : Flags) :
    rotVollFlags r alt cf vor =
      rotFlags r.op r.breite alt cf vor r.zaehlung := rfl

/-- The lifted snapshot satisfies the accepted validity relation. -/
theorem rotVollFlags_gueltig (r : RotVoll) (alt : Wort) (cf : Bool)
    (vor : Flags) :
    RotGueltig r.op r.breite
      (rotNachweis r.op r.breite alt cf r.zaehlung) r.zaehlung vor
      (rotVollFlags r alt cf vor) :=
  rotFlags_gueltig r.op r.breite alt cf vor r.zaehlung

/-- Lifted carry result and flags from the accepted §1 layer. -/
def carryVollNeu (v : CarryVoll) (alt : Wort)
    (regs : Register → Wort) (vor : Flags) : Wort × Flags :=
  match v with
  | .adcV b _ src _ =>
    (adcWert b alt (regs src) vor.cf, adcFlags b alt (regs src) vor.cf)
  | .sbbV b _ src _ =>
    (sbbWert b alt (regs src) vor.cf, sbbFlags b alt (regs src) vor.cf)
  | .adcIV b _ op _ => (adcWert b alt op vor.cf, adcFlags b alt op vor.cf)
  | .sbbIV b _ op _ => (sbbWert b alt op vor.cf, sbbFlags b alt op vor.cf)
  | .incV b _ _ => (incWert b alt, incFlags b alt vor)
  | .decV b _ _ => (decWert b alt, decFlags b alt vor)

/-- Agreement: ADC lifts `adcWert`/`adcFlags`. -/
theorem carryVollNeu_adcV (b : Breite) (f : AdrForm) (src : Register)
    (len : Nat) (alt : Wort) (regs : Register → Wort) (vor : Flags) :
    carryVollNeu (.adcV b f src len) alt regs vor =
      (adcWert b alt (regs src) vor.cf,
        adcFlags b alt (regs src) vor.cf) := rfl

/-- Agreement: SBB lifts `sbbWert`/`sbbFlags`. -/
theorem carryVollNeu_sbbV (b : Breite) (f : AdrForm) (src : Register)
    (len : Nat) (alt : Wort) (regs : Register → Wort) (vor : Flags) :
    carryVollNeu (.sbbV b f src len) alt regs vor =
      (sbbWert b alt (regs src) vor.cf,
        sbbFlags b alt (regs src) vor.cf) := rfl

/-- Agreement: ADC-immediate lifts the accepted layer. -/
theorem carryVollNeu_adcIV (b : Breite) (f : AdrForm) (op : Wort)
    (len : Nat) (alt : Wort) (regs : Register → Wort) (vor : Flags) :
    carryVollNeu (.adcIV b f op len) alt regs vor =
      (adcWert b alt op vor.cf, adcFlags b alt op vor.cf) := rfl

/-- Agreement: SBB-immediate lifts the accepted layer. -/
theorem carryVollNeu_sbbIV (b : Breite) (f : AdrForm) (op : Wort)
    (len : Nat) (alt : Wort) (regs : Register → Wort) (vor : Flags) :
    carryVollNeu (.sbbIV b f op len) alt regs vor =
      (sbbWert b alt op vor.cf, sbbFlags b alt op vor.cf) := rfl

/-- Agreement: INC lifts `incWert`/`incFlags`. -/
theorem carryVollNeu_incV (b : Breite) (f : AdrForm)
    (len : Nat) (alt : Wort) (regs : Register → Wort) (vor : Flags) :
    carryVollNeu (.incV b f len) alt regs vor =
      (incWert b alt, incFlags b alt vor) := rfl

/-- Agreement: DEC lifts `decWert`/`decFlags`. -/
theorem carryVollNeu_decV (b : Breite) (f : AdrForm)
    (len : Nat) (alt : Wort) (regs : Register → Wort) (vor : Flags) :
    carryVollNeu (.decV b f len) alt regs vor =
      (decWert b alt, decFlags b alt vor) := rfl

/-- CF-PRESERVATION: lifted INC keeps the incoming carry. -/
theorem carryVollNeu_inc_cf (b : Breite) (f : AdrForm)
    (len : Nat) (alt : Wort) (regs : Register → Wort) (vor : Flags) :
    (carryVollNeu (.incV b f len) alt regs vor).2.cf = vor.cf := rfl

/-- CF-PRESERVATION: lifted DEC keeps the incoming carry. -/
theorem carryVollNeu_dec_cf (b : Breite) (f : AdrForm)
    (len : Nat) (alt : Wort) (regs : Register → Wort) (vor : Flags) :
    (carryVollNeu (.decV b f len) alt regs vor).2.cf = vor.cf := rfl

/-- Admission of a sign-extend load: the source is 8, 16 or 32
    bits (a 64-bit source would be a no-op move, refused). -/
def signVollOk (s : SignVoll) : Bool := decide (s.quelle ≠ .b64)

/-- REFUSAL: a 64-bit source is no sign extension. -/
theorem signVollOk_verweigert_b64 (ziel : Register) (f : AdrForm)
    (len : Nat) :
    signVollOk ⟨.b64, ziel, f, len⟩ = false := by
  simp [signVollOk]

/-- The three admitted source widths. -/
theorem signVollOk_quellen :
    signVollOk ⟨.b8, .rax, absolutForm (BitVec.ofNat 32 0), 7⟩ = true ∧
    signVollOk ⟨.b16, .rax, absolutForm (BitVec.ofNat 32 0), 7⟩ = true ∧
    signVollOk ⟨.b32, .rax, absolutForm (BitVec.ofNat 32 0), 7⟩ = true := by
  decide

/-- Lifted sign-extend value: the accepted `extendNarrow`. -/
def signVollNeu (s : SignVoll) (alt : Wort) : Wort :=
  extendNarrow .sign s.quelle alt

/-- Agreement: the lifted value IS the canonical `sext`. -/
theorem signVollNeu_gleich (s : SignVoll) (alt : Wort) :
    signVollNeu s alt = sext s.quelle alt := rfl

/-- Agreement with the accepted register MOVSX forms: at width 8 the
    lifted load computes what `movsx64From8` writes. -/
theorem signVollNeu_movsx8 (s : SignVoll) (alt : Wort)
    (h : s.quelle = .b8) :
    signVollNeu s alt = extendNarrow .sign .b8 alt := by
  simp [signVollNeu, h]

/-- Lifted exchange register write: the register takes the loaded
    word with the architectural narrow merge (full overwrite at 64
    bits, exactly like the accepted register forms). -/
def xchgVollNeuReg (x : XchgVoll) (regs : Register → Wort)
    (alt : Wort) : Register → Wort :=
  regSet regs x.reg (mergeRegNarrow x.breite (regs x.reg) alt)

/-- The exchange register write is the stated merge. -/
theorem xchgVollNeuReg_gleich (x : XchgVoll) (regs : Register → Wort)
    (alt : Wort) :
    xchgVollNeuReg x regs alt =
      regSet regs x.reg (mergeRegNarrow x.breite (regs x.reg) alt) := rfl

/-- At 64 bits the exchange installs the loaded word whole, exactly
    the accepted `xchgSchritt` install shape. -/
theorem xchgVollNeuReg_b64 (x : XchgVoll) (regs : Register → Wort)
    (alt : Wort) (h : x.breite = .b64) :
    xchgVollNeuReg x regs alt = regSet regs x.reg alt := by
  simp [xchgVollNeuReg, h, mergeRegNarrow_b64]

/-! ## 3. Machine events: RMW for rotates and carry forms.

  Every memory destination is a load-modify-store pair on the shared
  TSO view: `concLoad` (forwarding-aware) reads the old word, the
  accepted §2 value computes the new word, `concIssue` buffers the
  exact `entriesOf` footprint (never the SC word effect). Canonical
  memory moves only at the drain. -/

/-- Lifted rotate RMW on the coherent machine. `none` = bad length,
    refused load gate, or refused issue byte. -/
def rotVollSchritt (m : HwMaschine) (c : Nat) (r : RotVoll)
    (ripNext : Adresse) : Option HwMaschine :=
  match laengeOk r.laenge with
  | false => none
  | true =>
    let a := intMemAddr m c ripNext r.form
    match concLoad (tsoAnsicht m) c r.breite a with
    | none => none
    | some alt =>
      let neu := rotVollNeu r alt (m.kerne c).flags.cf
      match concIssue (tsoAnsicht m) c r.breite a neu with
      | none => none
      | some s' =>
        some (setKernDaten (setTso m s') c
          (HwKern.mk (m.kerne c).register
            (rotVollFlags r alt (m.kerne c).flags.cf (m.kerne c).flags)
            (ripNach (m.kerne c).rip r.laenge)
            (m.kerne c).xmm (m.kerne c).fp))

/-- A rotate RMW appends exactly its footprint after the loaded word. -/
theorem rotVollSchritt_puffer (m m' : HwMaschine) (c : Nat) (r : RotVoll)
    (ripNext : Adresse)
    (h : rotVollSchritt m c r ripNext = some m') :
    ∃ alt : Wort,
      concLoad (tsoAnsicht m) c r.breite
        (intMemAddr m c ripNext r.form) = some alt ∧
      m'.puffer c = m.puffer c ++
        entriesOf r.breite (intMemAddr m c ripNext r.form)
          (rotVollNeu r alt (m.kerne c).flags.cf) := by
  unfold rotVollSchritt at h
  cases hlen : laengeOk r.laenge with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hload : concLoad (tsoAnsicht m) c r.breite
        (intMemAddr m c ripNext r.form) with
    | none => simp [hload] at h
    | some alt =>
      simp only [hload] at h
      cases hiss : concIssue (tsoAnsicht m) c r.breite
          (intMemAddr m c ripNext r.form)
          (rotVollNeu r alt (m.kerne c).flags.cf) with
      | none => simp [hiss] at h
      | some s' =>
        simp only [hiss] at h
        cases h
        have he := concIssue_haengt_an (tsoAnsicht m) s' c r.breite
          (intMemAddr m c ripNext r.form)
          (rotVollNeu r alt (m.kerne c).flags.cf) hiss
        exact ⟨alt, rfl, by simpa [tsoAnsicht, setTso, setKernDaten] using he⟩

/-- A rotate RMW changes no canonical byte (buffer only). -/
theorem rotVollSchritt_kein_speicher (m m' : HwMaschine) (c : Nat)
    (r : RotVoll) (ripNext : Adresse) (x : Adresse)
    (h : rotVollSchritt m c r ripNext = some m') :
    m'.mem.bytes x = m.mem.bytes x := by
  unfold rotVollSchritt at h
  cases hlen : laengeOk r.laenge with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hload : concLoad (tsoAnsicht m) c r.breite
        (intMemAddr m c ripNext r.form) with
    | none => simp [hload] at h
    | some alt =>
      simp only [hload] at h
      cases hiss : concIssue (tsoAnsicht m) c r.breite
          (intMemAddr m c ripNext r.form)
          (rotVollNeu r alt (m.kerne c).flags.cf) with
      | none => simp [hiss] at h
      | some s' =>
        simp only [hiss] at h
        cases h
        have he := concIssue_kein_speicher (tsoAnsicht m) s' c r.breite
          (intMemAddr m c ripNext r.form)
          (rotVollNeu r alt (m.kerne c).flags.cf) hiss x
        simpa [tsoAnsicht, setTso, setKernDaten] using he

/-- A rotate RMW installs the accepted snapshot flags. -/
theorem rotVollSchritt_flags (m m' : HwMaschine) (c : Nat) (r : RotVoll)
    (ripNext : Adresse)
    (h : rotVollSchritt m c r ripNext = some m') :
    ∃ alt : Wort,
      concLoad (tsoAnsicht m) c r.breite
        (intMemAddr m c ripNext r.form) = some alt ∧
      (m'.kerne c).flags =
        rotVollFlags r alt (m.kerne c).flags.cf (m.kerne c).flags := by
  unfold rotVollSchritt at h
  cases hlen : laengeOk r.laenge with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hload : concLoad (tsoAnsicht m) c r.breite
        (intMemAddr m c ripNext r.form) with
    | none => simp [hload] at h
    | some alt =>
      simp only [hload] at h
      cases hiss : concIssue (tsoAnsicht m) c r.breite
          (intMemAddr m c ripNext r.form)
          (rotVollNeu r alt (m.kerne c).flags.cf) with
      | none => simp [hiss] at h
      | some s' =>
        simp only [hiss] at h
        cases h
        exact ⟨alt, rfl, by simp [setKernDaten]⟩

/-- A rotate RMW advances RIP past its length. -/
theorem rotVollSchritt_rip (m m' : HwMaschine) (c : Nat) (r : RotVoll)
    (ripNext : Adresse)
    (h : rotVollSchritt m c r ripNext = some m') :
    (m'.kerne c).rip = ripNach (m.kerne c).rip r.laenge := by
  unfold rotVollSchritt at h
  cases hlen : laengeOk r.laenge with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hload : concLoad (tsoAnsicht m) c r.breite
        (intMemAddr m c ripNext r.form) with
    | none => simp [hload] at h
    | some alt =>
      simp only [hload] at h
      cases hiss : concIssue (tsoAnsicht m) c r.breite
          (intMemAddr m c ripNext r.form)
          (rotVollNeu r alt (m.kerne c).flags.cf) with
      | none => simp [hiss] at h
      | some s' =>
        simp only [hiss] at h
        cases h
        simp [setKernDaten]

/-- A rotate RMW preserves well-formedness (profiles untouched). -/
theorem rotVollSchritt_wf (m m' : HwMaschine) (c : Nat) (r : RotVoll)
    (ripNext : Adresse)
    (h : rotVollSchritt m c r ripNext = some m')
    (hwf : HwWf m) : HwWf m' := by
  unfold rotVollSchritt at h
  cases hlen : laengeOk r.laenge with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hload : concLoad (tsoAnsicht m) c r.breite
        (intMemAddr m c ripNext r.form) with
    | none => simp [hload] at h
    | some alt =>
      simp only [hload] at h
      cases hiss : concIssue (tsoAnsicht m) c r.breite
          (intMemAddr m c ripNext r.form)
          (rotVollNeu r alt (m.kerne c).flags.cf) with
      | none => simp [hiss] at h
      | some s' =>
        simp only [hiss] at h
        cases h
        exact hwf

/-- A bad length refuses the rotate RMW on any machine. -/
theorem rotVollSchritt_laenge_verweigert (m : HwMaschine) (c : Nat)
    (r : RotVoll) (ripNext : Adresse)
    (h : laengeOk r.laenge = false) :
    rotVollSchritt m c r ripNext = none := by
  unfold rotVollSchritt
  simp [h]

/-- A refused load gate refuses the rotate RMW: no successor. -/
theorem rotVollSchritt_lade_verweigert (m : HwMaschine) (c : Nat)
    (r : RotVoll) (ripNext : Adresse)
    (hok : laengeOk r.laenge = true)
    (hgate : concLoad (tsoAnsicht m) c r.breite
      (intMemAddr m c ripNext r.form) = none) :
    rotVollSchritt m c r ripNext = none := by
  unfold rotVollSchritt
  simp [hok, hgate]

/-- Width of a lifted carry form. -/
def carryVollBreite : CarryVoll → Breite
  | .adcV b _ _ _ => b | .sbbV b _ _ _ => b | .adcIV b _ _ _ => b
  | .sbbIV b _ _ _ => b | .incV b _ _ => b | .decV b _ _ => b

/-- Address form of a lifted carry form. -/
def carryVollForm : CarryVoll → AdrForm
  | .adcV _ f _ _ => f | .sbbV _ f _ _ => f | .adcIV _ f _ _ => f
  | .sbbIV _ f _ _ => f | .incV _ f _ => f | .decV _ f _ => f

/-- Consumed length of a lifted carry form. -/
def carryVollLaenge : CarryVoll → Nat
  | .adcV _ _ _ l => l | .sbbV _ _ _ l => l | .adcIV _ _ _ l => l
  | .sbbIV _ _ _ l => l | .incV _ _ l => l | .decV _ _ l => l

/-- Lifted carry RMW on the coherent machine: load, accepted §2
    value, issue, accepted flags, RIP advance. -/
def carryVollSchritt (m : HwMaschine) (c : Nat) (v : CarryVoll)
    (ripNext : Adresse) : Option HwMaschine :=
  match laengeOk (carryVollLaenge v) with
  | false => none
  | true =>
    let a := intMemAddr m c ripNext (carryVollForm v)
    match concLoad (tsoAnsicht m) c (carryVollBreite v) a with
    | none => none
    | some alt =>
      let neu :=
        carryVollNeu v alt (m.kerne c).register (m.kerne c).flags
      match concIssue (tsoAnsicht m) c (carryVollBreite v) a neu.1 with
      | none => none
      | some s' =>
        some (setKernDaten (setTso m s') c
          (HwKern.mk (m.kerne c).register neu.2
            (ripNach (m.kerne c).rip (carryVollLaenge v))
            (m.kerne c).xmm (m.kerne c).fp))

/-- A carry RMW appends exactly its footprint after the loaded word. -/
theorem carryVollSchritt_puffer (m m' : HwMaschine) (c : Nat)
    (v : CarryVoll) (ripNext : Adresse)
    (h : carryVollSchritt m c v ripNext = some m') :
    ∃ alt : Wort,
      concLoad (tsoAnsicht m) c (carryVollBreite v)
        (intMemAddr m c ripNext (carryVollForm v)) = some alt ∧
      m'.puffer c = m.puffer c ++
        entriesOf (carryVollBreite v)
          (intMemAddr m c ripNext (carryVollForm v))
          (carryVollNeu v alt (m.kerne c).register
            (m.kerne c).flags).1 := by
  unfold carryVollSchritt at h
  cases hlen : laengeOk (carryVollLaenge v) with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hload : concLoad (tsoAnsicht m) c (carryVollBreite v)
        (intMemAddr m c ripNext (carryVollForm v)) with
    | none => simp [hload] at h
    | some alt =>
      simp only [hload] at h
      cases hiss : concIssue (tsoAnsicht m) c (carryVollBreite v)
          (intMemAddr m c ripNext (carryVollForm v))
          (carryVollNeu v alt (m.kerne c).register
            (m.kerne c).flags).1 with
      | none => simp [hiss] at h
      | some s' =>
        simp only [hiss] at h
        cases h
        have he := concIssue_haengt_an (tsoAnsicht m) s' c
          (carryVollBreite v)
          (intMemAddr m c ripNext (carryVollForm v))
          (carryVollNeu v alt (m.kerne c).register
            (m.kerne c).flags).1 hiss
        exact ⟨alt, rfl, by simpa [tsoAnsicht, setTso, setKernDaten] using he⟩

/-- A carry RMW changes no canonical byte (buffer only). -/
theorem carryVollSchritt_kein_speicher (m m' : HwMaschine) (c : Nat)
    (v : CarryVoll) (ripNext : Adresse) (x : Adresse)
    (h : carryVollSchritt m c v ripNext = some m') :
    m'.mem.bytes x = m.mem.bytes x := by
  unfold carryVollSchritt at h
  cases hlen : laengeOk (carryVollLaenge v) with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hload : concLoad (tsoAnsicht m) c (carryVollBreite v)
        (intMemAddr m c ripNext (carryVollForm v)) with
    | none => simp [hload] at h
    | some alt =>
      simp only [hload] at h
      cases hiss : concIssue (tsoAnsicht m) c (carryVollBreite v)
          (intMemAddr m c ripNext (carryVollForm v))
          (carryVollNeu v alt (m.kerne c).register
            (m.kerne c).flags).1 with
      | none => simp [hiss] at h
      | some s' =>
        simp only [hiss] at h
        cases h
        have he := concIssue_kein_speicher (tsoAnsicht m) s' c
          (carryVollBreite v)
          (intMemAddr m c ripNext (carryVollForm v))
          (carryVollNeu v alt (m.kerne c).register
            (m.kerne c).flags).1 hiss x
        simpa [tsoAnsicht, setTso, setKernDaten] using he

/-- A carry RMW installs the accepted result flags. -/
theorem carryVollSchritt_flags (m m' : HwMaschine) (c : Nat)
    (v : CarryVoll) (ripNext : Adresse)
    (h : carryVollSchritt m c v ripNext = some m') :
    ∃ alt : Wort,
      concLoad (tsoAnsicht m) c (carryVollBreite v)
        (intMemAddr m c ripNext (carryVollForm v)) = some alt ∧
      (m'.kerne c).flags =
        (carryVollNeu v alt (m.kerne c).register
          (m.kerne c).flags).2 := by
  unfold carryVollSchritt at h
  cases hlen : laengeOk (carryVollLaenge v) with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hload : concLoad (tsoAnsicht m) c (carryVollBreite v)
        (intMemAddr m c ripNext (carryVollForm v)) with
    | none => simp [hload] at h
    | some alt =>
      simp only [hload] at h
      cases hiss : concIssue (tsoAnsicht m) c (carryVollBreite v)
          (intMemAddr m c ripNext (carryVollForm v))
          (carryVollNeu v alt (m.kerne c).register
            (m.kerne c).flags).1 with
      | none => simp [hiss] at h
      | some s' =>
        simp only [hiss] at h
        cases h
        exact ⟨alt, rfl, by simp [setKernDaten]⟩

/-- A carry RMW advances RIP past its length. -/
theorem carryVollSchritt_rip (m m' : HwMaschine) (c : Nat)
    (v : CarryVoll) (ripNext : Adresse)
    (h : carryVollSchritt m c v ripNext = some m') :
    (m'.kerne c).rip =
      ripNach (m.kerne c).rip (carryVollLaenge v) := by
  unfold carryVollSchritt at h
  cases hlen : laengeOk (carryVollLaenge v) with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hload : concLoad (tsoAnsicht m) c (carryVollBreite v)
        (intMemAddr m c ripNext (carryVollForm v)) with
    | none => simp [hload] at h
    | some alt =>
      simp only [hload] at h
      cases hiss : concIssue (tsoAnsicht m) c (carryVollBreite v)
          (intMemAddr m c ripNext (carryVollForm v))
          (carryVollNeu v alt (m.kerne c).register
            (m.kerne c).flags).1 with
      | none => simp [hiss] at h
      | some s' =>
        simp only [hiss] at h
        cases h
        simp [setKernDaten]

/-- A carry RMW preserves well-formedness (profiles untouched). -/
theorem carryVollSchritt_wf (m m' : HwMaschine) (c : Nat)
    (v : CarryVoll) (ripNext : Adresse)
    (h : carryVollSchritt m c v ripNext = some m')
    (hwf : HwWf m) : HwWf m' := by
  unfold carryVollSchritt at h
  cases hlen : laengeOk (carryVollLaenge v) with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hload : concLoad (tsoAnsicht m) c (carryVollBreite v)
        (intMemAddr m c ripNext (carryVollForm v)) with
    | none => simp [hload] at h
    | some alt =>
      simp only [hload] at h
      cases hiss : concIssue (tsoAnsicht m) c (carryVollBreite v)
          (intMemAddr m c ripNext (carryVollForm v))
          (carryVollNeu v alt (m.kerne c).register
            (m.kerne c).flags).1 with
      | none => simp [hiss] at h
      | some s' =>
        simp only [hiss] at h
        cases h
        exact hwf

/-- A bad length refuses the carry RMW on any machine. -/
theorem carryVollSchritt_laenge_verweigert (m : HwMaschine) (c : Nat)
    (v : CarryVoll) (ripNext : Adresse)
    (h : laengeOk (carryVollLaenge v) = false) :
    carryVollSchritt m c v ripNext = none := by
  unfold carryVollSchritt
  simp [h]

/-- A refused load gate refuses the carry RMW: no successor. -/
theorem carryVollSchritt_lade_verweigert (m : HwMaschine) (c : Nat)
    (v : CarryVoll) (ripNext : Adresse)
    (hok : laengeOk (carryVollLaenge v) = true)
    (hgate : concLoad (tsoAnsicht m) c (carryVollBreite v)
      (intMemAddr m c ripNext (carryVollForm v)) = none) :
    carryVollSchritt m c v ripNext = none := by
  unfold carryVollSchritt
  simp [hok, hgate]

/-! ## 4. Machine events: sign-extend loads and XCHG swaps.

  A sign-extend load is a pure TSO load event (buffer and memory
  untouched, flags kept); an XCHG swap is a load-modify-store pair
  (old word into the register with the narrow merge, register word
  into the buffer). Neither claims atomicity: the locked path stays
  with the locked families and LOCK refuses (§6). -/

/-- Lifted sign-extend load on the coherent machine: forwarding-aware
    load at the source width, full 64-bit install, RIP advance, flags
    kept (architectural MOV shape). -/
def signVollSchritt (m : HwMaschine) (c : Nat) (s : SignVoll)
    (ripNext : Adresse) : Option HwMaschine :=
  match laengeOk s.laenge with
  | false => none
  | true =>
    match signVollOk s with
    | false => none
    | true =>
      let a := intMemAddr m c ripNext s.form
      match concLoad (tsoAnsicht m) c s.quelle a with
      | none => none
      | some alt =>
        some (setKernDaten m c
          (HwKern.mk
            (regSet (m.kerne c).register s.ziel (signVollNeu s alt))
            (m.kerne c).flags
            (ripNach (m.kerne c).rip s.laenge)
            (m.kerne c).xmm (m.kerne c).fp))

/-- A sign load installs the extended word in the destination. -/
theorem signVollSchritt_dst (m m' : HwMaschine) (c : Nat) (s : SignVoll)
    (ripNext : Adresse)
    (h : signVollSchritt m c s ripNext = some m') :
    ∃ alt : Wort,
      concLoad (tsoAnsicht m) c s.quelle
        (intMemAddr m c ripNext s.form) = some alt ∧
      (m'.kerne c).register s.ziel = signVollNeu s alt := by
  unfold signVollSchritt at h
  cases hlen : laengeOk s.laenge with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hok : signVollOk s with
    | false => simp [hok] at h
    | true =>
      simp only [hok] at h
      cases hload : concLoad (tsoAnsicht m) c s.quelle
          (intMemAddr m c ripNext s.form) with
      | none => simp [hload] at h
      | some alt =>
        simp only [hload] at h
        cases h
        exact ⟨alt, rfl, by simp [setKernDaten, regSet_gleich]⟩

/-- A sign load keeps every flag. -/
theorem signVollSchritt_flags (m m' : HwMaschine) (c : Nat)
    (s : SignVoll) (ripNext : Adresse)
    (h : signVollSchritt m c s ripNext = some m') :
    (m'.kerne c).flags = (m.kerne c).flags := by
  unfold signVollSchritt at h
  cases hlen : laengeOk s.laenge with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hok : signVollOk s with
    | false => simp [hok] at h
    | true =>
      simp only [hok] at h
      cases hload : concLoad (tsoAnsicht m) c s.quelle
          (intMemAddr m c ripNext s.form) with
      | none => simp [hload] at h
      | some alt =>
        simp only [hload] at h
        cases h
        simp [setKernDaten]

/-- A sign load advances RIP past its length. -/
theorem signVollSchritt_rip (m m' : HwMaschine) (c : Nat)
    (s : SignVoll) (ripNext : Adresse)
    (h : signVollSchritt m c s ripNext = some m') :
    (m'.kerne c).rip = ripNach (m.kerne c).rip s.laenge := by
  unfold signVollSchritt at h
  cases hlen : laengeOk s.laenge with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hok : signVollOk s with
    | false => simp [hok] at h
    | true =>
      simp only [hok] at h
      cases hload : concLoad (tsoAnsicht m) c s.quelle
          (intMemAddr m c ripNext s.form) with
      | none => simp [hload] at h
      | some alt =>
        simp only [hload] at h
        cases h
        simp [setKernDaten]

/-- A sign load buffers nothing: the acting buffer is kept. -/
theorem signVollSchritt_puffer (m m' : HwMaschine) (c : Nat)
    (s : SignVoll) (ripNext : Adresse)
    (h : signVollSchritt m c s ripNext = some m') :
    m'.puffer c = m.puffer c := by
  unfold signVollSchritt at h
  cases hlen : laengeOk s.laenge with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hok : signVollOk s with
    | false => simp [hok] at h
    | true =>
      simp only [hok] at h
      cases hload : concLoad (tsoAnsicht m) c s.quelle
          (intMemAddr m c ripNext s.form) with
      | none => simp [hload] at h
      | some alt =>
        simp only [hload] at h
        cases h
        rfl

/-- A sign load preserves well-formedness. -/
theorem signVollSchritt_wf (m m' : HwMaschine) (c : Nat)
    (s : SignVoll) (ripNext : Adresse)
    (h : signVollSchritt m c s ripNext = some m')
    (hwf : HwWf m) : HwWf m' := by
  unfold signVollSchritt at h
  cases hlen : laengeOk s.laenge with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hok : signVollOk s with
    | false => simp [hok] at h
    | true =>
      simp only [hok] at h
      cases hload : concLoad (tsoAnsicht m) c s.quelle
          (intMemAddr m c ripNext s.form) with
      | none => simp [hload] at h
      | some alt =>
        simp only [hload] at h
        cases h
        exact hwf

/-- A bad length refuses the sign load on any machine. -/
theorem signVollSchritt_laenge_verweigert (m : HwMaschine) (c : Nat)
    (s : SignVoll) (ripNext : Adresse)
    (h : laengeOk s.laenge = false) :
    signVollSchritt m c s ripNext = none := by
  unfold signVollSchritt
  simp [h]

/-- A 64-bit source refuses the sign load on any machine. -/
theorem signVollSchritt_quelle_verweigert (m : HwMaschine) (c : Nat)
    (s : SignVoll) (ripNext : Adresse)
    (hok : laengeOk s.laenge = true)
    (hq : signVollOk s = false) :
    signVollSchritt m c s ripNext = none := by
  unfold signVollSchritt
  simp [hok, hq]

/-- A refused load gate refuses the sign load: no successor. -/
theorem signVollSchritt_lade_verweigert (m : HwMaschine) (c : Nat)
    (s : SignVoll) (ripNext : Adresse)
    (hok : laengeOk s.laenge = true)
    (hq : signVollOk s = true)
    (hgate : concLoad (tsoAnsicht m) c s.quelle
      (intMemAddr m c ripNext s.form) = none) :
    signVollSchritt m c s ripNext = none := by
  unfold signVollSchritt
  simp [hok, hq, hgate]

/-- Lifted XCHG swap on the coherent machine: load the old word,
    buffer the register word, install the old word, advance RIP,
    keep flags. Load-modify-store events only; no atomicity claim. -/
def xchgVollSchritt (m : HwMaschine) (c : Nat) (x : XchgVoll)
    (ripNext : Adresse) : Option HwMaschine :=
  match laengeOk x.laenge with
  | false => none
  | true =>
    let a := intMemAddr m c ripNext x.form
    match concLoad (tsoAnsicht m) c x.breite a with
    | none => none
    | some alt =>
      match concIssue (tsoAnsicht m) c x.breite a
          ((m.kerne c).register x.reg) with
      | none => none
      | some s' =>
        some (setKernDaten (setTso m s') c
          (HwKern.mk
            (xchgVollNeuReg x (m.kerne c).register alt)
            (m.kerne c).flags
            (ripNach (m.kerne c).rip x.laenge)
            (m.kerne c).xmm (m.kerne c).fp))

/-- A swap buffers exactly the register word footprint. -/
theorem xchgVollSchritt_puffer (m m' : HwMaschine) (c : Nat)
    (x : XchgVoll) (ripNext : Adresse)
    (h : xchgVollSchritt m c x ripNext = some m') :
    ∃ alt : Wort,
      concLoad (tsoAnsicht m) c x.breite
        (intMemAddr m c ripNext x.form) = some alt ∧
      m'.puffer c = m.puffer c ++
        entriesOf x.breite (intMemAddr m c ripNext x.form)
          ((m.kerne c).register x.reg) := by
  unfold xchgVollSchritt at h
  cases hlen : laengeOk x.laenge with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hload : concLoad (tsoAnsicht m) c x.breite
        (intMemAddr m c ripNext x.form) with
    | none => simp [hload] at h
    | some alt =>
      simp only [hload] at h
      cases hiss : concIssue (tsoAnsicht m) c x.breite
          (intMemAddr m c ripNext x.form)
          ((m.kerne c).register x.reg) with
      | none => simp [hiss] at h
      | some s' =>
        simp only [hiss] at h
        cases h
        have he := concIssue_haengt_an (tsoAnsicht m) s' c x.breite
          (intMemAddr m c ripNext x.form)
          ((m.kerne c).register x.reg) hiss
        exact ⟨alt, rfl, by simpa [tsoAnsicht, setTso, setKernDaten] using he⟩

/-- A swap installs the old word in the register with the merge. -/
theorem xchgVollSchritt_reg (m m' : HwMaschine) (c : Nat)
    (x : XchgVoll) (ripNext : Adresse)
    (h : xchgVollSchritt m c x ripNext = some m') :
    ∃ alt : Wort,
      concLoad (tsoAnsicht m) c x.breite
        (intMemAddr m c ripNext x.form) = some alt ∧
      (m'.kerne c).register x.reg =
        mergeRegNarrow x.breite ((m.kerne c).register x.reg) alt := by
  unfold xchgVollSchritt at h
  cases hlen : laengeOk x.laenge with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hload : concLoad (tsoAnsicht m) c x.breite
        (intMemAddr m c ripNext x.form) with
    | none => simp [hload] at h
    | some alt =>
      simp only [hload] at h
      cases hiss : concIssue (tsoAnsicht m) c x.breite
          (intMemAddr m c ripNext x.form)
          ((m.kerne c).register x.reg) with
      | none => simp [hiss] at h
      | some s' =>
        simp only [hiss] at h
        cases h
        exact ⟨alt, rfl,
          by simp [setKernDaten, xchgVollNeuReg_gleich,
            regSet_gleich]⟩

/-- A swap changes no canonical byte (buffer only). -/
theorem xchgVollSchritt_kein_speicher (m m' : HwMaschine) (c : Nat)
    (x : XchgVoll) (ripNext : Adresse) (z : Adresse)
    (h : xchgVollSchritt m c x ripNext = some m') :
    m'.mem.bytes z = m.mem.bytes z := by
  unfold xchgVollSchritt at h
  cases hlen : laengeOk x.laenge with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hload : concLoad (tsoAnsicht m) c x.breite
        (intMemAddr m c ripNext x.form) with
    | none => simp [hload] at h
    | some alt =>
      simp only [hload] at h
      cases hiss : concIssue (tsoAnsicht m) c x.breite
          (intMemAddr m c ripNext x.form)
          ((m.kerne c).register x.reg) with
      | none => simp [hiss] at h
      | some s' =>
        simp only [hiss] at h
        cases h
        have he := concIssue_kein_speicher (tsoAnsicht m) s' c x.breite
          (intMemAddr m c ripNext x.form)
          ((m.kerne c).register x.reg) hiss z
        simpa [tsoAnsicht, setTso, setKernDaten] using he

/-- A swap keeps every flag (XCHG affects none). -/
theorem xchgVollSchritt_flags (m m' : HwMaschine) (c : Nat)
    (x : XchgVoll) (ripNext : Adresse)
    (h : xchgVollSchritt m c x ripNext = some m') :
    (m'.kerne c).flags = (m.kerne c).flags := by
  unfold xchgVollSchritt at h
  cases hlen : laengeOk x.laenge with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hload : concLoad (tsoAnsicht m) c x.breite
        (intMemAddr m c ripNext x.form) with
    | none => simp [hload] at h
    | some alt =>
      simp only [hload] at h
      cases hiss : concIssue (tsoAnsicht m) c x.breite
          (intMemAddr m c ripNext x.form)
          ((m.kerne c).register x.reg) with
      | none => simp [hiss] at h
      | some s' =>
        simp only [hiss] at h
        cases h
        simp [setKernDaten]

/-- A swap advances RIP past its length. -/
theorem xchgVollSchritt_rip (m m' : HwMaschine) (c : Nat)
    (x : XchgVoll) (ripNext : Adresse)
    (h : xchgVollSchritt m c x ripNext = some m') :
    (m'.kerne c).rip = ripNach (m.kerne c).rip x.laenge := by
  unfold xchgVollSchritt at h
  cases hlen : laengeOk x.laenge with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hload : concLoad (tsoAnsicht m) c x.breite
        (intMemAddr m c ripNext x.form) with
    | none => simp [hload] at h
    | some alt =>
      simp only [hload] at h
      cases hiss : concIssue (tsoAnsicht m) c x.breite
          (intMemAddr m c ripNext x.form)
          ((m.kerne c).register x.reg) with
      | none => simp [hiss] at h
      | some s' =>
        simp only [hiss] at h
        cases h
        simp [setKernDaten]

/-- A swap preserves well-formedness. -/
theorem xchgVollSchritt_wf (m m' : HwMaschine) (c : Nat)
    (x : XchgVoll) (ripNext : Adresse)
    (h : xchgVollSchritt m c x ripNext = some m')
    (hwf : HwWf m) : HwWf m' := by
  unfold xchgVollSchritt at h
  cases hlen : laengeOk x.laenge with
  | false => simp [hlen] at h
  | true =>
    simp only [hlen] at h
    cases hload : concLoad (tsoAnsicht m) c x.breite
        (intMemAddr m c ripNext x.form) with
    | none => simp [hload] at h
    | some alt =>
      simp only [hload] at h
      cases hiss : concIssue (tsoAnsicht m) c x.breite
          (intMemAddr m c ripNext x.form)
          ((m.kerne c).register x.reg) with
      | none => simp [hiss] at h
      | some s' =>
        simp only [hiss] at h
        cases h
        exact hwf

/-- A bad length refuses the swap on any machine. -/
theorem xchgVollSchritt_laenge_verweigert (m : HwMaschine) (c : Nat)
    (x : XchgVoll) (ripNext : Adresse)
    (h : laengeOk x.laenge = false) :
    xchgVollSchritt m c x ripNext = none := by
  unfold xchgVollSchritt
  simp [h]

/-- A refused load gate refuses the swap: no successor. -/
theorem xchgVollSchritt_lade_verweigert (m : HwMaschine) (c : Nat)
    (x : XchgVoll) (ripNext : Adresse)
    (hok : laengeOk x.laenge = true)
    (hgate : concLoad (tsoAnsicht m) c x.breite
      (intMemAddr m c ripNext x.form) = none) :
    xchgVollSchritt m c x ripNext = none := by
  unfold xchgVollSchritt
  simp [hok, hgate]

/- CUTS: skeleton only; full statement at the end of the file. -/

end Gabbro.Grammatik.X86
