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
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Speicher.AddressEncoding
import Grammatik.X86.Hw.Familien.HwAddressed
import Grammatik.X86.TSO.Verriegelt.ConcurrentIntegerExecution
import Grammatik.X86.Befehle.Arithmetik.NarrowOps
import Grammatik.X86.Befehle.Ganzzahl.IntRotate
import Grammatik.X86.Befehle.Ganzzahl.IntCarryForms

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

/-! ## 5. Canonical lifted bytes: decode, encode, round trips.

  The accepted decoders refuse SIB choice, RIP-relative and disp8/disp0
  memory shapes, so the lifted bytes below are NEW canonical encodings
  (one family tag byte plus a config byte, then the accepted
  `encodeAdr` tail with its REX byte): tag 113 rotate, 114 carry, 115
  sign-extend, 116 XCHG. They extend the addressed space without
  shadowing any accepted row (no accepted decoder reads these tags).
  Self-consistency only; no silicon correspondence is claimed. -/

/-- Register carrying a rotate digit in its low three bits. -/
def rotRegFeld : RotOp → Register
  | .rol => .rax | .ror => .rcx | .rcl => .rdx | .rcr => .rbx

/-- The field register carries its digit. -/
theorem rotRegFeld_tief (o : RotOp) :
    regLow (rotRegFeld o) = rotOpFeld o := by
  cases o <;> rfl

/-- Canonical lifted rotate bytes: tag, digit-plus-width config, count
    byte, then the accepted address tail (REX first). -/
def rotVollEncode (r : RotVoll) : Option (List Byte) :=
  match encodeAdr (rotRegFeld r.op) r.form with
  | none => none
  | some tail =>
    some ([natByte 113,
      natByte (rotOpFeld r.op + 4 * breitenCode r.breite),
      natByte r.zaehlung] ++ tail)

/-- Lifted rotate decode: tag, config, count, REX check, then the
    accepted address tail. LOCK (240) never matches the tag. -/
def decodeRotVoll : List Byte → Option (RotVoll × List Byte)
  | b0 :: b1 :: b2 :: rest =>
    if byteNat b0 == 113 then
      match feldRotOp (byteNat b1 % 4), codeBreite (byteNat b1 / 4) with
      | some op, some b =>
        match rest with
        | rex :: rest2 =>
          match parseAdrTail 0 0 0 rest2 with
          | some (reg, f, rest') =>
            if reg = rotRegFeld op then
              if rex = rexFuer (rotRegFeld op) f then
                some (RotVoll.mk op b (byteNat b2) f
                  (3 + (rest.length - rest'.length)), rest')
              else none
            else none
          | none => none
        | [] => none
      | _, _ => none
    else none
  | _ => none

/-- An unadmitted form encodes to nothing. -/
theorem encodeAdr_verweigert_ohne_ok (reg : Register) (f : AdrForm)
    (h : adrOk f = false) :
    encodeAdr reg f = none := by
  unfold encodeAdr
  simp [h]

/-- An encoding needs an admitted address form. -/
theorem rotVollEncode_braucht_ok (r : RotVoll) (bs : List Byte)
    (h : rotVollEncode r = some bs) :
    adrOk r.form = true := by
  unfold rotVollEncode at h
  cases ht : encodeAdr (rotRegFeld r.op) r.form with
  | none => simp [ht] at h
  | some tail => exact encodeAdr_braucht_ok _ _ _ ht

/-- REFUSAL: `rsp` is never an index, so the lifted encode refuses. -/
theorem rotVollEncode_rsp_verweigert (b : Breite) (n : Nat) (len : Nat) :
    rotVollEncode ⟨.rol, b, n,
      skaliertForm .rbx .rsp 8 (BitVec.ofNat 32 5) .d8, len⟩ = none := by
  simp [rotVollEncode, encodeAdr_verweigert_ohne_ok,
    skaliertForm_rsp_verweigert]

/-- REFUSAL: `rbp` without displacement is refused. -/
theorem rotVollEncode_rbp_verweigert (o : RotOp) (b : Breite) (n : Nat)
    (len : Nat) :
    rotVollEncode ⟨o, b, n, basisKeinForm .rbp, len⟩ = none := by
  simp [rotVollEncode, encodeAdr_verweigert_ohne_ok,
    basisKeinForm_rbp_verweigert]

/-- ROUND TRIP (SIB): scaled index plus disp8 through lifted bytes. -/
theorem rotVollRundweg_sib :
    (rotVollEncode ⟨.rol, .b32, 1,
      skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8, 7⟩).bind
      decodeRotVoll =
      some (⟨.rol, .b32, 1,
        skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8, 7⟩, []) := by
  decide

/-- ROUND TRIP (RIP-relative): image reference through lifted bytes. -/
theorem rotVollRundweg_rip :
    (rotVollEncode ⟨.ror, .b64, 3,
      ripForm (BitVec.ofNat 32 4089), 9⟩).bind decodeRotVoll =
      some (⟨.ror, .b64, 3,
        ripForm (BitVec.ofNat 32 4089), 9⟩, []) := by
  decide

/-- Class index of a lifted carry form. -/
def carryVollKlasse : CarryVoll → Nat
  | .adcV .. => 0 | .sbbV .. => 1 | .adcIV .. => 2
  | .sbbIV .. => 3 | .incV .. => 4 | .decV .. => 5

/-- Canonical lifted carry bytes: tag, class-plus-width config, source
    code, the accepted address tail (REX first), immediate tail for the
    imm forms. -/
def carryVollEncode (v : CarryVoll) : Option (List Byte) :=
  match encodeAdr .rax (carryVollForm v) with
  | none => none
  | some tail =>
    let imm : List Byte :=
      match v with
      | .adcIV _ _ op _ => leBytes64 op
      | .sbbIV _ _ op _ => leBytes64 op
      | _ => []
    let src : Nat :=
      match v with
      | .adcV _ _ s _ => regCode s
      | .sbbV _ _ s _ => regCode s
      | _ => 0
    some ([natByte 114,
      natByte (carryVollKlasse v + 6 * breitenCode (carryVollBreite v)),
      natByte src] ++ tail ++ imm)

/-- Lifted carry decode: tag, config, source, REX check, accepted tail,
    immediate tail for the imm classes. -/
def decodeCarryVoll : List Byte → Option (CarryVoll × List Byte)
  | b0 :: b1 :: b2 :: rest =>
    if byteNat b0 == 114 then
      match codeBreite (byteNat b1 / 6), codeReg (byteNat b2) with
      | some b, some src =>
        match rest with
        | rex :: rest2 =>
          match parseAdrTail 0 0 0 rest2 with
          | some (reg, f, rest') =>
            if reg = .rax then
              if rex = rexFuer .rax f then
                let n := 3 + (rest.length - rest'.length)
                match byteNat b1 % 6 with
                | 0 => some (CarryVoll.adcV b f src n, rest')
                | 1 => some (CarryVoll.sbbV b f src n, rest')
                | 4 => some (CarryVoll.incV b f n, rest')
                | 5 => some (CarryVoll.decV b f n, rest')
                | 2 =>
                  match parseLe64 rest' with
                  | some (op, rest'') =>
                    some (CarryVoll.adcIV b f op
                      (3 + (rest.length - rest''.length)), rest'')
                  | none => none
                | 3 =>
                  match parseLe64 rest' with
                  | some (op, rest'') =>
                    some (CarryVoll.sbbIV b f op
                      (3 + (rest.length - rest''.length)), rest'')
                  | none => none
                | _ => none
              else none
            else none
          | none => none
        | [] => none
      | _, _ => none
    else none
  | _ => none

/-- An encoding needs an admitted address form. -/
theorem carryVollEncode_braucht_ok (v : CarryVoll) (bs : List Byte)
    (h : carryVollEncode v = some bs) :
    adrOk (carryVollForm v) = true := by
  unfold carryVollEncode at h
  cases ht : encodeAdr .rax (carryVollForm v) with
  | none => simp [ht] at h
  | some tail => exact encodeAdr_braucht_ok _ _ _ ht

/-- REFUSAL: `rsp` is never an index, so the lifted encode refuses. -/
theorem carryVollEncode_rsp_verweigert (b : Breite) (len : Nat) :
    carryVollEncode
      (CarryVoll.adcV b
        (skaliertForm .rbx .rsp 8 (BitVec.ofNat 32 5) .d8) .rcx
        len) = none := by
  have hnone : encodeAdr .rax
      (skaliertForm .rbx .rsp 8 (BitVec.ofNat 32 5) .d8) = none :=
    encodeAdr_verweigert_ohne_ok _ _
      (skaliertForm_rsp_verweigert _ _ _ _)
  have hform : carryVollForm
      (CarryVoll.adcV b
        (skaliertForm .rbx .rsp 8 (BitVec.ofNat 32 5) .d8) .rcx
        len) =
      skaliertForm .rbx .rsp 8 (BitVec.ofNat 32 5) .d8 := rfl
  unfold carryVollEncode
  rw [hform, hnone]

/-- ROUND TRIP (SIB): ADC with register source through lifted bytes. -/
theorem carryVollRundweg_sib :
    (carryVollEncode (CarryVoll.adcV .b32
      (skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8) .rcx
      7)).bind decodeCarryVoll =
      some (CarryVoll.adcV .b32
        (skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8) .rcx 7, []) := by
  decide

/-- ROUND TRIP (RIP-relative): INC through lifted bytes. -/
theorem carryVollRundweg_rip :
    (carryVollEncode (CarryVoll.incV .b64
      (ripForm (BitVec.ofNat 32 4089)) 9)).bind decodeCarryVoll =
      some (CarryVoll.incV .b64
        (ripForm (BitVec.ofNat 32 4089)) 9, []) := by
  decide

/-- ROUND TRIP (SIB immediate): ADC-immediate through lifted bytes. -/
theorem carryVollRundweg_sibImm :
    (carryVollEncode (CarryVoll.adcIV .b32
      (skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8)
      (BitVec.ofNat 64 5) 15)).bind decodeCarryVoll =
      some (CarryVoll.adcIV .b32
        (skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8)
        (BitVec.ofNat 64 5) 15, []) := by
  decide

/-- Canonical lifted sign-extend bytes: tag, source-width config,
    destination code, the accepted address tail (REX first). -/
def signVollEncode (s : SignVoll) : Option (List Byte) :=
  match encodeAdr .rax s.form with
  | none => none
  | some tail =>
    some ([natByte 115, natByte (breitenCode s.quelle),
      natByte (regCode s.ziel)] ++ tail)

/-- Lifted sign-extend decode: tag, config, destination, REX check,
    accepted tail. A 64-bit source refuses (no-op shape). -/
def decodeSignVoll : List Byte → Option (SignVoll × List Byte)
  | b0 :: b1 :: b2 :: rest =>
    if byteNat b0 == 115 then
      match codeBreite (byteNat b1), codeReg (byteNat b2) with
      | some .b64, _ => none
      | some sb, some dst =>
        match rest with
        | rex :: rest2 =>
          match parseAdrTail 0 0 0 rest2 with
          | some (reg, f, rest') =>
            if reg = .rax then
              if rex = rexFuer .rax f then
                some (SignVoll.mk sb dst f
                  (3 + (rest.length - rest'.length)), rest')
              else none
            else none
          | none => none
        | [] => none
      | _, _ => none
    else none
  | _ => none

/-- An encoding needs an admitted address form. -/
theorem signVollEncode_braucht_ok (s : SignVoll) (bs : List Byte)
    (h : signVollEncode s = some bs) :
    adrOk s.form = true := by
  unfold signVollEncode at h
  cases ht : encodeAdr .rax s.form with
  | none => simp [ht] at h
  | some tail => exact encodeAdr_braucht_ok _ _ _ ht

/-- REFUSAL: `rsp` is never an index, so the lifted encode refuses. -/
theorem signVollEncode_rsp_verweigert (len : Nat) :
    signVollEncode
      ⟨.b8, .rax,
        skaliertForm .rbx .rsp 8 (BitVec.ofNat 32 5) .d8, len⟩ = none := by
  have hnone : encodeAdr .rax
      (skaliertForm .rbx .rsp 8 (BitVec.ofNat 32 5) .d8) = none :=
    encodeAdr_verweigert_ohne_ok _ _
      (skaliertForm_rsp_verweigert _ _ _ _)
  unfold signVollEncode
  simp [hnone]

/-- REFUSAL: a 64-bit source decodes to nothing. -/
theorem decodeSignVoll_b64_verweigert :
    decodeSignVoll [natByte 115, natByte 3, natByte 0, natByte 72,
      natByte 3] = none := rfl

/-- ROUND TRIP (SIB): byte source through lifted bytes. -/
theorem signVollRundweg_sib :
    (signVollEncode ⟨.b8, .rax,
      skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8, 7⟩).bind
      decodeSignVoll =
      some (⟨.b8, .rax,
        skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8, 7⟩, []) := by
  decide

/-- ROUND TRIP (RIP-relative): double-word source through lifted bytes. -/
theorem signVollRundweg_rip :
    (signVollEncode ⟨.b32, .rdx,
      ripForm (BitVec.ofNat 32 4089), 9⟩).bind decodeSignVoll =
      some (⟨.b32, .rdx,
        ripForm (BitVec.ofNat 32 4089), 9⟩, []) := by
  decide

/-- Canonical lifted XCHG bytes: tag, width config, register code,
    the accepted address tail (REX first). -/
def xchgVollEncode (x : XchgVoll) : Option (List Byte) :=
  match encodeAdr .rax x.form with
  | none => none
  | some tail =>
    some ([natByte 116, natByte (breitenCode x.breite),
      natByte (regCode x.reg)] ++ tail)

/-- Lifted XCHG decode: tag, config, register, REX check, accepted tail. -/
def decodeXchgVoll : List Byte → Option (XchgVoll × List Byte)
  | b0 :: b1 :: b2 :: rest =>
    if byteNat b0 == 116 then
      match codeBreite (byteNat b1), codeReg (byteNat b2) with
      | some b, some r =>
        match rest with
        | rex :: rest2 =>
          match parseAdrTail 0 0 0 rest2 with
          | some (reg, f, rest') =>
            if reg = .rax then
              if rex = rexFuer .rax f then
                some (XchgVoll.mk b f r
                  (3 + (rest.length - rest'.length)), rest')
              else none
            else none
          | none => none
        | [] => none
      | _, _ => none
    else none
  | _ => none

/-- An encoding needs an admitted address form. -/
theorem xchgVollEncode_braucht_ok (x : XchgVoll) (bs : List Byte)
    (h : xchgVollEncode x = some bs) :
    adrOk x.form = true := by
  unfold xchgVollEncode at h
  cases ht : encodeAdr .rax x.form with
  | none => simp [ht] at h
  | some tail => exact encodeAdr_braucht_ok _ _ _ ht

/-- REFUSAL: `rsp` is never an index, so the lifted encode refuses. -/
theorem xchgVollEncode_rsp_verweigert (b : Breite) (len : Nat) :
    xchgVollEncode
      ⟨b, skaliertForm .rbx .rsp 8 (BitVec.ofNat 32 5) .d8, .rcx,
        len⟩ = none := by
  have hnone : encodeAdr .rax
      (skaliertForm .rbx .rsp 8 (BitVec.ofNat 32 5) .d8) = none :=
    encodeAdr_verweigert_ohne_ok _ _
      (skaliertForm_rsp_verweigert _ _ _ _)
  unfold xchgVollEncode
  simp [hnone]

/-- ROUND TRIP (SIB): word exchange through lifted bytes. -/
theorem xchgVollRundweg_sib :
    (xchgVollEncode ⟨.b64,
      skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8, .rcx,
      7⟩).bind decodeXchgVoll =
      some (⟨.b64,
        skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8, .rcx, 7⟩,
        []) := by
  decide

/-- ROUND TRIP (RIP-relative): word exchange through lifted bytes. -/
theorem xchgVollRundweg_rip :
    (xchgVollEncode ⟨.b64,
      ripForm (BitVec.ofNat 32 4089), .rax, 9⟩).bind decodeXchgVoll =
      some (⟨.b64,
        ripForm (BitVec.ofNat 32 4089), .rax, 9⟩, []) := by
  decide

/-! ## 6. LOCK stays refused.

  LOCK prefix (240) matches no lifted family tag, on any suffix: the
  locked RMW path stays with the locked families. Each pin below is a
  closed decidable observation. -/

/-- LOCK-prefixed bytes refuse the lifted rotate decode. -/
theorem decodeRotVoll_lock_verweigert (suffix : List Byte) :
    decodeRotVoll ([natByte 240] ++ suffix) = none := by
  match suffix with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: _ => rfl

/-- LOCK-prefixed bytes refuse the lifted carry decode. -/
theorem decodeCarryVoll_lock_verweigert (suffix : List Byte) :
    decodeCarryVoll ([natByte 240] ++ suffix) = none := by
  match suffix with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: _ => rfl

/-- LOCK-prefixed bytes refuse the lifted sign-extend decode. -/
theorem decodeSignVoll_lock_verweigert (suffix : List Byte) :
    decodeSignVoll ([natByte 240] ++ suffix) = none := by
  match suffix with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: _ => rfl

/-- LOCK-prefixed bytes refuse the lifted XCHG decode. -/
theorem decodeXchgVoll_lock_verweigert (suffix : List Byte) :
    decodeXchgVoll ([natByte 240] ++ suffix) = none := by
  match suffix with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: _ => rfl

/-! ## 8. Reached witness: two cores, SIB and RIP-relative forms.

  Core 0 runs a carry INC through the SIB form `rbx + rcx * 8`
  (8200), forwards the value to its own load while core 1 still reads
  zero, then drains it into shared memory (0 becomes 1, both cores
  observe). Chained on the drained machine, core 0 runs a rotate ROL
  through the same SIB form (1 becomes 2, same owner-only pattern).
  Core 1 then swaps through the RIP-relative form (register 7 in,
  old word 2 out) and, after the drain, sign-loads the landed word.
  Every claim below is a closed decidable observation. -/

/-- Witness SIB form: base `rbx`, index `rcx`, scale 8, disp8 zero. -/
def intMemWitSIB : AdrForm :=
  skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 0) .d8

/-- Witness RIP-relative form: next-RIP plus 4097. -/
def intMemWitRIP : AdrForm := ripForm (BitVec.ofNat 32 4097)

/-- Witness next-RIP bases (instruction lengths 7 and 9). -/
def intMemWitNext0 : Adresse := BitVec.ofNat 64 4103
def intMemWitNext1 : Adresse := BitVec.ofNat 64 4103

/-- Witness data address. -/
def intMemWitA : Adresse := BitVec.ofNat 64 8200

/-- Witness descriptors: INC, ROL-by-1, XCHG, sign load. -/
def intMemWitInc : CarryVoll := CarryVoll.incV .b32 intMemWitSIB 7
def intMemWitRol : RotVoll := RotVoll.mk .rol .b32 1 intMemWitSIB 7
def intMemWitXchg : XchgVoll := XchgVoll.mk .b32 intMemWitRIP .rdx 9
def intMemWitSign : SignVoll := SignVoll.mk .b32 .rax intMemWitRIP 9

/-- Witness shared bytes: zeroed. -/
def intMemWitBytes (_ : Adresse) : Byte := BitVec.ofNat 8 0

/-- Witness code permission: seven bytes at 4096. -/
def intMemWitCode (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4103)

/-- Witness data permission: sixteen bytes at 8192. -/
def intMemWitDaten (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8208)

/-- Witness shared memory. -/
def intMemWitMem : Speicher :=
  { bytes := intMemWitBytes, lesbar := intMemWitDaten,
    schreibbar := intMemWitDaten, ausfuehrbar := intMemWitCode }

/-- Witness core-0 registers: base, index, stack. -/
def intMemWitReg0 : Register → Wort := fun q =>
  if q = Register.rbx then BitVec.ofNat 64 8192
  else if q = Register.rcx then BitVec.ofNat 64 1
  else if q = Register.rsp then BitVec.ofNat 64 8704
  else BitVec.ofNat 64 0

/-- Witness core-1 registers: exchange value in `rdx`, stack. -/
def intMemWitReg1 : Register → Wort := fun q =>
  if q = Register.rdx then BitVec.ofNat 64 7
  else if q = Register.rsp then BitVec.ofNat 64 8704
  else BitVec.ofNat 64 0

/-- Witness cores: core 0 runs at 4096, core 1 idles on the
    (non-executable) data page. -/
def intMemWitKern : Nat → HwKern
  | 0 => HwKern.mk intMemWitReg0 zeugeFlags (BitVec.ofNat 64 4096)
      (fun _ => BitVec.ofNat 128 0) kontextReset
  | _ => HwKern.mk intMemWitReg1 zeugeFlags (BitVec.ofNat 64 8192)
      (fun _ => BitVec.ofNat 128 0) kontextReset

/-- Witness start machine: shared memory, two cores, empty buffers,
    full silicon with OS vector state. -/
def intMemWitM0 : HwMaschine :=
  HwMaschine.mk intMemWitMem intMemWitKern (fun _ => [])
    basisHw (fun _ => basisBereit)

/-- The witness machine is well-formed: full silicon admits all. -/
theorem intMemWitM0_wf : HwWf intMemWitM0 := by
  intro c f _
  cases f <;> rfl

/-- Read a buffer length out of a machine outcome. -/
def intMemBufOut (o : Option HwMaschine) (c : Nat) : Option Nat :=
  o.map (fun m => (m.puffer c).length)

/-- Read a core RIP out of a machine outcome. -/
def intMemRipOut (o : Option HwMaschine) (c : Nat) : Option Wort :=
  o.map (fun m => (m.kerne c).rip)

/-- Read a core register out of a machine outcome. -/
def intMemRegOut (o : Option HwMaschine) (c : Nat)
    (q : Register) : Option Wort :=
  o.map (fun m => (m.kerne c).register q)

/-- The SIB form names the data cell from pre-state registers. -/
theorem intMemWit_sib_addr :
    intMemAddr intMemWitM0 0 intMemWitNext0 intMemWitSIB =
      intMemWitA := by
  decide

/-- The RIP-relative form names the data cell from the next RIP. -/
theorem intMemWit_rip_addr :
    intMemAddr intMemWitM0 1 intMemWitNext1 intMemWitRIP =
      intMemWitA := by
  decide

/-- Both witness forms are admitted as data. -/
theorem intMemWit_form_ok :
    adrOk intMemWitSIB = true ∧ adrOk intMemWitRIP = true := by
  decide

/-- The data cell starts zeroed: the run really changes memory. -/
theorem intMemWit_anfang_null :
    intMemWitMem.bytes intMemWitA = BitVec.ofNat 8 0 := by
  decide

/-- Core 0 INC through the SIB form. -/
def intMemWitM1 : Option HwMaschine :=
  carryVollSchritt intMemWitM0 0 intMemWitInc intMemWitNext0

/-- The shared TSO state after the INC issue. -/
def intMemWitT1 : Option TSOZustand :=
  intMemWitM1.map tsoAnsicht

/-- Core 0 observes its own issued word (forwarding). -/
def intMemWitE1 : Option (Option Wort) :=
  intMemWitT1.map (fun s => concLoad s 0 .b32 intMemWitA)

/-- Core 1 observes the old word (no foreign forwarding). -/
def intMemWitF1 : Option (Option Wort) :=
  intMemWitT1.map (fun s => concLoad s 1 .b32 intMemWitA)

/-- Core 0 drains its four entries, one flush per state. -/
def intMemWitT2 : Option TSOZustand :=
  intMemWitT1.bind (fun s => flushKern s 0)

def intMemWitT3 : Option TSOZustand :=
  intMemWitT2.bind (fun s => flushKern s 0)

def intMemWitT4 : Option TSOZustand :=
  intMemWitT3.bind (fun s => flushKern s 0)

def intMemWitT5 : Option TSOZustand :=
  intMemWitT4.bind (fun s => flushKern s 0)

/-- The shared byte after the first drain. -/
def intMemWitN1 : Option (Option Byte) :=
  intMemWitT5.map (fun s => some (s.mem.bytes intMemWitA))

/-- The machine after the first drain (core data kept). -/
def intMemWitM1d : Option HwMaschine :=
  match intMemWitM1, intMemWitT5 with
  | some m1, some t5 => some (setTso m1 t5)
  | _, _ => none

/-- Core 0 ROL-by-1 through the same SIB form, chained on the drain. -/
def intMemWitM2 : Option HwMaschine :=
  intMemWitM1d.bind (fun m => rotVollSchritt m 0 intMemWitRol
    intMemWitNext0)

/-- The shared TSO state after the ROL issue. -/
def intMemWitT6 : Option TSOZustand :=
  intMemWitM2.map tsoAnsicht

/-- Core 0 observes its rotated word (forwarding). -/
def intMemWitE2 : Option (Option Wort) :=
  intMemWitT6.map (fun s => concLoad s 0 .b32 intMemWitA)

/-- Core 1 observes the drained word (no foreign forwarding). -/
def intMemWitF2 : Option (Option Wort) :=
  intMemWitT6.map (fun s => concLoad s 1 .b32 intMemWitA)

/-- Core 0 drains the rotated word, one flush per state. -/
def intMemWitT7 : Option TSOZustand :=
  intMemWitT6.bind (fun s => flushKern s 0)

def intMemWitT8 : Option TSOZustand :=
  intMemWitT7.bind (fun s => flushKern s 0)

def intMemWitT9 : Option TSOZustand :=
  intMemWitT8.bind (fun s => flushKern s 0)

def intMemWitT10 : Option TSOZustand :=
  intMemWitT9.bind (fun s => flushKern s 0)

/-- The shared byte after the second drain. -/
def intMemWitN2 : Option (Option Byte) :=
  intMemWitT10.map (fun s => some (s.mem.bytes intMemWitA))

/-- The machine after the second drain (core data kept). -/
def intMemWitM2d : Option HwMaschine :=
  match intMemWitM2, intMemWitT10 with
  | some m2, some t10 => some (setTso m2 t10)
  | _, _ => none

/-- The INC issues four buffer entries. -/
theorem intMemWit_m1_buf :
    intMemBufOut intMemWitM1 0 = some 4 := by
  decide

/-- The INC advances RIP past its length. -/
theorem intMemWit_m1_rip :
    intMemRipOut intMemWitM1 0 = some (BitVec.ofNat 64 4103) := by
  decide

/-- Forwarding: core 0 reads its own unflushed word. -/
theorem intMemWit_e1 :
    intMemWitE1 = some (some (BitVec.ofNat 64 1)) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem intMemWit_f1 :
    intMemWitF1 = some (some (BitVec.ofNat 64 0)) := by
  decide

/-- The first drain changes shared memory: the cell reads `0x01`. -/
theorem intMemWit_n1 :
    intMemWitN1 = some (some (BitVec.ofNat 8 1)) := by
  decide

/-- The ROL issues four buffer entries over the empty buffer. -/
theorem intMemWit_m2_buf :
    intMemBufOut intMemWitM2 0 = some 4 := by
  decide

/-- The ROL advances RIP past its length. -/
theorem intMemWit_m2_rip :
    intMemRipOut intMemWitM2 0 = some (BitVec.ofNat 64 4110) := by
  decide

/-- Forwarding: core 0 reads its rotated word. -/
theorem intMemWit_e2 :
    intMemWitE2 = some (some (BitVec.ofNat 64 2)) := by
  decide

/-- No foreign forwarding: core 1 still reads the drained word. -/
theorem intMemWit_f2 :
    intMemWitF2 = some (some (BitVec.ofNat 64 1)) := by
  decide

/-- The second drain changes shared memory: the cell reads `0x02`. -/
theorem intMemWit_n2 :
    intMemWitN2 = some (some (BitVec.ofNat 8 2)) := by
  decide

/-! ## 7. The adapter plug over the coherent machine.

  One checked event step per family on the shared TSO view, reusing
  the §3/§4 evaluators. Register-only forms never enter this plug;
  LOCK has no event (refused at decode, §6). -/

/-- Lifted family events: rotate RMW, carry RMW, sign load, XCHG swap,
    each with its next-RIP base, plus explicit refusal. -/
inductive IntMemEreignis where
  | rot (r : RotVoll) (ripNext : Adresse)
  | carry (v : CarryVoll) (ripNext : Adresse)
  | sign (s : SignVoll) (ripNext : Adresse)
  | xchg (x : XchgVoll) (ripNext : Adresse)
  | verweigert
  deriving DecidableEq, Repr

/-- The lifted adapter: one checked event step on the coherent machine. -/
def adapterIntMem : HwAdapter IntMemEreignis :=
  ⟨fun m c e =>
    match e with
    | .rot r ripNext => rotVollSchritt m c r ripNext
    | .carry v ripNext => carryVollSchritt m c v ripNext
    | .sign s ripNext => signVollSchritt m c s ripNext
    | .xchg x ripNext => xchgVollSchritt m c x ripNext
    | .verweigert => none⟩

/-- The refused event admits nothing. -/
theorem adapterIntMem_verweigert (m : HwMaschine) (c : Nat) :
    adapterIntMem.schritt m c .verweigert = none := rfl

/-- An adapter rotate step is a lifted rotate RMW. -/
theorem adapterIntMem_rot (m m' : HwMaschine) (c : Nat) (r : RotVoll)
    (ripNext : Adresse)
    (h : adapterIntMem.schritt m c (.rot r ripNext) = some m') :
    rotVollSchritt m c r ripNext = some m' := h

/-- An adapter carry step is a lifted carry RMW. -/
theorem adapterIntMem_carry (m m' : HwMaschine) (c : Nat)
    (v : CarryVoll) (ripNext : Adresse)
    (h : adapterIntMem.schritt m c (.carry v ripNext) = some m') :
    carryVollSchritt m c v ripNext = some m' := h

/-- An adapter sign step is a lifted sign load. -/
theorem adapterIntMem_sign (m m' : HwMaschine) (c : Nat)
    (s : SignVoll) (ripNext : Adresse)
    (h : adapterIntMem.schritt m c (.sign s ripNext) = some m') :
    signVollSchritt m c s ripNext = some m' := h

/-- An adapter XCHG step is a lifted swap. -/
theorem adapterIntMem_xchg (m m' : HwMaschine) (c : Nat)
    (x : XchgVoll) (ripNext : Adresse)
    (h : adapterIntMem.schritt m c (.xchg x ripNext) = some m') :
    xchgVollSchritt m c x ripNext = some m' := h

/-- Every adapter step preserves well-formedness: only core data,
    buffers and shared memory move; profiles are untouched. -/
theorem adapterIntMem_wf (m m' : HwMaschine) (c : Nat)
    (e : IntMemEreignis) (hwf : HwWf m)
    (h : adapterIntMem.schritt m c e = some m') : HwWf m' := by
  cases e with
  | rot r ripNext => exact rotVollSchritt_wf m m' c r ripNext h hwf
  | carry v ripNext => exact carryVollSchritt_wf m m' c v ripNext h hwf
  | sign s ripNext => exact signVollSchritt_wf m m' c s ripNext h hwf
  | xchg x ripNext => exact xchgVollSchritt_wf m m' c x ripNext h hwf
  | verweigert => simp [adapterIntMem] at h

/-- A bad length admits no adapter rotate step. -/
theorem adapterIntMem_rot_laenge (m : HwMaschine) (c : Nat)
    (r : RotVoll) (ripNext : Adresse)
    (h : laengeOk r.laenge = false) :
    adapterIntMem.schritt m c (.rot r ripNext) = none :=
  rotVollSchritt_laenge_verweigert m c r ripNext h

/-- A bad length admits no adapter carry step. -/
theorem adapterIntMem_carry_laenge (m : HwMaschine) (c : Nat)
    (v : CarryVoll) (ripNext : Adresse)
    (h : laengeOk (carryVollLaenge v) = false) :
    adapterIntMem.schritt m c (.carry v ripNext) = none :=
  carryVollSchritt_laenge_verweigert m c v ripNext h

/-- A bad length admits no adapter sign step. -/
theorem adapterIntMem_sign_laenge (m : HwMaschine) (c : Nat)
    (s : SignVoll) (ripNext : Adresse)
    (h : laengeOk s.laenge = false) :
    adapterIntMem.schritt m c (.sign s ripNext) = none :=
  signVollSchritt_laenge_verweigert m c s ripNext h

/-- A bad length admits no adapter XCHG step. -/
theorem adapterIntMem_xchg_laenge (m : HwMaschine) (c : Nat)
    (x : XchgVoll) (ripNext : Adresse)
    (h : laengeOk x.laenge = false) :
    adapterIntMem.schritt m c (.xchg x ripNext) = none :=
  xchgVollSchritt_laenge_verweigert m c x ripNext h

/-- Core 1 XCHG through the RIP-relative form, chained on the
    second drain: register 7 installs, old word 2 lands in `rdx`. -/
def intMemWitM3 : Option HwMaschine :=
  intMemWitM2d.bind (fun m => xchgVollSchritt m 1 intMemWitXchg
    intMemWitNext1)

/-- Core 1 drains its four swap entries, one flush per state. -/
def intMemWitT11 : Option TSOZustand :=
  intMemWitM3.map tsoAnsicht

def intMemWitT12 : Option TSOZustand :=
  intMemWitT11.bind (fun s => flushKern s 1)

def intMemWitT13 : Option TSOZustand :=
  intMemWitT12.bind (fun s => flushKern s 1)

def intMemWitT14 : Option TSOZustand :=
  intMemWitT13.bind (fun s => flushKern s 1)

def intMemWitT15 : Option TSOZustand :=
  intMemWitT14.bind (fun s => flushKern s 1)

/-- The shared byte after the third drain. -/
def intMemWitN3 : Option (Option Byte) :=
  intMemWitT15.map (fun s => some (s.mem.bytes intMemWitA))

/-- The machine after the third drain (core data kept). -/
def intMemWitM3d : Option HwMaschine :=
  match intMemWitM3, intMemWitT15 with
  | some m3, some t15 => some (setTso m3 t15)
  | _, _ => none

/-- Core 1 sign-loads the landed word through the RIP-relative form. -/
def intMemWitM4 : Option HwMaschine :=
  intMemWitM3d.bind (fun m => signVollSchritt m 1 intMemWitSign
    intMemWitNext1)

/-- The swap installs the old word in `rdx`. -/
theorem intMemWit_m3_rdx :
    intMemRegOut intMemWitM3 1 .rdx = some (BitVec.ofNat 64 2) := by
  decide

/-- The swap buffers four entries on core 1. -/
theorem intMemWit_m3_buf :
    intMemBufOut intMemWitM3 1 = some 4 := by
  decide

/-- The swap advances core-1 RIP past its length. -/
theorem intMemWit_m3_rip :
    intMemRipOut intMemWitM3 1 = some (BitVec.ofNat 64 8201) := by
  decide

/-- The third drain changes shared memory: the cell reads `0x07`. -/
theorem intMemWit_n3 :
    intMemWitN3 = some (some (BitVec.ofNat 8 7)) := by
  decide

/-- The sign load lands the swapped word in `rax`. -/
theorem intMemWit_m4_rax :
    intMemRegOut intMemWitM4 1 .rax = some (BitVec.ofNat 64 7) := by
  decide

/-- The sign load advances core-1 RIP past its length. -/
theorem intMemWit_m4_rip :
    intMemRipOut intMemWitM4 1 = some (BitVec.ofNat 64 8210) := by
  decide

/-- The adapter runs the witness INC: the plug agrees on the run. -/
theorem intMemWit_adapter_m1 :
    adapterIntMem.schritt intMemWitM0 0
      (IntMemEreignis.carry intMemWitInc intMemWitNext0) =
      intMemWitM1 := rfl

/-- THE JOINT WITNESS: a reached two-core run through a SIB form
    (carry INC then rotate ROL with owner-only forwarding and two
    observable drains, 0 to 1 to 2) and a RIP-relative form (XCHG
    swapping 7 for 2, drained to 7, sign-loaded back) -- beside the
    adapter agreement, the LOCK refusal, the SIB refusal and the
    well-formedness of the start machine. Non-degenerate: three
    drains observably change shared memory, and every buffered store
    is visible via forwarding to the owner only. -/
theorem intMemWit_zeuge :
    intMemAddr intMemWitM0 0 intMemWitNext0 intMemWitSIB =
        intMemWitA ∧
      intMemAddr intMemWitM0 1 intMemWitNext1 intMemWitRIP =
        intMemWitA ∧
      adrOk intMemWitSIB = true ∧ adrOk intMemWitRIP = true ∧
      intMemWitMem.bytes intMemWitA = BitVec.ofNat 8 0 ∧
      intMemBufOut intMemWitM1 0 = some 4 ∧
      intMemRipOut intMemWitM1 0 = some (BitVec.ofNat 64 4103) ∧
      intMemWitE1 = some (some (BitVec.ofNat 64 1)) ∧
      intMemWitF1 = some (some (BitVec.ofNat 64 0)) ∧
      intMemWitN1 = some (some (BitVec.ofNat 8 1)) ∧
      intMemBufOut intMemWitM2 0 = some 4 ∧
      intMemRipOut intMemWitM2 0 = some (BitVec.ofNat 64 4110) ∧
      intMemWitE2 = some (some (BitVec.ofNat 64 2)) ∧
      intMemWitF2 = some (some (BitVec.ofNat 64 1)) ∧
      intMemWitN2 = some (some (BitVec.ofNat 8 2)) ∧
      intMemRegOut intMemWitM3 1 .rdx = some (BitVec.ofNat 64 2) ∧
      intMemBufOut intMemWitM3 1 = some 4 ∧
      intMemRipOut intMemWitM3 1 = some (BitVec.ofNat 64 8201) ∧
      intMemWitN3 = some (some (BitVec.ofNat 8 7)) ∧
      intMemRegOut intMemWitM4 1 .rax = some (BitVec.ofNat 64 7) ∧
      intMemRipOut intMemWitM4 1 = some (BitVec.ofNat 64 8210) ∧
      adapterIntMem.schritt intMemWitM0 0
        (IntMemEreignis.carry intMemWitInc intMemWitNext0) =
        intMemWitM1 ∧
      decodeCarryVoll ([natByte 240] ++ []) = none ∧
      rotVollEncode ⟨.rol, .b32, 1,
        skaliertForm .rbx .rsp 8 (BitVec.ofNat 32 5) .d8, 7⟩ = none ∧
      HwWf intMemWitM0 := by
  refine ⟨intMemWit_sib_addr, intMemWit_rip_addr, ?_, ?_,
    intMemWit_anfang_null, intMemWit_m1_buf, intMemWit_m1_rip,
    intMemWit_e1, intMemWit_f1, intMemWit_n1, intMemWit_m2_buf,
    intMemWit_m2_rip, intMemWit_e2, intMemWit_f2, intMemWit_n2,
    intMemWit_m3_rdx, intMemWit_m3_buf, intMemWit_m3_rip,
    intMemWit_n3, intMemWit_m4_rax, intMemWit_m4_rip,
    intMemWit_adapter_m1, ?_, ?_, intMemWitM0_wf⟩
  · exact (intMemWit_form_ok).1
  · exact (intMemWit_form_ok).2
  · exact decodeCarryVoll_lock_verweigert []
  · exact rotVollEncode_rsp_verweigert .b32 1 7

/- CUTS:
    Proved here, layering over (never editing) the accepted producers:
    - §0: the lifted address IS the selected `adrEff`
      (`intMemAddr_basisForm` against `effAddr`); width codec bits
      round-trip (`codeBreite_breitenCode`).
    - §1: lifted memory descriptors for all three families over the
      full `AdrForm` set (SIB choice, RIP-relative, disp8/disp0):
      `RotVoll`, `CarryVoll` (ADC/SBB register and immediate source,
      INC/DEC), `SignVoll` (8/16/32-bit source, 64-bit refused),
      `XchgVoll`.
    - §2: value agreement with the accepted evaluators, never a
      second model: rotate ROL/ROR/RCL/RCR values and the executable
      flag snapshot with its validity proof; ADC/SBB/INC/DEC values
      and flags with CF preservation; sign extension IS `sext`;
      the exchange install IS the narrow merge (full word at 64
      bits, the accepted swap shape).
    - §3/§4: machine events as TSO load-modify-store pairs on the
      shared view (`concLoad` then `concIssue`): exact `entriesOf`
      footprint appended, no canonical byte changed, RIP advanced,
      accepted flags installed (rotates, carry), flags kept (sign,
      XCHG), well-formedness preserved; planted refusals for bad
      length, refused load gate and, for sign, the 64-bit source.
    - §5/§6: NEW canonical lifted bytes (tags 113-116, never read by
      any accepted decoder, so nothing is shadowed) with pinned
      SIB and RIP-relative round trips per family (rotate, carry
      register/immediate, sign, XCHG), encode-needs-admission,
      unadmitted-form refusals (`rsp` index, `rbp` without
      displacement, 64-bit sign source), and LOCK refusal on every
      tag (the locked path stays with the locked families).
    - §7: the `HwAdapter IntMemEreignis` plug with exact step
      agreement (each event IS its §3/§4 step), well-formedness
      preservation and length refusals.
    - §8: reached two-core joint witness (`intMemWit_zeuge`): SIB
      INC then SIB ROL with owner-only forwarding and two observable
      drains (0 to 1 to 2), RIP-relative XCHG (7 for 2, drained to
      7) and sign load back (7) -- beside adapter agreement, LOCK
      refusal, SIB refusal and well-formedness. Non-degenerate:
      three drains observably change shared memory; every buffered
      store is visible via forwarding to the owner only.
    NOT proved here, and not claimed:
    - No hardware correspondence: the lifted tags 113-116 are new
      canonical bytes with self-consistency only (round trips,
      pins); no Intel SDM heading is cited for them and no x86
      truth is claimed. Value shapes reuse the accepted silicon
      assumptions of IntRotate/IntCarryForms (count masks, CF/OF
      rows, CF preservation) without re-checking them.
    - No byte-fetched execution: the witness drives decoded
      descriptors; fetch/decode coverage of the lifted tags stays
      open (no `decodeExt`/`stepExt` arm, no length-cap theorem
      over the lifted bytes beyond the pinned lengths 7/9/15).
    - No atomicity: XCHG runs as load-modify-store events; the
      single-access/locked-leg claim stays with the locked
      families (`xchgSchritt` barrier, `WortGruppe` guards).
      Whole-word atomicity beyond byte drains is not claimed.
    - No fault beyond the carried gate refusals, no interrupts,
      no per-access target-to-W/GX simulation, no source/ABI/
      loader/entry/budget claim, no timing or power claim.
-/

#print axioms intMemAddr_basisForm
#print axioms codeBreite_breitenCode
#print axioms rotVollNeu_rol
#print axioms rotVollFlags_gueltig
#print axioms carryVollNeu_adcV
#print axioms carryVollNeu_inc_cf
#print axioms signVollNeu_gleich
#print axioms xchgVollNeuReg_b64
#print axioms rotVollSchritt_puffer
#print axioms rotVollSchritt_kein_speicher
#print axioms rotVollSchritt_wf
#print axioms carryVollSchritt_puffer
#print axioms carryVollSchritt_flags
#print axioms carryVollSchritt_wf
#print axioms signVollSchritt_dst
#print axioms signVollSchritt_wf
#print axioms xchgVollSchritt_puffer
#print axioms xchgVollSchritt_reg
#print axioms xchgVollSchritt_wf
#print axioms rotVollRundweg_sib
#print axioms rotVollRundweg_rip
#print axioms carryVollRundweg_sib
#print axioms carryVollRundweg_rip
#print axioms carryVollRundweg_sibImm
#print axioms signVollRundweg_sib
#print axioms signVollRundweg_rip
#print axioms xchgVollRundweg_sib
#print axioms xchgVollRundweg_rip
#print axioms decodeRotVoll_lock_verweigert
#print axioms decodeCarryVoll_lock_verweigert
#print axioms decodeSignVoll_lock_verweigert
#print axioms decodeXchgVoll_lock_verweigert
#print axioms adapterIntMem_verweigert
#print axioms adapterIntMem_wf
#print axioms intMemWitM0_wf
#print axioms intMemWit_zeuge

end Gabbro.Grammatik.X86
