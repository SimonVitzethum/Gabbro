/-
  Checked entry-state predicates over the loaded image (lane 348, C4).

  Validator/profile admission as `Bool`, never a hardware fault claim.
  Reuses canonical `Bild`, `Stapel`, `Speicher` and `Gleitprofil`.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Bild
import Grammatik.X86.Stapel
import Grammatik.X86.Gleitprofil

namespace Gabbro.Grammatik.X86

/-- Entry kinds of IMAGE-ABI section 5. -/
inductive EintrittArt where
  | hostedMain | nolibcMain | modulInit | modulExit
  | metallStart | fadenWurzel | klonKind | trapRueck
  deriving DecidableEq, Repr

/-- Expected interrupt-enable bit per entry kind. -/
def ifErwartet : EintrittArt → Bool
  | .hostedMain => true
  | .nolibcMain => true
  | .modulInit => true
  | .modulExit => true
  | .metallStart => false
  | .fadenWurzel => true
  | .klonKind => true
  | .trapRueck => false

/-- Guard page promised per entry kind. -/
def guardErforderlich : EintrittArt → Bool
  | .fadenWurzel => true
  | .klonKind => true
  | _ => false

/-- Checked entry machine state: canonical `Zustand` plus FP control,
    XMM-touch flag with its save bit, the IF bit, and the validator's
    guard finding at the promised guard address. -/
structure EintrittZustand where
  zustand : Zustand
  mxcsr : MXCSR
  xmmBeruehrt : Bool
  mxcsrGesichert : Bool
  ifBit : Bool
  guardOk : Bool

/-- Stack pointer as address (canonical register file). -/
def eintrittRsp (z : EintrittZustand) : Adresse :=
  z.zustand.register .rsp

/-- Call-boundary alignment of the entry stack pointer. -/
def stapelOk (z : EintrittZustand) : Bool :=
  ausgerichtet16 (eintrittRsp z)

/-- MXCSR discipline: touching XMM needs a validated save and a valid word. -/
def mxcsrOk (z : EintrittZustand) : Bool :=
  (!z.xmmBeruehrt) || (z.mxcsrGesichert && mxcsrGueltig z.mxcsr)

/-- IF discipline: the entry's IF bit matches its kind. -/
def ifOk (art : EintrittArt) (z : EintrittZustand) : Bool :=
  decide (z.ifBit = ifErwartet art)

/-- Guard discipline: a promised guard page must be found unmapped. -/
def guardOk (art : EintrittArt) (z : EintrittZustand) : Bool :=
  (!guardErforderlich art) || z.guardOk

/-- Single-probe guard check at `wache`: neither readable, writable nor
    executable. A full 4096-byte sweep is OPEN (see CUTS). -/
def schutzSeiteOk (m : Speicher) (wache : Adresse) : Bool :=
  (!m.lesbar wache) && (!m.schreibbar wache) && (!m.ausfuehrbar wache)

/-- Entry stack is readable and writable for one word below the top. -/
def stapelRW (z : EintrittZustand) : Bool :=
  let top := eintrittRsp z
  let basis := top - BitVec.ofNat 64 8
  lesbar8 z.zustand.speicher basis && schreibbar8 z.zustand.speicher basis

/-- Entry address is a listed machine entry of the image. -/
def eintragGelisted (bild : Bild) (rip : Nat) : Bool :=
  bild.eintraege.contains rip

/-- The checked entry predicate: well-formed image, listed entry, loaded
    executable byte at RIP, aligned readable/writable stack, guard where
    promised, MXCSR save where XMM is touched, IF per kind. Admission as
    `Bool`, never a hardware fault. -/
def eintrittOk (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand) : Bool :=
  wohlgeformt p bild &&
  eintragGelisted bild z.zustand.rip.toNat &&
  ladenAusfuehrbar bild bias z.zustand.rip.toNat &&
  stapelOk z && stapelRW z &&
  guardOk art z && mxcsrOk z && ifOk art z

/-- External transfer target: admitted only at a listed entry in an
    executable section. Anything else is a validator refusal. -/
def externZielOk (bild : Bild) (bias : Nat) (ziel : Nat) : Bool :=
  eintragGelisted bild ziel && eintragEnthalten bias bild.abschnitte ziel

/-- Manifest row without validated save/restore bytes admits nothing:
    trap return needs the named save sequence present as checked bytes. -/
def trapRueckOk (gesichertBytes : Bool) (art : EintrittArt)
    (z : EintrittZustand) : Bool :=
  gesichertBytes && ifOk art z && mxcsrOk z

/-- Kernel behaviour is named only: the child's defined register shape
    after the clone trampoline is a named assumption, never derived here. -/
inductive KernAntwort where
  | kindLauf : KernAntwort
  | unbekannt : KernAntwort
  deriving DecidableEq, Repr

/-- Witness stack top: 16-aligned. -/
def zeugenStapelTop : Adresse := BitVec.ofNat 64 0x8000

/-- Witness stack word base: one word below the top. -/
def zeugenStapelBasis : Adresse := zeugenStapelTop - BitVec.ofNat 64 8

/-- Witness guard probe address: outside image and stack. -/
def zeugenWache : Adresse := BitVec.ofNat 64 0x6000

/-- Witness memory: loaded image permissions plus a readable/writable
    stack window `[0x7000, 0x8000)`; stack never executable. -/
def zeugenSpeicherE : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0
    lesbar := fun a =>
      decide (0x7000 ≤ a.toNat ∧ a.toNat < 0x8000) ||
        ladenLesbar zeugenBild 0 a.toNat
    schreibbar := fun a =>
      decide (0x7000 ≤ a.toNat ∧ a.toNat < 0x8000) ||
        ladenSchreibbar zeugenBild 0 a.toNat
    ausfuehrbar := fun a => ladenAusfuehrbar zeugenBild 0 a.toNat }

/-- Witness flags: all clear, auxiliary undefined. -/
def zeugenFlagsE : Flags :=
  { cf := false, pf := false, af := none, zf := false,
    sf := false, of := false }

/-- Witness machine state: RIP at the listed code entry, RSP at the
    aligned top, memory is the loaded-image-plus-stack window. -/
def zeugenZustandE : Zustand :=
  { register := fun r => if r == Register.rsp then zeugenStapelTop
      else BitVec.ofNat 64 0
    flags := zeugenFlagsE
    rip := BitVec.ofNat 64 0x1000
    speicher := zeugenSpeicherE }

/-- Witness entry state for hosted main: no XMM touched, IF set,
    guard finding true. -/
def zeugenEintrittHosted : EintrittZustand :=
  { zustand := zeugenZustandE
    mxcsr := 0x1F80
    xmmBeruehrt := false
    mxcsrGesichert := false
    ifBit := true
    guardOk := true }

/-- ACCEPTANCE: the hosted-main predicate holds on the concrete loaded
    image prefix with an aligned readable/writable stack. -/
theorem zeugenEintrittHosted_ok :
    eintrittOk .p48 zeugenBild 0 .hostedMain zeugenEintrittHosted = true := by
  decide

/-- The witness stack word below the top is readable. -/
theorem zeugenStapel_lesbar :
    lesbar8 zeugenSpeicherE zeugenStapelBasis = true := by
  decide

/-- The witness stack word below the top is writable. -/
theorem zeugenStapel_schreibbar :
    schreibbar8 zeugenSpeicherE zeugenStapelBasis = true := by
  decide

/-- The witness guard probe is unmapped. -/
theorem zeugenWache_ok :
    schutzSeiteOk zeugenSpeicherE zeugenWache = true := by
  decide

/-- JOINT WITNESS: accepted entry plus a nonzero stack write that reads
    back and observably changes the byte. -/
theorem eintritt_zeuge :
    eintrittOk .p48 zeugenBild 0 .hostedMain zeugenEintrittHosted = true ∧
    ∃ (m m' : Speicher) (a : Adresse) (v : Wort),
      v ≠ 0 ∧ write64 m a v = some m' ∧ read64 m' a = some v ∧
        m.bytes a ≠ m'.bytes a := by
  have hwr : write64 zeugenSpeicherE zeugenStapelBasis 42 =
      some { zeugenSpeicherE with bytes := writeBytes zeugenSpeicherE zeugenStapelBasis 42 } := by
    unfold write64
    rw [if_pos zeugenStapel_schreibbar]
  refine ⟨zeugenEintrittHosted_ok, zeugenSpeicherE, _,
    zeugenStapelBasis, 42,
    by decide, hwr,
    read64_nach_write64 _ _ _ _ hwr zeugenStapel_lesbar, ?_⟩
  have hhit := writeBytesN_hit zeugenSpeicherE
    zeugenStapelBasis 42 8 0 (by decide) (by decide)
  rw [addrOff_null] at hhit
  show BitVec.ofNat 8 0 ≠
    writeBytes zeugenSpeicherE zeugenStapelBasis 42 zeugenStapelBasis
  unfold writeBytes
  rw [hhit]
  decide

/-- MXCSR DISCIPLINE: touching XMM without a validated save is refused,
    whatever the word is. Uses both the touch and the missing save. -/
theorem mxcsr_verweigert_ohne_sicherung (z : EintrittZustand)
    (ht : z.xmmBeruehrt = true) (hs : z.mxcsrGesichert = false) :
    mxcsrOk z = false := by
  unfold mxcsrOk
  rw [ht, hs]
  simp

/-- GUARD DISCIPLINE: a promised guard page with a missing finding is
    refused. Uses the promise and the missing finding. -/
theorem guard_verweigert_ohne_seite (art : EintrittArt) (z : EintrittZustand)
    (hp : guardErforderlich art = true) (hg : z.guardOk = false) :
    guardOk art z = false := by
  unfold guardOk
  rw [hp, hg]
  simp

/-- IF DISCIPLINE: a bit that misses the kind's expectation is refused.
    Uses the mismatch. -/
theorem if_verweigert_bei_abweichung (art : EintrittArt) (z : EintrittZustand)
    (h : z.ifBit ≠ ifErwartet art) :
    ifOk art z = false := by
  unfold ifOk
  rw [decide_eq_false h]

/-- An entry touching XMM without a save is refused at the predicate.
    Uses the touch, the missing save and the component refusal. -/
theorem eintritt_verweigert_mxcsr (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand)
    (ht : z.xmmBeruehrt = true) (hs : z.mxcsrGesichert = false) :
    eintrittOk p bild bias art z = false := by
  have h := mxcsr_verweigert_ohne_sicherung z ht hs
  unfold eintrittOk
  rw [h]
  simp

/-- An entry with a promised but missing guard page is refused.
    Uses the promise and the missing finding. -/
theorem eintritt_verweigert_guard (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand)
    (hp : guardErforderlich art = true) (hg : z.guardOk = false) :
    eintrittOk p bild bias art z = false := by
  have h := guard_verweigert_ohne_seite art z hp hg
  unfold eintrittOk
  rw [h]
  simp

/-- An entry with the wrong IF bit is refused. Uses the mismatch. -/
theorem eintritt_verweigert_if (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand)
    (h : z.ifBit ≠ ifErwartet art) :
    eintrittOk p bild bias art z = false := by
  have hi := if_verweigert_bei_abweichung art z h
  unfold eintrittOk
  rw [hi]
  simp

/-- A manifest row without validated save/restore bytes admits no trap
    return. Uses the missing bytes. -/
theorem trapRueck_verweigert_ohne_bytes (art : EintrittArt)
    (z : EintrittZustand) (h : gesichertBytes = false) :
    trapRueckOk gesichertBytes art z = false := by
  unfold trapRueckOk
  rw [h]
  simp

/-- An unlisted transfer target is refused. Uses the missing listing. -/
theorem externZiel_verweigert_unlisted (bild : Bild) (bias : Nat)
    (ziel : Nat) (h : eintragGelisted bild ziel = false) :
    externZielOk bild bias ziel = false := by
  unfold externZielOk
  rw [h]
  simp

/-- Concrete XMM-touching state without a validated save. -/
def zeugenEintrittXmmOhneSave : EintrittZustand :=
  { zustand := zeugenZustandE
    mxcsr := 0x1F80
    xmmBeruehrt := true
    mxcsrGesichert := false
    ifBit := true
    guardOk := true }

/-- REFUSAL: touching XMM the entry uses without a save admits nothing. -/
theorem zeugenXmm_verweigert :
    eintrittOk .p48 zeugenBild 0 .hostedMain zeugenEintrittXmmOhneSave
      = false := by
  decide

/-- Concrete thread-root state with the promised guard finding present. -/
def zeugenEintrittFaden : EintrittZustand :=
  { zustand := zeugenZustandE
    mxcsr := 0x1F80
    xmmBeruehrt := false
    mxcsrGesichert := false
    ifBit := true
    guardOk := true }

/-- ACCEPTANCE: the thread-root predicate holds where the promised guard
    page is found unmapped. -/
theorem zeugenEintrittFaden_ok :
    eintrittOk .p48 zeugenBild 0 .fadenWurzel zeugenEintrittFaden
      = true := by
  decide

/-- Concrete thread-root state with the promised guard page missing. -/
def zeugenEintrittFadenOhneGuard : EintrittZustand :=
  { zustand := zeugenZustandE
    mxcsr := 0x1F80
    xmmBeruehrt := false
    mxcsrGesichert := false
    ifBit := true
    guardOk := false }

/-- REFUSAL: a thread root without its promised guard page admits nothing. -/
theorem zeugenGuard_verweigert :
    eintrittOk .p48 zeugenBild 0 .fadenWurzel zeugenEintrittFadenOhneGuard
      = false := by
  decide

/-- REFUSAL: a transfer from outside the image to a non-entry is refused. -/
theorem zeugenExtern_verweigert :
    externZielOk zeugenBild 0 0x5000 = false := by
  decide

/-- REFUSAL: a manifest row without validated save/restore bytes admits
    no trap return. -/
theorem zeugenTrapManifest_verweigert :
    trapRueckOk false .trapRueck zeugenEintrittHosted = false := by
  decide

/-- Concrete hosted state with the wrong IF bit. -/
def zeugenEintrittFalschIF : EintrittZustand :=
  { zustand := zeugenZustandE
    mxcsr := 0x1F80
    xmmBeruehrt := false
    mxcsrGesichert := false
    ifBit := false
    guardOk := true }

/-- REFUSAL: a hosted entry with interrupts disabled at handoff admits
    nothing. -/
theorem zeugenIF_verweigert :
    eintrittOk .p48 zeugenBild 0 .hostedMain zeugenEintrittFalschIF
      = false := by
  decide

/-- Concrete nolibc state: `anfang` handoff done, IF set, no guard owed. -/
def zeugenEintrittNolibc : EintrittZustand :=
  { zustand := zeugenZustandE
    mxcsr := 0x1F80
    xmmBeruehrt := false
    mxcsrGesichert := false
    ifBit := true
    guardOk := false }

/-- ACCEPTANCE: nolibc handoff holds without a guard promise. -/
theorem zeugenEintrittNolibc_ok :
    eintrittOk .p48 zeugenBild 0 .nolibcMain zeugenEintrittNolibc
      = true := by
  decide

/-- Concrete module-init state. -/
def zeugenEintrittModul : EintrittZustand :=
  { zustand := zeugenZustandE
    mxcsr := 0x1F80
    xmmBeruehrt := false
    mxcsrGesichert := false
    ifBit := true
    guardOk := false }

/-- ACCEPTANCE: module init holds on the listed entry. -/
theorem zeugenEintrittModul_ok :
    eintrittOk .p48 zeugenBild 0 .modulInit zeugenEintrittModul
      = true := by
  decide

/-- Concrete bare-metal start state: IF clear, no guard owed here. -/
def zeugenEintrittMetall : EintrittZustand :=
  { zustand := zeugenZustandE
    mxcsr := 0x1F80
    xmmBeruehrt := false
    mxcsrGesichert := false
    ifBit := false
    guardOk := false }

/-- ACCEPTANCE: bare-metal `_start` holds with IF clear. -/
theorem zeugenEintrittMetall_ok :
    eintrittOk .p48 zeugenBild 0 .metallStart zeugenEintrittMetall
      = true := by
  decide

/-- Concrete clone-child trampoline state: guard found, IF set. -/
def zeugenEintrittKlon : EintrittZustand :=
  { zustand := zeugenZustandE
    mxcsr := 0x1F80
    xmmBeruehrt := false
    mxcsrGesichert := false
    ifBit := true
    guardOk := true }

/-- ACCEPTANCE: the clone-child trampoline state holds; kernel register
    behaviour behind it stays a named assumption (`KernAntwort`). -/
theorem zeugenEintrittKlon_ok :
    eintrittOk .p48 zeugenBild 0 .klonKind zeugenEintrittKlon
      = true := by
  decide

/-- ACCEPTANCE: a trap return with validated save bytes and IF clear. -/
theorem zeugenTrapRueck_ok :
    trapRueckOk true .trapRueck zeugenEintrittMetall = true := by
  decide

/-- A misaligned stack poisons the whole entry predicate. Uses the check. -/
theorem eintritt_verweigert_stapel (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand)
    (h : stapelOk z = false) :
    eintrittOk p bild bias art z = false := by
  unfold eintrittOk
  rw [h]
  simp

/-- An unlisted RIP poisons the whole entry predicate. Uses the check. -/
theorem eintritt_verweigert_unlisted (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand)
    (h : eintragGelisted bild z.zustand.rip.toNat = false) :
    eintrittOk p bild bias art z = false := by
  unfold eintrittOk
  rw [h]
  simp

/-- Misaligned witness top. -/
def zeugenStapelTopSchief : Adresse := BitVec.ofNat 64 0x8001

/-- Misaligned witness machine state. -/
def zeugenZustandSchief : Zustand :=
  { register := fun r => if r == Register.rsp then zeugenStapelTopSchief
      else BitVec.ofNat 64 0
    flags := zeugenFlagsE
    rip := BitVec.ofNat 64 0x1000
    speicher := zeugenSpeicherE }

/-- Misaligned witness entry state. -/
def zeugenEintrittSchief : EintrittZustand :=
  { zustand := zeugenZustandSchief
    mxcsr := 0x1F80
    xmmBeruehrt := false
    mxcsrGesichert := false
    ifBit := true
    guardOk := true }

/-- REFUSAL: a call-boundary stack that is not 16-aligned admits nothing. -/
theorem zeugenStapelSchief_verweigert :
    eintrittOk .p48 zeugenBild 0 .hostedMain zeugenEintrittSchief
      = false := by
  decide

/-- Witness machine state with an unlisted RIP. -/
def zeugenZustandFremd : Zustand :=
  { register := fun r => if r == Register.rsp then zeugenStapelTop
      else BitVec.ofNat 64 0
    flags := zeugenFlagsE
    rip := BitVec.ofNat 64 0x5000
    speicher := zeugenSpeicherE }

/-- Witness entry state with an unlisted RIP. -/
def zeugenEintrittFremd : EintrittZustand :=
  { zustand := zeugenZustandFremd
    mxcsr := 0x1F80
    xmmBeruehrt := false
    mxcsrGesichert := false
    ifBit := true
    guardOk := true }

/-- REFUSAL: an RIP that is no listed entry admits no entry. -/
theorem zeugenRipFremd_verweigert :
    eintrittOk .p48 zeugenBild 0 .hostedMain zeugenEintrittFremd
      = false := by
  decide

/-- ACCEPTANCE: module exit holds on the listed entry. -/
theorem zeugenEintrittModulExit_ok :
    eintrittOk .p48 zeugenBild 0 .modulExit zeugenEintrittModul
      = true := by
  decide

/- CUTS:
  - Guard is a single-probe check (`schutzSeiteOk` at one address), not a
    full 4096-byte sweep; the full sweep is OPEN.
  - Stack discipline covers one word below the top plus 16-alignment;
    whole-frame extents, red-zone rules and per-CPU stacks are OPEN.
  - `mxcsrGesichert`/`guardOk`/`gesichertBytes` are validator findings as
    `Bool`, not validated save/restore byte sequences; the XMM register
    file itself is not modelled here.
  - Kernel behaviour behind the clone trampoline is named only
    (`KernAntwort`); nothing is derived about it. Trap return and kernel
    premises qualify no image alone: `trapRueckOk` refuses without
    validated bytes, and a manifest row alone admits nothing.
  - No decoder: decoded instruction starts, control-flow target coverage,
    indirect-target certificates and patched-site re-decoding are OPEN
    (validator skeleton C5 owns them).
  - Refusal `Bool`s are validator/profile admission, never a hardware
    fault claim. Actual x86 permits many unaligned ordinary accesses;
    16-alignment is imposed only as the declared call-boundary contract
    at entries, and every refusal keeps the certified scalar path (the
    predicate refuses the entry, it does not fault hardware).
  - Out of scope here and OPEN: narrow 8/16/32 value/flag discipline,
    DIV/IDIV guard/fault-channel correspondence, float width/control/NaN
    observability, LOCK cost/cycle bounds, per-byte TSO atomicity/RMW
    correspondence, foreign-buffer drains, gate/OS software behaviour
    (user logic, never an assumption), source correspondence, TSO bridge,
    cost/budget transfer, and full final-byte/source/hardware closure.
  - Consumer interface: the shared IR (lane 287) is pending; nothing here
    invents a substitute IR or executor.
-/

#print axioms ifErwartet
#print axioms guardErforderlich
#print axioms zeugenEintrittHosted_ok
#print axioms zeugenStapel_lesbar
#print axioms zeugenStapel_schreibbar
#print axioms zeugenWache_ok
#print axioms eintritt_zeuge
#print axioms mxcsr_verweigert_ohne_sicherung
#print axioms guard_verweigert_ohne_seite
#print axioms if_verweigert_bei_abweichung
#print axioms eintritt_verweigert_mxcsr
#print axioms eintritt_verweigert_guard
#print axioms eintritt_verweigert_if
#print axioms trapRueck_verweigert_ohne_bytes
#print axioms externZiel_verweigert_unlisted
#print axioms zeugenXmm_verweigert
#print axioms zeugenEintrittFaden_ok
#print axioms zeugenGuard_verweigert
#print axioms zeugenExtern_verweigert
#print axioms zeugenTrapManifest_verweigert
#print axioms zeugenIF_verweigert
#print axioms zeugenEintrittNolibc_ok
#print axioms zeugenEintrittModul_ok
#print axioms zeugenEintrittMetall_ok
#print axioms zeugenEintrittKlon_ok
#print axioms zeugenTrapRueck_ok
#print axioms eintritt_verweigert_stapel
#print axioms eintritt_verweigert_unlisted
#print axioms zeugenStapelSchief_verweigert
#print axioms zeugenRipFremd_verweigert
#print axioms zeugenEintrittModulExit_ok

end Gabbro.Grammatik.X86
