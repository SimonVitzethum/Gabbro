/-
  File:      Grammatik/X86/MulDiv.lean
  Subject:   64-bit MUL/IMUL/DIV/IDIV as an extension of the one pilot semantics.

  Lane 336 (wave A2): helpers over the REAL canonical `Wort` (BitVec 64),
  the REAL `Zustand`/`Register`/`Flags` from `Grammatik/X86/Typen.lean`,
  the REAL `regSet`/`ripNach`/`laengeOk` step shapes from
  `Grammatik/X86/Ausfuehrung.lean` (no duplicated evaluator of the 14
  pilot forms), the REAL word products/quotients and flag-validity
  relations from `Grammatik/X86/Ganzzahl.lean` (no competing mul/div
  redefinition), and the REAL `sint` from `Grammatik/X86/FlagBeweis.lean`.
  New here: the 128-bit RDX:RAX dividend with its defined-when checks
  (divisor zero and quotient overflow both trap), the four new operation
  forms with their register-state transitions, the decided admission
  guard, and the never-pure policy for trapping operations.

  No source correspondence is claimed here; the bridge (lane 277) must
  still preserve source range and fault semantics.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ganzzahl
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.FlagBeweis

namespace Gabbro.Grammatik.X86

/-- The four new operation forms: one-operand MUL (RDX:RAX), two-operand
    IMUL (truncated into `dst`), DIV and IDIV over the RDX:RAX dividend.
    Wiring these into `Befehl`/`schritt`/decoder bytes awaits the Typen
    owner; this type exposes exactly how the one target semantics grows. -/
inductive MulDivBefehl where
  | mulRax (src : Register)
  | imul2 (dst src : Register)
  | divRax (src : Register)
  | idivRax (src : Register)
  deriving DecidableEq, Repr

/-- Unsigned value of the 128-bit RDX:RAX dividend. -/
def u128 (hoch tief : Wort) : Nat := hoch.toNat * 2 ^ 64 + tief.toNat

/-- Signed value of the 128-bit RDX:RAX dividend: the high word is the
    signed high half, the low word the unsigned low half. -/
def s128 (hoch tief : Wort) : Int := hoch.toInt * 2 ^ 64 + tief.toNat

/-! ## 1. Wide division with defined-when checks.

    Real DIV divides the 128-bit RDX:RAX dividend and traps (#DE) when
    the divisor is zero OR the quotient does not fit 64 bits. Real IDIV
    does the same over the signed dividend with truncation toward zero
    (never SAR floor: `-7 / 2 = -3`, remainder `-1`). Both traps map to
    the `hardware` stop class the source `FortschrittG` already names;
    the guard/fault/channel/order correspondence itself stays OPEN. -/

/-- Unsigned wide division: `none` exactly on divisor zero or a quotient
    that needs more than 64 bits. Results are `(quotient, remainder)`. -/
def divWeitU (hoch tief teiler : Wort) : Option (Wort × Wort) :=
  let dn := teiler.toNat
  if dn = 0 then none
  else
    let q := u128 hoch tief / dn
    let r := u128 hoch tief % dn
    if q < 2 ^ 64 then some (BitVec.ofNat 64 q, BitVec.ofNat 64 r)
    else none

/-- Signed wide division: `none` on divisor zero or a quotient outside
    the signed 64-bit range. Truncation toward zero via `tdiv`/`tmod`,
    wrapped exactly like `divS` in `Ganzzahl.lean`. -/
def divWeitS (hoch tief teiler : Wort) : Option (Wort × Wort) :=
  let yn := sVal .b64 teiler
  if yn = 0 then none
  else
    let q := (s128 hoch tief).tdiv yn
    let r := (s128 hoch tief).tmod yn
    if -(((2 ^ 63 : Nat) : Int)) ≤ q ∧ q < (((2 ^ 63 : Nat) : Int)) then
      some (BitVec.ofNat 64 (q.emod ((2 ^ 64 : Nat) : Int)).toNat,
        BitVec.ofNat 64 (r.emod ((2 ^ 64 : Nat) : Int)).toNat)
    else none

/-- Unsigned wide division refuses on divisor zero. -/
theorem divWeitU_verweigert_bei_null (hoch tief teiler : Wort)
    (h : teiler.toNat = 0) : divWeitU hoch tief teiler = none := by
  simp [divWeitU, h]

/-- Unsigned wide division refuses when the quotient needs 65 bits. -/
theorem divWeitU_verweigert_bei_ueberlauf (hoch tief teiler : Wort)
    (hpos : teiler.toNat ≠ 0)
    (hgross : ¬ u128 hoch tief / teiler.toNat < 2 ^ 64) :
    divWeitU hoch tief teiler = none := by
  simp [divWeitU, hpos, hgross]

/-- Unsigned wide division answers when the divisor is nonzero and the
    quotient fits 64 bits. -/
theorem divWeitU_antwortet (hoch tief teiler : Wort)
    (hpos : teiler.toNat ≠ 0)
    (hfit : u128 hoch tief / teiler.toNat < 2 ^ 64) :
    ∃ q r, divWeitU hoch tief teiler = some (q, r) := by
  simp [divWeitU, hpos, hfit]

/-- Signed wide division refuses on divisor zero. -/
theorem divWeitS_verweigert_bei_null (hoch tief teiler : Wort)
    (h : sVal .b64 teiler = 0) : divWeitS hoch tief teiler = none := by
  simp [divWeitS, h]

/-- Signed wide division refuses when the truncated quotient is below
    the signed 64-bit range. -/
theorem divWeitS_verweigert_bei_unten (hoch tief teiler : Wort)
    (hpos : sVal .b64 teiler ≠ 0)
    (hklein : (s128 hoch tief).tdiv (sVal .b64 teiler) < -(((2 ^ 63 : Nat) : Int))) :
    divWeitS hoch tief teiler = none := by
  simp [divWeitS, hpos]
  omega

/-- Signed wide division refuses when the truncated quotient is above
    the signed 64-bit range. -/
theorem divWeitS_verweigert_bei_oben (hoch tief teiler : Wort)
    (hpos : sVal .b64 teiler ≠ 0)
    (hgross : (((2 ^ 63 : Nat) : Int)) ≤ (s128 hoch tief).tdiv (sVal .b64 teiler)) :
    divWeitS hoch tief teiler = none := by
  simp [divWeitS, hpos]
  omega

/-! ## 2. MUL/IMUL flag snapshots: defined bits pinned, the rest kept.

    MUL sets CF = OF = unsigned carry; IMUL sets CF = OF = signed
    carry; SF/ZF/PF/AF are architecturally UNDEFINED for both. `Flags`
    stores all but AF as `Bool`, so following `Ganzzahl.lean` the
    snapshots pin exactly the defined bits (AF `none`) and KEEP the
    incoming SF/ZF/PF: preservation is an explicit modelling choice for
    undefined bits, not hardware truth. Each snapshot is proved to
    satisfy the corresponding `Ganzzahl` validity relation. DIV/IDIV
    leave every flag undefined and preserve the whole snapshot (§3). -/

/-- Unsigned MUL flag snapshot over incoming flags. -/
def mulFlagsU (f : Flags) (x y : Wort) : Flags :=
  { f with cf := mulTragU .b64 x y, of := mulTragU .b64 x y, af := none }

/-- Signed MUL (IMUL) flag snapshot over incoming flags. -/
def mulFlagsS (f : Flags) (x y : Wort) : Flags :=
  { f with cf := mulTragS .b64 x y, of := mulTragS .b64 x y, af := none }

/-- The unsigned snapshot satisfies the unsigned MUL validity relation. -/
theorem mulFlagsU_gueltig (f : Flags) (x y : Wort) :
    MulGueltigU .b64 x y (mulFlagsU f x y) := by
  simp [mulFlagsU, MulGueltigU]

/-- The signed snapshot satisfies the signed MUL validity relation. -/
theorem mulFlagsS_gueltig (f : Flags) (x y : Wort) :
    MulGueltigS .b64 x y (mulFlagsS f x y) := by
  simp [mulFlagsS, MulGueltigS]

/-! ## 3. The step extension: how the one target semantics grows.

    `mulDivSchritt` handles ONLY the four new forms above, reusing the
    canonical `laengeOk`/`ripNach`/`regSet` shapes and the §1/§2
    helpers. The 14 pilot `schritt` forms are untouched and never
    re-evaluated here. Outcomes: `ok` (architectural successor),
    `hardwareHalt` (the divide-error trap: divisor zero or quotient
    overflow, i.e. the `hardware` stop class), `misslungen` (bad decode
    length, mirroring `schritt`'s `none`). Wiring into `Befehl`,
    `schritt`, the decoder and the image stays OPEN with the Typen
    owner; the DIV/IDIV-to-`hardware` correspondence itself is OPEN. -/

/-- Decoded new-form instruction: operation plus checked length data. -/
structure MulDivDecodiert where
  befehl : MulDivBefehl
  laenge : Nat
  deriving DecidableEq, Repr

/-- Step outcome: successor, hardware trap, or decode refusal. -/
inductive MulDivErgebnis where
  | ok (nach : Zustand)
  | hardwareHalt
  | misslungen

/-- Single new-form step; the divide check is never folded away. -/
def mulDivSchritt (d : MulDivDecodiert) (s : Zustand) : MulDivErgebnis :=
  match laengeOk d.laenge with
  | false => .misslungen
  | true =>
    let nach := ripNach s.rip d.laenge
    match d.befehl with
    | .mulRax src =>
      let a := s.register Register.rax
      let v := s.register src
      .ok { s with register := regSet (regSet s.register Register.rax (mulLow .b64 a v)) Register.rdx (mulHighU .b64 a v), rip := nach, flags := mulFlagsU s.flags a v }
    | .imul2 dst src =>
      let a := s.register dst
      let v := s.register src
      .ok { s with register := regSet s.register dst (mulLow .b64 a v), rip := nach, flags := mulFlagsS s.flags a v }
    | .divRax src =>
      match divWeitU (s.register Register.rdx) (s.register Register.rax) (s.register src) with
      | some (q, r) =>
        .ok { s with register := regSet (regSet s.register Register.rax q) Register.rdx r, rip := nach }
      | none => .hardwareHalt
    | .idivRax src =>
      match divWeitS (s.register Register.rdx) (s.register Register.rax) (s.register src) with
      | some (q, r) =>
        .ok { s with register := regSet (regSet s.register Register.rax q) Register.rdx r, rip := ripNach s.rip d.laenge }
      | none => .hardwareHalt

/-! ## Step equations for the four new forms.

    Each equation pins the full successor or the trap; every premise is
    used. The divide check stays in the step: a `none` quotient is a
    `hardwareHalt`, never a folded-away value. -/

/-- `mulRax`: RDX:RAX holds the full unsigned product with the unsigned
    flag snapshot. -/
theorem md_mul_erfolg (d : MulDivDecodiert) (s : Zustand) (src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .mulRax src) :
    mulDivSchritt d s = .ok { s with register := regSet (regSet s.register Register.rax (mulLow .b64 (s.register Register.rax) (s.register src))) Register.rdx (mulHighU .b64 (s.register Register.rax) (s.register src)), rip := ripNach s.rip d.laenge, flags := mulFlagsU s.flags (s.register Register.rax) (s.register src) } := by
  unfold mulDivSchritt
  rw [hok, h]

/-- `imul2`: the destination holds the truncated product with the signed
    flag snapshot. -/
theorem md_imul_erfolg (d : MulDivDecodiert) (s : Zustand) (dst src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .imul2 dst src) :
    mulDivSchritt d s = .ok { s with register := regSet s.register dst (mulLow .b64 (s.register dst) (s.register src)), rip := ripNach s.rip d.laenge, flags := mulFlagsS s.flags (s.register dst) (s.register src) } := by
  unfold mulDivSchritt
  rw [hok, h]

/-- `divRax` success: RAX holds the quotient, RDX the remainder, flags
    preserved (all DIV flags are undefined). -/
theorem md_div_erfolg (d : MulDivDecodiert) (s : Zustand) (src : Register)
    (q r : Wort) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .divRax src)
    (hqr : divWeitU (s.register Register.rdx) (s.register Register.rax) (s.register src) = some (q, r)) :
    mulDivSchritt d s = .ok { s with register := regSet (regSet s.register Register.rax q) Register.rdx r, rip := ripNach s.rip d.laenge } := by
  unfold mulDivSchritt
  simp [hok, h, hqr]

/-- `divRax` trap: an undefined quotient is a hardware halt, never a
    value. -/
theorem md_div_halt (d : MulDivDecodiert) (s : Zustand) (src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .divRax src)
    (hqr : divWeitU (s.register Register.rdx) (s.register Register.rax) (s.register src) = none) :
    mulDivSchritt d s = .hardwareHalt := by
  unfold mulDivSchritt
  simp [hok, h, hqr]

/-- `idivRax` success: truncated quotient and remainder, flags kept. -/
theorem md_idiv_erfolg (d : MulDivDecodiert) (s : Zustand) (src : Register)
    (q r : Wort) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .idivRax src)
    (hqr : divWeitS (s.register Register.rdx) (s.register Register.rax) (s.register src) = some (q, r)) :
    mulDivSchritt d s = .ok { s with register := regSet (regSet s.register Register.rax q) Register.rdx r, rip := ripNach s.rip d.laenge } := by
  unfold mulDivSchritt
  simp [hok, h, hqr]

/-- `idivRax` trap: divisor zero or quotient overflow halts. -/
theorem md_idiv_halt (d : MulDivDecodiert) (s : Zustand) (src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .idivRax src)
    (hqr : divWeitS (s.register Register.rdx) (s.register Register.rax) (s.register src) = none) :
    mulDivSchritt d s = .hardwareHalt := by
  unfold mulDivSchritt
  simp [hok, h, hqr]

/-- A bad decode length refuses every new form, unconditionally. -/
theorem md_laenge_misslungen (d : MulDivDecodiert) (s : Zustand)
    (h : laengeOk d.laenge = false) : mulDivSchritt d s = .misslungen := by
  unfold mulDivSchritt
  simp [h]

/-! ## 4. Decided admission guard and the never-pure policy.

    `zugelassen` is validator admission (a `Bool`), NOT an invented
    hardware fault: a refused image is refused, never executed. The
    guard mirrors the step's own divide check, so refusal and trap
    agree. `rein` marks operations without any trap; trapping
    operations are never pure, hence never available for dead-code
    removal or motion across guards. -/

/-- Decided admission: DIV/IDIV exactly when their quotient is defined;
    MUL/IMUL always (they cannot trap). -/
def zugelassen (b : MulDivBefehl) (s : Zustand) : Bool :=
  match b with
  | .mulRax _ => true
  | .imul2 _ _ => true
  | .divRax src =>
    (divWeitU (s.register Register.rdx) (s.register Register.rax) (s.register src)).isSome
  | .idivRax src =>
    (divWeitS (s.register Register.rdx) (s.register Register.rax) (s.register src)).isSome

/-- Purity for motion/DCE: only the non-trapping multiplies qualify. -/
def rein : MulDivBefehl → Bool
  | .mulRax _ => true
  | .imul2 _ _ => true
  | .divRax _ => false
  | .idivRax _ => false

/-- The guard reads the wide quotient option for DIV. -/
theorem zugelassen_div_heisst (src : Register) (s : Zustand) :
    zugelassen (.divRax src) s =
      (divWeitU (s.register Register.rdx) (s.register Register.rax) (s.register src)).isSome := by
  rfl

/-- The guard reads the wide quotient option for IDIV. -/
theorem zugelassen_idiv_heisst (src : Register) (s : Zustand) :
    zugelassen (.idivRax src) s =
      (divWeitS (s.register Register.rdx) (s.register Register.rax) (s.register src)).isSome := by
  rfl

/-- A zero divisor is refused by the decided guard. -/
theorem zugelassen_verweigert_nullteiler (src : Register) (s : Zustand)
    (h : (s.register src).toNat = 0) :
    zugelassen (.divRax src) s = false := by
  rw [zugelassen_div_heisst]
  have hnone : divWeitU (s.register Register.rdx) (s.register Register.rax) (s.register src) = none :=
    divWeitU_verweigert_bei_null _ _ _ h
  rw [hnone]
  rfl

/-- A refused DIV image traps in the step: guard and trap agree. -/
theorem verweigert_heisst_halt (d : MulDivDecodiert) (s : Zustand)
    (src : Register) (h : d.befehl = .divRax src)
    (hok : laengeOk d.laenge = true)
    (hzu : zugelassen (.divRax src) s = false) :
    mulDivSchritt d s = .hardwareHalt := by
  have hnone : divWeitU (s.register Register.rdx) (s.register Register.rax) (s.register src) = none := by
    cases hopt : divWeitU (s.register Register.rdx) (s.register Register.rax) (s.register src) with
    | some qr =>
      rw [zugelassen_div_heisst] at hzu
      simp [hopt] at hzu
    | none => rfl
  exact md_div_halt d s src hok h hnone

/-- Trapping operations are never pure: DIV and IDIV fail `rein`. -/
theorem falle_nie_rein (b : MulDivBefehl) (src : Register)
    (h : b = .divRax src ∨ b = .idivRax src) : rein b = false := by
  cases h with
  | inl hdiv => subst hdiv; rfl
  | inr hidiv => subst hidiv; rfl

/-- Pure operations never trap: MUL steps are never a hardware halt. -/
theorem rein_ohne_halt_mul (d : MulDivDecodiert) (s : Zustand) (src : Register)
    (h : d.befehl = .mulRax src) (z : MulDivErgebnis)
    (hstep : mulDivSchritt d s = z) : z ≠ .hardwareHalt := by
  have hok : laengeOk d.laenge = true ∨ laengeOk d.laenge = false := by
    cases hlen : laengeOk d.laenge with
    | true => exact Or.inl rfl
    | false => exact Or.inr rfl
  cases hok with
  | inl htrue =>
    rw [md_mul_erfolg d s src htrue h] at hstep
    subst z
    intro hcon
    cases hcon
  | inr hfalse =>
    rw [md_laenge_misslungen d s hfalse] at hstep
    subst z
    intro hcon
    cases hcon

/-! ## 5. Joint witnesses: computed values through real steps and memory.

    All probes reuse the canonical witness memory/flags from
    `Speicher.lean`/`Ausfuehrung.lean`. Step results are projected to
    plain values before `decide` (states contain functions, so full
    state equality is not decidable); the general equations of §3/§4
    already pin the full states. -/

/-- Witness registers for MUL: RAX holds 6, RCX holds 7. -/
def mdRegMul : Register → Wort := fun q =>
  if q = Register.rax then 6
  else if q = Register.rcx then 7
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness state for MUL `6 * 7`. -/
def mdZustandMul : Zustand :=
  { register := mdRegMul, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := zeugeSpeicher }

/-- Witness registers for DIV: RDX:RAX holds 17, RCX holds 5. -/
def mdRegDiv : Register → Wort := fun q =>
  if q = Register.rax then 17
  else if q = Register.rdx then 0
  else if q = Register.rcx then 5
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness state for DIV `17 / 5`. -/
def mdZustandDiv : Zustand :=
  { register := mdRegDiv, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := zeugeSpeicher }

/-- Witness registers with a zero divisor in RCX. -/
def mdRegNull : Register → Wort := fun q =>
  if q = Register.rax then 17
  else if q = Register.rdx then 0
  else if q = Register.rcx then 0
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness state with divisor zero. -/
def mdZustandNull : Zustand :=
  { register := mdRegNull, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := zeugeSpeicher }

/-- Step projection: RAX, RDX and CF of an `ok` outcome. -/
def okWerte : MulDivErgebnis → Option (Wort × Wort × Bool)
  | .ok z => some (z.register Register.rax, z.register Register.rdx, z.flags.cf)
  | _ => none

/-- Step projection: whether the outcome is the hardware halt. -/
def istHalt : MulDivErgebnis → Bool
  | .hardwareHalt => true
  | _ => false

/-- MUL step probe: `6 * 7` lands RAX = 42, RDX = 0, CF clear. -/
theorem probe_mul_schritt :
    okWerte (mulDivSchritt ⟨.mulRax .rcx, 3⟩ mdZustandMul) =
      some (42, 0, false) := by
  decide

/-- DIV step probe: `17 / 5` lands RAX = 3, RDX = 2, flags kept. -/
theorem probe_div_schritt :
    okWerte (mulDivSchritt ⟨.divRax .rcx, 3⟩ mdZustandDiv) =
      some (3, 2, false) := by
  decide

/-- DIV trap probe: a zero divisor halts the step. -/
theorem probe_div_halt_schritt :
    istHalt (mulDivSchritt ⟨.divRax .rcx, 3⟩ mdZustandNull) = true := by
  decide

/-- Guard probe: the zero-divisor image is refused by the decided guard. -/
theorem probe_guard_null :
    zugelassen (.divRax .rcx) mdZustandNull = false := by
  decide

/-- Wide unsigned division answers `17 / 5 = 3` remainder `2`. -/
theorem probe_div_weit : divWeitU 0 17 5 = some (3, 2) := by
  decide

/-- Wide unsigned division refuses divisor zero. -/
theorem probe_div_weit_null : divWeitU 0 17 0 = none := by
  decide

/-- Wide unsigned division refuses the 65-bit quotient `2^64 / 1`. -/
theorem probe_div_weit_ueberlauf : divWeitU 1 0 1 = none := by
  decide

/-- Wide signed division truncates: `-7 / 2 = -3` remainder `-1`
    (never SAR floor, which would give `-4` remainder `1`). -/
theorem probe_idiv_rumpf :
    divWeitS 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFF9 2 =
      some (0xFFFFFFFFFFFFFFFD, 0xFFFFFFFFFFFFFFFF) := by
  decide

/-- Wide signed division refuses `INT_MIN / -1` (quotient overflow). -/
theorem probe_idiv_min :
    divWeitS 0xFFFFFFFFFFFFFFFF 0x8000000000000000 0xFFFFFFFFFFFFFFFF =
      none := by
  decide

/-! ## 6. Memory witness: quotient and remainder go through real memory.

    The non-trivial quotient `3` and remainder `2` of `17 / 5` are
    stored through the canonical permission-checked `write64` at
    adjacent footprints and read back through `read64`; the first store
    observably changes memory. This keeps the wide division executable
    against real byte memory. -/

/-- The witness memory after storing the quotient `3` at address zero. -/
def mdSpeicherNachQ : Speicher :=
  { zeugenSpeicher with bytes := writeBytes zeugenSpeicher 0 3 }

/-- The witness memory after also storing the remainder `2` at address 8. -/
def mdSpeicherNachR : Speicher :=
  { mdSpeicherNachQ with bytes := writeBytes mdSpeicherNachQ 8 2 }

/-- A computed quotient/remainder pair goes through memory and the
    quotient store observably changes it. -/
theorem muldiv_speicher_sonde :
    divWeitU 0 17 5 = some (3, 2) ∧
    ∃ m1 m2 : Speicher,
      write64 zeugenSpeicher 0 3 = some m1 ∧
      read64 m1 0 = some 3 ∧
      zeugenSpeicher.bytes 0 ≠ m1.bytes 0 ∧
      write64 m1 8 2 = some m2 ∧
      read64 m2 8 = some 2 := by
  refine ⟨by decide, mdSpeicherNachQ, mdSpeicherNachR, ?_, ?_, ?_, ?_, ?_⟩
  · have hwr1 : write64 zeugenSpeicher 0 3 = some mdSpeicherNachQ := by
      unfold write64
      have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
      rw [if_pos hc]
      rfl
    exact hwr1
  · have hwr1 : write64 zeugenSpeicher 0 3 = some mdSpeicherNachQ := by
      unfold write64
      have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
      rw [if_pos hc]
      rfl
    have hrd : lesbar8 zeugenSpeicher 0 = true := rfl
    exact read64_nach_write64 zeugenSpeicher _ 0 3 hwr1 hrd
  · have hhit := writeBytesN_hit zeugenSpeicher 0 3
      8 0 (by decide) (by decide)
    rw [addrOff_null (0 : Adresse)] at hhit
    show BitVec.ofNat 8 0 ≠ writeBytes zeugenSpeicher 0 3 0
    unfold writeBytes
    rw [hhit]
    decide
  · have hwr2 : write64 mdSpeicherNachQ 8 2 = some mdSpeicherNachR := by
      unfold write64
      have hc : schreibbar8 mdSpeicherNachQ 8 = true := rfl
      rw [if_pos hc]
      rfl
    exact hwr2
  · have hwr2 : write64 mdSpeicherNachQ 8 2 = some mdSpeicherNachR := by
      unfold write64
      have hc : schreibbar8 mdSpeicherNachQ 8 = true := rfl
      rw [if_pos hc]
      rfl
    have hrd : lesbar8 mdSpeicherNachQ 8 = true := rfl
    exact read64_nach_write64 mdSpeicherNachQ _ 8 2 hwr2 hrd

/- CUTS:
   - No instruction encoding or decoding: nothing here claims which
     bytes encode MUL/IMUL/DIV/IDIV; Codec owns that, and wiring the four
     new forms into `Befehl`/`schritt`/decoder/image stays OPEN with the
     Typen owner. `MulDivDecodiert.laenge` is checked input data (1..15).
   - No source correspondence: `passtU`/`passtS`-style range transfer,
     source lowering, duty reuse and the DIV/IDIV-to-`hardware` stop
     guard/fault/channel/order correspondence stay OPEN (bridge lane 277).
     `hardwareHalt` NAMES the stop class; it does not prove the mapping.
   - No cost transfer: MUL/IMUL/DIV/IDIV latency or throughput, CAS-style
     retry (not applicable here) and budget simulation are not modelled.
   - No TSO/concurrency bridge: all facts are sequential over one word
     or one `Speicher`; aligned multi-byte atomicity, tearing and the GX
     refinement stay with the TSO lane.
   - No hardware verification: the quotient-overflow rule, the CF/OF
     carry rules, the truncation direction and the flag-validity
     relations are STATED executable semantics, not verified against
     silicon; the even-parity reading of PF is inherited from Wort.lean.
   - Undefined MUL/IMUL SF/ZF/PF bits are preserved from the incoming
     snapshot as an explicit modelling choice (proved to satisfy the
     `Ganzzahl` validity relations); DIV/IDIV preserve all flags.
   - This file adds no new source-language construct or checker rule:
     no diagnostic, poison-probe, example or CLI numbers are taken.
-/

#print axioms u128
#print axioms s128
#print axioms divWeitU
#print axioms divWeitS
#print axioms divWeitU_verweigert_bei_null
#print axioms divWeitU_verweigert_bei_ueberlauf
#print axioms divWeitU_antwortet
#print axioms divWeitS_verweigert_bei_null
#print axioms divWeitS_verweigert_bei_unten
#print axioms divWeitS_verweigert_bei_oben
#print axioms mulFlagsU_gueltig
#print axioms mulFlagsS_gueltig
#print axioms mulDivSchritt
#print axioms md_mul_erfolg
#print axioms md_imul_erfolg
#print axioms md_div_erfolg
#print axioms md_div_halt
#print axioms md_idiv_erfolg
#print axioms md_idiv_halt
#print axioms md_laenge_misslungen
#print axioms zugelassen_div_heisst
#print axioms zugelassen_idiv_heisst
#print axioms zugelassen_verweigert_nullteiler
#print axioms verweigert_heisst_halt
#print axioms falle_nie_rein
#print axioms rein_ohne_halt_mul
#print axioms probe_mul_schritt
#print axioms probe_div_schritt
#print axioms probe_div_halt_schritt
#print axioms probe_guard_null
#print axioms probe_div_weit
#print axioms probe_div_weit_null
#print axioms probe_div_weit_ueberlauf
#print axioms probe_idiv_rumpf
#print axioms probe_idiv_min
#print axioms muldiv_speicher_sonde

end Gabbro.Grammatik.X86
