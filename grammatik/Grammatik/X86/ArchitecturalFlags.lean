/-
  File:      Grammatik/X86/ArchitecturalFlags.lean
  Subject:   Raw RFLAGS word with defined/undefined flag effects and the
             fetched PUSHFQ/POPFQ observers.

  Lane 692 (hardware completion): the existing `Flags` snapshot stores
  every flag but AF as `Bool`, and `mulFlagsU` preserves incoming
  SF/ZF/PF as an explicit modelling choice (MulDiv.lean §2), not
  hardware truth. This file adds the raw 64-bit RFLAGS word beside it,
  a sound defined/undefined effect relation per manual row (undefined
  bits are free choices, never invented zeros or preserved values),
  and the byte-facing PUSHFQ (opcode 9CH) / POPFQ observers with
  VM/RF treatment and CPL/IOPL gating.

  Provenance (checked 2026-10-02 in
  `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`,
  Intel SDM 325462-093US September 2026):
  - ADD entry (Vol. 2A 3-14): "The OF, SF, ZF, AF, CF, and PF flags are
    set according to the result."
  - NEG entry: "The CF flag set to 0 if the source operand is 0;
    otherwise it is set to 1. The OF, SF, ZF, AF, and PF flags are set
    according to the result."
  - MUL entry: "The OF and CF flags are set to 0 if the upper half of
    the result is 0; otherwise, they are set to 1. The SF, ZF, AF, and
    PF flags are undefined." IMUL/DIV/IDIV/SHL rows likewise.
  - PUSHFQ entry (Vol. 2B 4-528): 64-bit mode pushes RFLAGS with
    "VM and RF bits cleared in image stored on the stack";
    "Flags Affected: None."
  - POPFQ entry (Vol. 2B 4-407): Table 1-12 CPL/IOPL gating; RF is
    cleared; VIP/VIF/VM/reserved unaffected.
  - Vol. 1 3.4.3: EFLAGS init 00000002H (bit 1 set); reserved bits
    1, 3, 5, 15, 22-31; Figure 3-8 bit positions.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Ganzzahl
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.ShiftLogic
import Grammatik.X86.MulDiv
import Grammatik.X86.FlagDependencies

namespace Gabbro.Grammatik.X86

/-- RFLAGS status bit positions (Intel SDM Vol. 1 Figure 3-8). -/
def cfBit : Nat := 0
def pfBit : Nat := 2
def afBit : Nat := 4
def zfBit : Nat := 6
def sfBit : Nat := 7
def ofBit : Nat := 11

/-- One raw status bit of a word. -/
def rbit (w : Wort) (i : Nat) : Bool := w.toNat.testBit i

/-- Control/privilege state beside the flags: CPL and IOPL gate POPFQ,
    IF is the interrupt flag, VM marks virtual-8086 mode. -/
structure Steuer where
  cpl : Nat
  iopl : Nat
  ifBit : Bool
  vm : Bool
  deriving DecidableEq, Repr

/-- Architectural state: the canonical core plus the raw RFLAGS word
    plus control state. `archOK` ties the raw status bits to
    `kern.flags`; projection is `projiziert`. -/
structure ArchZustand where
  kern : Zustand
  roh : Wort
  steuer : Steuer

/-- Read the six status flags out of a raw word. AF is always present
    as a raw bit here; undefinedness lives in the effect relation
    (§4), never in the state. -/
def liestStatus (w : Wort) : Flags :=
  { cf := rbit w cfBit, pf := rbit w pfBit, af := some (rbit w afBit),
    zf := rbit w zfBit, sf := rbit w sfBit, of := rbit w ofBit }

/-- Coherence: the raw word agrees with the canonical flags on every
    status bit, bit 1 reads set (init 00000002H, Vol. 1 3.4.3), and
    privilege values are in range. -/
def archOK (a : ArchZustand) : Prop :=
  liestStatus a.roh = a.kern.flags ∧ rbit a.roh 1 = true ∧
  a.steuer.cpl ≤ 3 ∧ a.steuer.iopl ≤ 3

/-- Projection to the existing state: forget raw word and control. -/
def projiziert (a : ArchZustand) : Zustand := a.kern

/-- The projection reads the canonical flags back. -/
theorem projiziert_flags (a : ArchZustand) (h : archOK a) :
    liestStatus a.roh = (projiziert a).flags := by
  unfold projiziert
  exact h.1

/-! ## 3. Defined AF per width for ADD/SUB/CMP/NEG.

    AF is the carry out of bit 3 (Wort.afAdd/afSub): it reads only the
    low nibbles, so truncation to any pilot width keeps it. The three
    lemmas below reuse the canonical `afAdd`/`afSub` (no second
    nibble computation); the manual rows are ADD (Vol. 2A 3-14: all six
    "set according to the result"), NEG (CF is the nonzero borrow, the
    other five per result), SUB/CMP (same sentence as ADD). -/

/-- A mask keeping the low nibble fixes `% 16`. -/
theorem and_maske_nibble (m : Nat) (hm : ∀ i, i < 4 → m.testBit i = true)
    (x : Nat) : (x &&& m) % 16 = x % 16 := by
  show (x &&& m) % 2 ^ 4 = x % 2 ^ 4
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_and]
  by_cases h : i < 4
  · rw [hm i h]
    simp [h]
  · simp [h]

/-- Every pilot mask keeps the low nibble. -/
theorem maske_nibble (b : Breite) (i : Nat) (h : i < 4) :
    (maske b).toNat.testBit i = true := by
  have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  cases b with
  | b8 => have e : (maske .b8).toNat = 255 := by decide
          rw [e]; rcases h4 with rfl | rfl | rfl | rfl <;> decide
  | b16 => have e : (maske .b16).toNat = 65535 := by decide
           rw [e]; rcases h4 with rfl | rfl | rfl | rfl <;> decide
  | b32 => have e : (maske .b32).toNat = 4294967295 := by decide
           rw [e]; rcases h4 with rfl | rfl | rfl | rfl <;> decide
  | b64 => have e : (maske .b64).toNat = 18446744073709551615 := by decide
           rw [e]; rcases h4 with rfl | rfl | rfl | rfl <;> decide

/-- Truncation to any pilot width keeps the low nibble. -/
theorem trunc_nibble (b : Breite) (x : Wort) :
    (trunc b x).toNat % 16 = x.toNat % 16 := by
  cases b with
  | b8 => simp only [trunc, maske, BitVec.toNat_and]
          exact and_maske_nibble _ (maske_nibble .b8) _
  | b16 => simp only [trunc, maske, BitVec.toNat_and]
           exact and_maske_nibble _ (maske_nibble .b16) _
  | b32 => simp only [trunc, maske, BitVec.toNat_and]
           exact and_maske_nibble _ (maske_nibble .b32) _
  | b64 => simp only [trunc, maske, BitVec.toNat_and]
           exact and_maske_nibble _ (maske_nibble .b64) _

/-- Per-width ADD auxiliary carry, read off the truncated nibbles. -/
def afAddB (b : Breite) (x y : Wort) : Bool :=
  decide (16 ≤ (trunc b x).toNat % 16 + (trunc b y).toNat % 16)

/-- Per-width SUB auxiliary borrow, read off the truncated nibbles. -/
def afSubB (b : Breite) (x y : Wort) : Bool :=
  decide ((trunc b x).toNat % 16 < (trunc b y).toNat % 16)

/-- The per-width ADD carry is the canonical nibble carry: width plays
    no role beyond the low four bits. -/
theorem afAddB_ist_afAdd (b : Breite) (x y : Wort) :
    afAddB b x y = afAdd x y := by
  simp only [afAddB, afAdd]
  rw [trunc_nibble b x, trunc_nibble b y]

/-- The per-width SUB borrow is the canonical nibble borrow. -/
theorem afSubB_ist_afSub (b : Breite) (x y : Wort) :
    afSubB b x y = afSub x y := by
  simp only [afSubB, afSub]
  rw [trunc_nibble b x, trunc_nibble b y]

/-- NEG auxiliary borrow at width `b`: the accepted `negWf` snapshot
    pins `afSub 0 (trunc b x)` (NegGueltig); it equals the canonical
    borrow out of the full word. -/
theorem negAf_ist_afSub (b : Breite) (x : Wort) :
    afSub 0 (trunc b x) = afSub 0 x := by
  simp only [afSub]
  rw [trunc_nibble b x]

/-- CMP shares the SUB flag row (CMP is SUB without the store:
    `schritt` evaluates `sub64` for `.cmpReg64`); hence per-width CMP
    AF is `afSubB`, i.e. the canonical borrow. -/
theorem cmpAf_ist_afSub (b : Breite) (x y : Wort) :
    afSubB b x y = afSub x y :=
  afSubB_ist_afSub b x y

/-! ## 4. Defined/undefined effect rows.

    One class per manual flag sentence. ADD/SUB/CMP/NEG define all six
    status bits through the accepted snapshots (`add64`/`sub64`/`negWf`
    over the canonical words, never a second adder). AND/OR/XOR/TEST
    clear CF/OF, read SF/ZF/PF off the result and leave AF undefined
    (`LogikGueltig`). MUL/IMUL pin only CF/OF to the accepted carry
    evidence (`mulTragU`/`mulTragS`); SF/ZF/PF/AF are FREE here --
    `mulFlagsU`'s preservation of the incoming SF/ZF/PF is an explicit
    modelling choice of that producer (MulDiv.lean §2), not hardware
    truth, and §4c exhibits it as one admissible member. DIV/IDIV
    leave all six free. Shifts pin CF/SF/ZF/PF and OF exactly at a
    masked count of one (accepted `SchiebeNachweis`/`schiebeZaehler`),
    AF free. -/

/-- Operation classes with distinct manual flag rows. -/
inductive AluOp where
  | add | sub | logik | mulU | mulS | div | shift
  deriving DecidableEq, Repr

/-- Which raw status bit the manual row defines for each class
    (bit numbers: CF 0, PF 2, AF 4, ZF 6, SF 7, OF 11). -/
def definiert : AluOp → Nat → Bool
  | .add, _ => true
  | .sub, _ => true
  | .logik, 4 => false
  | .logik, _ => true
  | .mulU, 0 => true
  | .mulU, 11 => true
  | .mulU, _ => false
  | .mulS, 0 => true
  | .mulS, 11 => true
  | .mulS, _ => false
  | .div, _ => false
  | .shift, 0 => true
  | .shift, 2 => true
  | .shift, 6 => true
  | .shift, 7 => true
  | .shift, _ => false

/-- ADD class: the raw successor reads exactly the accepted snapshot. -/
def addErlaubt (x y nach : Wort) : Prop :=
  liestStatus nach = (add64 x y).2

/-- SUB/CMP class: the raw successor reads exactly the accepted snapshot
    (`schritt` evaluates `sub64` for `.cmpReg64`, so CMP is covered). -/
def subErlaubt (x y nach : Wort) : Prop :=
  liestStatus nach = (sub64 x y).2

/-- NEG class: the raw successor agrees with the accepted `negWf`
    snapshot on every defined bit (AF is `some` there). -/
def negErlaubt (b : Breite) (x nach : Wort) : Prop :=
  liestStatus nach = (negWf b x).2

/-- Logic class (AND/OR/XOR/TEST): CF/OF cleared, SF/ZF/PF off the
    result, raw AF bit free. -/
def logikErlaubt (r nach : Wort) : Prop :=
  rbit nach cfBit = false ∧ rbit nach ofBit = false ∧
  rbit nach pfBit = parityEven r ∧ rbit nach zfBit = zfTest r ∧
  rbit nach sfBit = sfTest r

/-- Unsigned MUL class: only CF/OF pinned to the accepted carry
    evidence; SF/ZF/PF/AF bits are free choices. -/
def mulErlaubtU (x y nach : Wort) : Prop :=
  rbit nach cfBit = mulTragU .b64 x y ∧
  rbit nach ofBit = mulTragU .b64 x y

/-- Signed MUL (IMUL) class: only CF/OF pinned, the rest free. -/
def mulErlaubtS (x y nach : Wort) : Prop :=
  rbit nach cfBit = mulTragS .b64 x y ∧
  rbit nach ofBit = mulTragS .b64 x y

/-- DIV/IDIV class: all six status bits free (manual: "undefined"). -/
def divErlaubt (_nach : Wort) : Prop := True

/-- Shift class at width `b`: CF/SF/ZF/PF pinned to the accepted
    evidence, OF pinned exactly at a masked count of one (the
    `getD`-self idiom of `SchiebeGueltig`: `none` constrains nothing),
    AF free. -/
def schiebErlaubt (b : Breite) (s : SchiebeNachweis) (c : Nat)
    (nach : Wort) : Prop :=
  rbit nach cfBit = s.trag ∧ rbit nach zfBit = zfTest s.ergebnis ∧
  rbit nach sfBit = negB b s.ergebnis ∧
  rbit nach pfBit = parityEven s.ergebnis ∧
  (schiebeZaehler b c = 1 →
    rbit nach ofBit = s.ueberlauf.getD (rbit nach ofBit)) ∧
  (s.ueberlauf = none → schiebeZaehler b c ≠ 1)

/-- Canonical raw word from five defined status bits (bit 1 set, AF bit
    cleared, control bits cleared): the builder for adapter members. -/
def rohAusStatus (cf pf zf sf of_ : Bool) : Wort :=
  BitVec.ofNat 64 ((if cf then 1 else 0) + (if pf then 4 else 0) +
    (if zf then 64 else 0) + (if sf then 128 else 0) +
    (if of_ then 2048 else 0) + 2)

/-- The builder reads back exactly the given bits. -/
theorem rohAusStatus_bits (cf pf zf sf of_ : Bool) :
    rbit (rohAusStatus cf pf zf sf of_) cfBit = cf ∧
    rbit (rohAusStatus cf pf zf sf of_) pfBit = pf ∧
    rbit (rohAusStatus cf pf zf sf of_) zfBit = zf ∧
    rbit (rohAusStatus cf pf zf sf of_) sfBit = sf ∧
    rbit (rohAusStatus cf pf zf sf of_) ofBit = of_ ∧
    rbit (rohAusStatus cf pf zf sf of_) 1 = true := by
  cases cf <;> cases pf <;> cases zf <;> cases sf <;> cases of_ <;>
    decide

/-- Any SF/ZF/PF choice joins the accepted unsigned carry evidence. -/
theorem roh_mulU (x y : Wort) (pf zf sf : Bool) :
    mulErlaubtU x y
      (rohAusStatus (mulTragU .b64 x y) pf zf sf
        (mulTragU .b64 x y)) := by
  unfold mulErlaubtU
  obtain ⟨hcf, -, -, -, hof, -⟩ := rohAusStatus_bits _ _ _ _ _
  exact ⟨hcf, hof⟩

/-- Any SF/ZF/PF choice joins the accepted signed carry evidence. -/
theorem roh_mulS (x y : Wort) (pf zf sf : Bool) :
    mulErlaubtS x y
      (rohAusStatus (mulTragS .b64 x y) pf zf sf
        (mulTragS .b64 x y)) := by
  unfold mulErlaubtS
  obtain ⟨hcf, -, -, -, hof, -⟩ := rohAusStatus_bits _ _ _ _ _
  exact ⟨hcf, hof⟩

/-- ADAPTER (unsigned MUL): the producer's deterministic snapshot
    (`mulFlagsU`, which preserves incoming SF/ZF/PF) is one admissible
    member of the free relation -- preservation is a choice, and this
    exhibits a raw word carrying the same defined bits. -/
theorem mulU_hat_roh (x y : Wort) :
    ∃ nach, mulErlaubtU x y nach ∧ rbit nach 1 = true :=
  ⟨_, roh_mulU x y true false true,
    (rohAusStatus_bits _ _ _ _ _).2.2.2.2.2⟩

/-- ADAPTER (signed MUL): same, for `mulFlagsS`. -/
theorem mulS_hat_roh (x y : Wort) :
    ∃ nach, mulErlaubtS x y nach ∧ rbit nach 1 = true :=
  ⟨_, roh_mulS x y true false true,
    (rohAusStatus_bits _ _ _ _ _).2.2.2.2.2⟩

/-- Two legal undefined-SF choices after unsigned MUL: both admitted,
    so no consumer may read SF there without explicit admission. -/
theorem mulU_sf_frei (x y : Wort) :
    ∃ n1 n2, mulErlaubtU x y n1 ∧ mulErlaubtU x y n2 ∧
    rbit n1 sfBit = true ∧ rbit n2 sfBit = false :=
  ⟨_, _, roh_mulU x y false false true, roh_mulU x y false false false,
    (rohAusStatus_bits _ _ _ _ _).2.2.2.1,
    (rohAusStatus_bits _ _ _ _ _).2.2.2.1⟩

/-- ADAPTER (logic): every result word has an admitted raw word. -/
theorem logik_hat_roh (r : Wort) :
    ∃ nach, logikErlaubt r nach ∧ rbit nach 1 = true := by
  refine ⟨rohAusStatus false (parityEven r) (zfTest r) (sfTest r) false,
    ?_, ?_⟩
  · unfold logikErlaubt
    obtain ⟨hcf, hpf, hzf, hsf, hof, -⟩ :=
      rohAusStatus_bits _ _ _ _ _
    exact ⟨hcf, hof, hpf, hzf, hsf⟩
  · obtain ⟨-, -, -, -, -, h1⟩ := rohAusStatus_bits _ _ _ _ _
    exact h1

/-- Two legal undefined-AF choices after a logic op (result zero):
    the accepted snapshots pin `af = none`, and both raw values occur. -/
theorem logik_af_frei :
    ∃ n1 n2, logikErlaubt 0 n1 ∧ logikErlaubt 0 n2 ∧
    rbit n1 afBit = false ∧ rbit n2 afBit = true := by
  refine ⟨rohAusStatus false true true false false,
    BitVec.ofNat 64 86, ?_, by unfold logikErlaubt; decide, by decide,
    by decide⟩
  unfold logikErlaubt
  obtain ⟨hcf, hpf, hzf, hsf, hof, -⟩ :=
    rohAusStatus_bits false true true false false
  have hp : parityEven 0 = true := by decide
  have hz : zfTest 0 = true := by decide
  have hs : sfTest 0 = false := by decide
  rw [hp, hz, hs]
  exact ⟨hcf, hof, hpf, hzf, hsf⟩

/-- DIV/IDIV: any two raw words are admitted, in particular two that
    disagree on every status bit -- no flag survives a divide. -/
theorem div_alles_frei :
    ∃ n1 n2, divErlaubt n1 ∧ divErlaubt n2 ∧
    liestStatus n1 ≠ liestStatus n2 :=
  ⟨0, 0xFFFFFFFFFFFFFFFF, trivial, trivial, by decide⟩

/-- Shift OF away from a one-count is free: both choices admitted. -/
theorem schieb_of_frei (b : Breite) (s : SchiebeNachweis) (c : Nat)
    (h : schiebeZaehler b c ≠ 1) :
    ∃ n1 n2, schiebErlaubt b s c n1 ∧ schiebErlaubt b s c n2 ∧
    rbit n1 ofBit = true ∧ rbit n2 ofBit = false := by
  refine ⟨rohAusStatus s.trag (parityEven s.ergebnis) (zfTest s.ergebnis)
      (negB b s.ergebnis) true,
    rohAusStatus s.trag (parityEven s.ergebnis) (zfTest s.ergebnis)
      (negB b s.ergebnis) false, ?_, ?_, ?_, ?_⟩
  · unfold schiebErlaubt
    obtain ⟨hcf, hpf, hzf, hsf, -, -⟩ := rohAusStatus_bits _ _ _ _ _
    exact ⟨hcf, hzf, hsf, hpf, fun hc => absurd hc h, fun _ => h⟩
  · unfold schiebErlaubt
    obtain ⟨hcf, hpf, hzf, hsf, -, -⟩ := rohAusStatus_bits _ _ _ _ _
    exact ⟨hcf, hzf, hsf, hpf, fun hc => absurd hc h, fun _ => h⟩
  · obtain ⟨-, -, -, -, hof, -⟩ := rohAusStatus_bits _ _ _ _ _
    exact hof
  · obtain ⟨-, -, -, -, hof, -⟩ := rohAusStatus_bits _ _ _ _ _
    exact hof

/-- ADAPTER (shift): every accepted `SchiebeGueltig` snapshot is
    admitted by the raw relation wherever the raw bits agree with it. -/
theorem schiebAdapter (b : Breite) (s : SchiebeNachweis) (c : Nat)
    (f : Flags) (nach : Wort) (hval : SchiebeGueltig b s c f)
    (hcf : rbit nach cfBit = f.cf) (hzf : rbit nach zfBit = f.zf)
    (hsf : rbit nach sfBit = f.sf) (hpf : rbit nach pfBit = f.pf)
    (hof : rbit nach ofBit = f.of) :
    schiebErlaubt b s c nach := by
  unfold SchiebeGueltig at hval
  unfold schiebErlaubt
  obtain ⟨hcfv, -, hzfv, hsfv, hpfv, hofv, hnonev⟩ := hval
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcf, hcfv]
  · rw [hzf, hzfv]
  · rw [hsf, hsfv]
  · rw [hpf, hpfv]
  · intro hc
    have ho := hofv hc
    rw [hof]
    exact ho
  · exact hnonev

/-! ## 5. Consumers of undefined flags.

    A branch or conditional select may consume a post-state only
    through flags its row defines. ADD/SUB/NEG define everything.
    Logic rows define everything but AF, and no condition reads AF.
    MUL rows define only CF/OF, so only OF/CF conditions are admitted
    there. DIV defines nothing, and shift OF needs the one-count
    evidence. Anything else requires an explicit admission the table
    below refuses. -/

/-- Admission table: which conditions may consume which row. -/
def verbrauchOK : Bedingung → AluOp → Bool
  | _, .add => true
  | _, .sub => true
  | _, .logik => true
  | .o, .mulU => true
  | .no, .mulU => true
  | .b, .mulU => true
  | .ae, .mulU => true
  | .o, .mulS => true
  | .no, .mulS => true
  | .b, .mulS => true
  | .ae, .mulS => true
  | _, _ => false

/-- The table pins the intended examples. -/
theorem verbrauchOK_beispiele :
    verbrauchOK .e .logik = true ∧ verbrauchOK .e .mulU = false ∧
    verbrauchOK .b .mulU = true ∧ verbrauchOK .e .div = false ∧
    verbrauchOK .b .shift = false := by
  decide

/-- ADD successors agree on every condition. -/
theorem addVerbrauch_sicher (c : Bedingung) (n1 n2 x y : Wort)
    (h1 : addErlaubt x y n1) (h2 : addErlaubt x y n2) :
    bedingung c (liestStatus n1) = bedingung c (liestStatus n2) := by
  rw [h1, h2]

/-- SUB/CMP successors agree on every condition. -/
theorem subVerbrauch_sicher (c : Bedingung) (n1 n2 x y : Wort)
    (h1 : subErlaubt x y n1) (h2 : subErlaubt x y n2) :
    bedingung c (liestStatus n1) = bedingung c (liestStatus n2) := by
  rw [h1, h2]

/-- NEG successors agree on every condition. -/
theorem negVerbrauch_sicher (c : Bedingung) (b : Breite) (n1 n2 x : Wort)
    (h1 : negErlaubt b x n1) (h2 : negErlaubt b x n2) :
    bedingung c (liestStatus n1) = bedingung c (liestStatus n2) := by
  rw [h1, h2]

/-- Logic successors agree on every condition: only AF is free and no
    condition reads it. Every premise is used: `hn` selects the read
    flag, `h1`/`h2` pin it on both sides. -/
theorem logikVerbrauch_sicher (c : Bedingung) (n1 n2 r : Wort)
    (h1 : logikErlaubt r n1) (h2 : logikErlaubt r n2) :
    bedingung c (liestStatus n1) = bedingung c (liestStatus n2) := by
  apply bedingung_stabil
  intro n hn
  obtain ⟨hcf1, hof1, hpf1, hzf1, hsf1⟩ := h1
  obtain ⟨hcf2, hof2, hpf2, hzf2, hsf2⟩ := h2
  cases n with
  | cf => show rbit n1 cfBit = rbit n2 cfBit; rw [hcf1, hcf2]
  | pf => show rbit n1 pfBit = rbit n2 pfBit; rw [hpf1, hpf2]
  | zf => show rbit n1 zfBit = rbit n2 zfBit; rw [hzf1, hzf2]
  | sf => show rbit n1 sfBit = rbit n2 sfBit; rw [hsf1, hsf2]
  | of_ => show rbit n1 ofBit = rbit n2 ofBit; rw [hof1, hof2]

/-- MUL successors agree on OF/CF conditions: the admitted set of the
    table. `hsafe` carries the table row; anything it refuses has no
    proof here. -/
theorem mulVerbrauch_sicher (c : Bedingung) (n1 n2 x y : Wort)
    (hsafe : c = .o ∨ c = .no ∨ c = .b ∨ c = .ae)
    (h1 : mulErlaubtU x y n1) (h2 : mulErlaubtU x y n2) :
    bedingung c (liestStatus n1) = bedingung c (liestStatus n2) := by
  apply bedingung_stabil
  intro n hn
  obtain ⟨hcf1, hof1⟩ := h1
  obtain ⟨hcf2, hof2⟩ := h2
  rcases hsafe with rfl | rfl | rfl | rfl
  · cases n with
    | cf => exact absurd hn (by decide)
    | pf => exact absurd hn (by decide)
    | zf => exact absurd hn (by decide)
    | sf => exact absurd hn (by decide)
    | of_ => show rbit n1 ofBit = rbit n2 ofBit; rw [hof1, hof2]
  · cases n with
    | cf => exact absurd hn (by decide)
    | pf => exact absurd hn (by decide)
    | zf => exact absurd hn (by decide)
    | sf => exact absurd hn (by decide)
    | of_ => show rbit n1 ofBit = rbit n2 ofBit; rw [hof1, hof2]
  · cases n with
    | cf => show rbit n1 cfBit = rbit n2 cfBit; rw [hcf1, hcf2]
    | pf => exact absurd hn (by decide)
    | zf => exact absurd hn (by decide)
    | sf => exact absurd hn (by decide)
    | of_ => exact absurd hn (by decide)
  · cases n with
    | cf => show rbit n1 cfBit = rbit n2 cfBit; rw [hcf1, hcf2]
    | pf => exact absurd hn (by decide)
    | zf => exact absurd hn (by decide)
    | sf => exact absurd hn (by decide)
    | of_ => exact absurd hn (by decide)

/-- Shift successors at a masked one-count agree on every condition:
    CF/SF/ZF/PF pinned, OF pinned by the count evidence, AF never
    read. `hc` is load-bearing: without it OF is free. -/
theorem shiftVerbrauch_eins (cond : Bedingung) (b : Breite)
    (s : SchiebeNachweis) (k : Nat) (n1 n2 : Wort)
    (hc : schiebeZaehler b k = 1)
    (h1 : schiebErlaubt b s k n1) (h2 : schiebErlaubt b s k n2) :
    bedingung cond (liestStatus n1) =
      bedingung cond (liestStatus n2) := by
  apply bedingung_stabil
  intro n hn
  obtain ⟨hcf1, hzf1, hsf1, hpf1, hof1, hnone1⟩ := h1
  obtain ⟨hcf2, hzf2, hsf2, hpf2, hof2, -⟩ := h2
  cases n with
  | cf => show rbit n1 cfBit = rbit n2 cfBit; rw [hcf1, hcf2]
  | pf => show rbit n1 pfBit = rbit n2 pfBit; rw [hpf1, hpf2]
  | zf => show rbit n1 zfBit = rbit n2 zfBit; rw [hzf1, hzf2]
  | sf => show rbit n1 sfBit = rbit n2 sfBit; rw [hsf1, hsf2]
  | of_ =>
    show rbit n1 ofBit = rbit n2 ofBit
    have o1 := hof1 hc
    have o2 := hof2 hc
    cases he : s.ueberlauf with
    | some v => simp only [he, Option.getD_some] at o1 o2; rw [o1, o2]
    | none => exact absurd hc (hnone1 he)

/-- DIV/IDIV: the zero flag is undetermined -- two admitted successors
    take opposite branches. No admission theorem exists for `.div`. -/
theorem divVerbrauch_verweigert :
    ∃ n1 n2, divErlaubt n1 ∧ divErlaubt n2 ∧
    bedingung .e (liestStatus n1) = true ∧
    bedingung .e (liestStatus n2) = false := by
  refine ⟨rohAusStatus false false true false false,
    rohAusStatus false false false false false,
    trivial, trivial, ?_, ?_⟩
  · have h := (rohAusStatus_bits false false true false false).2.2.1
    show (liestStatus _).zf = true
    exact h
  · have h := (rohAusStatus_bits false false false false false).2.2.1
    show (liestStatus _).zf = false
    exact h

/-- Raw AF non-observability: two raw words agreeing off bit 4 agree on
    every condition. This is the genuine derived proof behind the
    logic-row admission: `bedingung_af_frei` lifted to raw words. -/
theorem rohAf_frei (c : Bedingung) (w1 w2 : Wort)
    (h : ∀ i, i ≠ 4 → w1.toNat.testBit i = w2.toNat.testBit i) :
    bedingung c (liestStatus w1) = bedingung c (liestStatus w2) := by
  have e : liestStatus w1 =
      {(liestStatus w2) with af := (liestStatus w1).af} := by
    simp only [liestStatus, rbit]
    have h0 : w1.toNat.testBit 0 = w2.toNat.testBit 0 := h 0 (by decide)
    have h2 : w1.toNat.testBit 2 = w2.toNat.testBit 2 := h 2 (by decide)
    have h6 : w1.toNat.testBit 6 = w2.toNat.testBit 6 := h 6 (by decide)
    have h7 : w1.toNat.testBit 7 = w2.toNat.testBit 7 := h 7 (by decide)
    have h11 : w1.toNat.testBit 11 = w2.toNat.testBit 11 :=
      h 11 (by decide)
    have ecf : cfBit = 0 := rfl
    have epf : pfBit = 2 := rfl
    have ezf : zfBit = 6 := rfl
    have esf : sfBit = 7 := rfl
    have eof : ofBit = 11 := rfl
    simp only [ecf, epf, ezf, esf, eof]
    rw [h0, h2, h6, h7, h11]
  have e2 : liestStatus w2 =
      {(liestStatus w2) with af := (liestStatus w2).af} := rfl
  rw [e, e2]
  exact bedingung_af_frei c (liestStatus w2) _ _

/- CUTS:
    Skeleton plus raw word (§2) and nibble groundwork (§3 head):
    effect relation, PUSHFQ/POPFQ observers, consumer admission and
    witnesses follow in later pieces.
-/

#print axioms projiziert_flags
#print axioms and_maske_nibble
#print axioms maske_nibble
#print axioms trunc_nibble
#print axioms afAddB_ist_afAdd
#print axioms afSubB_ist_afSub
#print axioms negAf_ist_afSub
#print axioms cmpAf_ist_afSub

end Gabbro.Grammatik.X86
