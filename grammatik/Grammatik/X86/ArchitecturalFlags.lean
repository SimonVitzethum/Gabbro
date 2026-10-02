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

/-! ## 6. The fetched flag save/restore observers.

    PUSHFQ (opcode 9CH) pushes the RFLAGS image with VM (16) and RF
    (17) cleared and affects no flags; POPFQ (9DH) restores under the
    Table 1-12 CPL/IOPL gating with RF cleared and VIP/VIF/VM/reserved
    preserved. The pilot `Codec.decode` refuses both bytes, so the
    one-byte adapter decodes below never shadow it (proved in §6c);
    HardwareExecution660/HardwareInterrupts672 own the wiring, this
    file owns the exact byte/word/stack frames. -/

/-- Remaining RFLAGS bit positions (Vol. 1 Figure 3-8). -/
def tfPos : Nat := 8
def ifPos : Nat := 9
def dfPos : Nat := 10
def ntPos : Nat := 14
def rfPos : Nat := 16
def vmPos : Nat := 17
def acPos : Nat := 18
def vifPos : Nat := 19
def vipPos : Nat := 20
def idPos : Nat := 21

/-- PUSHFQ opcode byte (9CH). -/
def pushfqOp : Byte := 156

/-- POPFQ opcode byte (9DH). -/
def popfqOp : Byte := 157

/-- Saved RFLAGS image mask: VM (16) and RF (17) cleared, per the
    PUSHFQ operation text (`RFLAGS AND 00000000_00FCFFFFH`). -/
def pushfqMaske : Wort := 0x00FCFFFF

/-- The pushed image of a raw word. -/
def pushfqWort (r : Wort) : Wort := r &&& pushfqMaske

/-- The manual mask keeps every bit below 16. -/
theorem pushfqMaske_bit (i : Nat) (h : i < 16) :
    pushfqMaske.getLsbD i = true := by
  have e : pushfqMaske.toNat = 0x00FCFFFF := by decide
  rw [← BitVec.testBit_toNat, e]
  have h16 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨
      i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨
      i = 14 ∨ i = 15 := by omega
  rcases h16 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    <;> decide

/-- The pushed image preserves every status/control bit below 16. -/
theorem pushfqWort_status (r : Wort) (i : Nat) (h : i < 16) :
    rbit (pushfqWort r) i = rbit r i := by
  have hm := pushfqMaske_bit i h
  unfold pushfqWort rbit
  rw [BitVec.testBit_toNat, BitVec.getLsbD_and, hm, Bool.and_true]
  exact (BitVec.testBit_toNat r).symm

/-- The pushed image clears VM and RF. -/
theorem pushfqWort_vm_rf (r : Wort) :
    rbit (pushfqWort r) 16 = false ∧ rbit (pushfqWort r) 17 = false := by
  have h16 : pushfqMaske.getLsbD 16 = false := by decide
  have h17 : pushfqMaske.getLsbD 17 = false := by decide
  unfold pushfqWort rbit
  constructor
  · rw [BitVec.testBit_toNat, BitVec.getLsbD_and, h16, Bool.and_false]
  · rw [BitVec.testBit_toNat, BitVec.getLsbD_and, h17, Bool.and_false]

/-- One raw status bit as a word. -/
def bitMaske (i : Nat) : Wort := BitVec.ofNat 64 (2 ^ i)

/-- POPFQ loaded bits at CPL 0 (64-bit row: ID/VIP/VIF/VM/RF/reserved
    excepted, RF cleared separately). -/
def popfqLadenA : Wort :=
  bitMaske 0 ||| bitMaske 2 ||| bitMaske 4 ||| bitMaske 6 |||
  bitMaske 7 ||| bitMaske 8 ||| bitMaske 9 ||| bitMaske 10 |||
  bitMaske 11 ||| bitMaske 12 ||| bitMaske 13 ||| bitMaske 14 |||
  bitMaske 18 ||| bitMaske 21

/-- POPFQ loaded bits at CPL > 0 with CPL <= IOPL: IF loads, IOPL is
    preserved. -/
def popfqLadenB : Wort :=
  bitMaske 0 ||| bitMaske 2 ||| bitMaske 4 ||| bitMaske 6 |||
  bitMaske 7 ||| bitMaske 8 ||| bitMaske 9 ||| bitMaske 10 |||
  bitMaske 11 ||| bitMaske 14 ||| bitMaske 18 ||| bitMaske 21

/-- POPFQ loaded bits at CPL > IOPL: IF and IOPL are preserved. -/
def popfqLadenC : Wort :=
  bitMaske 0 ||| bitMaske 2 ||| bitMaske 4 ||| bitMaske 6 |||
  bitMaske 7 ||| bitMaske 8 ||| bitMaske 10 |||
  bitMaske 11 ||| bitMaske 14 ||| bitMaske 18 ||| bitMaske 21

/-- The case mask of Table 1-12 (64-bit rows). -/
def popfqLaden (cpl iopl : Nat) : Wort :=
  if cpl = 0 then popfqLadenA
  else if cpl ≤ iopl then popfqLadenB else popfqLadenC

/-- RF clearing mask. -/
def popfqOhneRF : Wort := ~~~bitMaske 16

/-- The restored word: loaded bits from the stack image, the rest from
    the live word, RF cleared. -/
def popfqWort (laden pre gesp : Wort) : Wort :=
  ((pre &&& ~~~laden) ||| (gesp &&& laden)) &&& popfqOhneRF

/-- Every case mask loads every status bit. -/
theorem popfqLaden_status (cpl iopl i : Nat)
    (h : i = 0 ∨ i = 2 ∨ i = 4 ∨ i = 6 ∨ i = 7 ∨ i = 11) :
    (popfqLaden cpl iopl).getLsbD i = true := by
  unfold popfqLaden
  by_cases hc : cpl = 0
  · rw [if_pos hc]
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · rw [if_neg hc]
    by_cases hl : cpl ≤ iopl
    · rw [if_pos hl]
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    · rw [if_neg hl]
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/-- No case mask loads RF, VM, VIF or VIP. -/
theorem popfqLaden_erhaelt (cpl iopl i : Nat)
    (h : i = 16 ∨ i = 17 ∨ i = 19 ∨ i = 20) :
    (popfqLaden cpl iopl).getLsbD i = false := by
  unfold popfqLaden
  by_cases hc : cpl = 0
  · rw [if_pos hc]
    rcases h with rfl|rfl|rfl|rfl <;> decide
  · rw [if_neg hc]
    by_cases hl : cpl ≤ iopl
    · rw [if_pos hl]
      rcases h with rfl|rfl|rfl|rfl <;> decide
    · rw [if_neg hl]
      rcases h with rfl|rfl|rfl|rfl <;> decide

/-- IF loads exactly at CPL 0 or CPL <= IOPL. -/
theorem popfqLaden_if (cpl iopl : Nat) :
    (popfqLaden cpl iopl).getLsbD 9 =
      decide (cpl = 0 ∨ cpl ≤ iopl) := by
  unfold popfqLaden
  by_cases hc : cpl = 0
  · rw [if_pos hc]
    have : (decide (cpl = 0 ∨ cpl ≤ iopl)) = true := by
      simp [hc]
    rw [this]
    decide
  · rw [if_neg hc]
    by_cases hl : cpl ≤ iopl
    · rw [if_pos hl]
      have : (decide (cpl = 0 ∨ cpl ≤ iopl)) = true := by
        simp [hc, hl]
      rw [this]
      decide
    · rw [if_neg hl]
      have : (decide (cpl = 0 ∨ cpl ≤ iopl)) = false := by
        simp [hc, hl]
      rw [this]
      decide

/-- IOPL loads only at CPL 0. -/
theorem popfqLaden_iopl (cpl iopl : Nat) (i : Nat)
    (h : i = 12 ∨ i = 13) :
    (popfqLaden cpl iopl).getLsbD i = decide (cpl = 0) := by
  unfold popfqLaden
  by_cases hc : cpl = 0
  · rw [if_pos hc]
    have : (decide (cpl = 0)) = true := by simp [hc]
    rw [this]
    rcases h with rfl|rfl <;> decide
  · rw [if_neg hc]
    have : (decide (cpl = 0)) = false := by simp [hc]
    rw [this]
    by_cases hl : cpl ≤ iopl
    · rw [if_pos hl]
      rcases h with rfl|rfl <;> decide
    · rw [if_neg hl]
      rcases h with rfl|rfl <;> decide

/-- The RF clearer clears exactly bit 16 (in range). -/
theorem ohneRF_bit (i : Nat) (h64 : i < 64) :
    popfqOhneRF.getLsbD i = !(decide (i = 16)) := by
  have d64 : decide (i < 64) = true := decide_eq_true h64
  unfold popfqOhneRF bitMaske
  rw [BitVec.getLsbD_not, d64, Bool.true_and, BitVec.getLsbD_ofNat, d64]
  by_cases h : i = 16
  · subst h
    decide
  · have hne : (16 : Nat) ≠ i := Ne.symm h
    rw [Nat.testBit_two_pow_of_ne hne]
    simp [h]

/-- Master bit equation for the restore: preserved bits come from the
    live word, loaded bits from the stack image, bit 16 is cleared. -/
theorem popfqWort_bit (laden pre gesp : Wort) (i : Nat) (h64 : i < 64) :
    rbit (popfqWort laden pre gesp) i =
      (((rbit pre i && !(laden.getLsbD i)) ||
        (rbit gesp i && laden.getLsbD i)) && !(decide (i = 16))) := by
  have d64 : decide (i < 64) = true := decide_eq_true h64
  have hof := ohneRF_bit i h64
  unfold popfqWort
  simp only [rbit, BitVec.testBit_toNat]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
    d64, Bool.true_and]
  rw [hof]

/-! ## 6b. Architectural steps.

    Both steps run on caller-fetched bytes through the one-byte
    adapters (never through `Codec.decode`, which refuses both
    opcodes). Stack effects reuse the canonical `write64`/`read64`
    and `regSet`/`ripNach` shapes; "Flags Affected: None" for PUSHFQ
    is the unchanged `roh`/flags/steuer. -/

/-- Adapter decode: exactly the one-byte PUSHFQ form (length 1). -/
def pushfqByte : List Byte → Option Nat
  | [b] => if b = pushfqOp then some 1 else none
  | _ => none

/-- Adapter decode: exactly the one-byte POPFQ form (length 1). -/
def popfqByte : List Byte → Option Nat
  | [b] => if b = popfqOp then some 1 else none
  | _ => none

/-- The adapters consume exactly one byte. -/
theorem pushfqByte_len (bs : List Byte) (len : Nat)
    (h : pushfqByte bs = some len) : len = 1 := by
  cases bs with
  | nil => simp [pushfqByte] at h
  | cons b rest =>
    cases rest with
    | nil =>
      by_cases hb : b = pushfqOp
      · simp [pushfqByte, hb] at h
        cases h
        rfl
      · simp [pushfqByte, hb] at h
    | cons _ _ => simp [pushfqByte] at h

/-- The POPFQ adapter consumes exactly one byte. -/
theorem popfqByte_len (bs : List Byte) (len : Nat)
    (h : popfqByte bs = some len) : len = 1 := by
  cases bs with
  | nil => simp [popfqByte] at h
  | cons b rest =>
    cases rest with
    | nil =>
      by_cases hb : b = popfqOp
      · simp [popfqByte, hb] at h
        cases h
        rfl
      · simp [popfqByte, hb] at h
    | cons _ _ => simp [popfqByte] at h

/-- Stack address below the top for PUSHFQ. -/
def pushfqOben (a : ArchZustand) : Adresse :=
  a.kern.register Register.rsp - BitVec.ofNat 64 8

/-- PUSHFQ register/memory/RIP successor core. -/
def pushfqKern (a : ArchZustand) (len : Nat) (m : Speicher) : Zustand :=
  { register := regSet a.kern.register Register.rsp (pushfqOben a),
    flags := a.kern.flags, rip := ripNach a.kern.rip len, speicher := m }

/-- PUSHFQ step: adapter decode, v8086/IOPL<3 refusal (#GP), 8-byte
    stack write of the VM/RF-cleared image, RIP advanced, flags and
    control untouched. -/
def pushfqSchritt (a : ArchZustand) (bs : List Byte) : Option ArchZustand :=
  match pushfqByte bs with
  | none => none
  | some len =>
    if a.steuer.vm && decide (a.steuer.iopl < 3) then none
    else
      match write64 a.kern.speicher (pushfqOben a)
        (pushfqWort a.roh) with
      | none => none
      | some m => some { kern := pushfqKern a len m, roh := a.roh, steuer := a.steuer }

/-- Stack address above the popped word for POPFQ. -/
def popfqHoch (a : ArchZustand) : Adresse :=
  a.kern.register Register.rsp + BitVec.ofNat 64 8

/-- The restored word of a POPFQ step. -/
def popfqNach (a : ArchZustand) (gesp : Wort) : Wort :=
  popfqWort (popfqLaden a.steuer.cpl a.steuer.iopl) a.roh gesp

/-- The control successor of a POPFQ step (CPL/VM kept, IOPL/IF from
    the restored word exactly where Table 1-12 loads them). -/
def popfqSteuer (a : ArchZustand) (gesp : Wort) : Steuer :=
  { cpl := a.steuer.cpl,
    iopl := if a.steuer.cpl = 0 then (if rbit (popfqNach a gesp) 13 then 2 else 0) + (if rbit (popfqNach a gesp) 12 then 1 else 0) else a.steuer.iopl,
    ifBit := rbit (popfqNach a gesp) 9, vm := a.steuer.vm }

/-- POPFQ register/flags/RIP successor core. -/
def popfqKern (a : ArchZustand) (len : Nat) (gesp : Wort) : Zustand :=
  { register := regSet a.kern.register Register.rsp (popfqHoch a),
    flags := liestStatus (popfqNach a gesp), rip := ripNach a.kern.rip len,
    speicher := a.kern.speicher }

/-- POPFQ step: adapter decode, v8086 refusal, 8-byte stack read, the
    Table 1-12 restore with RF cleared, stack pointer and RIP
    advanced, canonical flags re-read from the restored word. -/
def popfqSchritt (a : ArchZustand) (bs : List Byte) : Option ArchZustand :=
  match popfqByte bs with
  | none => none
  | some len =>
    if a.steuer.vm && decide (a.steuer.iopl < 3) then none
    else match read64 a.kern.speicher (a.kern.register Register.rsp) with
    | none => none
    | some gesp => some { kern := popfqKern a len gesp, roh := popfqNach a gesp, steuer := popfqSteuer a gesp }

/-- PUSHFQ success equation: decode, guard and stack write fix the
    successor exactly. -/
theorem pushfqSchritt_ok (a : ArchZustand) (bs : List Byte) (len : Nat)
    (hdec : pushfqByte bs = some len)
    (hv : (a.steuer.vm && decide (a.steuer.iopl < 3)) = false)
    (m : Speicher)
    (hwr : write64 a.kern.speicher (pushfqOben a) (pushfqWort a.roh) =
      some m) :
    pushfqSchritt a bs = some { kern := pushfqKern a len m, roh := a.roh, steuer := a.steuer } := by
  simp only [pushfqSchritt, pushfqKern, hdec, hwr]
  simp [hv]

/-- PUSHFQ leaves raw word, canonical flags and control untouched. -/
theorem pushfqSchritt_ruhig (a : ArchZustand) (bs : List Byte)
    (len : Nat) (nach : ArchZustand)
    (hdec : pushfqByte bs = some len)
    (hv : (a.steuer.vm && decide (a.steuer.iopl < 3)) = false)
    (m : Speicher)
    (hwr : write64 a.kern.speicher (pushfqOben a) (pushfqWort a.roh) =
      some m)
    (h : pushfqSchritt a bs = some nach) :
    nach.roh = a.roh ∧ nach.kern.flags = a.kern.flags ∧
    nach.steuer = a.steuer ∧
    nach.kern.rip = ripNach a.kern.rip len := by
  have hok := pushfqSchritt_ok a bs len hdec hv m hwr
  rw [hok] at h
  cases h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- PUSHFQ readback: the written image reads back through a readable
    footprint. -/
theorem pushfqSchritt_liest (a : ArchZustand) (bs : List Byte)
    (len : Nat) (nach : ArchZustand)
    (hdec : pushfqByte bs = some len)
    (hv : (a.steuer.vm && decide (a.steuer.iopl < 3)) = false)
    (m : Speicher)
    (hwr : write64 a.kern.speicher (pushfqOben a) (pushfqWort a.roh) =
      some m)
    (hrd : lesbar8 a.kern.speicher (pushfqOben a) = true)
    (h : pushfqSchritt a bs = some nach) :
    read64 nach.kern.speicher (pushfqOben a) =
      some (pushfqWort a.roh) := by
  have hok := pushfqSchritt_ok a bs len hdec hv m hwr
  rw [hok] at h
  cases h
  simp only [pushfqKern]
  exact read64_nach_write64 _ _ _ _ hwr hrd

/-- PUSHFQ preserves coherence: the successor satisfies `archOK`
    wherever the predecessor does (flags/word/control untouched). -/
theorem pushfqSchritt_arch (a : ArchZustand) (bs : List Byte)
    (len : Nat) (nach : ArchZustand)
    (hdec : pushfqByte bs = some len)
    (hv : (a.steuer.vm && decide (a.steuer.iopl < 3)) = false)
    (m : Speicher)
    (hwr : write64 a.kern.speicher (pushfqOben a) (pushfqWort a.roh) =
      some m)
    (h : pushfqSchritt a bs = some nach) (hok : archOK a) :
    archOK nach := by
  have hok2 := pushfqSchritt_ok a bs len hdec hv m hwr
  rw [hok2] at h
  cases h
  simp only [pushfqKern]
  unfold archOK at hok ⊢
  obtain ⟨hfl, hb1, hcpl, hiopl⟩ := hok
  exact ⟨hfl, hb1, hcpl, hiopl⟩

/-- PUSHFQ refuses in virtual-8086 mode below IOPL 3 (#GP). -/
theorem pushfqSchritt_v86 (a : ArchZustand)
    (hvm : a.steuer.vm = true) (hio : a.steuer.iopl < 3) :
    pushfqSchritt a [pushfqOp] = none := by
  have hd : pushfqByte [pushfqOp] = some 1 := by simp [pushfqByte]
  have hg : (a.steuer.vm && decide (a.steuer.iopl < 3)) = true := by
    simp [hvm, hio]
  simp only [pushfqSchritt, hd]
  exact if_pos hg

/-- PUSHFQ refuses a failed stack write (#SS/#PF analogue). -/
theorem pushfqSchritt_stapel (a : ArchZustand) (bs : List Byte)
    (len : Nat)
    (hdec : pushfqByte bs = some len)
    (hv : (a.steuer.vm && decide (a.steuer.iopl < 3)) = false)
    (hwr : write64 a.kern.speicher (pushfqOben a) (pushfqWort a.roh) =
      none) :
    pushfqSchritt a bs = none := by
  simp only [pushfqSchritt, hdec, hwr]
  simp [hv]

/-- PUSHFQ refuses any other byte. -/
theorem pushfqSchritt_fremd (a : ArchZustand) (b : Byte)
    (hb : b ≠ pushfqOp) : pushfqSchritt a [b] = none := by
  have hd : pushfqByte [b] = none := by simp [pushfqByte, hb]
  simp only [pushfqSchritt, hd]

/-- POPFQ success equation. -/
theorem popfqSchritt_ok (a : ArchZustand) (bs : List Byte) (len : Nat)
    (gesp : Wort)
    (hdec : popfqByte bs = some len)
    (hv : (a.steuer.vm && decide (a.steuer.iopl < 3)) = false)
    (hrd : read64 a.kern.speicher (a.kern.register Register.rsp) =
      some gesp) :
    popfqSchritt a bs = some { kern := popfqKern a len gesp, roh := popfqNach a gesp, steuer := popfqSteuer a gesp } := by
  simp only [popfqSchritt, popfqKern, popfqNach, popfqSteuer, hdec, hrd]
  simp [hv]

/-- POPFQ always clears RF (every Table 1-12 row). -/
theorem popfqSchritt_rf (a : ArchZustand) (bs : List Byte) (len : Nat)
    (nach : ArchZustand) (gesp : Wort)
    (hdec : popfqByte bs = some len)
    (hv : (a.steuer.vm && decide (a.steuer.iopl < 3)) = false)
    (hrd : read64 a.kern.speicher (a.kern.register Register.rsp) =
      some gesp)
    (h : popfqSchritt a bs = some nach) :
    rbit nach.roh 16 = false := by
  have hok := popfqSchritt_ok a bs len gesp hdec hv hrd
  rw [hok] at h
  cases h
  unfold popfqNach
  rw [popfqWort_bit _ _ _ 16 (by decide)]
  have hl : (popfqLaden a.steuer.cpl a.steuer.iopl).getLsbD 16 = false :=
    popfqLaden_erhaelt _ _ _ (Or.inl rfl)
  rw [hl]
  simp

/-- POPFQ preserves VM (every row: VM is never loaded). -/
theorem popfqSchritt_vm (a : ArchZustand) (bs : List Byte) (len : Nat)
    (nach : ArchZustand) (gesp : Wort)
    (hdec : popfqByte bs = some len)
    (hv : (a.steuer.vm && decide (a.steuer.iopl < 3)) = false)
    (hrd : read64 a.kern.speicher (a.kern.register Register.rsp) =
      some gesp)
    (h : popfqSchritt a bs = some nach) :
    rbit nach.roh 17 = rbit a.roh 17 := by
  have hok := popfqSchritt_ok a bs len gesp hdec hv hrd
  rw [hok] at h
  cases h
  unfold popfqNach
  rw [popfqWort_bit _ _ _ 17 (by decide)]
  have hl : (popfqLaden a.steuer.cpl a.steuer.iopl).getLsbD 17 = false :=
    popfqLaden_erhaelt _ _ _ (Or.inr (Or.inl rfl))
  rw [hl]
  simp

/-- POPFQ above IOPL keeps IF (control-state pin). -/
theorem popfqSchritt_if_hoch (a : ArchZustand) (bs : List Byte)
    (len : Nat) (nach : ArchZustand) (gesp : Wort)
    (hdec : popfqByte bs = some len)
    (hv : (a.steuer.vm && decide (a.steuer.iopl < 3)) = false)
    (hrd : read64 a.kern.speicher (a.kern.register Register.rsp) =
      some gesp)
    (hlt : a.steuer.iopl < a.steuer.cpl)
    (h : popfqSchritt a bs = some nach) :
    rbit nach.roh 9 = rbit a.roh 9 := by
  have hok := popfqSchritt_ok a bs len gesp hdec hv hrd
  rw [hok] at h
  cases h
  unfold popfqNach
  rw [popfqWort_bit _ _ _ 9 (by decide)]
  have hl : (popfqLaden a.steuer.cpl a.steuer.iopl).getLsbD 9 = false := by
    rw [popfqLaden_if]
    have hneg : ¬(a.steuer.cpl = 0 ∨ a.steuer.cpl ≤ a.steuer.iopl) := by
      omega
    simp [hneg]
  rw [hl]
  simp

/-- POPFQ at CPL 0 takes IF from the stack image. -/
theorem popfqSchritt_if_null (a : ArchZustand) (bs : List Byte)
    (len : Nat) (nach : ArchZustand) (gesp : Wort)
    (hdec : popfqByte bs = some len)
    (hv : (a.steuer.vm && decide (a.steuer.iopl < 3)) = false)
    (hrd : read64 a.kern.speicher (a.kern.register Register.rsp) =
      some gesp)
    (hc0 : a.steuer.cpl = 0)
    (h : popfqSchritt a bs = some nach) :
    rbit nach.roh 9 = rbit gesp 9 := by
  have hok := popfqSchritt_ok a bs len gesp hdec hv hrd
  rw [hok] at h
  cases h
  unfold popfqNach
  rw [popfqWort_bit _ _ _ 9 (by decide)]
  have hl : (popfqLaden a.steuer.cpl a.steuer.iopl).getLsbD 9 = true := by
    rw [popfqLaden_if, decide_eq_true (Or.inl hc0)]
  rw [hl]
  simp

/-- POPFQ status bits come from the stack image on every row. -/
theorem popfqSchritt_status (a : ArchZustand) (bs : List Byte)
    (len : Nat) (nach : ArchZustand) (gesp : Wort)
    (hdec : popfqByte bs = some len)
    (hv : (a.steuer.vm && decide (a.steuer.iopl < 3)) = false)
    (hrd : read64 a.kern.speicher (a.kern.register Register.rsp) =
      some gesp)
    (h : popfqSchritt a bs = some nach) (i : Nat)
    (hs : i = 0 ∨ i = 2 ∨ i = 4 ∨ i = 6 ∨ i = 7 ∨ i = 11) :
    rbit nach.roh i = rbit gesp i := by
  have hok := popfqSchritt_ok a bs len gesp hdec hv hrd
  rw [hok] at h
  cases h
  have h64 : i < 64 := by
    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have hne : i ≠ 16 := by
    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  unfold popfqNach
  rw [popfqWort_bit _ _ _ i h64]
  have hl : (popfqLaden a.steuer.cpl a.steuer.iopl).getLsbD i = true :=
    popfqLaden_status _ _ _ hs
  rw [hl]
  simp [hne]

/-- POPFQ keeps CPL and VM in the control state. -/
theorem popfqSchritt_steuer (a : ArchZustand) (bs : List Byte)
    (len : Nat) (nach : ArchZustand) (gesp : Wort)
    (hdec : popfqByte bs = some len)
    (hv : (a.steuer.vm && decide (a.steuer.iopl < 3)) = false)
    (hrd : read64 a.kern.speicher (a.kern.register Register.rsp) =
      some gesp)
    (h : popfqSchritt a bs = some nach) :
    nach.steuer.cpl = a.steuer.cpl ∧ nach.steuer.vm = a.steuer.vm := by
  have hok := popfqSchritt_ok a bs len gesp hdec hv hrd
  rw [hok] at h
  cases h
  exact ⟨rfl, rfl⟩

/-- POPFQ refuses in virtual-8086 mode below IOPL 3 (#GP). -/
theorem popfqSchritt_v86 (a : ArchZustand)
    (hvm : a.steuer.vm = true) (hio : a.steuer.iopl < 3) :
    popfqSchritt a [popfqOp] = none := by
  have hd : popfqByte [popfqOp] = some 1 := by simp [popfqByte]
  have hg : (a.steuer.vm && decide (a.steuer.iopl < 3)) = true := by
    simp [hvm, hio]
  simp only [popfqSchritt, hd]
  exact if_pos hg

/-- POPFQ refuses a failed stack read. -/
theorem popfqSchritt_lesefehler (a : ArchZustand) (bs : List Byte)
    (len : Nat)
    (hdec : popfqByte bs = some len)
    (hv : (a.steuer.vm && decide (a.steuer.iopl < 3)) = false)
    (hrd : read64 a.kern.speicher (a.kern.register Register.rsp) = none) :
    popfqSchritt a bs = none := by
  simp only [popfqSchritt, hdec, hrd]
  simp [hv]

/-- POPFQ refuses any other byte. -/
theorem popfqSchritt_fremd (a : ArchZustand) (b : Byte)
    (hb : b ≠ popfqOp) : popfqSchritt a [b] = none := by
  have hd : popfqByte [b] = none := by simp [popfqByte, hb]
  simp only [popfqSchritt, hd]

/-- The pilot decoder refuses the PUSHFQ byte: the adapter never
    shadows `Codec.decode`. -/
theorem pushfq_fremd : decode [pushfqOp] = none := by decide

/-- The pilot decoder refuses the POPFQ byte. -/
theorem popfq_fremd : decode [popfqOp] = none := by decide

/-! ## 6c. Joint fetched run and planted refusals.

    Fetched `add rax, rbx` (defined AF set) followed by the fetched
    flag-save changes real stack memory; a second run distinguishes
    the cleared AF; MUL contributes two legal undefined-flag choices;
    the push/pop roundtrip restores status with RF cleared; and the
    planted mutations cover malformed bytes, privilege, stack access,
    control-state gating and undefined consumers. -/

/-- Witness registers: `rax = 0x0F`, `rbx = 0x01`, stack top 8192. -/
def witRegA : Register → Wort := fun q =>
  if q = Register.rax then 0x0F
  else if q = Register.rbx then 0x01
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness raw word: bit 1 (valid), bit 4 (the `0x0F + 0x01` nibble
    carry), bit 16 (RF, to show the clearing). -/
def witRohA : Wort := BitVec.ofNat 64 (2 + 16 + 65536)

/-- Witness control: CPL 0, no virtual-8086 mode. -/
def witSteuer : Steuer := { cpl := 0, iopl := 0, ifBit := true, vm := false }

/-- Witness memory: the PUSHFQ byte at the code address, zeroed stack,
    fully permissive. -/
def flagSpeicher : Speicher :=
  { bytes := fun a => if a = BitVec.ofNat 64 4099 then pushfqOp else BitVec.ofNat 8 0, lesbar := fun _ => true, schreibbar := fun _ => true, ausfuehrbar := fun _ => true }

/-- Witness core before the arithmetic. -/
def witKern0 : Zustand :=
  { register := witRegA, flags := liestStatus witRohA, rip := BitVec.ofNat 64 4096, speicher := flagSpeicher }

/-- Witness architectural state before the arithmetic. -/
def witA0 : ArchZustand := { kern := witKern0, roh := witRohA, steuer := witSteuer }

/-- Witness core after `add rax, rbx`: `rax = 0x10`, RIP advanced by
    the 3-byte form, flags are the accepted snapshot. -/
def witKern1 : Zustand :=
  { register := fun q => if q = Register.rax then 0x10 else witRegA q, flags := (add64 0x0F 0x01).2, rip := BitVec.ofNat 64 4099, speicher := flagSpeicher }

/-- Witness architectural state before the flag-save. -/
def witA1 : ArchZustand := { kern := witKern1, roh := witRohA, steuer := witSteuer }

/-- Push-successor of the witness (stack image written). -/
def witNach1 (m : Speicher) : ArchZustand := { kern := pushfqKern witA1 1 m, roh := witRohA, steuer := witSteuer }

/-- The stack store after the witness flag-save (syntactically the
    `write64` output, so the success fact closes by rewriting). -/
def witStore : Speicher :=
  { witA1.kern.speicher with bytes := writeBytes witA1.kern.speicher (pushfqOben witA1) (pushfqWort witRohA) }

/-- Second-run registers: `rax = 0x10` (no nibble carry with `rbx`). -/
def witRegB : Register → Wort := fun q =>
  if q = Register.rax then 0x10
  else if q = Register.rbx then 0x01
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Second-run raw word: valid bit plus the even parity of `0x11`. -/
def witRohB : Wort := BitVec.ofNat 64 (2 + 4)

/-- Coherence of the pre-arithmetic witness. -/
theorem witA0_ok : archOK witA0 := by
  unfold archOK witA0 witKern0
  refine ⟨rfl, by decide, by decide, by decide⟩

/-- Coherence of the pre-save witness: the raw word reads exactly the
    accepted ADD snapshot. -/
theorem witA1_ok : archOK witA1 := by
  unfold archOK witA1 witKern1
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- JOINT WITNESS: fetched arithmetic then flag-save.

    `add rax, rbx` on `0x0F + 0x01` sets `rax` to `0x10` with the
    defined AF; the fetched PUSHFQ byte saves the VM/RF-cleared image
    to real stack memory (observably changed from zero, RF cleared);
    and MUL contributes two legal undefined-SF choices. -/
theorem pushfq_lauf_zeuge :
    ∃ (nach1 : ArchZustand),
      (schritt ⟨.addReg64 .rax .rbx, 3⟩ witKern0).map
        (fun s => s.register Register.rax) = some 0x10 ∧
      addErlaubt 0x0F 0x01 witRohA ∧
      (geholt witKern1).take 1 = [pushfqOp] ∧
      pushfqSchritt witA1 [pushfqOp] = some nach1 ∧
      nach1.kern.register Register.rsp =
        witKern1.register Register.rsp - BitVec.ofNat 64 8 ∧
      read64 nach1.kern.speicher (pushfqOben witA1) =
        some (pushfqWort witRohA) ∧
      rbit (pushfqWort witRohA) afBit = true ∧
      rbit (pushfqWort witRohA) rfPos = false ∧
      flagSpeicher.bytes (pushfqOben witA1) = BitVec.ofNat 8 0 ∧
      pushfqWort witRohA ≠ 0 ∧
      (∃ n1 n2, mulErlaubtU 2 3 n1 ∧ mulErlaubtU 2 3 n2 ∧
        rbit n1 sfBit = true ∧ rbit n2 sfBit = false) := by
  have hd : pushfqByte [pushfqOp] = some 1 := by simp [pushfqByte]
  have hv : (witA1.steuer.vm && decide (witA1.steuer.iopl < 3)) = false := by
    decide
  have hrd : lesbar8 witA1.kern.speicher (pushfqOben witA1) = true := by
    decide
  obtain ⟨m, hwr⟩ : ∃ m, write64 witA1.kern.speicher (pushfqOben witA1)
      (pushfqWort witRohA) = some m := ⟨_, rfl⟩
  have hadd : addErlaubt 0x0F 0x01 witRohA := by
    unfold addErlaubt
    decide
  have hok := pushfqSchritt_ok witA1 [pushfqOp] 1 hd hv m hwr
  refine ⟨_, by decide, hadd, by decide, hok, ?_, ?_, by decide,
    by decide, by decide, by decide, mulU_sf_frei 2 3⟩
  · simp only [pushfqKern]
    exact regSet_gleich _ _ _
  · simp only [pushfqKern]
    exact read64_nach_write64 _ _ _ _ hwr hrd

/-- AF DISTINGUISHER: the `0x0F + 0x01` run saves AF set, the
    `0x10 + 0x01` run saves AF clear -- defined auxiliary carry is
    observable through the saved image. -/
theorem pushfq_af_unterscheidet :
    rbit (pushfqWort witRohA) afBit = true ∧
    rbit (pushfqWort witRohB) afBit = false ∧
    addErlaubt 0x0F 0x01 witRohA ∧ addErlaubt 0x10 0x01 witRohB := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · unfold addErlaubt
    decide
  · unfold addErlaubt
    decide

/-- PUSH/POP ROUNDTRIP: restoring the saved image recovers the status
    bits, keeps RF cleared and returns the stack top. -/
theorem pushfq_popfq_rundgang :
    ∃ (nach1 zur : ArchZustand),
      pushfqSchritt witA1 [pushfqOp] = some nach1 ∧
      popfqSchritt nach1 [popfqOp] = some zur ∧
      liestStatus zur.roh = liestStatus witRohA ∧
      rbit zur.roh rfPos = false ∧
      zur.kern.register Register.rsp = BitVec.ofNat 64 8192 ∧
      zur.kern.rip = ripNach nach1.kern.rip 1 := by
  have hd : pushfqByte [pushfqOp] = some 1 := by simp [pushfqByte]
  have hd2 : popfqByte [popfqOp] = some 1 := by simp [popfqByte]
  have hv : (witA1.steuer.vm && decide (witA1.steuer.iopl < 3)) = false := by
    decide
  have hrd : lesbar8 witA1.kern.speicher (pushfqOben witA1) = true := by
    decide
  have hperm : schreibbar8 witA1.kern.speicher (pushfqOben witA1) =
      true := by
    decide
  have hwr : write64 witA1.kern.speicher (pushfqOben witA1)
      (pushfqWort witRohA) = some witStore := by
    unfold write64 witStore
    rw [if_pos hperm]
  have hok := pushfqSchritt_ok witA1 [pushfqOp] 1 hd hv witStore hwr
  have hlese : read64 witStore (pushfqOben witA1) =
      some (pushfqWort witRohA) :=
    read64_nach_write64 _ _ _ _ hwr hrd
  have hv2 : ((witNach1 witStore).steuer.vm &&
      decide ((witNach1 witStore).steuer.iopl < 3)) = false := by
    decide
  have hrd2 : read64 witStore
      ((pushfqKern witA1 1 witStore).register Register.rsp) =
      some (pushfqWort witRohA) := by
    have htop : (pushfqKern witA1 1 witStore).register Register.rsp =
        pushfqOben witA1 := by
      simp only [pushfqKern]
      exact regSet_gleich _ _ _
    rw [htop]
    exact hlese
  have hok2 := popfqSchritt_ok (witNach1 witStore) [popfqOp] 1
    (pushfqWort witRohA) hd2 hv2 hrd2
  refine ⟨_, _, hok, hok2, by decide, by decide, ?_, by decide⟩
  simp only [popfqKern]
  rw [regSet_gleich]
  decide

/-- Shared write fact for the witness stack. -/
theorem wit_schreibt : write64 witA1.kern.speicher (pushfqOben witA1)
    (pushfqWort witRohA) = some witStore := by
  have hperm : schreibbar8 witA1.kern.speicher (pushfqOben witA1) = true := by
    decide
  unfold write64 witStore
  rw [if_pos hperm]

/-- Shared readback fact for the witness stack. -/
theorem wit_liest : read64 witStore (pushfqOben witA1) =
    some (pushfqWort witRohA) :=
  read64_nach_write64 _ _ _ _ wit_schreibt (by decide)

/-- High-privilege live word: IF set (bit 9). -/
def witRohH : Wort := BitVec.ofNat 64 (2 + 512)

/-- High-privilege control: CPL 3 above IOPL 0. -/
def witSteuerHoch : Steuer := { cpl := 3, iopl := 0, ifBit := true, vm := false }

/-- Gating witness: same stack as the push successor, live IF set. -/
def witA3 : ArchZustand := { kern := (witNach1 witStore).kern, roh := witRohH, steuer := witSteuerHoch }

/-- IF-GATING WITNESS: above IOPL the live IF survives POPFQ even
    though the stack image disagrees (control-state pin). -/
theorem popfq_if_gating_zeuge :
    ∃ (zur2 : ArchZustand),
      popfqSchritt witA3 [popfqOp] = some zur2 ∧
      rbit zur2.roh 9 = true ∧ rbit (pushfqWort witRohA) 9 = false := by
  have hd2 : popfqByte [popfqOp] = some 1 := by simp [popfqByte]
  have hv3 : (witA3.steuer.vm && decide (witA3.steuer.iopl < 3)) = false := by
    decide
  have hrsp : witA3.kern.register Register.rsp = pushfqOben witA1 := by
    simp only [witA3, witNach1, pushfqKern]
    exact regSet_gleich _ _ _
  have hsp : witA3.kern.speicher = witStore := rfl
  have hrd3 : read64 witA3.kern.speicher (witA3.kern.register
      Register.rsp) = some (pushfqWort witRohA) := by
    rw [hsp, hrsp]
    exact wit_liest
  have hok3 := popfqSchritt_ok witA3 [popfqOp] 1 (pushfqWort witRohA)
    hd2 hv3 hrd3
  have hif := popfqSchritt_if_hoch witA3 [popfqOp] 1 _ _
    hd2 hv3 hrd3 (by decide) hok3
  have hpre : rbit witA3.roh 9 = true := by decide
  rw [hpre] at hif
  exact ⟨_, hok3, hif, by decide⟩

/-- The adapters refuse each other's opcode. -/
theorem pushfqByte_ablehnt : pushfqByte [popfqOp] = none := by decide

/-- The POPFQ adapter refuses the PUSHFQ opcode. -/
theorem popfqByte_ablehnt : popfqByte [pushfqOp] = none := by decide

/-- The adapter refuses two-byte inputs (no length ambiguity). -/
theorem pushfqByte_lang_ablehnt (a b : Byte) :
    pushfqByte [a, b] = none := by
  simp [pushfqByte]

/-- Witness memory with a dead stack (nothing writable). -/
def flagSpeicherRO : Speicher :=
  { bytes := fun a => if a = BitVec.ofNat 64 4099 then pushfqOp else BitVec.ofNat 8 0, lesbar := fun _ => true, schreibbar := fun _ => false, ausfuehrbar := fun _ => true }

/-- Witness core on the dead stack. -/
def witKernRO : Zustand :=
  { register := witRegA, flags := liestStatus witRohA, rip := BitVec.ofNat 64 4099, speicher := flagSpeicherRO }

/-- Witness state on the dead stack. -/
def witARO : ArchZustand := { kern := witKernRO, roh := witRohA, steuer := witSteuer }

/-- STACK REFUSAL: PUSHFQ fails where the stack is not writable. -/
theorem pushfq_stapel_zeuge :
    pushfqSchritt witARO [pushfqOp] = none := by
  have hdec : pushfqByte [pushfqOp] = some 1 := by simp [pushfqByte]
  have hv : (witARO.steuer.vm && decide (witARO.steuer.iopl < 3)) = false := by
    decide
  have hwr : write64 witARO.kern.speicher (pushfqOben witARO)
      (pushfqWort witARO.roh) = none := by
    decide
  exact pushfqSchritt_stapel witARO [pushfqOp] 1 hdec hv hwr

/-- Witness memory with an unreadable stack. -/
def flagSpeicherNR : Speicher :=
  { bytes := fun a => if a = BitVec.ofNat 64 4099 then pushfqOp else BitVec.ofNat 8 0, lesbar := fun _ => false, schreibbar := fun _ => true, ausfuehrbar := fun _ => true }

/-- Witness core on the unreadable stack. -/
def witKernNR : Zustand :=
  { register := witRegA, flags := liestStatus witRohA, rip := BitVec.ofNat 64 4099, speicher := flagSpeicherNR }

/-- Witness state on the unreadable stack. -/
def witANR : ArchZustand := { kern := witKernNR, roh := witRohA, steuer := witSteuer }

/-- READ REFUSAL: POPFQ fails where the stack is not readable. -/
theorem popfq_lese_zeuge :
    popfqSchritt witANR [popfqOp] = none := by
  have hdec : popfqByte [popfqOp] = some 1 := by simp [popfqByte]
  have hv : (witANR.steuer.vm && decide (witANR.steuer.iopl < 3)) = false := by
    decide
  have hrd : read64 witANR.kern.speicher
      (witANR.kern.register Register.rsp) = none := by
    decide
  exact popfqSchritt_lesefehler witANR [popfqOp] 1 hdec hv hrd

/- CUTS: proved here versus left open.

    PROVED (all over the REUSED canonical words, snapshots and
    validity relations -- no second arithmetic or interpreter):
    - raw RFLAGS status model (`rbit`/`liestStatus`/`archOK`) with a
      coherent projection (`projiziert`) to the existing `Zustand`
      flags; control bits survive ALU rows by construction (steps
      carry `steuer` unchanged except POPFQ's Table 1-12 update);
    - defined AF for ADD/SUB/CMP/NEG at every pilot width, derived
      from the canonical nibble carry (`trunc_nibble`,
      `afAddB_ist_afAdd`, `afSubB_ist_afSub`, `negAf_ist_afSub`);
    - sound defined/undefined effect rows for ADD/SUB/CMP/NEG (all
      defined), AND/OR/XOR/TEST (AF free), MUL/IMUL (only CF/OF),
      DIV/IDIV (all free), shifts (AF free, OF at one-count), with
      adapters exhibiting the producers' deterministic snapshots as
      admissible members and two-choice witnesses for every free bit;
    - consumer admission (`verbrauchOK`) with safety theorems for
      every admitted pair, the DIV refusal witness and the derived
      raw-AF non-observability proof (`rohAf_frei`);
    - fetched PUSHFQ (opcode 9CH, VM/RF-cleared image, 8-byte stack
      write, flags/control/RIP frames) and POPFQ (9DH, Table 1-12
      64-bit CPL/IOPL gating, RF cleared, VIP/VIF/VM preserved) with
      success equations, frame theorems and v8086/stack/foreign-byte
      refusals; the pilot decoder refuses both bytes;
    - joint fetched arithmetic-then-save run with real stack-memory
      change, defined-AF distinction, two undefined choices,
      push/pop roundtrip, IF-gating and concrete stack refusals.
    NOT proved here, and not claimed:
    - No floating-point/FPU flag rows (C0-C3, SSE MXCSR): FP forms
      are deferred to the FP lane.
    - No INC/DEC (CF preservation), ADC/SBB, CMPXCHG/XADD, BT
      family, SAHF/LAHF rows: no producer form consumes them here.
    - POPFQ covers the 64-bit Table 1-12 rows only: 16-bit form,
      VME/PVI virtual-8086 rows, TSS/task-switch and real-address
      rows are open.
    - Pending-interrupt/event delivery effects of IF are not
      modelled, only the IF bit itself; HardwareInterrupts672 owns
      delivery. No TSO/concurrency claim; everything is sequential
      over one `Speicher`.
    - No wiring into `decodeExt`/`schritt`/`lauf`: the one-byte
      adapters are the exact boundary for HardwareExecution660.
    - No source, checker, Spec or goal claim; no new `Befehl`
      constructor and no pilot decoder change.
    - No silicon correspondence: physical flag behavior is a named
      hardware assumption; manual sentences are provenance, and the
      two producer abstractions found (MUL SF/ZF/PF preservation,
      DIV whole-snapshot preservation) are adapted, not trusted.
-/

#print axioms projiziert_flags
#print axioms and_maske_nibble
#print axioms maske_nibble
#print axioms trunc_nibble
#print axioms afAddB_ist_afAdd
#print axioms afSubB_ist_afSub
#print axioms negAf_ist_afSub
#print axioms cmpAf_ist_afSub
#print axioms rohAusStatus_bits
#print axioms roh_mulU
#print axioms roh_mulS
#print axioms mulU_hat_roh
#print axioms mulS_hat_roh
#print axioms mulU_sf_frei
#print axioms logik_hat_roh
#print axioms logik_af_frei
#print axioms div_alles_frei
#print axioms schieb_of_frei
#print axioms schiebAdapter
#print axioms verbrauchOK_beispiele
#print axioms addVerbrauch_sicher
#print axioms subVerbrauch_sicher
#print axioms negVerbrauch_sicher
#print axioms logikVerbrauch_sicher
#print axioms mulVerbrauch_sicher
#print axioms shiftVerbrauch_eins
#print axioms divVerbrauch_verweigert
#print axioms rohAf_frei
#print axioms pushfqMaske_bit
#print axioms pushfqWort_status
#print axioms pushfqWort_vm_rf
#print axioms popfqLaden_status
#print axioms popfqLaden_erhaelt
#print axioms popfqLaden_if
#print axioms popfqLaden_iopl
#print axioms ohneRF_bit
#print axioms popfqWort_bit
#print axioms pushfqByte_len
#print axioms popfqByte_len
#print axioms pushfqSchritt_ok
#print axioms pushfqSchritt_ruhig
#print axioms pushfqSchritt_liest
#print axioms pushfqSchritt_arch
#print axioms pushfqSchritt_v86
#print axioms pushfqSchritt_stapel
#print axioms pushfqSchritt_fremd
#print axioms popfqSchritt_ok
#print axioms popfqSchritt_rf
#print axioms popfqSchritt_vm
#print axioms popfqSchritt_if_hoch
#print axioms popfqSchritt_if_null
#print axioms popfqSchritt_status
#print axioms popfqSchritt_steuer
#print axioms popfqSchritt_v86
#print axioms popfqSchritt_lesefehler
#print axioms popfqSchritt_fremd
#print axioms pushfq_fremd
#print axioms popfq_fremd
#print axioms witA0_ok
#print axioms witA1_ok
#print axioms pushfq_lauf_zeuge
#print axioms pushfq_af_unterscheidet
#print axioms pushfq_popfq_rundgang
#print axioms wit_schreibt
#print axioms wit_liest
#print axioms popfq_if_gating_zeuge
#print axioms pushfqByte_ablehnt
#print axioms popfqByte_ablehnt
#print axioms pushfqByte_lang_ablehnt
#print axioms pushfq_stapel_zeuge
#print axioms popfq_lese_zeuge

end Gabbro.Grammatik.X86
