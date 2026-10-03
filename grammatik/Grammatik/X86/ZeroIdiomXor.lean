/-
  File:      Grammatik/X86/ZeroIdiomXor.lean
  Subject:   Zero idiom XOR reg, reg (opcode 31/r, same register only).

  Lane 754: the 31/r zero idiom ONLY, with a flag-liveness proof at the
  site. Value and flags reuse the accepted canonical operations
  (`Wort.xor64`, `Ganzzahl.LogikGueltig`, `Ausfuehrung.schritt`,
  `Codec.encode`/`decode`); nothing is redefined here. A codec round
  trip alone is NOT hardware fidelity (see CUTS).

  Manual provenance (from `.tmp/HARDWARE-REFERENCES/REFERENCES.json`,
  read, not verified here): Intel SDM combined volumes 1-4,
  edition 325462-093US, September 2026. The XOR r/m64, r64 encoding
  (REX.W + 31 /r) and its flag effects (CF/OF cleared, SF/ZF/PF from
  the zero result, AF undefined) are stated semantics, not verified
  against silicon (see CUTS).
-/
import Grammatik.X86.Codec
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Wort
import Grammatik.X86.Ganzzahl
import Grammatik.X86.ExtendedExecution

namespace Gabbro.Grammatik.X86

/-- A zero idiom names the register it zeroes: `XOR r, r`. -/
abbrev ZeroForm := Register

/-- Canonical bytes of the zero idiom: the pilot 31/r row with both
    sides the same register. Encoding is routed, never reimplemented. -/
def encodeZero (r : Register) : List Byte :=
  encode (.xorReg64 r r)

/-- A decoded zero idiom: the register with its consumed length as
    checked data (3 for every canonical row). -/
structure ZeroDecodiert where
  reg : Register
  laenge : Nat
  deriving DecidableEq, Repr

/-- Decode filter: the pilot decoder, accepted ONLY for `XOR r, r`.
    A general `XOR dst, src` with `dst != src` is explicitly refused
    (`none`); every non-XOR row is refused through the pilot `none`. -/
def decodeZero (bs : List Byte) : Option (ZeroDecodiert × List Byte) :=
  match decode bs with
  | some ((⟨.xorReg64 dst src, n⟩ : Decodiert), rest) =>
    if _ : dst = src then some (⟨dst, n⟩, rest) else none
  | _ => none

/-! ## 1. Codec: lengths, round trip, explicit refusals. -/

/-- Every zero-idiom encoding is 3 bytes, within the 1..15 bound. -/
theorem encodeZero_laenge (r : Register) :
    (encodeZero r).length = 3 ∧ 1 ≤ (encodeZero r).length ∧
      (encodeZero r).length ≤ 15 := by
  cases r <;> decide

/-- The decoded length passes the pilot length guard. -/
theorem zeroLaenge_ok (d : ZeroDecodiert) (h : d.laenge = 3) :
    laengeOk d.laenge = true := by
  rw [h]; decide

/-- Round trip: decoding inverts encoding with the suffix. -/
theorem roundtripZero (r : Register) (suffix : List Byte) :
    decodeZero (encodeZero r ++ suffix) =
      some ((⟨r, 3⟩ : ZeroDecodiert), suffix) := by
  cases r <;> rfl

/-- A successful round trip consumes exactly its decoded length. -/
theorem roundtripZero_len_ok (r : Register) (suffix : List Byte) :
    decodeZero (encodeZero r ++ suffix) =
        some ((⟨r, 3⟩ : ZeroDecodiert), suffix) ∧
      3 + suffix.length = (encodeZero r ++ suffix).length := by
  refine ⟨roundtripZero r suffix, ?_⟩
  have h := (encodeZero_laenge r).1
  rw [List.length_append, h]

/-- A general XOR with distinct registers is explicitly refused. -/
theorem decodeZero_verweigert_fremd (dst src : Register)
    (suffix : List Byte) (h : dst ≠ src) :
    decodeZero (encode (.xorReg64 dst src) ++ suffix) = none := by
  have hrt := roundtrip_xorReg64 dst src suffix
  unfold decodeZero
  rw [hrt]
  simp [h]

/-- A successful zero decode is a pilot XOR-self decode at the same
    length: no row is re-decided, only filtered. -/
theorem decodeZero_ist_pilot (bs : List Byte) (d : ZeroDecodiert)
    (rest : List Byte)
    (h : decodeZero bs = some (d, rest)) :
    decode bs = some ((⟨.xorReg64 d.reg d.reg, d.laenge⟩ : Decodiert), rest) := by
  unfold decodeZero at h
  cases hbs : decode bs with
  | none =>
    rw [hbs] at h
    simp at h
  | some p =>
    rw [hbs] at h
    obtain ⟨d0, rest0⟩ := p
    cases d0 with
    | mk b0 n0 =>
      cases b0 with
      | xorReg64 dst src =>
        dsimp only at h
        by_cases heq : dst = src
        · rw [dif_pos heq] at h
          cases h with
          | refl =>
            subst heq
            rfl
        · rw [dif_neg heq] at h
          cases h
      | movImm64 _ _ =>
        dsimp only at h
        cases h
      | movReg64 _ _ =>
        dsimp only at h
        cases h
      | addReg64 _ _ =>
        dsimp only at h
        cases h
      | subReg64 _ _ =>
        dsimp only at h
        cases h
      | cmpReg64 _ _ =>
        dsimp only at h
        cases h
      | load64 _ _ _ =>
        dsimp only at h
        cases h
      | store64 _ _ _ =>
        dsimp only at h
        cases h
      | jump32 _ =>
        dsimp only at h
        cases h
      | jumpIf32 _ _ =>
        dsimp only at h
        cases h
      | call32 _ =>
        dsimp only at h
        cases h
      | push64 _ =>
        dsimp only at h
        cases h
      | pop64 _ =>
        dsimp only at h
        cases h
      | ret =>
        dsimp only at h
        cases h

/-! ## 2. Execution: value zero plus clobbered flags.

    The step IS the accepted pilot `schritt` on the XOR-self row: every
    admitted final byte executes through the common architecture, never
    through a second implementation. Memory is never touched; the step
    cannot fault (register-only operands, length-checked). -/

/-- One zero-idiom step: the accepted pilot step on `XOR reg, reg`. -/
def zeroSchritt (d : ZeroDecodiert) (s : Zustand) : Option Zustand :=
  schritt (⟨.xorReg64 d.reg d.reg, d.laenge⟩ : Decodiert) s

/-- The step is the accepted pilot step: no second implementation. -/
theorem zeroSchritt_ist_schritt (d : ZeroDecodiert) (s : Zustand) :
    zeroSchritt d s =
      schritt (⟨.xorReg64 d.reg d.reg, d.laenge⟩ : Decodiert) s := rfl

/-- The zero-idiom value is zero: `x ^^^ x = 0` through the reused
    `xor64` (whose first projection the accepted step writes). -/
theorem xor_selbst_null (x : Wort) : (xor64 x x).1 = 0 := by
  simp [xor64, BitVec.xor_self]

/-- The zero-idiom flag snapshot: CF/OF cleared, AF undefined, ZF set,
    SF clear, PF set (even parity of the zero low byte). -/
theorem xor_selbst_flags (x : Wort) :
    (xor64 x x).2 =
      Flags.mk false true none true false false := by
  simp [xor64, zfTest, sfTest, parityEven, popCount8, bitAt]

/-- The zero-idiom snapshot satisfies the accepted logic validity
    relation over the zero result. -/
theorem xor_selbst_gueltig (x : Wort) :
    LogikGueltig (xor64 x x).1 (xor64 x x).2 := by
  rw [xor_selbst_null, xor_selbst_flags]
  simp [LogikGueltig, zfTest, sfTest, parityEven, popCount8, bitAt]

/-- A successful zero step passed the length check. -/
theorem zeroSchritt_ok (d : ZeroDecodiert) (s s' : Zustand)
    (h : zeroSchritt d s = some s') :
    laengeOk d.laenge = true := by
  by_cases hg : laengeOk d.laenge = true
  · exact hg
  · have hfalse : laengeOk d.laenge = false := by
      simpa using hg
    have hnone := schritt_laenge_verweigert
      (⟨.xorReg64 d.reg d.reg, d.laenge⟩ : Decodiert) s hfalse
    unfold zeroSchritt at h
    rw [hnone] at h
    cases h

/-- A successful zero step writes zero into the register. -/
theorem zeroSchritt_wert (d : ZeroDecodiert) (s s' : Zustand)
    (h : zeroSchritt d s = some s') :
    s'.register d.reg = 0 := by
  have hok := zeroSchritt_ok d s s' h
  have hstep := schritt_xorReg64
    (⟨.xorReg64 d.reg d.reg, d.laenge⟩ : Decodiert) s d.reg d.reg hok rfl
  unfold zeroSchritt at h
  rw [hstep] at h
  cases h
  show regSet s.register d.reg
    (xor64 (s.register d.reg) (s.register d.reg)).1 d.reg = 0
  rw [regSet_gleich]
  exact xor_selbst_null _

/-- A successful zero step clobbers every flag with the zero snapshot:
    CF/OF cleared, AF undefined, ZF set, SF clear, PF set. -/
theorem zeroSchritt_flags (d : ZeroDecodiert) (s s' : Zustand)
    (h : zeroSchritt d s = some s') :
    s'.flags = Flags.mk false true none true false false := by
  have hok := zeroSchritt_ok d s s' h
  have hstep := schritt_xorReg64
    (⟨.xorReg64 d.reg d.reg, d.laenge⟩ : Decodiert) s d.reg d.reg hok rfl
  unfold zeroSchritt at h
  rw [hstep] at h
  cases h
  rw [schrittRegister_flags]
  exact xor_selbst_flags _

/-- A successful zero step never touches memory: no access order,
    no permission change, no TSO/store-buffer effect. -/
theorem zeroSchritt_speicher (d : ZeroDecodiert) (s s' : Zustand)
    (h : zeroSchritt d s = some s') :
    s'.speicher = s.speicher := by
  have hok := zeroSchritt_ok d s s' h
  exact schritt_xorReg64_speicher _ s s' d.reg d.reg hok rfl h

/-- A successful zero step advances RIP past the decoded length. -/
theorem zeroSchritt_rip (d : ZeroDecodiert) (s s' : Zustand)
    (h : zeroSchritt d s = some s') :
    s'.rip = ripNach s.rip d.laenge := by
  have hok := zeroSchritt_ok d s s' h
  have hstep := schritt_xorReg64
    (⟨.xorReg64 d.reg d.reg, d.laenge⟩ : Decodiert) s d.reg d.reg hok rfl
  unfold zeroSchritt at h
  rw [hstep] at h
  cases h
  exact schrittRegister_rip _ _ _ _ _

/-- A successful zero step keeps every other register. -/
theorem zeroSchritt_fremd (d : ZeroDecodiert) (s s' : Zustand)
    (h : zeroSchritt d s = some s') (q : Register)
    (hq : q ≠ d.reg) :
    s'.register q = s.register q := by
  have hok := zeroSchritt_ok d s s' h
  have hstep := schritt_xorReg64
    (⟨.xorReg64 d.reg d.reg, d.laenge⟩ : Decodiert) s d.reg d.reg hok rfl
  unfold zeroSchritt at h
  rw [hstep] at h
  cases h
  show regSet s.register d.reg
    (xor64 (s.register d.reg) (s.register d.reg)).1 q = s.register q
  exact regSet_fremd _ _ _ _ hq

/-! ## 3. Flag liveness at the site: refusal where a flag survives.

    The idiom clobbers CF/PF/ZF/SF/OF (§2) and leaves AF undefined, so
    the site may use it only where no flag is live. AF is absent from
    the demand by construction: a demand for AF can never be admitted
    because the idiom defines no AF value to preserve. -/

/-- Liveness demand at the site: which flags the code after the site
    reads. -/
structure FlagBedarf where
  cf : Bool
  pf : Bool
  zf : Bool
  sf : Bool
  of : Bool
  deriving DecidableEq, Repr

/-- The site may use the zero idiom only where no flag survives:
    every demand must be dead. -/
def darfNullen (b : FlagBedarf) : Bool :=
  (!b.cf && !b.pf && !b.zf && !b.sf && !b.of)

/-- A demand is live where it asks for at least one flag. -/
def Lebendig (b : FlagBedarf) : Prop :=
  b.cf = true ∨ b.pf = true ∨ b.zf = true ∨ b.sf = true ∨ b.of = true

/-- Site replacement: the zero idiom where no flag is live, explicit
    refusal where any flag survives. The consumed length is the
    canonical 3. -/
def ersetzeDurchNull (r : Register) (b : FlagBedarf) :
    Option ZeroDecodiert :=
  if darfNullen b then some (⟨r, 3⟩ : ZeroDecodiert) else none

/-- Admission is exactly dead demand, over all five flags. -/
theorem darfNullen_heisst (b : FlagBedarf) :
    darfNullen b = true ↔ ¬ Lebendig b := by
  cases b with
  | mk cf pf zf sf of =>
    cases cf <;> cases pf <;> cases zf <;> cases sf <;> cases of <;>
      simp [darfNullen, Lebendig]

/-- Refusal where a flag survives: a live demand never becomes the
    idiom. -/
theorem ersetze_verweigert_bei_lebendig (r : Register) (b : FlagBedarf)
    (h : Lebendig b) :
    ersetzeDurchNull r b = none := by
  have hf : darfNullen b = false := by
    cases hdb : darfNullen b with
    | true =>
      have hnl := (darfNullen_heisst b).mp hdb
      exact absurd h hnl
    | false => rfl
  unfold ersetzeDurchNull
  simp [hf]

/-- Admission where every flag is dead: a dead demand becomes the
    idiom at the canonical length. -/
theorem ersetze_erlaubt_bei_tot (r : Register) (b : FlagBedarf)
    (h : ¬ Lebendig b) :
    ersetzeDurchNull r b = some (⟨r, 3⟩ : ZeroDecodiert) := by
  have ht : darfNullen b = true := (darfNullen_heisst b).mpr h
  unfold ersetzeDurchNull
  simp [ht]

/-! ## 4. Joint witness data: decoded idiom feeding a memory store.

    The witness register file holds 42 in `rax` (zeroed observably by
    the idiom) with the stack top at 8192; memory is the fully
    readable/writable zeroed `zeugeSpeicher`. The demand keeps ZF live
    (the refusal side) while every other flag is dead. -/

/-- Witness register file: 42 in `rax`, the stack top at 8192. -/
def zeroZeugeReg : Register → Wort := fun q =>
  if q = Register.rax then 42
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness start state: code at 4096 over zeroed memory. -/
def zeroZeugeStart : Zustand :=
  { register := zeroZeugeReg, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := zeugeSpeicher }

/-- Witness demand: only ZF live, every other flag dead. -/
def zeroBedarfLebendig : FlagBedarf :=
  ⟨false, false, true, false, false⟩

/-- Witness run: the zero idiom, then 7 into `rbx`, then the pilot
    store of `rbx` through the stack pointer. -/
def progZero : List Decodiert :=
  [⟨.xorReg64 .rax .rax, 3⟩,
   ⟨.movImm64 .rbx 7, 10⟩,
   ⟨.store64 .rsp .rbx (BitVec.ofNat 32 0), 8⟩]

/-! ## 5. Site connection: value zero plus clobbered flags, and
    refusal where a flag survives.

    From a successful filter decode and a successful idiom step: the
    bytes are the pilot XOR-self row (no re-decision, so every
    admitted final byte executes through the common architecture),
    the register holds zero, every flag carries the zero snapshot
    (CF/OF cleared, AF undefined, ZF set, SF clear, PF set) satisfying
    the accepted `LogikGueltig`, memory is untouched, RIP advances
    past the 3 canonical bytes -- and a live demand is refused. -/

/-- The zero-idiom site connection: decoded bytes, zero value,
    clobbered flags with validity, untouched memory, advanced RIP,
    and refusal of a live demand. -/
theorem ZeroIdiomXor_verbindung (r : Register) (s s' : Zustand)
    (pfx rest : List Byte) (b : FlagBedarf)
    (hdec : decodeZero pfx = some ((⟨r, 3⟩ : ZeroDecodiert), rest))
    (hstep : zeroSchritt (⟨r, 3⟩ : ZeroDecodiert) s = some s')
    (hleb : Lebendig b) :
    decode pfx = some ((⟨.xorReg64 r r, 3⟩ : Decodiert), rest) ∧
      s'.register r = 0 ∧
      s'.flags = Flags.mk false true none true false false ∧
      s'.speicher = s.speicher ∧
      s'.rip = ripNach s.rip 3 ∧
      LogikGueltig 0 s'.flags ∧
      ersetzeDurchNull r b = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact decodeZero_ist_pilot pfx ⟨r, 3⟩ rest hdec
  · exact zeroSchritt_wert ⟨r, 3⟩ s s' hstep
  · exact zeroSchritt_flags ⟨r, 3⟩ s s' hstep
  · exact zeroSchritt_speicher ⟨r, 3⟩ s s' hstep
  · exact zeroSchritt_rip ⟨r, 3⟩ s s' hstep
  · have hfl := zeroSchritt_flags ⟨r, 3⟩ s s' hstep
    rw [hfl]
    have hg := xor_selbst_gueltig (s.register r)
    rw [xor_selbst_null, xor_selbst_flags] at hg
    exact hg
  · exact ersetze_verweigert_bei_lebendig r b hleb

/-! ## 6. Pins and planted refusals: bytes, neighbours, truncation.

    Pinned bytes ground the row: `XOR rax, rax` is REX.W, 31, C0
    (register-direct ModRM with both fields zero). Every non-idiom
    row -- every non-XOR pilot form and every distinct-register XOR
    -- is explicitly refused; truncated prefixes refuse. -/

/-- Pinned bytes: `XOR rax, rax` is REX.W, 31, C0. -/
theorem pin_zero_rax :
    encodeZero .rax = [natByte 72, natByte 49, natByte 192] := by
  decide

/-- Pinned decode: `XOR rax, rax`. -/
theorem pin_zero_rax_dekode :
    decodeZero [natByte 72, natByte 49, natByte 192] =
      some (((⟨.rax, 3⟩ : ZeroDecodiert)), []) := by
  decide

/-- Every non-XOR pilot form is explicitly refused, over any suffix:
    only the 31/r same-register row counts as the idiom. -/
theorem decodeZero_verweigert_nicht_xor (b : Befehl)
    (suffix : List Byte) (h : ∀ dst src, b ≠ .xorReg64 dst src) :
    decodeZero (encode b ++ suffix) = none := by
  unfold decodeZero
  rw [roundtrip b suffix]
  cases b with
  | xorReg64 dst src => exact absurd rfl (h dst src)
  | movImm64 _ _ => rfl
  | movReg64 _ _ => rfl
  | addReg64 _ _ => rfl
  | subReg64 _ _ => rfl
  | cmpReg64 _ _ => rfl
  | load64 _ _ _ => rfl
  | store64 _ _ _ => rfl
  | jump32 _ => rfl
  | jumpIf32 _ _ => rfl
  | call32 _ => rfl
  | push64 _ => rfl
  | pop64 _ => rfl
  | ret => rfl

/-- Neighbour pins: the closest pilot rows (MOV/ADD/SUB/CMP over the
    same registers) refuse, over any suffix. -/
theorem pin_nachbarn_verweigert (suffix : List Byte) :
    decodeZero (encode (.movReg64 .rax .rbx) ++ suffix) = none ∧
      decodeZero (encode (.addReg64 .rax .rbx) ++ suffix) = none ∧
      decodeZero (encode (.subReg64 .rax .rbx) ++ suffix) = none ∧
      decodeZero (encode (.cmpReg64 .rax .rbx) ++ suffix) = none := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    apply decodeZero_verweigert_nicht_xor <;> intros dst src <;> simp_all

/-- Truncated rows refuse: empty, lone REX, REX plus opcode without
    ModRM. -/
theorem sonde_zero_abgeschnitten :
    decodeZero [] = none ∧
      decodeZero [natByte 72] = none ∧
      decodeZero [natByte 72, natByte 49] = none := by
  decide

/-! ## 8. Byte-facing dispatcher: the idiom runs through the accepted
    unified step.

    The pilot row underlying the idiom steps through `laufAlt` (the
    accepted lift of `schritt` to `FpZustand`) and hence through the
    accepted unified dispatcher `stepExt`: XMM and the FP context are
    untouched, `kern` carries exactly the zero-idiom successor. -/

/-- The idiom step lifts to the accepted old-state lift with the zero
    successor on `kern`. -/
theorem zeroSchritt_laufAlt (r : Register) (t : FpZustand) (s' : Zustand)
    (h : zeroSchritt (⟨r, 3⟩ : ZeroDecodiert) t.kern = some s') :
    laufAlt (⟨.xorReg64 r r, 3⟩ : Decodiert) t =
      some { t with kern := s' } := by
  have h2 : schritt (⟨.xorReg64 r r, 3⟩ : Decodiert) t.kern = some s' := h
  unfold laufAlt
  rw [h2]

/-- The idiom runs through the accepted unified dispatcher: the pilot
    arm IS the zero-idiom successor on `kern`. -/
theorem zeroSchritt_stepExt (r : Register) (t : FpZustand)
    (b : BereitProfil) (s' : Zustand)
    (h : zeroSchritt (⟨r, 3⟩ : ZeroDecodiert) t.kern = some s') :
    stepExt (.pilot (⟨.xorReg64 r r, 3⟩ : Decodiert)) t b =
      .weiter { t with kern := s' } :=
  stepExt_pilot _ _ _ b (zeroSchritt_laufAlt r t s' h)

/-! ## 7. Joint witness: decoded idiom, executed zero, live refusal,
    and a memory-changing reached run.

    The canonical zero-idiom bytes decode at length 3, the accepted
    step zeroes `rax` from 42 with the zero flag snapshot, the ZF-live
    demand is refused -- and the reached three-step run stores 7
    observably (the data byte moves from 0 to 7 while every permission
    is kept). Non-degenerate: a store-changing reached execution plus
    planted refusals, jointly instantiated. -/

/-- Joint witness for `ZeroIdiomXor_verbindung`: canonical bytes, the
    executed zero step, the live-demand refusal, and a store-changing
    reached run from zeroed memory. -/
theorem ZeroIdiomXor_verbindung_zeuge :
    ∃ (s s' : Zustand) (b : FlagBedarf),
      decodeZero (encodeZero .rax) = some ((⟨.rax, 3⟩ : ZeroDecodiert), []) ∧
      zeroSchritt (⟨.rax, 3⟩ : ZeroDecodiert) s = some s' ∧
      Lebendig b ∧
      s'.register .rax = 0 ∧
      s'.flags = Flags.mk false true none true false false ∧
      (lauf progZero s).map
          (fun t => t.speicher.bytes (BitVec.ofNat 64 8192)) =
        some (BitVec.ofNat 8 7) ∧
      s.speicher.bytes (BitVec.ofNat 64 8192) = BitVec.ofNat 8 0 := by
  have hstep := schritt_xorReg64
    (⟨.xorReg64 .rax .rax, 3⟩ : Decodiert) zeroZeugeStart .rax .rax
    (by decide) rfl
  obtain ⟨s', hs'⟩ : ∃ s', schritt (⟨.xorReg64 .rax .rax, 3⟩ : Decodiert)
      zeroZeugeStart = some s' := ⟨_, hstep⟩
  have hs'' : zeroSchritt (⟨.rax, 3⟩ : ZeroDecodiert) zeroZeugeStart =
      some s' := hs'
  refine ⟨zeroZeugeStart, s', zeroBedarfLebendig, ?_, hs'', ?_, ?_, ?_, ?_, ?_⟩
  · have h := roundtripZero .rax []
    simpa using h
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact zeroSchritt_wert _ _ _ hs''
  · exact zeroSchritt_flags _ _ _ hs''
  · decide
  · rfl

/- CUTS:
    Proved here (all over the REUSED canonical `Wort.xor64`,
    `Ganzzahl.LogikGueltig`, `Ausfuehrung.schritt`/`lauf`,
    `Codec.encode`/`decode`/`roundtrip`, `ScalarFloat.laufAlt` and the
    accepted unified dispatcher `ExtendedExecution.stepExt` -- no new
    machine, no new arithmetic, no new decoder, no source claim):
    - canonical 31/r same-register bytes (`encodeZero`, length 3 within
      1..15), a pilot-parsing filter decoder (`decodeZero`, REX.W 31
      rows with equal registers only), generic round trips with
      decoded-length/suffix consistency, the filter-correctness link
      (`decodeZero_ist_pilot`: no row re-decided), general refusal of
      every non-XOR pilot form and every distinct-register XOR plus
      closed neighbour/truncation pins;
    - value zero (`xor_selbst_null`: `x ^^^ x = 0` through reused
      `xor64`), the clobbered-flag snapshot (`xor_selbst_flags`:
      CF/OF cleared, AF undefined, ZF set, SF clear, PF set) with the
      accepted validity relation (`xor_selbst_gueltig`), and the
      length-checked step (`zeroSchritt` IS the pilot step) with value,
      flag, memory-untouched, RIP and frame facts;
    - flag liveness at the site (`FlagBedarf`/`darfNullen`/`Lebendig`,
      AF absent by construction): admission exactly where no flag
      survives (`darfNullen_heisst`, `ersetze_erlaubt_bei_tot`) and
      explicit refusal where any flag survives
      (`ersetze_verweigert_bei_lebendig`);
    - the site connection (`ZeroIdiomXor_verbindung`): pilot bytes,
      zero value, clobbered flags with validity, untouched memory,
      advanced RIP and live-demand refusal;
    - the joint witness (`ZeroIdiomXor_verbindung_zeuge`): canonical
      bytes, the executed zero step from 42, the ZF-live refusal, and
      a store-changing reached run (data byte 0 to 7);
    - the byte-facing dispatcher link (`zeroSchritt_laufAlt`,
      `zeroSchritt_stepExt`): XMM/FP untouched, `kern` carries the
      zero successor.
    NOT proved here, and not claimed:
    - No hardware correspondence: encodings and flag effects follow the
      stated Intel SDM rows (combined volumes 1-4, 325462-093US, XOR
      r/m64 r64 entry and flag chapter as modelled in `Wort.lean`),
      checked here only as self-consistency, not silicon.
    - No 32-bit `XOR r32, r32` zero-extension form, no 8/16-bit forms,
      no memory-operand XOR, no `SUB r, r` idiom: only 64-bit
      register-direct 31/r is covered; everything else refuses.
    - No liveness/available-flags analysis and no optimiser claim: the
      demand is site data, never a program-wide result; nothing here
      selects instructions by itself.
    - No TSO/GX bridge (the step is register-only with no store
      buffer effect by construction), no cost/time claim, no source,
      checker, Spec or goal claim; validator refusal (`none`) is never
      an architectural fault.
-/

#print axioms encodeZero_laenge
#print axioms roundtripZero
#print axioms roundtripZero_len_ok
#print axioms decodeZero_verweigert_fremd
#print axioms decodeZero_ist_pilot
#print axioms zeroSchritt_ist_schritt
#print axioms xor_selbst_null
#print axioms xor_selbst_flags
#print axioms xor_selbst_gueltig
#print axioms zeroSchritt_ok
#print axioms zeroSchritt_wert
#print axioms zeroSchritt_flags
#print axioms zeroSchritt_speicher
#print axioms zeroSchritt_rip
#print axioms zeroSchritt_fremd
#print axioms darfNullen_heisst
#print axioms ersetze_verweigert_bei_lebendig
#print axioms ersetze_erlaubt_bei_tot
#print axioms pin_zero_rax
#print axioms pin_zero_rax_dekode
#print axioms decodeZero_verweigert_nicht_xor
#print axioms pin_nachbarn_verweigert
#print axioms sonde_zero_abgeschnitten
#print axioms zeroSchritt_laufAlt
#print axioms zeroSchritt_stepExt
#print axioms ZeroIdiomXor_verbindung
#print axioms ZeroIdiomXor_verbindung_zeuge

end Gabbro.Grammatik.X86
