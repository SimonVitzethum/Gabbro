/-
  File:      Grammatik/X86/AddressEncoding.lean
  Subject:   Efficient full selected address encodings over canonical registers.

  Lane 664: generic selected address-form parser/encoder for the §2B scope
  (disp0/disp8/disp32 smallest-first, base+index*scale+disp with REX high
  registers, absent base/index, RIP-relative, LEA purity). The pilot keeps
  its base+disp32 rows (`Codec.decode`/`Ausfuehrung.schritt` unchanged);
  this module never re-decodes them. Provenance: in-repo
  `dokumente/x86/BYTE-PILOT.md` (canonical pilot contract),
  `DIRECT-COMPILER-DESIGN.md` §§2A/2B/2D/3/3A (selected scope), and the
  accepted `Codec`/`Ausfuehrung`/`Byteschritt` modules. The lane clone has
  no `.tmp/HARDWARE-REFERENCES/REFERENCES.json`; no silicon manual page is
  claimed below (see CUTS and the lane report).
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Codec
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Byteschritt
import Grammatik.X86.ControlFlow

namespace Gabbro.Grammatik.X86

/-- Sign extension of one displacement byte to a full word. -/
def disp8Wort (b : Byte) : Wort := sext .b8 (BitVec.ofNat 64 b.toNat)

/-- Zero displacement byte extends to zero. -/
theorem disp8Wort_null : disp8Wort (natByte 0) = 0 := by
  decide

/-! ## 1. Signed 8-bit displacement boundaries. -/

/-- Displacement `-1` as one byte: every upper bit fills. -/
theorem disp8Wort_negEins : disp8Wort (natByte 255) = 0xFFFFFFFFFFFFFFFF := by
  decide

/-- Largest forward disp8: the value is kept. -/
theorem disp8Wort_maxPos : disp8Wort (natByte 127) = 127 := by
  decide

/-- Largest backward disp8: upper bits fill. -/
theorem disp8Wort_minNeg : disp8Wort (natByte 128) = 0xFFFFFFFFFFFFFF80 := by
  decide

/-- A wrong signed reading changes the value: `0x80` is `-128`,
    never `+128`. -/
theorem disp8Wort_falsch_positiv :
    disp8Wort (natByte 128) ≠ (128 : Wort) := by
  decide

/-! ## 2. SIB scale codes (architectural 1/2/4/8 only). -/

/-- Admitted scales: exactly 1, 2, 4 and 8. -/
def skalaOk (n : Nat) : Bool := decide (n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8)

/-- Scale to its two SIB bits. -/
def skalaCode : Nat → Nat
  | 1 => 0 | 2 => 1 | 4 => 2 | _ => 3

/-- Two SIB bits back to a scale. -/
def codeSkala : Nat → Nat
  | 0 => 1 | 1 => 2 | 2 => 4 | _ => 8

/-- Admitted scales round-trip through the SIB bits. -/
theorem codeSkala_skalaCode (n : Nat) (h : skalaOk n = true) :
    codeSkala (skalaCode n) = n := by
  have hp : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 := of_decide_eq_true h
  rcases hp with rfl | rfl | rfl | rfl <;> rfl

/-- Zero is no admitted scale. -/
theorem skalaOk_null : skalaOk 0 = false := by
  decide

/-- Three is no admitted scale. -/
theorem skalaOk_drei : skalaOk 3 = false := by
  decide

/-! ## 3. Canonical 48-bit virtual addresses. -/

/-- Canonical address check: the value fits the low half or the high
    half of the space (bits 63:48 repeat bit 47). -/
def kanonisch48 (a : Adresse) : Bool :=
  decide (a.toNat < 2 ^ 47 ∨ 2 ^ 64 - 2 ^ 47 ≤ a.toNat)

/-- The witness stack region is canonical. -/
theorem kanonisch48_8192 : kanonisch48 (BitVec.ofNat 64 8192) = true := by
  decide

/-- The top of the space is canonical (high half). -/
theorem kanonisch48_hoch :
    kanonisch48 (BitVec.ofNat 64 (2 ^ 64 - 8)) = true := by
  decide

/-- NONCANONICAL: bit 47 set with zero high bits is a hole. -/
theorem kanonisch48_loch :
    kanonisch48 (BitVec.ofNat 64 (2 ^ 47)) = false := by
  decide

/-! ## 4. Selected address forms (the §2B scope). -/

/-- Displacement kind: absent, one signed byte, or four little-endian
    bytes. Smallest-first choice is proved in §7. -/
inductive DispArt where
  | kein | d8 | d32
  deriving DecidableEq, Repr

/-- Consumed displacement bytes of one kind. -/
def dispLaenge : DispArt → Nat
  | .kein => 0 | .d8 => 1 | .d32 => 4

/-- Displacement lengths are within one instruction. -/
theorem dispLaenge_bereich (a : DispArt) : dispLaenge a ≤ 4 := by
  cases a <;> decide

/-- Generic selected address form over the canonical registers:
    optional base, optional index with SIB scale, displacement kind,
    and the RIP-relative flag. -/
structure AdrForm where
  base : Option Register
  index : Option Register
  skala : Nat
  disp : BitVec 32
  art : DispArt
  rip : Bool
  deriving DecidableEq, Repr

/-- One byte as a 32-bit displacement value. -/
def u8Nach32 (e : Byte) : BitVec 32 := BitVec.ofNat 32 e.toNat

/-- Admission of one form: scales only with an index, `rsp` never an
    index, RIP-relative only as disp32 without registers, absent base
    only with disp32, and `rbp`/`r13` never without displacement
    (mod=00 r/m=101 is RIP-relative, never those bases). -/
def adrOk (f : AdrForm) : Bool :=
  (match f.index with
    | none => decide (f.skala = 1)
    | some i => skalaOk f.skala && decide (i ≠ .rsp)) &&
  (if f.rip then
    match f.base, f.index, f.art with
    | none, none, .d32 => true
    | _, _, _ => false
   else true) &&
  (match f.base, f.rip with
    | none, false => decide (f.art = .d32)
    | _, _ => true) &&
  (match f.base with
    | some .rbp => decide (f.art ≠ .kein)
    | some .r13 => decide (f.art ≠ .kein)
    | _ => true)

/-- Base plus full displacement (the pilot-owned shape as data:
    the encoder below refuses it, `Codec.decode` keeps it). -/
def basisForm (b : Register) (d : BitVec 32) : AdrForm :=
  ⟨some b, none, 1, d, .d32, false⟩

/-- Base plus one displacement byte. -/
def basisDisp8Form (b : Register) (e : Byte) : AdrForm :=
  ⟨some b, none, 1, u8Nach32 e, .d8, false⟩

/-- Base without displacement. -/
def basisKeinForm (b : Register) : AdrForm :=
  ⟨some b, none, 1, BitVec.ofNat 32 0, .kein, false⟩

/-- Full scaled-index form. -/
def skaliertForm (b idx : Register) (k : Nat) (d : BitVec 32)
    (a : DispArt) : AdrForm :=
  ⟨some b, some idx, k, d, a, false⟩

/-- RIP-relative form (position-independent image data only). -/
def ripForm (d : BitVec 32) : AdrForm :=
  ⟨none, none, 1, d, .d32, true⟩

/-- Absolute disp32-only form (encoded with a SIB, never RIP). -/
def absolutForm (d : BitVec 32) : AdrForm :=
  ⟨none, none, 1, d, .d32, false⟩

/-- Index-only form (no base; disp32 only, SIB base-absent). -/
def indexForm (idx : Register) (k : Nat) (d : BitVec 32) : AdrForm :=
  ⟨none, some idx, k, d, .d32, false⟩

/-- A base outside `rbp`/`r13` with disp32 is admitted as data. -/
theorem basisForm_ok (b : Register) (d : BitVec 32)
    (hb : b ≠ .rbp) (h13 : b ≠ .r13) :
    adrOk (basisForm b d) = true := by
  simp [basisForm, adrOk, hb, h13]

/-- A base outside `rbp`/`r13` with disp8 is admitted. -/
theorem basisDisp8Form_ok (b : Register) (e : Byte)
    (hb : b ≠ .rbp) (h13 : b ≠ .r13) :
    adrOk (basisDisp8Form b e) = true := by
  simp [basisDisp8Form, adrOk, u8Nach32, hb, h13]

/-- A base outside `rbp`/`r13` without displacement is admitted. -/
theorem basisKeinForm_ok (b : Register)
    (hb : b ≠ .rbp) (h13 : b ≠ .r13) :
    adrOk (basisKeinForm b) = true := by
  simp [basisKeinForm, adrOk, hb, h13]

/-- The RIP-relative form is admitted. -/
theorem ripForm_ok (d : BitVec 32) : adrOk (ripForm d) = true := by
  rfl

/-- The absolute disp32-only form is admitted. -/
theorem absolutForm_ok (d : BitVec 32) : adrOk (absolutForm d) = true := by
  rfl

/-- REFUSAL: `rsp` is never an index (SIB index 100 means absent). -/
theorem skaliertForm_rsp_verweigert (b : Register) (k : Nat)
    (d : BitVec 32) (a : DispArt) :
    adrOk (skaliertForm b .rsp k d a) = false := by
  simp [skaliertForm, adrOk]

/-- REFUSAL: `rbp` as a base needs a displacement. -/
theorem basisKeinForm_rbp_verweigert :
    adrOk (basisKeinForm .rbp) = false := by
  decide

/-! ## 5. Effective addresses: pure arithmetic, never a memory read. -/

/-- The displacement value of one form: absent is zero, disp8 is the
    sign-extended low byte, disp32 is the sign-extended word. -/
def dispWortArt (f : AdrForm) : Wort :=
  match f.art with
  | .kein => 0
  | .d8 => disp8Wort (natByte (f.disp.toNat % 256))
  | .d32 => dispWort f.disp

/-- A disp8 form carries the sign extension of its byte. -/
theorem dispWortArt_d8 (bo bi : Option Register) (k : Nat) (e : Byte)
    (r : Bool) :
    dispWortArt ⟨bo, bi, k, u8Nach32 e, .d8, r⟩ = disp8Wort e := by
  have he := e.isLt
  have hmod : (u8Nach32 e).toNat % 256 = e.toNat := by
    unfold u8Nach32
    rw [BitVec.toNat_ofNat]
    have h1 : e.toNat % 2 ^ 32 = e.toNat :=
      Nat.mod_eq_of_lt (by omega)
    rw [h1]
    exact Nat.mod_eq_of_lt he
  simp only [dispWortArt, hmod]
  have hbyte : natByte (e.toNat) = e := by
    have h0 := natByte_byteNat e
    simpa [byteNat] using h0
  rw [hbyte]

/-- Sign extension agrees across widths: the `-1` byte names the same
    offset as the `-1` double word. -/
theorem disp8_d32_gleich_negEins :
    dispWortArt ⟨none, none, 1, BitVec.ofNat 32 4294967295, .d32, true⟩ =
      disp8Wort (natByte 255) := by
  decide

/-- Generic selected effective address: the RIP-next value for
    RIP-relative forms, else base, plus index times scale, plus the
    sign-extended displacement. Pure word arithmetic only. -/
def adrEff (s : Zustand) (ripNext : Adresse) (f : AdrForm) : Adresse :=
  let b : Wort :=
    match f.base with
    | some r => s.register r
    | none => 0
  let x : Wort :=
    match f.index with
    | some r => s.register r * BitVec.ofNat 64 f.skala
    | none => 0
  match f.rip with
  | true => ripNext + x + dispWortArt f
  | false => b + x + dispWortArt f

/-- BRIDGE: a base-plus-disp32 form IS the pilot address. -/
theorem adrEff_basisForm (s : Zustand) (b : Register) (d : BitVec 32)
    (n : Adresse) :
    adrEff s n (basisForm b d) = effAddr s b d := by
  simp [adrEff, basisForm, dispWortArt, effAddr]

/-- The unscaled scaled form is the pilot address (no second model). -/
theorem adrEff_skaliert_eins (s : Zustand) (b idx : Register)
    (d : BitVec 32) (a : DispArt) (n : Adresse)
    (h0 : s.register idx = 0) :
    adrEff s n (skaliertForm b idx 1 d a) =
      adrEff s n ⟨some b, none, 1, d, a, false⟩ := by
  simp [adrEff, skaliertForm, h0, dispWortArt]

/-- The address reads two registers only: same base and index values
    give the same scaled address. -/
theorem adrEff_skaliert_prestate (s1 s2 : Zustand) (b idx : Register)
    (k : Nat) (d : BitVec 32) (a : DispArt) (n : Adresse)
    (hb : s1.register b = s2.register b)
    (hi : s1.register idx = s2.register idx) :
    adrEff s1 n ⟨some b, some idx, k, d, a, false⟩ =
      adrEff s2 n ⟨some b, some idx, k, d, a, false⟩ := by
  simp [adrEff, hb, hi]

/-- The RIP-relative address reads the next RIP only. -/
theorem adrEff_rip_prestate (s : Zustand) (n1 n2 : Adresse)
    (d : BitVec 32) (h : n1 = n2) :
    adrEff s n1 (ripForm d) = adrEff s n2 (ripForm d) := by
  simp [adrEff, ripForm, h]

/-- RELOCATION (from bytes, not trusted input): moving the base by `t`
    moves a scaled address by `t`, modularly. -/
theorem adrEff_verschiebung (s1 s2 : Zustand) (b idx : Register)
    (k : Nat) (d : BitVec 32) (a : DispArt) (n : Adresse) (t : Wort)
    (hb : s2.register b = s1.register b + t)
    (hi : s2.register idx = s1.register idx) :
    adrEff s2 n ⟨some b, some idx, k, d, a, false⟩ =
      adrEff s1 n ⟨some b, some idx, k, d, a, false⟩ + t := by
  simp only [adrEff, hb, hi]
  ac_rfl

/-! ## 6. LEA: pure address arithmetic, no flags, no memory event. -/

/-- LEA step: the destination holds the selected address, RIP advances
    past `l`; flags and memory are untouched by construction. -/
def leaFormSchritt (dst : Register) (f : AdrForm) (l : Nat) (s : Zustand)
    (ripNext : Adresse) : Option Zustand :=
  match laengeOk l with
  | false => none
  | true => some { s with register := regSet s.register dst (adrEff s ripNext f), rip := ripNach s.rip l }

/-- LEA writes exactly the destination register. -/
theorem leaFormSchritt_dst (dst : Register) (f : AdrForm) (l : Nat)
    (s s' : Zustand) (ripNext : Adresse)
    (hok : laengeOk l = true)
    (hstep : leaFormSchritt dst f l s ripNext = some s') :
    s'.register dst = adrEff s ripNext f := by
  unfold leaFormSchritt at hstep
  rw [hok] at hstep
  cases hstep
  simp [regSet]

/-- LEA never clobbers flags. -/
theorem leaFormSchritt_flags (dst : Register) (f : AdrForm) (l : Nat)
    (s s' : Zustand) (ripNext : Adresse)
    (hok : laengeOk l = true)
    (hstep : leaFormSchritt dst f l s ripNext = some s') :
    s'.flags = s.flags := by
  unfold leaFormSchritt at hstep
  rw [hok] at hstep
  cases hstep
  rfl

/-- LEA is no memory event: every byte is kept. -/
theorem leaFormSchritt_speicher (dst : Register) (f : AdrForm) (l : Nat)
    (s s' : Zustand) (ripNext : Adresse)
    (hok : laengeOk l = true)
    (hstep : leaFormSchritt dst f l s ripNext = some s') :
    s'.speicher = s.speicher := by
  unfold leaFormSchritt at hstep
  rw [hok] at hstep
  cases hstep
  rfl

/-- LEA keeps every other register. -/
theorem leaFormSchritt_fremd (dst q : Register) (f : AdrForm) (l : Nat)
    (s s' : Zustand) (ripNext : Adresse)
    (hok : laengeOk l = true)
    (hstep : leaFormSchritt dst f l s ripNext = some s')
    (hq : q ≠ dst) :
    s'.register q = s.register q := by
  unfold leaFormSchritt at hstep
  rw [hok] at hstep
  cases hstep
  exact regSet_fremd s.register dst q (adrEff s ripNext f) hq

/-- A bad length refuses the LEA. -/
theorem leaFormSchritt_laenge_verweigert (dst : Register) (f : AdrForm)
    (l : Nat) (s : Zustand) (ripNext : Adresse)
    (h : laengeOk l = false) :
    leaFormSchritt dst f l s ripNext = none := by
  unfold leaFormSchritt
  simp [h]

/-- BRIDGE to the accepted pilot LEA (`ControlFlow.leaAnwenden`): on a
    base-plus-disp32 form the selected LEA reaches exactly the pilot
    LEA state. The old pilot is reused, never redefined. -/
theorem leaFormSchritt_basisForm (dst b : Register) (d : BitVec 32)
    (l : Nat) (s : Zustand) (ripNext : Adresse)
    (hok : laengeOk l = true) :
    leaFormSchritt dst (basisForm b d) l s ripNext =
      some ({ leaAnwenden s dst b d with rip := ripNach s.rip l }) := by
  unfold leaFormSchritt leaAnwenden
  rw [hok, adrEff_basisForm]

/-! ## 7. Canonical encoder: REX/ModRM/SIB/displacement bytes.

    The pilot keeps mod=10 base-plus-disp32 (`Codec.decode`); the arms
    below return `none` there, so no accepted pilot form is re-decided.
    REX.X carries a high index register, which the pilot refuses. -/

/-- REX.W prefix with R/X/B extension bits. -/
def rexAddr (r x b : Nat) : Byte :=
  natByte (72 + 4 * (r % 2) + 2 * (x % 2) + b % 2)

/-- Without an index extension it is the pilot REX. -/
theorem rexAddr_ohne_x (r b : Nat) (hr : r < 2) (hb : b < 2) :
    rexAddr r 0 b = rexByte r b := by
  unfold rexAddr rexByte
  rw [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hb]
  simp

/-- ModRM byte over a mod field and two 3-bit codes. -/
def modrmByte (mod reg rm : Nat) : Byte :=
  natByte (mod * 64 + (reg % 8) * 8 + rm % 8)

/-- SIB byte over scale bits and two 3-bit codes. -/
def sibByte (sk idx base : Nat) : Byte :=
  natByte ((sk % 4) * 64 + (idx % 8) * 8 + base % 8)

/-- The REX byte of one form: R from the reg field, X from the index,
    B from the base. -/
def rexFuer (reg : Register) (f : AdrForm) : Byte :=
  let r := regHigh reg
  let x := match f.index with | some i => regHigh i | none => 0
  let b := match f.base with | some q => regHigh q | none => 0
  rexAddr r x b

/-- Canonical tail bytes (REX + ModRM [+ SIB] [+ displacement]) of one
    selected form for one reg field. Base-only disp32 is pilot-owned
    and refused; index-only admits disp32 only (SIB base-absent forces
    four displacement bytes). -/
def encodeAdr (reg : Register) (f : AdrForm) : Option (List Byte) :=
  match adrOk f with
  | false => none
  | true =>
    let rex := rexFuer reg f
    let rl := regLow reg
    match f.base, f.index, f.art, f.rip with
    | none, none, .d32, true =>
      some (rex :: modrmByte 0 rl 5 :: leBytes32 f.disp)
    | none, none, .d32, false =>
      some (rex :: modrmByte 0 rl 4 :: sibByte 0 4 5 :: leBytes32 f.disp)
    | none, some idx, _, false =>
      match f.art with
      | .d32 =>
        some (rex :: modrmByte 0 rl 4 :: sibByte (skalaCode f.skala) (regLow idx) 5 :: leBytes32 f.disp)
      | _ => none
    | some b, none, _, false =>
      if regLow b == 4 then
        match f.art with
        | .kein => some [rex, modrmByte 0 rl 4, sibByte 0 4 4]
        | .d8 => some (rex :: modrmByte 1 rl 4 :: sibByte 0 4 4 :: [natByte (f.disp.toNat % 256)])
        | .d32 => none
      else
        match f.art with
        | .kein => some [rex, modrmByte 0 rl (regLow b)]
        | .d8 => some (rex :: modrmByte 1 rl (regLow b) :: [natByte (f.disp.toNat % 256)])
        | .d32 => none
    | some b, some idx, _, false =>
      match f.art with
      | .kein => some [rex, modrmByte 0 rl 4, sibByte (skalaCode f.skala) (regLow idx) (regLow b)]
      | .d8 => some (rex :: modrmByte 1 rl 4 :: sibByte (skalaCode f.skala) (regLow idx) (regLow b) :: [natByte (f.disp.toNat % 256)])
      | .d32 => some (rex :: modrmByte 2 rl 4 :: sibByte (skalaCode f.skala) (regLow idx) (regLow b) :: leBytes32 f.disp)
    | _, _, _, _ => none

/-- An encoding needs an admitted form. -/
theorem encodeAdr_braucht_ok (reg : Register) (f : AdrForm)
    (bs : List Byte) (h : encodeAdr reg f = some bs) :
    adrOk f = true := by
  unfold encodeAdr at h
  cases hbf : adrOk f with
  | false =>
    simp only [hbf] at h
    cases h
  | true => rfl

/-- PILOT OWNS base-plus-disp32: the encoder refuses it. -/
theorem encodeAdr_pilot_basis :
    encodeAdr .rax (basisForm .rbx (BitVec.ofNat 32 5)) = none := by
  decide

/-- PILOT OWNS the SIB-36 disp32 shape: refused here too. -/
theorem encodeAdr_pilot_rsp :
    encodeAdr .rax ⟨some .rsp, none, 1, BitVec.ofNat 32 5, .d32, false⟩ =
      none := by
  decide

/-- Consumed lengths, pinned per shape: base without displacement. -/
theorem encodeAdr_laenge_basisKein :
    (encodeAdr .rax (basisKeinForm .rbx)).map List.length = some 2 := by
  decide

/-- Consumed lengths: base through `rsp` needs the SIB byte. -/
theorem encodeAdr_laenge_basisKein_rsp :
    (encodeAdr .rax (basisKeinForm .rsp)).map List.length = some 3 := by
  decide

/-- Consumed lengths: base plus one displacement byte. -/
theorem encodeAdr_laenge_basisDisp8 :
    (encodeAdr .rax (basisDisp8Form .rbx (natByte 5))).map List.length =
      some 3 := by
  decide

/-- Consumed lengths: scaled index plus one displacement byte. -/
theorem encodeAdr_laenge_skaliertDisp8 :
    (encodeAdr .rax (skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8)).map
      List.length = some 4 := by
  decide

/-- Consumed lengths: scaled index plus four displacement bytes. -/
theorem encodeAdr_laenge_skaliertDisp32 :
    (encodeAdr .rax (skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d32)).map
      List.length = some 7 := by
  decide

/-- Consumed lengths: RIP-relative. -/
theorem encodeAdr_laenge_rip :
    (encodeAdr .rax (ripForm (BitVec.ofNat 32 4089))).map List.length =
      some 6 := by
  decide

/-- Consumed lengths: absolute disp32-only through a SIB. -/
theorem encodeAdr_laenge_absolut :
    (encodeAdr .rax (absolutForm (BitVec.ofNat 32 8192))).map List.length =
      some 7 := by
  decide

/-- REFUSAL: index-only with disp8 is unencodable (SIB base-absent
    forces disp32). -/
theorem encodeAdr_indexDisp8_verweigert :
    encodeAdr .rax ⟨none, some .rcx, 8, u8Nach32 (natByte 5), .d8, false⟩ =
      none := by
  decide

/-! ## 8. Compact displacement choice: smallest first. -/

/-- A displacement fits one signed byte. -/
def passtIn8 (d : BitVec 32) : Bool :=
  decide (d.toNat < 128 ∨ 2 ^ 32 - 128 ≤ d.toNat)

/-- Smallest-first selector. -/
def kompaktArt (d : BitVec 32) : DispArt :=
  if passtIn8 d then .d8 else .d32

/-- A fitting displacement takes the byte form. -/
theorem kompaktArt_klein (d : BitVec 32) (h : passtIn8 d = true) :
    kompaktArt d = .d8 := by
  simp [kompaktArt, h]

/-- A large displacement takes the double-word form. -/
theorem kompaktArt_gross (d : BitVec 32) (h : passtIn8 d = false) :
    kompaktArt d = .d32 := by
  simp [kompaktArt, h]

/-- Pins: 5 and -1 fit, 1000 does not. -/
theorem kompaktArt_beispiele :
    kompaktArt (BitVec.ofNat 32 5) = .d8 ∧
      kompaktArt (BitVec.ofNat 32 4294967295) = .d8 ∧
      kompaktArt (BitVec.ofNat 32 1000) = .d32 := by
  decide

/-- COMPACT: the byte form saves three bytes at the same address. -/
theorem kompakt_ersparnis :
    ((encodeAdr .rax (skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8)).map
      List.length = some 4) ∧
    ((encodeAdr .rax (skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d32)).map
      List.length = some 7) ∧
    adrEff zeugeZustand (BitVec.ofNat 64 0)
        (skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8) =
      adrEff zeugeZustand (BitVec.ofNat 64 0)
        (skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d32) := by
  decide

/-! ## 9. Parser: ModRM/SIB/displacement back to selected forms.

    mod=10 base-only and mod=10 SIB-36 are pilot-owned and refused, so
    no accepted pilot form is re-decided. mod=11 (register-direct) is
    refused: it names no address. -/

/-- SIB index field: 100 with X=0 is absent, else the extended register. -/
def sibReg (x ii : Nat) : Option (Option Register) :=
  if ii == 4 && x == 0 then some none
  else
    match codeReg (x * 8 + ii) with
    | some q => some (some q)
    | none => none

/-- Parse one ModRM/SIB/displacement tail under REX bits R/X/B into
    the reg field, the selected form and the remaining bytes. -/
def parseAdrTail (r x b : Nat) :
    List Byte → Option (Register × AdrForm × List Byte)
  | [] => none
  | m :: rest =>
    let mod := byteNat m / 64
    let rg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    match codeReg (r * 8 + rg) with
    | none => none
    | some regR =>
      if mod == 3 then none
      else if mod == 2 then
        if rm == 4 then
          match rest with
          | [] => none
          | sib :: rest2 =>
            if byteNat sib == 36 && x == 0 then none
            else
              let sk := byteNat sib / 64
              let ii := byteNat sib / 8 % 8
              let bb := byteNat sib % 8
              match sibReg x ii, codeReg (b * 8 + bb) with
              | some idxO, some baseR =>
                match parseLe32 rest2 with
                | some (d, rest3) =>
                  some (regR, ⟨some baseR, idxO, codeSkala sk, d, .d32, false⟩, rest3)
                | none => none
              | _, _ => none
        else none
      else if mod == 1 then
        if rm == 4 then
          match rest with
          | [] => none
          | _ :: [] => none
          | sib :: e :: rest2 =>
            let sk := byteNat sib / 64
            let ii := byteNat sib / 8 % 8
            let bb := byteNat sib % 8
            match sibReg x ii, codeReg (b * 8 + bb) with
            | some idxO, some baseR =>
              some (regR, ⟨some baseR, idxO, codeSkala sk, u8Nach32 e, .d8, false⟩, rest2)
            | _, _ => none
        else
          match rest with
          | [] => none
          | e :: rest2 =>
            match codeReg (b * 8 + rm) with
            | some baseR =>
              some (regR, ⟨some baseR, none, 1, u8Nach32 e, .d8, false⟩, rest2)
            | none => none
      else
        if rm == 5 then
          match parseLe32 rest with
          | some (d, rest') => some (regR, ripForm d, rest')
          | none => none
        else if rm == 4 then
          match rest with
          | [] => none
          | sib :: rest2 =>
            let sk := byteNat sib / 64
            let ii := byteNat sib / 8 % 8
            let bb := byteNat sib % 8
            if bb == 5 then
              match sibReg x ii, parseLe32 rest2 with
              | some idxO, some (d, rest3) =>
                some (regR, ⟨none, idxO, codeSkala sk, d, .d32, false⟩, rest3)
              | _, _ => none
            else
              match sibReg x ii, codeReg (b * 8 + bb) with
              | some idxO, some baseR =>
                some (regR, ⟨some baseR, idxO, codeSkala sk, BitVec.ofNat 32 0, .kein, false⟩, rest2)
              | _, _ => none
        else
          match codeReg (b * 8 + rm) with
          | some baseR =>
            some (regR, ⟨some baseR, none, 1, BitVec.ofNat 32 0, .kein, false⟩, rest)
          | none => none

/-! ## 10. Codec round trips, pinned per shape. -/

/-- ROUND TRIP: scaled index plus disp8. -/
theorem rundweg_skaliertDisp8 :
    parseAdrTail 0 0 0 [natByte 68, natByte 203, natByte 5] =
      some (.rax, skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8, []) := by
  decide

/-- ROUND TRIP: scaled index with high registers plus disp32
    (REX 75 carries X=1 and B=1). -/
theorem rundweg_skaliertHoch :
    parseAdrTail 0 1 1
      [natByte 132, natByte 136, natByte 16, natByte 0, natByte 0,
        natByte 0] =
      some (.rax, skaliertForm .r8 .r9 4 (BitVec.ofNat 32 16) .d32, []) := by
  decide

/-- ROUND TRIP: base plus disp8. -/
theorem rundweg_basisDisp8 :
    parseAdrTail 0 0 0 [natByte 67, natByte 5] =
      some (.rax, basisDisp8Form .rbx (natByte 5), []) := by
  decide

/-- ROUND TRIP: base without displacement. -/
theorem rundweg_basisKein :
    parseAdrTail 0 0 0 [natByte 3] =
      some (.rax, basisKeinForm .rbx, []) := by
  decide

/-- ROUND TRIP: RIP-relative. -/
theorem rundweg_rip :
    parseAdrTail 0 0 0
      [natByte 5, natByte 249, natByte 15, natByte 0, natByte 0] =
      some (.rax, ripForm (BitVec.ofNat 32 4089), []) := by
  decide

/-- ROUND TRIP: absolute disp32-only through a SIB. -/
theorem rundweg_absolut :
    parseAdrTail 0 0 0
      [natByte 4, natByte 37, natByte 0, natByte 32, natByte 0,
        natByte 0] =
      some (.rax, absolutForm (BitVec.ofNat 32 8192), []) := by
  decide

/-- ROUND TRIP: index-only with disp32. -/
theorem rundweg_indexForm :
    parseAdrTail 0 0 0
      [natByte 4, natByte 205, natByte 8, natByte 0, natByte 0,
        natByte 0] =
      some (.rax, indexForm .rcx 8 (BitVec.ofNat 32 8), []) := by
  decide

/-- Parsed scaled forms are admitted. -/
theorem rundweg_form_ok :
    adrOk (skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8) = true ∧
      adrOk (skaliertForm .r8 .r9 4 (BitVec.ofNat 32 16) .d32) = true ∧
      adrOk (ripForm (BitVec.ofNat 32 4089)) = true ∧
      adrOk (absolutForm (BitVec.ofNat 32 8192)) = true ∧
      adrOk (indexForm .rcx 8 (BitVec.ofNat 32 8)) = true := by
  decide

/-! ## 11. No second decoder: the pilot keeps its rows. -/

/-- The parser refuses the pilot base-plus-disp32 tail. -/
theorem parser_weist_pilot_basis_zurueck :
    parseAdrTail 0 0 0
      [natByte 131, natByte 5, natByte 0, natByte 0, natByte 0] = none := by
  decide

/-- The parser refuses the pilot SIB-36 tail. -/
theorem parser_weist_pilot_sib_zurueck :
    parseAdrTail 0 0 0
      [natByte 132, natByte 36, natByte 16, natByte 0, natByte 0,
        natByte 0] = none := by
  decide

/-- The pilot refuses X-extended bytes (no 0x4B-class REX there). -/
theorem pilot_weist_x_zurueck :
    decode [natByte 75, natByte 139, natByte 132, natByte 136,
      natByte 16, natByte 0, natByte 0, natByte 0] = none := by
  decide

/-- REFUSAL: empty input. -/
theorem parser_verweigert_leer : parseAdrTail 0 0 0 [] = none := rfl

/-- REFUSAL: register-direct names no address. -/
theorem parser_verweigert_mod3 :
    parseAdrTail 0 0 0 [natByte 192] = none := by
  decide

/-- REFUSAL: missing SIB byte (truncated). -/
theorem parser_verweigert_ohne_sib :
    parseAdrTail 0 0 0 [natByte 68] = none := by
  decide

/-- REFUSAL: SIB present but the displacement byte missing. -/
theorem parser_verweigert_kurze_disp8 :
    parseAdrTail 0 0 0 [natByte 68, natByte 203] = none := by
  decide

/-- REFUSAL: wrong signed displacement is a different address, never
    silently the same: `0xFF` is `-1`, not `255`. -/
theorem falsche_disp8_aendert_adresse :
    adrEff zeugeZustand (BitVec.ofNat 64 0)
        ⟨some .rbx, none, 1, u8Nach32 (natByte 255), .d8, false⟩ ≠
      adrEff zeugeZustand (BitVec.ofNat 64 0)
        ⟨some .rbx, none, 1, BitVec.ofNat 32 255, .d32, false⟩ := by
  decide

/-- ROUND TRIP: base `rsp` without displacement needs its SIB byte. -/
theorem rundweg_basisKein_rsp :
    parseAdrTail 0 0 0 [natByte 4, natByte 36] =
      some (.rax, basisKeinForm .rsp, []) := by
  decide

/-! ## 12. Full byte forms: LEA (8D) and indexed store (89).

    Neither opcode is accepted by the pilot (`Codec.decode` refuses
    0x8D everywhere and 0x89 only in its mod=10 rows), so both forms
    extend the dispatcher without shadowing it. -/

/-- LEA bytes: REX.W (72..79) plus 0x8D plus a selected tail.
    A missing REX.W or a legacy prefix refuses. -/
def decodeLea : List Byte → Option (Register × AdrForm × List Byte)
  | [] => none
  | r :: rest =>
    if 72 ≤ byteNat r ∧ byteNat r < 80 then
      let rv := byteNat r - 72
      let rBit := rv / 4
      let xBit := rv / 2 % 2
      let bBit := rv % 2
      match rest with
      | [] => none
      | op :: rest2 =>
        if byteNat op == 141 then parseAdrTail rBit xBit bBit rest2
        else none
    else none

/-- LEA pin: scaled index plus disp8 through bytes. -/
theorem lea_dekodiert_skaliert :
    decodeLea [natByte 72, natByte 141, natByte 68, natByte 203,
      natByte 5] =
      some (.rax, skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8, []) := by
  decide

/-- LEA pin: high registers through an X-extended REX. -/
theorem lea_dekodiert_hoch :
    decodeLea [natByte 75, natByte 141, natByte 132, natByte 136,
      natByte 16, natByte 0, natByte 0, natByte 0] =
      some (.rax, skaliertForm .r8 .r9 4 (BitVec.ofNat 32 16) .d32, []) := by
  decide

/-- LEA pin: RIP-relative image reference. -/
theorem lea_dekodiert_rip :
    decodeLea [natByte 72, natByte 141, natByte 5, natByte 249,
      natByte 15, natByte 0, natByte 0] =
      some (.rax, ripForm (BitVec.ofNat 32 4089), []) := by
  decide

/-- The pilot refuses every LEA byte string (0x8D is no pilot opcode). -/
theorem pilot_weist_lea_zurueck :
    decode [natByte 72, natByte 141, natByte 68, natByte 203,
      natByte 5] = none := by
  decide

/-- REFUSAL: a legacy operand-size prefix before LEA. -/
theorem lea_verweigert_vorsatz :
    decodeLea [natByte 102, natByte 72, natByte 141, natByte 68,
      natByte 203, natByte 5] = none := by
  decide

/-- REFUSAL: LEA without REX.W (64-bit address arithmetic needs it). -/
theorem lea_verweigert_ohne_rex :
    decodeLea [natByte 141, natByte 68, natByte 203, natByte 5] = none := by
  decide

/-- Indexed store bytes: REX.W plus 0x89 plus a selected tail.
    Pilot-owned tails stay refused by `parseAdrTail`. -/
def decodeStoreIdx : List Byte → Option (Register × AdrForm × List Byte)
  | [] => none
  | r :: rest =>
    if 72 ≤ byteNat r ∧ byteNat r < 80 then
      let rv := byteNat r - 72
      let rBit := rv / 4
      let xBit := rv / 2 % 2
      let bBit := rv % 2
      match rest with
      | [] => none
      | op :: rest2 =>
        if byteNat op == 137 then parseAdrTail rBit xBit bBit rest2
        else none
    else none

/-- Store pin: high base and index through an X-extended REX. -/
theorem store_dekodiert_hoch :
    decodeStoreIdx [natByte 75, natByte 137, natByte 68, natByte 200,
      natByte 0] =
      some (.rax,
        ⟨some .r8, some .r9, 8, u8Nach32 (natByte 0), .d8, false⟩, []) := by
  decide

/-- The pilot-owned store tail stays refused here too. -/
theorem store_weist_pilot_basis_zurueck :
    decodeStoreIdx [natByte 72, natByte 137, natByte 131, natByte 5,
      natByte 0, natByte 0, natByte 0] = none := by
  decide

/-- REFUSAL: a store without REX.W is not canonical. -/
theorem store_verweigert_ohne_rex :
    decodeStoreIdx [natByte 137, natByte 68, natByte 200, natByte 0] =
      none := by
  decide

/-! ## 13. Fetched byte steps over actual executable memory. -/

/-- One fetched LEA step: decode the actual fetched window, run the
    pure address write with the post-decode RIP as the RIP base. -/
def leaGeholtSchritt (s : Zustand) : Option Zustand :=
  match decodeLea (geholt s) with
  | none => none
  | some (dst, f, rest) =>
    let l := (geholt s).length - rest.length
    match laengeOk l with
    | false => none
    | true => leaFormSchritt dst f l s (ripNach s.rip l)

/-- One fetched indexed-store step: the source register lands through
    the selected address; permissions decide loudly. -/
def adrStoreSchritt (s : Zustand) : Option Zustand :=
  match decodeStoreIdx (geholt s) with
  | none => none
  | some (srcR, f, rest) =>
    let l := (geholt s).length - rest.length
    match laengeOk l with
    | false => none
    | true =>
      match write64 s.speicher (adrEff s (ripNach s.rip l) f) (s.register srcR) with
      | some m => some { s with speicher := m, rip := ripNach s.rip l }
      | none => none

/-! ## 14. Footprint admission: mapping, no-wrap, permissions.

    The computed address admits its eight-byte footprint only under
    the canonical-address check, the no-wrap range and the per-byte
    rights; relocation moves the base, and the displacement travels
    in the checked final bytes (`parseLe32_leBytes32`). -/

/-- Under no-wrap the footprint bytes of a selected address are Nat
    additions. -/
theorem adrFuss_addrs (s : Zustand) (ripNext : Adresse) (f : AdrForm)
    (h : OhneUmbruch (adrEff s ripNext f)) (i : Nat) (hi : i < 8) :
    (addrOff (adrEff s ripNext f) i).toNat =
      (adrEff s ripNext f).toNat + i :=
  ohneUmbruch_addrs _ h i hi

/-- Read rights admit a read at the selected address. -/
theorem adrLesen_erlaubt (m : Speicher) (s : Zustand) (ripNext : Adresse)
    (f : AdrForm) (h : lesbar8 m (adrEff s ripNext f) = true) :
    ∃ v, read64 m (adrEff s ripNext f) = some v := by
  exact ⟨bytesWort (readBytes m (adrEff s ripNext f)), by simp [read64, h]⟩

/-- Write rights admit a write at the selected address. -/
theorem adrSchreiben_erlaubt (m : Speicher) (s : Zustand)
    (ripNext : Adresse) (f : AdrForm)
    (h : schreibbar8 m (adrEff s ripNext f) = true) :
    ∃ m', write64 m (adrEff s ripNext f) (s.register .rax) = some m' := by
  exact ⟨{ m with bytes := writeBytes m (adrEff s ripNext f) (s.register .rax) }, by simp [write64, h]⟩

/-- A successful selected store keeps every permission. -/
theorem adrStore_berechtigungen (m m' : Speicher) (s : Zustand)
    (ripNext : Adresse) (f : AdrForm) (v : Wort)
    (hwr : write64 m (adrEff s ripNext f) v = some m') :
    m'.lesbar = m.lesbar ∧ m'.schreibbar = m.schreibbar ∧
      m'.ausfuehrbar = m.ausfuehrbar :=
  write64_erhaelt_berechtigungen m (adrEff s ripNext f) v m' hwr

/-- WRAP REFUSAL: the top of the space admits no eight-byte footprint. -/
theorem adrFuss_verweigert_rand :
    ¬ OhneUmbruch (BitVec.ofNat 64 (2 ^ 64 - 4)) := by
  unfold OhneUmbruch
  decide

/-- Full footprint admission: canonical address, no wrap, and the
    rights of the access direction. -/
def fussZugelassen (m : Speicher) (a : Adresse) (schreiben : Bool) : Bool :=
  kanonisch48 a && decide (a.toNat + 8 ≤ 2 ^ 64) &&
    (if schreiben then schreibbar8 m a else lesbar8 m a)

/-- The checked displacement travels in the final bytes. -/
theorem bildDisp_trifft (d : BitVec 32) (suffix : List Byte) :
    parseLe32 (leBytes32 d ++ suffix) = some (d, suffix) :=
  parseLe32_leBytes32 d suffix

/-- Pin: the RIP-reference displacement parses out of final bytes. -/
theorem bildDisp_pin_4089 :
    parseLe32 [natByte 249, natByte 15, natByte 0, natByte 0] =
      some (BitVec.ofNat 32 4089, []) := by
  decide

/-! ## 15. Reached witnesses: fetched LEA and scaled store.

    Both witnesses fetch CLOSED bytes from actual executable memory:
    the LEA computes `rbx + rcx * 8 + 5 = 8205` into `rax` without
    touching flags or memory, and the high-register scaled store
    writes `rax = 42` through `r8 + r9 * 8 = 8200`, observably
    changing data memory from zero. -/

/-- LEA witness image: `lea rax, [rbx + rcx*8 + 5]`. -/
def leaWitBild : List Byte :=
  [natByte 72, natByte 141, natByte 68, natByte 203, natByte 5]

/-- LEA witness code bytes: the image at 4096, zeroes elsewhere. -/
def leaWitBytes (a : Adresse) : Byte :=
  if a.toNat < 4096 then BitVec.ofNat 8 0
  else
    match leaWitBild[a.toNat - 4096]? with
    | some b => b
    | none => BitVec.ofNat 8 0

/-- LEA witness execute permission: exactly the five image bytes. -/
def leaWitCode (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4101)

/-- LEA witness data permission: sixteen bytes at 8192. -/
def leaWitDaten (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8208)

/-- LEA witness memory: code is execute-only, data read/write-only. -/
def leaWitSpeicher : Speicher :=
  { bytes := leaWitBytes, lesbar := leaWitDaten,
    schreibbar := leaWitDaten, ausfuehrbar := leaWitCode }

/-- LEA witness registers: `rbx = 8192`, `rcx = 1`. -/
def leaWitReg : Register → Wort
  | .rax => BitVec.ofNat 64 0
  | .rbx => BitVec.ofNat 64 8192
  | .rcx => BitVec.ofNat 64 1
  | .rsp => BitVec.ofNat 64 8704
  | _ => BitVec.ofNat 64 0

/-- LEA witness start state: code at 4096. -/
def leaWitZustand : Zustand :=
  { register := leaWitReg, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := leaWitSpeicher }

/-- The fetched LEA computes `8192 + 8 + 5 = 8205` into `rax`. -/
theorem leaWit_rechnet :
    (leaGeholtSchritt leaWitZustand).map (fun s => s.register .rax) =
      some (BitVec.ofNat 64 8205) := by
  decide

/-- The fetched LEA keeps the flags. -/
theorem leaWit_flags :
    (leaGeholtSchritt leaWitZustand).map (fun s => s.flags) =
      some zeugeFlags := by
  decide

/-- The fetched LEA is no memory event: the data byte stays zero. -/
theorem leaWit_speicher_ruht :
    (leaGeholtSchritt leaWitZustand).map
      (fun s => s.speicher.bytes (BitVec.ofNat 64 8205)) =
      some (BitVec.ofNat 8 0) := by
  decide

/-- The fetched LEA advances RIP past its five bytes. -/
theorem leaWit_rip :
    (leaGeholtSchritt leaWitZustand).map (fun s => s.rip) =
      some (BitVec.ofNat 64 4101) := by
  decide

/-- Past the image the LEA fetch refuses. -/
theorem leaWit_nachBild_verweigert :
    leaGeholtSchritt { leaWitZustand with rip := BitVec.ofNat 64 4101 } =
      none := by
  decide

/-- Store witness image: `mov [r8 + r9*8 + 0], rax` (REX.X+B). -/
def storeWitBild : List Byte :=
  [natByte 75, natByte 137, natByte 68, natByte 200, natByte 0]

/-- Store witness code bytes: the image at 4096, zeroes elsewhere. -/
def storeWitBytes (a : Adresse) : Byte :=
  if a.toNat < 4096 then BitVec.ofNat 8 0
  else
    match storeWitBild[a.toNat - 4096]? with
    | some b => b
    | none => BitVec.ofNat 8 0

/-- Store witness execute permission: exactly the five image bytes. -/
def storeWitCode (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4101)

/-- Store witness data permission: sixteen bytes at 8192. -/
def storeWitDaten (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8208)

/-- Store witness memory: code is execute-only, data read/write-only. -/
def storeWitSpeicher : Speicher :=
  { bytes := storeWitBytes, lesbar := storeWitDaten,
    schreibbar := storeWitDaten, ausfuehrbar := storeWitCode }

/-- Store witness registers: `rax = 42`, `r8 = 8192`, `r9 = 1`. -/
def storeWitReg : Register → Wort
  | .rax => BitVec.ofNat 64 42
  | .r8 => BitVec.ofNat 64 8192
  | .r9 => BitVec.ofNat 64 1
  | .rsp => BitVec.ofNat 64 8704
  | _ => BitVec.ofNat 64 0

/-- Store witness start state: code at 4096. -/
def storeWitZustand : Zustand :=
  { register := storeWitReg, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := storeWitSpeicher }

/-- JOINT WITNESS: the fetched high-register scaled store lands 42 at
    `r8 + r9 * 8 = 8200`, reads back, started from zero, and advances
    RIP past its five bytes. -/
theorem storeWit_zeuge :
    (adrStoreSchritt storeWitZustand).map
        (fun s => s.speicher.bytes (BitVec.ofNat 64 8200)) =
        some (BitVec.ofNat 8 42) ∧
      (adrStoreSchritt storeWitZustand).bind
          (fun s => read64 s.speicher (BitVec.ofNat 64 8200)) =
        some (BitVec.ofNat 64 42) ∧
      storeWitZustand.speicher.bytes (BitVec.ofNat 64 8200) =
        BitVec.ofNat 8 0 ∧
      (adrStoreSchritt storeWitZustand).map (fun s => s.rip) =
        some (BitVec.ofNat 64 4101) := by
  decide

/-- PERMISSION REFUSAL: the same fetched store with dark data memory
    admits no step. -/
theorem storeWit_dunkel_verweigert :
    adrStoreSchritt { storeWitZustand with speicher :=
      { storeWitSpeicher with schreibbar := fun _ => false } } = none := by
  decide

/-- ADMISSION PINS: the witness footprint is admitted for both
    directions; the wrap edge, the noncanonical hole and dark memory
    are refused. -/
theorem fussZugelassen_beispiele :
    fussZugelassen storeWitSpeicher (BitVec.ofNat 64 8200) true = true ∧
      fussZugelassen storeWitSpeicher (BitVec.ofNat 64 8200) false =
        true ∧
      fussZugelassen storeWitSpeicher (BitVec.ofNat 64 (2 ^ 64 - 4))
          true = false ∧
      fussZugelassen storeWitSpeicher (BitVec.ofNat 64 (2 ^ 47))
          false = false := by
  decide

/- CUTS:
    Proved here: canonical REX/ModRM/SIB/displacement encoder and
    parser for the selected §2B address scope (disp0/disp8/disp32
    smallest-first, base+index*scale+disp with REX high registers,
    absent base/index, RIP-relative, absolute disp32-only); consumed
    lengths pinned per shape (2, 3, 4, 6, 7 bytes); sign-extension
    pins and cross-width address equality; the pilot bridge
    (`adrEff_basisForm` against `effAddr`); LEA purity (flags and
    memory untouched, no memory read); full LEA/store byte forms
    through fetched execution with reached memory-changing joint
    witnesses; footprint admission (canonical address, no wrap,
    per-direction rights); relocation-relevant displacement travel in
    final bytes; explicit refusals (pilot rows, mod=3, missing SIB,
    truncated disp, wrong signed reading, legacy prefix, missing
    REX.W, wrap edge, noncanonical hole, dark permissions).
    NOT proved here, and not claimed:
    - No silicon correspondence: shapes follow `BYTE-PILOT.md` and
      `DIRECT-COMPILER-DESIGN.md` §2B as stated contracts; the lane
      clone has no `.tmp/HARDWARE-REFERENCES/REFERENCES.json`, so no
      manual heading or page is cited and no hardware truth is
      claimed for SIB corner rows (e.g. index `r12` sharing byte 36
      with the no-index shape is disambiguated by REX.X here, which
      the pilot refuses wholesale).
    - No generic round trip over all 256 register pairs and no uniform
      length-bound theorem: each shape class is pinned on closed
      bytes, and the register-dependent SIB split (`rsp`/`r12` base)
      is pinned on both sides.
    - No base-only disp0/disp8 pilot rows: the pilot keeps mod=10
      disp32 (`BYTE-PILOT.md`); compact base-only forms need new
      pilot rows plus review, owned by a follow-up producer.
    - No width/branch/immediate forms: disp0/disp8/disp32 selection
      covers addresses only; imm8/imm32 arithmetic, short branches,
      SETcc/CMOV stores and vector gathers stay with lanes
      integer666/locked662/FP668 over this stable API (`adrEff`,
      `dispWortArt`, `encodeAdr`, `parseAdrTail`, `decodeLea`,
      `decodeStoreIdx`, `leaFormSchritt`, `leaGeholtSchritt`,
      `adrStoreSchritt`, `kanonisch48`, `fussZugelassen`).
    - No TSO/GX bridge: footprints are sequential per-byte sets;
      tearing and visibility stay open.
    - No source correspondence, no ABI/loader/entry/budget claim.
-/

#print axioms disp8Wort_null
#print axioms disp8Wort_negEins
#print axioms codeSkala_skalaCode
#print axioms kanonisch48_8192
#print axioms kanonisch48_loch
#print axioms basisForm_ok
#print axioms skaliertForm_rsp_verweigert
#print axioms dispWortArt_d8
#print axioms adrEff_basisForm
#print axioms adrEff_skaliert_prestate
#print axioms adrEff_verschiebung
#print axioms leaFormSchritt_flags
#print axioms leaFormSchritt_speicher
#print axioms leaFormSchritt_basisForm
#print axioms rexAddr_ohne_x
#print axioms encodeAdr_braucht_ok
#print axioms encodeAdr_pilot_basis
#print axioms kompakt_ersparnis
#print axioms rundweg_skaliertDisp8
#print axioms rundweg_skaliertHoch
#print axioms rundweg_rip
#print axioms parser_weist_pilot_basis_zurueck
#print axioms pilot_weist_x_zurueck
#print axioms falsche_disp8_aendert_adresse
#print axioms lea_dekodiert_skaliert
#print axioms pilot_weist_lea_zurueck
#print axioms lea_verweigert_vorsatz
#print axioms store_dekodiert_hoch
#print axioms leaWit_rechnet
#print axioms leaWit_speicher_ruht
#print axioms storeWit_zeuge
#print axioms storeWit_dunkel_verweigert
#print axioms fussZugelassen_beispiele
#print axioms adrLesen_erlaubt
#print axioms adrStore_berechtigungen
#print axioms bildDisp_trifft

end Gabbro.Grammatik.X86
