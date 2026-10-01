/-
  File:      Grammatik/X86/EffectiveAddress.lean
  Subject:   Effective addresses and signed displacements over the canonical pilot vocabulary.

  Lane 416 (continuous reserve): reusable facts about the ACTUAL pilot
  `effAddr`/`dispWort` of `Ausfuehrung.lean`, consumed by the real
  load/store steps (`schritt` `.load64`/`.store64`) and their extracted
  footprints (`Zugriffe.zugriff`). Modular physical address arithmetic
  (always defined, wraps) is separated from non-wrapping admitted region
  ranges (`Speicher.OhneUmbruch`, `Regionen` extents plus permission
  checks). The future scaled-index helper reuses the canonical
  registers/words/memory and records its missing native codec/step
  extension in CUTS. No new register, memory, decoder or source model is
  invented here.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Regionen
import Grammatik.X86.Zugriffe

namespace Gabbro.Grammatik.X86

/-- Zero displacement sign-extends to zero. -/
theorem dispWort_null : dispWort (BitVec.ofNat 32 0) = 0 := by
  decide

/-- Zero displacement addresses the base register itself. -/
theorem effAddr_null (s : Zustand) (base : Register) :
    effAddr s base (BitVec.ofNat 32 0) = s.register base := by
  simp [effAddr, dispWort_null]

/-! ## 1. Modular subtraction bridges (used by the shifts below). -/

/-- Adding all-ones is subtracting one, modularly. -/
theorem wort_add_allOnes (x : Wort) :
    x + 0xFFFFFFFFFFFFFFFF = x - 1 := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have h1 : (0xFFFFFFFFFFFFFFFF : Wort).toNat = 2 ^ 64 - 1 := by decide
  have h2 : (1 : Wort).toNat = 1 := by decide
  rw [BitVec.toNat_add, BitVec.toNat_sub, h1, h2]
  omega

/-- Adding the `-5` word is subtracting five, modularly. -/
theorem wort_add_negFuenf (x : Wort) :
    x + 0xFFFFFFFFFFFFFFFB = x - 5 := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have h1 : (0xFFFFFFFFFFFFFFFB : Wort).toNat = 2 ^ 64 - 5 := by decide
  have h2 : (5 : Wort).toNat = 5 := by decide
  rw [BitVec.toNat_add, BitVec.toNat_sub, h1, h2]
  omega

/-- Adding the `minNeg` word is subtracting `2 ^ 31`, modularly. -/
theorem wort_add_minNeg (x : Wort) :
    x + 0xFFFFFFFF80000000 = x - BitVec.ofNat 64 2147483648 := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have h1 : (0xFFFFFFFF80000000 : Wort).toNat = 2 ^ 64 - 2147483648 := by
    decide
  have h2 : (BitVec.ofNat 64 2147483648).toNat = 2147483648 := by decide
  rw [BitVec.toNat_add, BitVec.toNat_sub, h1, h2]
  omega

/-! ## 2. Signed displacement boundaries.

    The pilot displacement is a 32-bit value sign-extended to 64 bits
    (`dispWort`), so `0xFFFFFFFF` moves one byte BACKWARDS, `0x7FFFFFFF`
    is the largest forward step and `0x80000000` the largest backward
    step. All four are pinned by `decide`; the three `effAddr` shifts
    below are what the load/store consumers move by. -/

/-- Displacement `-1`: the sign extension fills every upper bit. -/
theorem dispWort_negEins :
    dispWort (BitVec.ofNat 32 4294967295) = 0xFFFFFFFFFFFFFFFF := by
  decide

/-- Displacement `-5` (the branch/codec pin shape): sign extension fills. -/
theorem dispWort_negFuenf :
    dispWort (BitVec.ofNat 32 4294967291) = 0xFFFFFFFFFFFFFFFB := by
  decide

/-- Largest forward displacement: no fill, value kept. -/
theorem dispWort_maxPos :
    dispWort (BitVec.ofNat 32 2147483647) = 0x7FFFFFFF := by
  decide

/-- Largest backward displacement: upper bits filled, low bit 31 kept. -/
theorem dispWort_minNeg :
    dispWort (BitVec.ofNat 32 2147483648) = 0xFFFFFFFF80000000 := by
  decide

/-- A `-1` displacement steps one byte below the base register. -/
theorem effAddr_negEins (s : Zustand) (base : Register) :
    effAddr s base (BitVec.ofNat 32 4294967295) =
      s.register base - 1 := by
  simp only [effAddr, dispWort_negEins]
  exact wort_add_allOnes (s.register base)

/-- A `-5` displacement steps five bytes below the base register. -/
theorem effAddr_negFuenf (s : Zustand) (base : Register) :
    effAddr s base (BitVec.ofNat 32 4294967291) =
      s.register base - 5 := by
  simp only [effAddr, dispWort_negFuenf]
  exact wort_add_negFuenf (s.register base)

/-- The largest forward displacement adds `2 ^ 31 - 1` modularly. -/
theorem effAddr_maxPos (s : Zustand) (base : Register) :
    effAddr s base (BitVec.ofNat 32 2147483647) =
      s.register base + 0x7FFFFFFF := by
  simp [effAddr, dispWort_maxPos]

/-- The largest backward displacement subtracts `2 ^ 31` modularly. -/
theorem effAddr_minNeg (s : Zustand) (base : Register) :
    effAddr s base (BitVec.ofNat 32 2147483648) =
      s.register base - BitVec.ofNat 64 2147483648 := by
  simp only [effAddr, dispWort_minNeg]
  exact wort_add_minNeg (s.register base)

/-! ## 3. Prestate aliasing: the address reads one register only.

    `effAddr` is a pure function of the base register value plus the
    displacement: two prestates agreeing on the base give the same
    address, whatever their flags, memory or other registers hold. -/

/-- The effective address depends only on the base register value:
    two prestates agreeing there give the same address. -/
theorem effAddr_prestate (s1 s2 : Zustand) (base : Register)
    (disp : BitVec 32)
    (h : s1.register base = s2.register base) :
    effAddr s1 base disp = effAddr s2 base disp := by
  simp [effAddr, h]

/-- ALIAS: different bases may still name the same address, so no
    injectivity is claimed. Here `rax = 16` with displacement `0`
    aliases `rbx = 0` with displacement `16`. -/
theorem effAddr_alias_beispiel :
    effAddr { zeugeZustand with register := regSet zeugeZustand.register Register.rax 16 } Register.rax (BitVec.ofNat 32 0) =
    effAddr zeugeZustand Register.rbx (BitVec.ofNat 32 16) := by
  decide

/-! ## 4. Modular value versus admitted range.

    The modular sum always exists and wraps; admission is a separate
    checked step (`OhneUmbruch` for the footprint, region extents plus
    permission checks for reads and writes). A wrapped value is never
    an admission. -/

/-- WRAP VALUE: `0xFFFF...FF + 1` is modular `0`. -/
theorem effAddr_umlauf_wert :
    effAddr { zeugeZustand with register := regSet zeugeZustand.register Register.rax 0xFFFFFFFFFFFFFFFF } Register.rax (BitVec.ofNat 32 1) = 0 := by
  decide

/-- NO ADMISSION FROM WRAP: an address at the top of the space admits
    no eight-byte footprint: `2 ^ 64 - 4 + 8` leaves 64 bits. -/
theorem effAddr_rand_kein_ohneUmbruch :
    ¬ OhneUmbruch (BitVec.ofNat 64 (2 ^ 64 - 4)) := by
  unfold OhneUmbruch
  decide

/-- The top-of-space address above is what a `-4`-based access computes:
    the modular value exists while the footprint is refused. -/
theorem effAddr_rand_wert :
    effAddr { zeugeZustand with register := regSet zeugeZustand.register Register.rax (BitVec.ofNat 64 (2 ^ 64 - 4)) } Register.rax (BitVec.ofNat 32 0) =
      BitVec.ofNat 64 (2 ^ 64 - 4) := by
  decide

/-- Under no-wrap, the footprint bytes of an effective address are Nat
    additions: the admitted-range view of the modular address. -/
theorem effAddr_fuss_addrs (s : Zustand) (base : Register)
    (disp : BitVec 32)
    (h : OhneUmbruch (effAddr s base disp)) (i : Nat) (hi : i < 8) :
    (addrOff (effAddr s base disp) i).toNat =
      (effAddr s base disp).toNat + i :=
  ohneUmbruch_addrs _ h i hi

/-! ## 5. Region admission: the checked range view.

    A region extent plus no-wrap admits every footprint byte of the
    effective address as `inRegion`. Permissions (`lesbar8`,
    `schreibbar8`) stay a separate check on the initialised memory:
    extent admission never grants rights by itself. -/

/-- An effective address inside a region extent names admitted bytes:
    every footprint byte is `inRegion`. -/
theorem effAddr_in_region (s : Zustand) (base : Register)
    (disp : BitVec 32) (r : Region)
    (hlo : r.basis ≤ (effAddr s base disp).toNat)
    (hhi : (effAddr s base disp).toNat + 8 ≤ r.basis + r.len)
    (hwrap : (effAddr s base disp).toNat + 8 ≤ 2 ^ 64)
    (i : Nat) (hi : i < 8) :
    inRegion r (addrOff (effAddr s base disp) i).toNat = true := by
  have hnw : OhneUmbruch (effAddr s base disp) := hwrap
  have e := ohneUmbruch_addrs (effAddr s base disp) hnw i hi
  unfold inRegion
  simp only [decide_eq_true_eq, e]
  omega

/-! ## 6. Consumed by the actual pilot load/store steps.

    The two lemmas below tie the address math to the real `schritt`
    transitions and their extracted `zugriff` footprints: a successful
    load reads exactly the effective address, a successful store writes
    exactly its eight bytes. Refusals at the effective address admit no
    step at all. -/

/-- A successful pilot `load` reads exactly the effective address: the
    destination holds the word, memory is untouched, and the extracted
    footprint names the same eight bytes. -/
theorem effAddr_load_schritt (d : Decodiert) (s s' : Zustand)
    (dst base : Register) (disp : BitVec 32) (v : Wort)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .load64 dst base disp)
    (hrd : read64 s.speicher (effAddr s base disp) = some v)
    (hstep : schritt d s = some s') :
    s'.register dst = v ∧ s'.speicher = s.speicher ∧
      zugriff d s = ⟨Fuss (effAddr s base disp), [], none⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [schritt_load64_erfolg d s dst base disp v hok h hrd] at hstep
    cases hstep
    simp [schrittRegister, regSet]
  · exact schritt_load64_speicher d s s' dst base disp v hok h hrd hstep
  · exact zugriff_load64 d s dst base disp h

/-- A successful pilot `store` writes exactly the eight bytes at the
    effective address: every changed byte lies in the footprint, write
    permissions are preserved, and the stored word is the source
    register named by the extraction. -/
theorem effAddr_store_schritt (d : Decodiert) (s s' : Zustand)
    (base src : Register) (disp : BitVec 32) (m : Speicher)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .store64 base src disp)
    (hwr : write64 s.speicher (effAddr s base disp) (s.register src) =
      some m)
    (hstep : schritt d s = some s') :
    (∀ x, s'.speicher.bytes x ≠ s.speicher.bytes x →
      x ∈ Fuss (effAddr s base disp)) ∧
    s'.speicher.schreibbar = s.speicher.schreibbar ∧
    (zugriff d s).speicherWert = some (s.register src) := by
  obtain ⟨hbytes, _, hschr, _, hwert⟩ :=
    erfolg_store64_im_fuss s s' base src disp m d hok h hwr hstep
  rw [zugriff_store64 d s base src disp h] at hbytes
  simp only at hbytes
  exact ⟨hbytes, hschr, hwert⟩

/-- A failed `load` read at the effective address admits no step. -/
theorem effAddr_load_verweigert (d : Decodiert) (s s' : Zustand)
    (dst base : Register) (disp : BitVec 32)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .load64 dst base disp)
    (hrd : read64 s.speicher (effAddr s base disp) = none)
    (hstep : schritt d s = some s') : False :=
  zugriff_load64_versagt_kein_erfolg s s' dst base disp d hok h hrd hstep

/-- A failed `store` write at the effective address admits no step. -/
theorem effAddr_store_verweigert (d : Decodiert) (s s' : Zustand)
    (base src : Register) (disp : BitVec 32)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .store64 base src disp)
    (hwr : write64 s.speicher (effAddr s base disp) (s.register src) = none)
    (hstep : schritt d s = some s') : False :=
  zugriff_store64_versagt_kein_erfolg s s' base src disp d hok h hwr hstep

/-! ## 7. Future scaled-index helper (no native consumer yet).

    The pilot `Befehl` has no scaled-index form: every load/store steps
    through `effAddr` (base plus displacement). The helper below is pure
    address math over the CANONICAL registers, words and displacement,
    with the same prestate-aliasing discipline; its native SIB codec
    row and `schritt` extension are MISSING (see CUTS). The unscaled
    case coincides with the pilot address, so no second address model
    is invented. -/

/-- Future scaled-index address over the canonical vocabulary: base
    plus index times scale plus the sign-extended displacement. Pure
    address math only; no `Befehl`, codec row or `schritt` consumes it. -/
def skaliertAddr (s : Zustand) (base idx : Register) (skala : Nat)
    (disp : BitVec 32) : Adresse :=
  s.register base + s.register idx * BitVec.ofNat 64 skala + dispWort disp

/-- The unscaled case is the pilot address: no second address model. -/
theorem skaliertAddr_skala_null (s : Zustand) (base idx : Register)
    (disp : BitVec 32) :
    skaliertAddr s base idx 0 disp = effAddr s base disp := by
  simp [skaliertAddr, effAddr]

/-- The scaled address depends only on the two register values: two
    prestates agreeing on both give the same address (alias prestate
    for the future consumer). -/
theorem skaliertAddr_prestate (s1 s2 : Zustand) (base idx : Register)
    (skala : Nat) (disp : BitVec 32)
    (hb : s1.register base = s2.register base)
    (hi : s1.register idx = s2.register idx) :
    skaliertAddr s1 base idx skala disp =
      skaliertAddr s2 base idx skala disp := by
  simp [skaliertAddr, hb, hi]

/-- DIVERGENCE: a scaled address is genuinely beyond the pilot: with
    `rsp = 8192`, `rbx = 20`, scale `8` and displacement `0` the scaled
    address is `8192 + 160` while the pilot address stays at `8192`. -/
theorem skaliertAddr_weicht_ab :
    skaliertAddr { zeugeZustand with register := regSet zeugeZustand.register Register.rbx 20 } Register.rsp Register.rbx 8 (BitVec.ofNat 32 0) = BitVec.ofNat 64 8352 ∧
    effAddr zeugeZustand Register.rsp (BitVec.ofNat 32 0) = BitVec.ofNat 64 8192 := by
  decide

/-! ## 8. Reached witnesses: a memory-changing run and a refusal.

    The joint witness runs the real pilot program through its effective
    address: `rsp + 0` is `8192`, the reached state holds `rbx = 42`
    and the byte at `8192` observably changed from zero. The negative
    witness refuses the same effective address under dark memory. -/

/-- JOINT WITNESS: the witness store runs through its effective
    address `rsp + 0 = 8192`: the run reaches `rbx = 42` and the byte
    at `8192` changed from `0` to `42`. -/
theorem effAddr_lauf_zeuge :
    effAddr zeugeZustand Register.rsp (BitVec.ofNat 32 0) =
      BitVec.ofNat 64 8192 ∧
    ((lauf zeugeProg zeugeZustand).map
      (fun s => s.register Register.rbx) = some 42) ∧
    ((lauf zeugeProg zeugeZustand).map
      (fun s => s.speicher.bytes (BitVec.ofNat 64 8192)) =
      some (BitVec.ofNat 8 42)) ∧
    (zeugeZustand.speicher.bytes (BitVec.ofNat 64 8192) =
      BitVec.ofNat 8 0) := by
  exact ⟨by decide, zeuge_speicher_aendert_sich⟩

/-- Dark memory: nothing readable or writable (fault witness). -/
def dunkelSpeicher : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0
    lesbar := fun _ => false
    schreibbar := fun _ => false
    ausfuehrbar := fun _ => false }

/-- NEGATIVE WITNESS: the same effective address with dark memory
    refuses the load: no read permission means `none`, and the step
    refuses with it — never a silent value. -/
theorem effAddr_laden_verweigert_zeuge :
    read64 dunkelSpeicher
      (effAddr zeugeZustand Register.rsp (BitVec.ofNat 32 0)) = none ∧
    schritt ⟨.load64 Register.rax Register.rsp (BitVec.ofNat 32 0), 4⟩
      { zeugeZustand with speicher := dunkelSpeicher } = none := by
  have hrd : read64 dunkelSpeicher
      (effAddr zeugeZustand Register.rsp (BitVec.ofNat 32 0)) = none := by
    decide
  refine ⟨hrd, ?_⟩
  have hok : laengeOk 4 = true := by decide
  have hrd2 : read64 { zeugeZustand with speicher := dunkelSpeicher }.speicher
      (effAddr { zeugeZustand with speicher := dunkelSpeicher }
        Register.rsp (BitVec.ofNat 32 0)) = none := by
    decide
  exact schritt_load64_verweigert _ _ _ _ _ hok rfl hrd2

/-! ## 9. Joint witnesses for the step-consumption theorems.

    Every premise of `effAddr_load_schritt` / `effAddr_store_schritt`
    is instantiated jointly on concrete values: `rax = 42` moves
    through `rsp + 0 = 8192`, with the observably changed byte and the
    reached memory-changing write beside it. -/
/-- JOINT WITNESS for `effAddr_store_schritt`: `rax = 42` is stored
    through `rsp + 0 = 8192`; the reached state carries the written
    byte, which observably changed from zero. -/
theorem effAddr_store_schritt_zeuge :
    (∃ (s' : Zustand),
      schritt { befehl := Befehl.store64 Register.rsp Register.rax (BitVec.ofNat 32 0), laenge := 4 }
        { zeugeZustand with register := regSet zeugeZustand.register Register.rax 42 } = some s' ∧
      s'.speicher.bytes (BitVec.ofNat 64 8192) = BitVec.ofNat 8 42) ∧
    (∃ (m : Speicher),
      write64 zeugeSpeicher (BitVec.ofNat 64 8192) 42 = some m ∧
      m.bytes (BitVec.ofNat 64 8192) ≠
        zeugeSpeicher.bytes (BitVec.ofNat 64 8192)) := by
  have hrd_perm : lesbar8 zeugeSpeicher (BitVec.ofNat 64 8192) = true := rfl
  have hwr_perm : schreibbar8 zeugeSpeicher (BitVec.ofNat 64 8192) = true :=
    rfl
  have hwr : write64 zeugeSpeicher (BitVec.ofNat 64 8192) 42 = some { zeugeSpeicher with bytes := writeBytes zeugeSpeicher (BitVec.ofNat 64 8192) 42 } := by
    unfold write64
    rw [if_pos hwr_perm]
  -- NOTE: single-line struct updates only (multi-line breaks the parser).
  have haddr1 : effAddr { zeugeZustand with register := regSet zeugeZustand.register Register.rax 42 } Register.rsp (BitVec.ofNat 32 0) = BitVec.ofNat 64 8192 := by
    decide
  have hreg : { zeugeZustand with register := regSet zeugeZustand.register Register.rax 42 }.register Register.rax = 42 := by
    decide
  have hwrS : write64 { zeugeZustand with register := regSet zeugeZustand.register Register.rax 42 }.speicher (effAddr { zeugeZustand with register := regSet zeugeZustand.register Register.rax 42 } Register.rsp (BitVec.ofNat 32 0)) ({ zeugeZustand with register := regSet zeugeZustand.register Register.rax 42 }.register Register.rax) = some { zeugeSpeicher with bytes := writeBytes zeugeSpeicher (BitVec.ofNat 64 8192) 42 } := by
    rw [haddr1, hreg]
    exact hwr
  have hok : laengeOk 4 = true := by decide
  have hstep := schritt_store64_erfolg
    { befehl := Befehl.store64 Register.rsp Register.rax (BitVec.ofNat 32 0), laenge := 4 }
    { zeugeZustand with register := regSet zeugeZustand.register Register.rax 42 }
    Register.rsp Register.rax (BitVec.ofNat 32 0)
    { zeugeSpeicher with bytes := writeBytes zeugeSpeicher (BitVec.ofNat 64 8192) 42 }
    hok rfl hwrS
  have hhit := writeBytesN_hit zeugeSpeicher (BitVec.ofNat 64 8192) 42 8 0
    (by decide) (by decide)
  rw [addrOff_null] at hhit
  refine ⟨⟨_, hstep, ?_⟩, ⟨_, hwr, ?_⟩⟩
  · show writeBytes zeugeSpeicher (BitVec.ofNat 64 8192) 42
      (BitVec.ofNat 64 8192) = BitVec.ofNat 8 42
    unfold writeBytes
    rw [hhit]
    decide
  · show writeBytes zeugeSpeicher (BitVec.ofNat 64 8192) 42
      (BitVec.ofNat 64 8192) ≠ zeugeSpeicher.bytes (BitVec.ofNat 64 8192)
    unfold writeBytes
    rw [hhit]
    decide

/-- JOINT WITNESS for `effAddr_load_schritt`: the stored `42` reads
    back through `rsp + 0 = 8192` into `rbx`; the write went through
    and reads back beside it. -/
theorem effAddr_load_schritt_zeuge :
    (∃ (s' : Zustand),
      schritt { befehl := Befehl.load64 Register.rbx Register.rsp (BitVec.ofNat 32 0), laenge := 4 }
        { zeugeZustand with speicher := { zeugeSpeicher with bytes := writeBytes zeugeSpeicher (BitVec.ofNat 64 8192) 42 } } = some s' ∧
      s'.register Register.rbx = 42) ∧
    (∃ (m : Speicher),
      write64 zeugeSpeicher (BitVec.ofNat 64 8192) 42 = some m ∧
      read64 m (BitVec.ofNat 64 8192) = some 42) := by
  have hrd_perm : lesbar8 zeugeSpeicher (BitVec.ofNat 64 8192) = true := rfl
  have hwr_perm : schreibbar8 zeugeSpeicher (BitVec.ofNat 64 8192) = true :=
    rfl
  have hwr : write64 zeugeSpeicher (BitVec.ofNat 64 8192) 42 = some { zeugeSpeicher with bytes := writeBytes zeugeSpeicher (BitVec.ofNat 64 8192) 42 } := by
    unfold write64
    rw [if_pos hwr_perm]
  have hrd := read64_nach_write64 zeugeSpeicher { zeugeSpeicher with bytes := writeBytes zeugeSpeicher (BitVec.ofNat 64 8192) 42 } (BitVec.ofNat 64 8192) 42 hwr hrd_perm
  have haddr : effAddr { zeugeZustand with speicher := { zeugeSpeicher with bytes := writeBytes zeugeSpeicher (BitVec.ofNat 64 8192) 42 } } Register.rsp (BitVec.ofNat 32 0) = BitVec.ofNat 64 8192 := by
    decide
  have hrdS : read64 { zeugeZustand with speicher := { zeugeSpeicher with bytes := writeBytes zeugeSpeicher (BitVec.ofNat 64 8192) 42 } }.speicher (effAddr { zeugeZustand with speicher := { zeugeSpeicher with bytes := writeBytes zeugeSpeicher (BitVec.ofNat 64 8192) 42 } } Register.rsp (BitVec.ofNat 32 0)) = some 42 := by
    rw [haddr]
    exact hrd
  have hok : laengeOk 4 = true := by decide
  have hstep := schritt_load64_erfolg
    { befehl := Befehl.load64 Register.rbx Register.rsp (BitVec.ofNat 32 0), laenge := 4 }
    { zeugeZustand with speicher := { zeugeSpeicher with bytes := writeBytes zeugeSpeicher (BitVec.ofNat 64 8192) 42 } }
    Register.rbx Register.rsp (BitVec.ofNat 32 0) 42 hok rfl hrdS
  refine ⟨⟨_, hstep, by decide⟩, ⟨_, hwr, hrd⟩⟩

/- CUTS:
   Proved here: sign-extension pins for the pilot displacement
   (`dispWort` at zero, minus-one, minus-five, maxPos and minNeg)
   with the resulting `effAddr` shifts; modular subtraction bridges; prestate-aliasing (same base
   gives same address) with an explicit non-injectivity example;
   modular-wrap value probes separated from `OhneUmbruch` admission;
   the no-wrap footprint view and region-extent admission of an
   effective address; consumption by the actual pilot steps
   (`effAddr_load_schritt`, `effAddr_store_schritt`, both refusals)
   with their `zugriff` footprints; the future `skaliertAddr` helper
   over the canonical vocabulary with its unscaled coincidence and a
   divergence probe; a memory-changing reached run through `rsp + 0`,
   a dark-memory refusal, and joint `_zeuge` companions for both
   consumption theorems.
   NOT proved here, and not claimed:
   - No hardware correspondence: address math reuses `dispWort`,
     faults are the existing permission-checked `read64`/`write64`
     outcomes, not silicon.
   - No native scaled-index support: `skaliertAddr` has no `Befehl`
     constructor, no `Codec` row and no `schritt` case; any future SIB
     form needs its own decode/step extension plus review.
   - No alignment admission: ordinary accesses impose no alignment
     check here (actual behaviour); any profile alignment stays a
     validator-side decision owned elsewhere.
   - No TSO/GX bridge: footprints are sequential byte sets (`Fuss`),
     not atomic multi-byte events and not an interleaving trace;
     tearing, visibility and grouping stay OPEN.
   - No source correspondence, no ABI/loader, no cost/time transfer,
     no whole-image and no full source-to-byte validation claim.
-/

#print axioms dispWort_null
#print axioms effAddr_null
#print axioms wort_add_allOnes
#print axioms wort_add_negFuenf
#print axioms wort_add_minNeg
#print axioms dispWort_negEins
#print axioms dispWort_negFuenf
#print axioms dispWort_maxPos
#print axioms dispWort_minNeg
#print axioms effAddr_negEins
#print axioms effAddr_negFuenf
#print axioms effAddr_maxPos
#print axioms effAddr_minNeg
#print axioms effAddr_prestate
#print axioms effAddr_alias_beispiel
#print axioms effAddr_umlauf_wert
#print axioms effAddr_rand_kein_ohneUmbruch
#print axioms effAddr_rand_wert
#print axioms effAddr_fuss_addrs
#print axioms effAddr_in_region
#print axioms effAddr_load_schritt
#print axioms effAddr_store_schritt
#print axioms effAddr_load_verweigert
#print axioms effAddr_store_verweigert
#print axioms skaliertAddr_skala_null
#print axioms skaliertAddr_prestate
#print axioms skaliertAddr_weicht_ab
#print axioms effAddr_lauf_zeuge
#print axioms effAddr_laden_verweigert_zeuge
#print axioms effAddr_store_schritt_zeuge
#print axioms effAddr_load_schritt_zeuge

end Gabbro.Grammatik.X86
