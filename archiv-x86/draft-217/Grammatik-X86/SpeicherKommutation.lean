/-
  Disjoint byte-memory commutation for the direct x86-64 validation pilot
  (lane 289).

  Over the canonical `Speicher` vocabulary of `Grammatik.X86.Typen` and the
  permission-checked `read64`/`write64` of `Grammatik.X86.Speicher`: two
  successful 64-bit stores at disjoint footprints commute (byte-extensionally,
  with permissions unchanged), reads survive unrelated stores, and a
  source-independent stable-footprint condition captures what a private
  spill slot needs (established by a store, preserved by disjoint stores).

  This is target-memory commutation only: no whole-program atomicity, no TSO
  refinement, and address disjointness alone never means thread-private --
  publication, foreign readers and locks stay higher-level source obligations
  (see CUTS).
-/
import Grammatik.X86.Speicher

namespace Gabbro.Grammatik.X86

/-- Footprint membership as an existentially quantified byte index. -/
theorem mem_Fuss_iff (a x : Adresse) :
    x ∈ Fuss a ↔ ∃ k : Fin 8, addrOff a k.val = x := by
  rw [← leseEreignisse_acht, leseEreignisse_mem]
  constructor
  · rintro ⟨k, hk, he⟩
    exact ⟨⟨k, hk⟩, he⟩
  · rintro ⟨⟨k, hk⟩, he⟩
    exact ⟨k, hk, he⟩

/-! ## 2. Single-store facts over `write64` -/

/-- A successful store places the word's bytes on its footprint. -/
theorem write64_trifft (m m' : Speicher) (a : Adresse) (v : Wort) (k : Nat)
    (hk : k < 8) (hwr : write64 m a v = some m') :
    m'.bytes (addrOff a k) = wortByte v k := by
  unfold write64 at hwr
  by_cases hc : schreibbar8 m a = true
  · rw [if_pos hc] at hwr
    cases hwr
    show writeBytes m a v (addrOff a k) = wortByte v k
    unfold writeBytes
    exact writeBytesN_hit m a v 8 k hk (Nat.le_refl 8)
  · rw [if_neg hc] at hwr
    cases hwr

/-- A successful store proves its footprint was writable. -/
theorem schreibbar8_aus_write64 (m m' : Speicher) (a : Adresse) (v : Wort)
    (hwr : write64 m a v = some m') : schreibbar8 m a = true := by
  cases heq : schreibbar8 m a with
  | true => rfl
  | false => exact absurd hwr (write64_verweigert_kein_effekt m m' a v heq)

/-- Footprint disjointness is symmetric. -/
theorem disjunkt_symm (a b : Adresse) (h : Disjunkt a b) : Disjunkt b a :=
  fun i j hi hj he => h j i hj hi he.symm

/-! ## 3. Commutation of two successful stores at disjoint footprints -/

/-- Two successful 64-bit stores at disjoint footprints commute: both orders
    agree on every byte, and every permission field still reads as before.
    Permissions are independent fields (`write64_erhaelt_berechtigungen`);
    disjointness is used for the byte-extensional part. -/
theorem write64_kommutiert (m m1 m2 m_ab m_ba : Speicher)
    (a b : Adresse) (v w : Wort)
    (hwr1 : write64 m a v = some m1)
    (hwrAB : write64 m1 b w = some m_ab)
    (hwr2 : write64 m b w = some m2)
    (hwrBA : write64 m2 a v = some m_ba)
    (hdis : Disjunkt a b) :
    (∀ x, m_ab.bytes x = m_ba.bytes x) ∧
      m_ab.lesbar = m.lesbar ∧ m_ab.schreibbar = m.schreibbar ∧
      m_ab.ausfuehrbar = m.ausfuehrbar ∧
      m_ba.lesbar = m.lesbar ∧ m_ba.schreibbar = m.schreibbar ∧
      m_ba.ausfuehrbar = m.ausfuehrbar := by
  have perm1 := write64_erhaelt_berechtigungen m a v m1 hwr1
  have permAB := write64_erhaelt_berechtigungen m1 b w m_ab hwrAB
  have perm2 := write64_erhaelt_berechtigungen m b w m2 hwr2
  have permBA := write64_erhaelt_berechtigungen m2 a v m_ba hwrBA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    by_cases ha : x ∈ Fuss a
    · obtain ⟨k, rfl⟩ := (mem_Fuss_iff a x).mp ha
      have e1 : m1.bytes (addrOff a k.val) = wortByte v k.val :=
        write64_trifft m m1 a v k.val k.isLt hwr1
      have e2 : m_ab.bytes (addrOff a k.val) = m1.bytes (addrOff a k.val) :=
        write64_rahmen m1 m_ab b _ w hwrAB (fun j hj => hdis k.val j k.isLt hj)
      have e3 : m_ba.bytes (addrOff a k.val) = wortByte v k.val :=
        write64_trifft m2 m_ba a v k.val k.isLt hwrBA
      rw [e2, e1, e3]
    · by_cases hb : x ∈ Fuss b
      · obtain ⟨j, rfl⟩ := (mem_Fuss_iff b x).mp hb
        have e1 : m_ab.bytes (addrOff b j.val) = wortByte w j.val :=
          write64_trifft m1 m_ab b w j.val j.isLt hwrAB
        have e2 : m_ba.bytes (addrOff b j.val) = m2.bytes (addrOff b j.val) :=
          write64_rahmen m2 m_ba a _ v hwrBA
            (fun k hk => Ne.symm (hdis k j.val hk j.isLt))
        have e3 : m2.bytes (addrOff b j.val) = wortByte w j.val :=
          write64_trifft m m2 b w j.val j.isLt hwr2
        rw [e1, e2, e3]
      · have gAB : m_ab.bytes x = m1.bytes x :=
          write64_rahmen m1 m_ab b x w hwrAB (fun j hj he =>
            hb ((mem_Fuss_iff b x).mpr ⟨⟨j, hj⟩, he.symm⟩))
        have g1 : m1.bytes x = m.bytes x :=
          write64_rahmen m m1 a x v hwr1 (fun k hk he =>
            ha ((mem_Fuss_iff a x).mpr ⟨⟨k, hk⟩, he.symm⟩))
        have gBA : m_ba.bytes x = m2.bytes x :=
          write64_rahmen m2 m_ba a x v hwrBA (fun k hk he =>
            ha ((mem_Fuss_iff a x).mpr ⟨⟨k, hk⟩, he.symm⟩))
        have g2 : m2.bytes x = m.bytes x :=
          write64_rahmen m m2 b x w hwr2 (fun j hj he =>
            hb ((mem_Fuss_iff b x).mpr ⟨⟨j, hj⟩, he.symm⟩))
        rw [gAB, g1, gBA, g2]
  · rw [permAB.1, perm1.1]
  · rw [permAB.2.1, perm1.2.1]
  · rw [permAB.2.2, perm1.2.2]
  · rw [permBA.1, perm2.1]
  · rw [permBA.2.1, perm2.2.1]
  · rw [permBA.2.2, perm2.2.2]

/-! ## 4. Reads survive unrelated stores -/

/-- A value already read at `a` still reads after a disjoint store at `b`. -/
theorem read64_erst_bleibt (m1 m_ab : Speicher) (a b : Adresse) (v w : Wort)
    (hwr : write64 m1 b w = some m_ab)
    (hrd : read64 m1 a = some v)
    (hdis : Disjunkt b a) :
    read64 m_ab a = some v := by
  rw [read64_rahmen m1 m_ab b a w hwr hdis, hrd]

/-- A read at `c` survives two stores at footprints disjoint from `c`,
    in either order shape: the two-store analogue of `read64_rahmen`. -/
theorem read64_nach_zwei_fremd (m m1 m_ab : Speicher) (a b c : Adresse)
    (v w : Wort)
    (hwr1 : write64 m a v = some m1)
    (hwr2 : write64 m1 b w = some m_ab)
    (hdis1 : Disjunkt a c) (hdis2 : Disjunkt b c) :
    read64 m_ab c = read64 m c := by
  have e2 := read64_rahmen m1 m_ab b c w hwr2 hdis2
  have e1 := read64_rahmen m m1 a c v hwr1 hdis1
  rw [e2, e1]

/-! ## 5. A stable-footprint condition for private spill slots -/

/-- A footprint is stable for a snapshot when its bytes match the snapshot
    and it stays readable and writable: exactly what a private spill slot
    needs so a later reload can be justified without re-reading memory.
    Source-independent: no ownership, publication or lock premise appears;
    those stay higher-level source obligations (see CUTS). -/
def StabilFuss (m : Speicher) (a : Adresse) (snap : Fin 8 → Byte) : Prop :=
  (∀ k : Fin 8, m.bytes (addrOff a k.val) = snap k) ∧
    lesbar8 m a = true ∧ schreibbar8 m a = true

/-- A successful store establishes a stable footprint for its own bytes. -/
theorem stabilFuss_nach_schreiben (m m' : Speicher) (a : Adresse) (v : Wort)
    (hwr : write64 m a v = some m')
    (hrd : lesbar8 m a = true) :
    StabilFuss m' a (fun k => wortByte v k.val) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    exact write64_trifft m m' a v k.val k.isLt hwr
  · rw [lesbar8_nach_schreiben m m' a a v hwr]
    exact hrd
  · rw [schreibbar8_nach_schreiben m m' a a v hwr]
    exact schreibbar8_aus_write64 m m' a v hwr

/-- A stable footprint survives a disjoint store: bytes by the frame,
    permissions because a store only replaces `bytes`. -/
theorem stabilFuss_bleibt (m m' : Speicher) (a b : Adresse) (v : Wort)
    (snap : Fin 8 → Byte)
    (hwr : write64 m a v = some m')
    (hdis : Disjunkt a b)
    (hstab : StabilFuss m b snap) :
    StabilFuss m' b snap := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    rw [write64_rahmen m m' a _ v hwr
      (fun j hj => Ne.symm (hdis j k.val hj k.isLt))]
    exact hstab.1 k
  · rw [lesbar8_nach_schreiben m m' a b v hwr]
    exact hstab.2.1
  · rw [schreibbar8_nach_schreiben m m' a b v hwr]
    exact hstab.2.2

/-- A stable footprint reloads its snapshot word and stays writable. -/
theorem stabilFuss_liest (m : Speicher) (a : Adresse) (snap : Fin 8 → Byte)
    (hstab : StabilFuss m a snap) :
    read64 m a = some (bytesWort snap) ∧ schreibbar8 m a = true := by
  refine ⟨?_, hstab.2.2⟩
  unfold read64
  rw [if_pos hstab.2.1]
  congr 1
  have hbytes : readBytes m a = snap := by
    funext k
    show m.bytes (addrOff a k.val) = snap k
    exact hstab.1 k
  rw [hbytes]

/-! ## 6. Reached two-store witness over distinct footprints -/

/-- Fully permissive zeroed target memory. -/
def zweiSpeicher0 : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0
    lesbar := fun _ => true
    schreibbar := fun _ => true
    ausfuehrbar := fun _ => false }

/-- First stored word (low byte `0x08`). -/
def zweiWertV : Wort := BitVec.ofNat 64 0x0102030405060708

/-- Second stored word (low byte `0x18`). -/
def zweiWertW : Wort := BitVec.ofNat 64 0x1112131415161718

/-- The low byte of each witness word. -/
theorem zweiByteV : wortByte zweiWertV 0 = BitVec.ofNat 8 0x08 := by
  decide

theorem zweiByteW : wortByte zweiWertW 0 = BitVec.ofNat 8 0x18 := by
  decide

/-- The witness addresses `0` and `16` have disjoint footprints. -/
theorem zweiDisjunkt : Disjunkt (0 : Adresse) (16 : Adresse) :=
  disjunkt_von_intervallen 0 16 (by unfold OhneUmbruch; decide)
    (by unfold OhneUmbruch; decide) (Or.inl (by decide))

/-- Witness state after the first store (`0x0102…0708` at address `0`). -/
def zweiNachA : Speicher := { zweiSpeicher0 with bytes := writeBytes zweiSpeicher0 0 zweiWertV }

/-- Witness state after the second store alone (`0x1112…1718` at `16`). -/
def zweiNachB : Speicher := { zweiSpeicher0 with bytes := writeBytes zweiSpeicher0 16 zweiWertW }

/-- Witness state after both stores in `A`-then-`B` order. -/
def zweiNachAB : Speicher := { zweiNachA with bytes := writeBytes zweiNachA 16 zweiWertW }

/-- Witness state after both stores in `B`-then-`A` order. -/
def zweiNachBA : Speicher := { zweiNachB with bytes := writeBytes zweiNachB 0 zweiWertV }

/-- The first witness store reaches. -/
theorem zweiSchrittA : write64 zweiSpeicher0 (0 : Adresse) zweiWertV = some zweiNachA := by
  unfold write64
  have hc : schreibbar8 zweiSpeicher0 (0 : Adresse) = true := rfl
  rw [if_pos hc]
  rfl

/-- The second witness store reaches on its own. -/
theorem zweiSchrittB : write64 zweiSpeicher0 (16 : Adresse) zweiWertW = some zweiNachB := by
  unfold write64
  have hc : schreibbar8 zweiSpeicher0 (16 : Adresse) = true := rfl
  rw [if_pos hc]
  rfl

/-- The second witness store reaches after the first. -/
theorem zweiSchrittAB : write64 zweiNachA (16 : Adresse) zweiWertW = some zweiNachAB := by
  unfold write64
  have hc : schreibbar8 zweiNachA (16 : Adresse) = true := rfl
  rw [if_pos hc]
  rfl

/-- The first witness store reaches after the second. -/
theorem zweiSchrittBA : write64 zweiNachB (0 : Adresse) zweiWertV = some zweiNachBA := by
  unfold write64
  have hc : schreibbar8 zweiNachB (0 : Adresse) = true := rfl
  rw [if_pos hc]
  rfl

/-- The first footprint observably changes (low byte `0x00` to `0x08`). -/
theorem zweiWechseltA : zweiNachAB.bytes (addrOff (0 : Adresse) 0) ≠ zweiSpeicher0.bytes (addrOff (0 : Adresse) 0) := by
  have f1 : zweiNachAB.bytes (addrOff (0 : Adresse) 0) = zweiNachA.bytes (addrOff (0 : Adresse) 0) := write64_rahmen _ _ _ _ _ zweiSchrittAB (fun j hj => zweiDisjunkt 0 j (by decide) hj)
  have f2 : zweiNachA.bytes (addrOff (0 : Adresse) 0) = wortByte zweiWertV 0 := write64_trifft _ _ _ _ 0 (by decide) zweiSchrittA
  have z0 : zweiSpeicher0.bytes (addrOff (0 : Adresse) 0) = BitVec.ofNat 8 0 := rfl
  rw [f1, f2, zweiByteV, z0]
  decide

/-- The second footprint observably changes (low byte `0x00` to `0x18`). -/
theorem zweiWechseltB : zweiNachAB.bytes (addrOff (16 : Adresse) 0) ≠ zweiSpeicher0.bytes (addrOff (16 : Adresse) 0) := by
  have hit : zweiNachAB.bytes (addrOff (16 : Adresse) 0) = wortByte zweiWertW 0 := write64_trifft _ _ _ _ 0 (by decide) zweiSchrittAB
  have z0 : zweiSpeicher0.bytes (addrOff (16 : Adresse) 0) = BitVec.ofNat 8 0 := rfl
  rw [hit, zweiByteW, z0]
  decide

/-- Joint witness for `write64_kommutiert`: both stores reach (`some`) in
    both orders, both footprints observably change (low bytes `0x00` become
    `0x08` and `0x18`), and both orders agree on every byte. Every premise
    of the commutation theorem is instantiated here. -/
theorem write64_kommutiert_zeuge :
    ∃ (m m1 m2 m_ab m_ba : Speicher) (a b : Adresse) (v w : Wort),
      v ≠ w ∧
      write64 m a v = some m1 ∧ write64 m1 b w = some m_ab ∧
      write64 m b w = some m2 ∧ write64 m2 a v = some m_ba ∧
      Disjunkt a b ∧
      m_ab.bytes (addrOff a 0) ≠ m.bytes (addrOff a 0) ∧
      m_ab.bytes (addrOff b 0) ≠ m.bytes (addrOff b 0) ∧
      (∀ x, m_ab.bytes x = m_ba.bytes x) := by
  refine ⟨zweiSpeicher0, zweiNachA, zweiNachB, zweiNachAB, zweiNachBA,
    0, 16, zweiWertV, zweiWertW,
    by decide, zweiSchrittA, zweiSchrittAB, zweiSchrittB, zweiSchrittBA,
    zweiDisjunkt, zweiWechseltA, zweiWechseltB, ?_⟩
  have h := write64_kommutiert _ _ _ _ _ _ _ _ _ zweiSchrittA zweiSchrittAB
    zweiSchrittB zweiSchrittBA zweiDisjunkt
  exact h.1

/- CUTS:
   - Target-memory commutation only, sequential over one `Speicher` at a
     time: no whole-program atomicity claim, no concurrent tearing claim,
     no TSO granularity/refinement (per-byte event hooks `leseEreignisse` /
     `schreibEreignisse` are reused for membership only here; the GX/TSO
     bridge stays with its lane).
   - OPEN (higher-level source obligations, never concluded from address
     disjointness here): publication / foreign readers / locks, i.e. no
     thread-privacy or ownership theorem; `StabilFuss` justifies a spill
     reload only once the source level owns the slot privately.
   - No decoder, encoder, instruction semantics, ABI/loader, cost transfer,
     source correspondence or final-image acceptance is proved here.
   - Only 64-bit `read64`/`write64` commute here; the 1/2/4-byte forms have
     the same `writeBytesN` shape and would commute the same way, but the
     width-indexed `readBreite`/`writeBreite` commutation is not stated.
   - Permissions are independent fields: commutation keeps them equal to
     the pre-state; no permission is ever created or widened by a store.
-/

#print axioms mem_Fuss_iff
#print axioms write64_trifft
#print axioms schreibbar8_aus_write64
#print axioms disjunkt_symm
#print axioms write64_kommutiert
#print axioms read64_erst_bleibt
#print axioms read64_nach_zwei_fremd
#print axioms stabilFuss_nach_schreiben
#print axioms stabilFuss_bleibt
#print axioms stabilFuss_liest
#print axioms zweiByteV
#print axioms zweiByteW
#print axioms zweiDisjunkt
#print axioms zweiSchrittA
#print axioms zweiSchrittB
#print axioms zweiSchrittAB
#print axioms zweiSchrittBA
#print axioms zweiWechseltA
#print axioms zweiWechseltB
#print axioms write64_kommutiert_zeuge

end Gabbro.Grammatik.X86
