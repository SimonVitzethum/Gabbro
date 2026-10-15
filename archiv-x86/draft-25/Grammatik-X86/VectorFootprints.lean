/-
  File:      Grammatik/X86/VectorFootprints.lean
  Subject:   Packed-vector byte footprints with checked extent and alias admission.

  Lane 426 (continuous Lean proof reserve): generic 16-byte footprints for
  the packed 128-bit words of `Vektor.lean` (two ordered canonical 8-byte
  chunks), over the canonical `Speicher.lean` byte vocabulary. Proves
  footprint membership/length, the Prop-to-Bool disjointness bridge the
  `OverlapRefusal.lean` checker consumes, vector-vector disjointness from
  checked Nat intervals, checked carrier extent (`fussEnthalten`) with a
  partial-tail refusal, and alias admission/refusal through the existing
  `klassifiziere`/`aliasZulassen` policy. No vector store atomicity is
  claimed (the torn intermediate state of `vecWrite_teilt` stands); full
  native vector lowering stays OPEN (see CUTS).
-/
import Grammatik.X86.Vektor
import Grammatik.X86.Regionen
import Grammatik.X86.OverlapRefusal

namespace Gabbro.Grammatik.X86

/-- The 16-byte footprint of a packed-vector access: the two ordered
    canonical 8-byte chunk footprints concatenated. Per-byte events, not
    one atomic occurrence. -/
def vecFuss (a : Adresse) : List Adresse :=
  Fuss a ++ Fuss (vecHiAddr a)

/-- A 16-byte vector carrier: a readable/writable, never-executable
    extent of exactly two words at `basis`. -/
def vecTraeger (basis : Nat) : Region :=
  { basis := basis, len := 16, lesbar := true,
    schreibbar := true, ausfuehrbar := false }

/-- A vector footprint is sixteen per-byte events. -/
theorem vecFuss_laenge (a : Adresse) : (vecFuss a).length = 16 := by
  simp [vecFuss, fuss_laenge]

/-- Membership in a vector footprint is membership in either chunk. -/
theorem vecFuss_mem (a x : Adresse) :
    x ∈ vecFuss a ↔ x ∈ Fuss a ∨ x ∈ Fuss (vecHiAddr a) := by
  simp [vecFuss]

/-- BRIDGE (missing fact the checker consumes): Prop footprint
    disjointness decides to a positive Bool answer over the two
    8-byte footprints. Every premise is used. -/
theorem fussDisjunktB_von_Disjunkt (a b : Adresse)
    (h : Disjunkt a b) : fussDisjunktB (Fuss a) (Fuss b) = true := by
  rw [fussDisjunktB, List.all_eq_true]
  intro x hx
  rw [List.all_eq_true]
  intro y hy
  rw [fuss_mem] at hx hy
  obtain ⟨i, hi, rfl⟩ := hx
  obtain ⟨j, hj, rfl⟩ := hy
  simp [h i j hi hj]

/-- The two chunks of one vector footprint are checker-disjoint under
    the explicit 16-byte no-wrap condition. -/
theorem vecFuss_chunks_disjunkt (a : Adresse) (h : OhneUmbruch16 a) :
    fussDisjunktB (Fuss a) (Fuss (vecHiAddr a)) = true :=
  fussDisjunktB_von_Disjunkt a (vecHiAddr a) (vecChunks_disjoint a h)

/-- The 16-byte no-wrap condition covers both 8-byte chunk checks. -/
theorem vecOhneUmbruch_chunks (a : Adresse) (h : OhneUmbruch16 a) :
    OhneUmbruch a ∧ OhneUmbruch (vecHiAddr a) := by
  unfold OhneUmbruch16 at h
  unfold OhneUmbruch
  have e0 : (vecHiAddr a).toNat = a.toNat + 8 :=
    addrOff_nat a 8 (by omega)
  omega

/-- Two vector footprints are checker-disjoint when their checked 16-byte
    Nat intervals are disjoint, under no-wrap on both sides. Every
    premise is used: `hA`/`hB` place all four chunk pairs, `h` separates
    the intervals. -/
theorem vecFuss_disjunkt (a b : Adresse)
    (hA : OhneUmbruch16 a) (hB : OhneUmbruch16 b)
    (h : a.toNat + 16 ≤ b.toNat ∨ b.toNat + 16 ≤ a.toNat) :
    fussDisjunktB (vecFuss a) (vecFuss b) = true := by
  obtain ⟨hA1, hA2⟩ := vecOhneUmbruch_chunks a hA
  obtain ⟨hB1, hB2⟩ := vecOhneUmbruch_chunks b hB
  have eA : (vecHiAddr a).toNat = a.toNat + 8 := by
    unfold OhneUmbruch16 at hA; exact addrOff_nat a 8 (by omega)
  have eB : (vecHiAddr b).toNat = b.toNat + 8 := by
    unfold OhneUmbruch16 at hB; exact addrOff_nat b 8 (by omega)
  have p11 := fussDisjunktB_von_Disjunkt a b
    (disjunkt_von_intervallen a b hA1 hB1 (by omega))
  have p12 := fussDisjunktB_von_Disjunkt a (vecHiAddr b)
    (disjunkt_von_intervallen a (vecHiAddr b) hA1 hB2 (by omega))
  have p21 := fussDisjunktB_von_Disjunkt (vecHiAddr a) b
    (disjunkt_von_intervallen (vecHiAddr a) b hA2 hB1 (by omega))
  have p22 := fussDisjunktB_von_Disjunkt (vecHiAddr a) (vecHiAddr b)
    (disjunkt_von_intervallen (vecHiAddr a) (vecHiAddr b) hA2 hB2 (by omega))
  rw [fussDisjunktB, List.all_eq_true]
  intro x hx
  rw [vecFuss_mem] at hx
  rw [List.all_eq_true]
  intro y hy
  rw [vecFuss_mem] at hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have hne : x ≠ y := by
      intro he; subst he
      exact (fussDisjunktB_klingt _ _ p11 x hx) hy
    exact bne_iff_ne.mpr hne
  · have hne : x ≠ y := by
      intro he; subst he
      exact (fussDisjunktB_klingt _ _ p12 x hx) hy
    exact bne_iff_ne.mpr hne
  · have hne : x ≠ y := by
      intro he; subst he
      exact (fussDisjunktB_klingt _ _ p21 x hx) hy
    exact bne_iff_ne.mpr hne
  · have hne : x ≠ y := by
      intro he; subst he
      exact (fussDisjunktB_klingt _ _ p22 x hx) hy
    exact bne_iff_ne.mpr hne

/-- A footprint with one byte outside the region is refused: the
    checked-extent refusal half every consumer reuses. -/
theorem fussEnthalten_verweigert_ausserhalb (f : List Adresse) (r : Region)
    (x : Adresse) (hx : x ∈ f) (hxin : inRegion r x.toNat = false) :
    fussEnthalten f r = false := by
  unfold fussEnthalten
  by_cases h : f.all (fun a => inRegion r a.toNat) = true
  · exfalso
    have hm := (List.all_eq_true.mp h) x hx
    rw [hxin] at hm
    exact Bool.false_ne_true hm
  · exact Bool.eq_false_iff.mpr h

/-- CHECKED EXTENT, ACCEPT: a 16-byte vector footprint at the carrier
    base lies inside its carrier, under the explicit no-wrap bound. -/
theorem vecFuss_in_traeger (c : Nat) (hwrap : c + 16 ≤ 2 ^ 64) :
    fussEnthalten (vecFuss (natAdresse c)) (vecTraeger c) = true := by
  have hi : vecHiAddr (natAdresse c) = natAdresse (c + 8) :=
    natAdresse_addrs c 8 (by omega)
  rw [fussEnthalten, List.all_eq_true]
  intro x hx
  rw [vecFuss_mem] at hx
  rcases hx with hx | hx
  · rw [fuss_mem] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    have had : (addrOff (natAdresse c) k).toNat = c + k := by
      have hnk := natAdresse_addrs c k (by omega)
      rw [hnk]
      unfold natAdresse
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    show inRegion (vecTraeger c) (addrOff (natAdresse c) k).toNat = true
    rw [had]
    unfold inRegion vecTraeger
    simp only [decide_eq_true_eq]
    omega
  · rw [hi, fuss_mem] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have had : (addrOff (natAdresse (c + 8)) j).toNat = c + 8 + j := by
      have hnk := natAdresse_addrs (c + 8) j (by omega)
      rw [hnk]
      unfold natAdresse
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    show inRegion (vecTraeger c) (addrOff (natAdresse (c + 8)) j).toNat = true
    rw [had]
    unfold inRegion vecTraeger
    simp only [decide_eq_true_eq]
    omega

/-- CHECKED EXTENT, PARTIAL-TAIL REFUSAL: a vector footprint starting
    eight bytes past the carrier base sticks its tail (bytes `c+16`
    through `c+23`) past the carrier end, so the checked extent refuses
    it. The last tail byte is the witness. -/
theorem vecFuss_teilschwanz_verweigert (c : Nat) (hwrap : c + 24 ≤ 2 ^ 64) :
    fussEnthalten (vecFuss (natAdresse (c + 8))) (vecTraeger c) = false := by
  have hi : vecHiAddr (natAdresse (c + 8)) = natAdresse (c + 16) :=
    natAdresse_addrs (c + 8) 8 (by omega)
  have had : (addrOff (natAdresse (c + 16)) 7).toNat = c + 23 := by
    have hnk := natAdresse_addrs (c + 16) 7 (by omega)
    rw [hnk, show (c + 16) + 7 = c + 23 from by omega]
    unfold natAdresse
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply fussEnthalten_verweigert_ausserhalb _ _
    (addrOff (vecHiAddr (natAdresse (c + 8))) 7)
  · rw [vecFuss_mem]
    right
    rw [hi, fuss_mem]
    exact ⟨7, by decide, rfl⟩
  · rw [hi, had]
    unfold inRegion vecTraeger
    simp only [decide_eq_false_iff_not]
    omega

/-- ALIAS ADMISSION: checker-disjoint vector footprints classify as
    `disjunkt` and pass the conservative policy. -/
theorem vecFuss_alias_zugelassen (a b : Adresse)
    (h : fussDisjunktB (vecFuss a) (vecFuss b) = true) :
    klassifiziere (vecFuss a) (vecFuss b) = .disjunkt ∧
      aliasZulassen (klassifiziere (vecFuss a) (vecFuss b)) = true := by
  refine ⟨klassifiziere_disjunkt _ _ h, ?_⟩
  rw [klassifiziere_disjunkt _ _ h]
  rfl

/-- ALIAS REFUSAL, CONCRETE: the vector footprints at 8192 and 8200
    share the eight tail bytes 8200..8207, so the classifier answers
    `unbekannt` and the policy refuses the pair. -/
theorem vecFuss_teilueberlapp_verweigert :
    klassifiziere (vecFuss (natAdresse 8192))
        (vecFuss (natAdresse 8200)) = .unbekannt ∧
      aliasZulassen (klassifiziere (vecFuss (natAdresse 8192))
        (vecFuss (natAdresse 8200))) = false := by
  have h1 : klassifiziere (vecFuss (natAdresse 8192))
      (vecFuss (natAdresse 8200)) = .unbekannt := by
    decide
  exact ⟨h1, by rw [h1]; rfl⟩

/-- JOINT WITNESS: a nonzero packed-vector store at address zero goes
    through both ordered chunk writes, reads back, and observably
    changes the byte; the footprint is admitted inside its carrier, the
    eight-byte-shifted tail is refused, and the next footprint is
    disjoint and alias-admitted. -/
theorem vectorFootprints_zeuge :
    ∃ (m' : Speicher) (v : Vektor),
      v ≠ 0 ∧ vecWrite vecZeugenSpeicher 0 v = some m' ∧
      vecRead m' 0 = some v ∧
      vecZeugenSpeicher.bytes 0 ≠ m'.bytes 0 ∧
      fussEnthalten (vecFuss (natAdresse 0)) (vecTraeger 0) = true ∧
      fussEnthalten (vecFuss (natAdresse 8)) (vecTraeger 0) = false ∧
      fussDisjunktB (vecFuss (natAdresse 0))
        (vecFuss (natAdresse 16)) = true ∧
      aliasZulassen (klassifiziere (vecFuss (natAdresse 0))
        (vecFuss (natAdresse 16))) = true := by
  have h1 : write64 vecZeugenSpeicher 0 (vLo vecZeugenVektor)
      = some vecZeugenM1 := by
    unfold write64
    have hc : schreibbar8 vecZeugenSpeicher 0 = true := rfl
    rw [if_pos hc]
    rfl
  have h2 : write64 vecZeugenM1 (vecHiAddr 0) (vHi vecZeugenVektor)
      = some vecZeugenM2 := by
    unfold write64
    have hc : schreibbar8 vecZeugenM1 (vecHiAddr 0) = true := rfl
    rw [if_pos hc]
    rfl
  have hw : vecWrite vecZeugenSpeicher 0 vecZeugenVektor
      = some vecZeugenM2 := by
    unfold vecWrite
    rw [h1]
    exact h2
  have hrd1 : lesbar8 vecZeugenSpeicher 0 = true := rfl
  have hrd2 : lesbar8 vecZeugenSpeicher (vecHiAddr 0) = true := rfl
  have hno : OhneUmbruch16 (0 : Adresse) := by
    unfold OhneUmbruch16
    decide
  have hback := vecRead_nach_write vecZeugenSpeicher vecZeugenM1
    vecZeugenM2 0 vecZeugenVektor h1 h2 hrd1 hrd2 hno
  have hhit : writeBytes vecZeugenSpeicher 0 (vLo vecZeugenVektor) 0 =
      wortByte (vLo vecZeugenVektor) 0 := by
    have h := writeBytesN_hit vecZeugenSpeicher 0 (vLo vecZeugenVektor) 8 0
      (by decide) (by decide)
    rwa [addrOff_null] at h
  have hmiss : ∀ k : Nat, k < 8 → (0 : Adresse) ≠ addrOff (vecHiAddr 0) k := by
    intro k hk hcon
    have e : (addrOff (vecHiAddr 0) k).toNat = 8 + k := by
      have e0 : (vecHiAddr (0 : Adresse)).toNat = 8 := by decide
      have hkk : (vecHiAddr (0 : Adresse)).toNat + k < 2 ^ 64 := by omega
      rw [addrOff_nat _ _ hkk, e0]
    have z : (0 : Adresse).toNat = 0 := by decide
    have hcon2 := congrArg BitVec.toNat hcon
    rw [z, e] at hcon2
    omega
  have hframe : vecZeugenM2.bytes 0 = vecZeugenM1.bytes 0 :=
    writeBytesN_miss vecZeugenM1 (vecHiAddr 0) (vHi vecZeugenVektor) 8 0 hmiss
  have hchg : vecZeugenSpeicher.bytes 0 ≠ vecZeugenM2.bytes 0 := by
    rw [hframe]
    show BitVec.ofNat 8 0 ≠ vecZeugenM1.bytes 0
    have e1 : vecZeugenM1.bytes 0 =
        writeBytes vecZeugenSpeicher 0 (vLo vecZeugenVektor) 0 := rfl
    rw [e1, hhit]
    decide
  have hA0 : OhneUmbruch16 (natAdresse 0) := by
    unfold OhneUmbruch16
    decide
  have hA16 : OhneUmbruch16 (natAdresse 16) := by
    unfold OhneUmbruch16
    decide
  have hinter : (natAdresse 0).toNat + 16 ≤ (natAdresse 16).toNat := by
    decide
  have hdis := vecFuss_disjunkt (natAdresse 0) (natAdresse 16) hA0 hA16
    (Or.inl hinter)
  have hadm := (vecFuss_alias_zugelassen _ _ hdis).2
  exact ⟨vecZeugenM2, vecZeugenVektor, by decide, hw, hback, hchg,
    vecFuss_in_traeger 0 (by decide),
    vecFuss_teilschwanz_verweigert 0 (by decide), hdis, hadm⟩

/- CUTS:
    - 16-byte footprints only: `vecFuss` is the concatenation of the two
      ordered canonical 8-byte chunk footprints of `Vektor.lean`; every
      lemma is sequential over one canonical `Speicher`. No vector store
      atomicity is claimed: the torn intermediate state proved by
      `vecWrite_teilt` stands, and footprint disjointness never implies
      atomicity or reordering of shared operations.
    - No native vector lowering: no decoder/ABI/image claim, no source
      correspondence (lowering to `P`/`exec`), no fault order across
      lanes, no tearing correspondence against the per-access TSO bridge,
      no FP lanes, no call-log preservation (`FolgeG`), no budget
      transfer for the two chunk accesses, no progress interaction.
      `simdFreigabe` stays `false` until all of it is proved.
    - No new ISA, no XMM register file, no second evaluator: only the
      existing `vecWrite`/`vecRead`/`vecHiAddr`/`Disjunkt`/`Fuss`/
      `fussEnthalten`/`klassifiziere`/`aliasZulassen`/`inRegion`/
      `natAdresse` vocabulary is consumed.
    - Hardware faults and profile admission refusals differ: `zugriffOk`-
      style admission here is validator/profile admission over
      footprints, never a hardware fault claim.
-/

#print axioms vecFuss_laenge
#print axioms vecFuss_mem
#print axioms fussDisjunktB_von_Disjunkt
#print axioms vecFuss_chunks_disjunkt
#print axioms vecOhneUmbruch_chunks
#print axioms vecFuss_disjunkt
#print axioms fussEnthalten_verweigert_ausserhalb
#print axioms vecFuss_in_traeger
#print axioms vecFuss_teilschwanz_verweigert
#print axioms vecFuss_alias_zugelassen
#print axioms vecFuss_teilueberlapp_verweigert
#print axioms vectorFootprints_zeuge

end Gabbro.Grammatik.X86
