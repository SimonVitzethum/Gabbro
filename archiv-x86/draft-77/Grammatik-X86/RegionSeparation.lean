/-
  File:      Grammatik/X86/RegionSeparation.lean
  Subject:   Finite pairwise separation checker over target regions.

  Lane 432 (continuous proof reserve): ONE generic reusable separation
  checker over finite `Region` lists from the canonical `Regionen.lean`
  vocabulary, sound for actual target regions, image layout and byte
  footprints. It decides pairwise `regionDisjunkt` plus an explicit
  no-wrap bound, bridges accepted image sections (`Bild.lean`) into
  regions, and derives actual `Speicher.lean` store frames (`read64`
  preservation, per-byte frame) for writes inside one accepted region.
  Consumer: the shared-IR validator skeleton (C5 / `valX86_sound` shape
  of IR-VALIDIERUNG.md) may consume `trennungOk` verdicts; no substitute
  IR is invented here. Source/linker/loader correspondence is OPEN.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Regionen
import Grammatik.X86.Bild
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.TableLayout

namespace Gabbro.Grammatik.X86

/-- Pairwise disjointness of a finite region list (quadratic decided check). -/
def allePaareDisjunkt : List Region → Bool
  | [] => true
  | r :: rest => rest.all (fun q => regionDisjunkt r q) && allePaareDisjunkt rest

/-- Explicit no-wrap bound of one region extent (Nat addition never wraps). -/
def keinUmbruchR (r : Region) : Bool :=
  decide (r.basis + r.len ≤ 2 ^ 64)

/-- Every listed region satisfies the no-wrap bound. -/
def alleOhneUmbruch : List Region → Bool
  | [] => true
  | r :: rest => keinUmbruchR r && alleOhneUmbruch rest

/-- The separation verdict: no wrap anywhere, pairwise disjoint everywhere. -/
def trennungOk : List Region → Bool
  | rs => alleOhneUmbruch rs && allePaareDisjunkt rs

/-- One image section as a target region under a load bias. -/
def abschnittAlsRegion (bias : Nat) (s : Abschnitt) : Region :=
  { basis := bias + s.vaddr, len := s.memLen, lesbar := s.lesbar,
    schreibbar := s.schreibbar, ausfuehrbar := s.ausfuehrbar }

/-- Disjointness is symmetric (used to read the one-sided check both ways). -/
theorem regionDisjunkt_symm (a b : Region) :
    regionDisjunkt a b = regionDisjunkt b a := by
  simp [regionDisjunkt, or_comm]

/-- SOUNDNESS of the pairwise check: every two distinct listed regions
    are disjoint. Every premise is used. -/
theorem allePaareDisjunkt_mem (rs : List Region)
    (h : allePaareDisjunkt rs = true) (a b : Region)
    (ha : a ∈ rs) (hb : b ∈ rs) (hne : a ≠ b) :
    regionDisjunkt a b = true := by
  induction rs generalizing a b with
  | nil => simp at ha
  | cons r rest ih =>
    simp only [allePaareDisjunkt, Bool.and_eq_true] at h
    obtain ⟨hhead, htail⟩ := h
    simp at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hne
    · rw [List.all_eq_true] at hhead
      exact hhead b hb
    · rw [List.all_eq_true] at hhead
      rw [regionDisjunkt_symm]
      exact hhead a ha
    · exact ih htail a b ha hb hne

/-- SOUNDNESS of the no-wrap check: every listed region meets the bound. -/
theorem alleOhneUmbruch_mem (rs : List Region)
    (h : alleOhneUmbruch rs = true) (a : Region) (ha : a ∈ rs) :
    keinUmbruchR a = true := by
  induction rs generalizing a with
  | nil => simp at ha
  | cons r rest ih =>
    simp only [alleOhneUmbruch, Bool.and_eq_true] at h
    obtain ⟨hhead, htail⟩ := h
    simp at ha
    rcases ha with rfl | ha
    · exact hhead
    · exact ih htail a ha

/-- The verdict carries the pairwise check (used by every frame consumer). -/
theorem trennungOk_paare (rs : List Region)
    (h : trennungOk rs = true) : allePaareDisjunkt rs = true := by
  unfold trennungOk at h
  rw [Bool.and_eq_true] at h
  exact h.2

/-- The verdict carries the no-wrap check (used by every frame consumer). -/
theorem trennungOk_ohne (rs : List Region)
    (h : trennungOk rs = true) : alleOhneUmbruch rs = true := by
  unfold trennungOk at h
  rw [Bool.and_eq_true] at h
  exact h.1

/-- BRIDGE from region disjointness to byte-footprint disjointness:
    two 8-byte accesses contained in disjoint regions have disjoint
    footprints (per-byte events, never one atomic occurrence). -/
theorem regionDisjunkt_fuss_disjunkt (a b : Region) (x y : Adresse)
    (hd : regionDisjunkt a b = true)
    (hx : a.basis ≤ x.toNat ∧ x.toNat + 8 ≤ a.basis + a.len)
    (hy : b.basis ≤ y.toNat ∧ y.toNat + 8 ≤ b.basis + b.len)
    (hAx : OhneUmbruch x) (hAy : OhneUmbruch y) :
    Disjunkt x y := by
  apply disjunkt_von_intervallen x y hAx hAy
  unfold regionDisjunkt at hd
  simp only [decide_eq_true_eq] at hd
  unfold OhneUmbruch at hAx hAy
  omega

/-- READ FRAME: a successful 8-byte store in one region preserves a read
    in a disjoint region. -/
theorem trennung_schreibt_rahmen (m m' : Speicher)
    (a b : Region) (x y : Adresse) (v : Wort)
    (hd : regionDisjunkt a b = true)
    (hx : a.basis ≤ x.toNat ∧ x.toNat + 8 ≤ a.basis + a.len)
    (hy : b.basis ≤ y.toNat ∧ y.toNat + 8 ≤ b.basis + b.len)
    (hAx : OhneUmbruch x) (hAy : OhneUmbruch y)
    (hwr : write64 m x v = some m') :
    read64 m' y = read64 m y := by
  exact read64_rahmen m m' x y v hwr
    (regionDisjunkt_fuss_disjunkt a b x y hd hx hy hAx hAy)

/-- BYTE FRAME: a successful 8-byte store in one region changes no byte
    of a disjoint region's extent. -/
theorem trennung_schreibt_bytes (m m' : Speicher)
    (a b : Region) (x : Adresse) (v : Wort)
    (hd : regionDisjunkt a b = true)
    (hx : a.basis ≤ x.toNat ∧ x.toNat + 8 ≤ a.basis + a.len)
    (hAx : OhneUmbruch x)
    (z : Adresse)
    (hz : b.basis ≤ z.toNat ∧ z.toNat < b.basis + b.len)
    (hwr : write64 m x v = some m') :
    m'.bytes z = m.bytes z := by
  apply write64_rahmen m m' x z v hwr
  intro k hk heq
  have ek := ohneUmbruch_addrs x hAx k hk
  have hzk : z.toNat = x.toNat + k := by rw [heq, ek]
  unfold regionDisjunkt at hd
  simp only [decide_eq_true_eq] at hd
  omega

/-- MULTI-REGION READ FRAME: under one accepted verdict, a store in one
    listed region preserves reads in any other listed region. -/
theorem trennung_rahmen_mehrere (rs : List Region)
    (m m' : Speicher) (a b : Region) (x y : Adresse) (v : Wort)
    (hsep : trennungOk rs = true)
    (ha : a ∈ rs) (hb : b ∈ rs) (hne : a ≠ b)
    (hx : a.basis ≤ x.toNat ∧ x.toNat + 8 ≤ a.basis + a.len)
    (hy : b.basis ≤ y.toNat ∧ y.toNat + 8 ≤ b.basis + b.len)
    (hAx : OhneUmbruch x) (hAy : OhneUmbruch y)
    (hwr : write64 m x v = some m') :
    read64 m' y = read64 m y := by
  have hd := allePaareDisjunkt_mem rs (trennungOk_paare rs hsep) a b ha hb hne
  exact trennung_schreibt_rahmen m m' a b x y v hd hx hy hAx hAy hwr

/-- MULTI-REGION BYTE FRAME: under one accepted verdict, a store in one
    listed region changes no byte of any other listed region's extent. -/
theorem trennung_bytes_mehrere (rs : List Region)
    (m m' : Speicher) (a b : Region) (x : Adresse) (v : Wort)
    (hsep : trennungOk rs = true)
    (ha : a ∈ rs) (hb : b ∈ rs) (hne : a ≠ b)
    (hx : a.basis ≤ x.toNat ∧ x.toNat + 8 ≤ a.basis + a.len)
    (hAx : OhneUmbruch x)
    (z : Adresse)
    (hz : b.basis ≤ z.toNat ∧ z.toNat < b.basis + b.len)
    (hwr : write64 m x v = some m') :
    m'.bytes z = m.bytes z := by
  have hd := allePaareDisjunkt_mem rs (trennungOk_paare rs hsep) a b ha hb hne
  exact trennung_schreibt_bytes m m' a b x v hd hx hAx z hz hwr

/-- One mapped interval pair gives region disjointness (the `virtReich`
    bounds are exactly the region bounds). -/
theorem virtReich_regionDisjunkt (bias : Nat) (s t : Abschnitt)
    (h : disjunktPaar (bias + s.vaddr) (bias + s.vaddr + s.memLen)
      (bias + t.vaddr) (bias + t.vaddr + t.memLen) = true) :
    regionDisjunkt (abschnittAlsRegion bias s)
      (abschnittAlsRegion bias t) = true := by
  unfold disjunktPaar regionDisjunkt abschnittAlsRegion at *
  simp only [decide_eq_true_eq] at h ⊢
  exact h

/-- LAYOUT BRIDGE: pairwise disjoint mapped virtual intervals give an
    accepted region list. The image validator stays the decider; this
    only re-reads its verdict in region vocabulary. -/
theorem paarweise_virt_trennung (bias : Nat) (secs : List Abschnitt)
    (h : paarweise (virtReich bias) secs = true) :
    allePaareDisjunkt (secs.map (abschnittAlsRegion bias)) = true := by
  induction secs with
  | nil => rfl
  | cons s rest ih =>
    simp only [paarweise, Bool.and_eq_true] at h
    obtain ⟨hhead, htail⟩ := h
    simp only [List.map_cons, allePaareDisjunkt, Bool.and_eq_true]
    constructor
    · rw [List.all_eq_true]
      intro q hq
      rw [List.mem_map] at hq
      obtain ⟨t, ht, rfl⟩ := hq
      rw [List.all_eq_true] at hhead
      have ht2 := hhead t ht
      simp only [virtReich] at ht2
      exact virtReich_regionDisjunkt bias s t ht2
    · exact ih htail

/-- MEMBER NO-WRAP: under one accepted verdict, every listed region
    meets the no-wrap bound (frame consumers need this per member). -/
theorem trennungMitglied_ohneUmbruch (rs : List Region)
    (h : trennungOk rs = true) (a : Region) (ha : a ∈ rs) :
    keinUmbruchR a = true :=
  alleOhneUmbruch_mem rs (trennungOk_ohne rs h) a ha

/-! ## Witnesses: three accepted regions, refusals, actual store frame. -/

/-- Witness region A: eight writable bytes at 8192. -/
def trennRegionA : Region :=
  { basis := 8192, len := 8, lesbar := true,
    schreibbar := true, ausfuehrbar := false }

/-- Witness region B: eight writable bytes at 8200. -/
def trennRegionB : Region :=
  { basis := 8200, len := 8, lesbar := true,
    schreibbar := true, ausfuehrbar := false }

/-- Witness region C: sixteen writable bytes at 65536. -/
def trennRegionC : Region :=
  { basis := 65536, len := 16, lesbar := true,
    schreibbar := true, ausfuehrbar := false }

/-- The three-region witness list. -/
def trennRegionen : List Region :=
  [trennRegionA, trennRegionB, trennRegionC]

/-- ACCEPTED: the three witness regions separate (no wrap, pairwise disjoint). -/
theorem trennung_zeugen_ok : trennungOk trennRegionen = true := by
  decide

/-- The first two witness regions are disjoint (single-pair probe). -/
theorem trennDisjunktAB :
    regionDisjunkt trennRegionA trennRegionB = true := by
  decide

/-- Overlapping probe region: `[8196, 8204)` shares bytes with region A. -/
def trennRegionUeberlapp : Region :=
  { basis := 8196, len := 8, lesbar := true,
    schreibbar := true, ausfuehrbar := false }

/-- Wrapping probe region: `[2 ^ 64 - 4, 2 ^ 64 + 4)` leaves 64 bits. -/
def trennRegionUmbruch : Region :=
  { basis := 2 ^ 64 - 4, len := 8, lesbar := true,
    schreibbar := true, ausfuehrbar := false }

/-- OVERLAP REFUSAL: `[8192, 8200)` and `[8196, 8204)` share bytes. -/
theorem trennUeberlapp_verweigert :
    allePaareDisjunkt [trennRegionA, trennRegionUeberlapp] = false := by
  decide

/-- WRAP REFUSAL: `[2 ^ 64 - 4, 2 ^ 64 + 4)` leaves 64 bits. -/
theorem trennUmbruch_verweigert :
    alleOhneUmbruch [trennRegionUmbruch] = false := by
  decide

/-- A wrapping extent fails the whole verdict, not just one leg. -/
theorem trennUmbruch_trennung_verweigert :
    trennungOk [trennRegionUmbruch] = false := by
  decide

/-- Witness memory: zero bytes, fully readable/writable, never executable. -/
def trennSpeicher : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0
    lesbar := fun _ => true
    schreibbar := fun _ => true
    ausfuehrbar := fun _ => false }

/-- The 8-byte access at 8192 lies in region A (decided containment). -/
theorem trennEnthaltenA :
    trennRegionA.basis ≤ (natAdresse 8192).toNat ∧
    (natAdresse 8192).toNat + 8 ≤
      trennRegionA.basis + trennRegionA.len := by
  decide

/-- The 8-byte access at 8200 lies in region B (decided containment). -/
theorem trennEnthaltenB :
    trennRegionB.basis ≤ (natAdresse 8200).toNat ∧
    (natAdresse 8200).toNat + 8 ≤
      trennRegionB.basis + trennRegionB.len := by
  decide

/-- No-wrap facts for both witness access addresses. -/
theorem trennOhne8192 : OhneUmbruch (natAdresse 8192) := by
  unfold OhneUmbruch
  decide

theorem trennOhne8200 : OhneUmbruch (natAdresse 8200) := by
  unfold OhneUmbruch
  decide

/-- Region A is writable for eight bytes at 8192 in the witness memory. -/
theorem trennSchreibbar8_8192 :
    schreibbar8 trennSpeicher (natAdresse 8192) = true := by
  decide

/-- Region B is readable for eight bytes at 8200 in the witness memory. -/
theorem trennLesbar8_8200 :
    lesbar8 trennSpeicher (natAdresse 8200) = true := by
  decide

/-- The witness read at 8200 succeeds with value zero (so the preserved
    read below is a real successful read, never a vacuous `none`). -/
theorem trennLiest8200 :
    read64 trennSpeicher (natAdresse 8200) = some 0 := by
  unfold read64
  rw [if_pos trennLesbar8_8200]
  decide

/-- POSITIVE ACTUAL STORE FRAME: a nonzero `write64` at 8192 (region A)
    goes through, the `read64` at 8200 (region B) is preserved, the byte
    at 8200 is unchanged, and the byte at 8192 observably changed. The
    read/byte preservation runs through the generic separation lemmas. -/
theorem rahmen_zeugen_schreibt :
    ∃ (m' : Speicher),
      write64 trennSpeicher (natAdresse 8192) 42 = some m' ∧
      read64 m' (natAdresse 8200) =
        read64 trennSpeicher (natAdresse 8200) ∧
      read64 trennSpeicher (natAdresse 8200) = some 0 ∧
      m'.bytes (natAdresse 8200) =
        trennSpeicher.bytes (natAdresse 8200) ∧
      trennSpeicher.bytes (natAdresse 8192) ≠
        m'.bytes (natAdresse 8192) := by
  have hwr : write64 trennSpeicher (natAdresse 8192) 42 =
      some { trennSpeicher with
        bytes := writeBytes trennSpeicher (natAdresse 8192) 42 } := by
    unfold write64
    rw [if_pos trennSchreibbar8_8192]
  refine ⟨_, hwr, ?_, ?_, ?_, ?_⟩
  · exact trennung_schreibt_rahmen trennSpeicher _ trennRegionA
      trennRegionB _ _ 42 trennDisjunktAB trennEnthaltenA
      trennEnthaltenB trennOhne8192 trennOhne8200 hwr
  · exact trennLiest8200
  · exact trennung_schreibt_bytes trennSpeicher _ trennRegionA
      trennRegionB _ 42 trennDisjunktAB trennEnthaltenA
      trennOhne8192 _ ⟨by decide, by decide⟩ hwr
  · have hhit := writeBytesN_hit trennSpeicher (natAdresse 8192) 42 8 0
      (by decide) (by decide)
    rw [addrOff_null] at hhit
    show BitVec.ofNat 8 0 ≠
      writeBytes trennSpeicher (natAdresse 8192) 42 (natAdresse 8192)
    unfold writeBytes
    rw [hhit]
    decide

/-! ## Image witnesses: an accepted three-section image feeds the checker. -/

/-- Witness file: 32 zero bytes backing all three sections. -/
def trennDatei : List Byte :=
  List.replicate 32 (BitVec.ofNat 8 0)

/-- Witness section A: eight writable bytes at 8192. -/
def trennAbschnittA : Abschnitt :=
  { dateiOff := 0, dateiLen := 8, vaddr := 8192, memLen := 8,
    lesbar := true, schreibbar := true, ausfuehrbar := false, ausr := 8 }

/-- Witness section B: eight writable bytes at 8200. -/
def trennAbschnittB : Abschnitt :=
  { dateiOff := 8, dateiLen := 8, vaddr := 8200, memLen := 8,
    lesbar := true, schreibbar := true, ausfuehrbar := false, ausr := 8 }

/-- Witness section C: sixteen writable bytes at 65536. -/
def trennAbschnittC : Abschnitt :=
  { dateiOff := 16, dateiLen := 16, vaddr := 65536, memLen := 16,
    lesbar := true, schreibbar := true, ausfuehrbar := false, ausr := 8 }

/-- The three-section witness image: fixed bias, no entries, no relocations. -/
def trennBild : Bild :=
  { datei := trennDatei
    abschnitte := [trennAbschnittA, trennAbschnittB, trennAbschnittC]
    reloks := []
    eintraege := []
    modus := .fest }

/-- The witness image is accepted under profile 48. -/
theorem trennBild_wohlgeformt :
    wohlgeformt .p48 trennBild = true := by
  decide

/-- Its mapped virtual intervals are pairwise disjoint (decided layout). -/
theorem trennBild_paar :
    paarweise (virtReich 0) trennBild.abschnitte = true := by
  decide

/-- IMAGE-TO-REGION: the accepted image's sections separate as regions,
    through the generic layout bridge. -/
theorem trennBild_trennung :
    allePaareDisjunkt
      (trennBild.abschnitte.map (abschnittAlsRegion 0)) = true :=
  paarweise_virt_trennung 0 _ trennBild_paar

/-! ## Joint witness: verdict, writer, reached run and store frame. -/

/-- JOINT WITNESS: the verdict accepts three regions, some source function
    writes a table (non-degenerate: table `konto` with writer `setze`), the
    reached instruction run observably changed memory (byte 42 at 8192),
    and a real store in region A preserves region B through the generic
    multi-region frame. -/
theorem trennung_zeuge :
    trennungOk trennRegionen = true ∧
    (zeugenU.fns.get ⟨0, by decide⟩).schreibt = ["konto"] ∧
    ((lauf zeugeProg zeugeZustand).map
      (fun s => s.speicher.bytes (BitVec.ofNat 64 8192)) =
      some (BitVec.ofNat 8 42)) ∧
    (∃ (m' : Speicher),
      write64 trennSpeicher (natAdresse 8192) 42 = some m' ∧
      read64 m' (natAdresse 8200) =
        read64 trennSpeicher (natAdresse 8200) ∧
      trennSpeicher.bytes (natAdresse 8192) ≠
        m'.bytes (natAdresse 8192)) := by
  refine ⟨trennung_zeugen_ok, zeugenU_schreibt,
    zeuge_speicher_aendert_sich.2.1, ?_⟩
  obtain ⟨m', hwr, hrd, _, _, hchg⟩ := rahmen_zeugen_schreibt
  exact ⟨m', hwr, hrd, hchg⟩

/-- VERDICT-LEVEL FRAME WITNESS: under the accepted three-region verdict,
    every successful store in region A preserves reads in regions B and C;
    membership and inequality are decided, the frame is the generic lemma. -/
theorem trennung_rahmen_zeugen (m m' : Speicher) (v : Wort)
    (hx : trennRegionA.basis ≤ (natAdresse 8192).toNat ∧
      (natAdresse 8192).toNat + 8 ≤
        trennRegionA.basis + trennRegionA.len)
    (hyB : trennRegionB.basis ≤ (natAdresse 8200).toNat ∧
      (natAdresse 8200).toNat + 8 ≤
        trennRegionB.basis + trennRegionB.len)
    (hwr : write64 m (natAdresse 8192) v = some m') :
    read64 m' (natAdresse 8200) = read64 m (natAdresse 8200) := by
  exact trennung_rahmen_mehrere trennRegionen m m' trennRegionA
    trennRegionB _ _ v trennung_zeugen_ok (by decide) (by decide)
    (by decide) hx hyB trennOhne8192 trennOhne8200 hwr

/-- VERDICT-LEVEL BYTE FRAME WITNESS: under the accepted three-region
    verdict, every successful store in region A changes no byte of
    region B's extent; the byte membership is decided, the frame is the
    generic multi-region lemma. -/
theorem trennung_bytes_zeugen (m m' : Speicher) (v : Wort)
    (hx : trennRegionA.basis ≤ (natAdresse 8192).toNat ∧
      (natAdresse 8192).toNat + 8 ≤
        trennRegionA.basis + trennRegionA.len)
    (hz : trennRegionB.basis ≤ (natAdresse 8200).toNat ∧
      (natAdresse 8200).toNat < trennRegionB.basis + trennRegionB.len)
    (hwr : write64 m (natAdresse 8192) v = some m') :
    m'.bytes (natAdresse 8200) = m.bytes (natAdresse 8200) := by
  exact trennung_bytes_mehrere trennRegionen m m' trennRegionA
    trennRegionB _ v trennung_zeugen_ok (by decide) (by decide)
    (by decide) hx trennOhne8192 _ hz hwr

/- CUTS:
    - No source correspondence: nothing here claims the regions are the
      lowering of any Gabbro table, duty, contract, cost or template, and
      no `Zielsatz/Spec` statement is touched. The joint witness only
      reuses the existing writer fact (`zeugenU_schreibt`) and the reached
      run (`zeuge_speicher_aendert_sich`) as non-degeneracy evidence.
    - No freshness claim: `trennungOk` checks given regions; fresh regions
      are capabilities from checked `reserviere`, never number-to-pointer
      casts. `natAdresse` names addresses for probes only.
    - No loader/image integration beyond the bridge: `paarweise_virt_trennung`
      re-reads the image validator's verdict in region vocabulary; mapping,
      entries, relocations and the loader contract stay with `Bild.lean`.
    - No concurrency claim: disjointness is sequential footprint
      disjointness over one `Speicher`; per-access TSO refinement and any
      multi-byte atomicity stay with the TSO bridge. `Fuss` addresses are
      per-byte events, not one atomic occurrence.
    - No decoder, encoder, instruction semantics, ABI, cost transfer,
      budget, progress, timing or whole-image acceptance is proved here.
    - Consumer interface: the shared-IR validator skeleton (C5 /
      `valX86_sound` shape of IR-VALIDIERUNG.md) may consume `trennungOk`
      verdicts; no substitute IR is invented here.
    - Alignment beyond containment is target data: the checker decides
      extents and disjointness only; declared alignment stays with the
      layout/profile that declares it.
-/

#print axioms regionDisjunkt_symm
#print axioms allePaareDisjunkt_mem
#print axioms alleOhneUmbruch_mem
#print axioms trennungOk_paare
#print axioms trennungOk_ohne
#print axioms trennungMitglied_ohneUmbruch
#print axioms regionDisjunkt_fuss_disjunkt
#print axioms trennung_schreibt_rahmen
#print axioms trennung_schreibt_bytes
#print axioms trennung_rahmen_mehrere
#print axioms trennung_bytes_mehrere
#print axioms virtReich_regionDisjunkt
#print axioms paarweise_virt_trennung
#print axioms trennung_zeugen_ok
#print axioms trennDisjunktAB
#print axioms trennUeberlapp_verweigert
#print axioms trennUmbruch_verweigert
#print axioms trennUmbruch_trennung_verweigert
#print axioms trennEnthaltenA
#print axioms trennEnthaltenB
#print axioms trennOhne8192
#print axioms trennOhne8200
#print axioms trennSchreibbar8_8192
#print axioms trennLesbar8_8200
#print axioms trennLiest8200
#print axioms rahmen_zeugen_schreibt
#print axioms trennBild_wohlgeformt
#print axioms trennBild_paar
#print axioms trennBild_trennung
#print axioms trennung_zeuge
#print axioms trennung_rahmen_zeugen
#print axioms trennung_bytes_zeugen

end Gabbro.Grammatik.X86
