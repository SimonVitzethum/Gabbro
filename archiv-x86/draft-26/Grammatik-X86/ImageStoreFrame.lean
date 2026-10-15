/-
  File:      Grammatik/X86/ImageStoreFrame.lean
  Subject:   Code and relocation preservation under real data stores.

  Lane 602: connects the checked `Bild` section mapping/permissions,
  `CodeImmutability` fetch preservation, actual `Speicher`/`Byteschritt`
  stores and `RelocatedExecution` patch-and-redecode into generic
  preservation of fetched/decode code bytes after permitted data stores.
  Physical disjointness is derived from the checked section mapping
  (pairwise `virtReich` disjointness) or selected-region separation, never
  from an unexplained noninterference premise. Relocated code, aliasing
  addresses and load bias are handled explicitly. No source-ownership to
  target-disjointness claim; the source layout bridge stays an explicit cut.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Bild
import Grammatik.X86.Byteschritt
import Grammatik.X86.CodeImmutability
import Grammatik.X86.RelocatedExecution
import Grammatik.X86.LoadedExecution
import Grammatik.X86.RegionSeparation
import Grammatik.X86.Vektor
import Grammatik.X86.TableLayout
import Grammatik.X86.Ausfuehrung

namespace Gabbro.Grammatik.X86

/-- A code section: executable and never writable (checked W^X shape). -/
def istCodeAbschnitt (s : Abschnitt) : Bool :=
  s.ausfuehrbar && !s.schreibbar

/-- A data section: writable and never executable (checked W^X shape). -/
def istDatenAbschnitt (s : Abschnitt) : Bool :=
  s.schreibbar && !s.ausfuehrbar

/-! ## 1. Section shapes and checked-place vocabulary.

    A permitted data store targets a writable, never-executable section;
    code lives in an executable, never-writable one. `datenStelle` and
    `codeStelle` read the checked loader map (`abteilFinden`), never a
    second register. -/

/-- W^X AGREEMENT (code): a code-shaped section meets the image W^X check. -/
theorem istCodeAbschnitt_wx (s : Abschnitt)
    (h : istCodeAbschnitt s = true) : wxOk s = true := by
  cases h1 : s.schreibbar <;> cases h2 : s.ausfuehrbar <;>
    simp_all [istCodeAbschnitt, wxOk]

/-- W^X AGREEMENT (data): a data-shaped section meets the image W^X check. -/
theorem istDatenAbschnitt_wx (s : Abschnitt)
    (h : istDatenAbschnitt s = true) : wxOk s = true := by
  cases h1 : s.schreibbar <;> cases h2 : s.ausfuehrbar <;>
    simp_all [istDatenAbschnitt, wxOk]

/-- Probe: the witness code section is code-shaped. -/
theorem probe_code_code : istCodeAbschnitt zeugenCode = true := by
  decide

/-- Probe: the witness data section is data-shaped. -/
theorem probe_daten_daten : istDatenAbschnitt zeugenDaten = true := by
  decide

/-- A data-shaped section is never code-shaped: the checks are exclusive. -/
theorem daten_nicht_code (s : Abschnitt)
    (h : istDatenAbschnitt s = true) : istCodeAbschnitt s = false := by
  cases h1 : s.schreibbar <;> cases h2 : s.ausfuehrbar <;>
    simp_all [istDatenAbschnitt, istCodeAbschnitt]

/-- A loaded address names a permitted data-store target: the checked map
    finds a data-shaped section there. -/
def datenStelle (bild : Bild) (bias a : Nat) : Bool :=
  match abteilFinden bild.abschnitte bias a with
  | none => false
  | some s => istDatenAbschnitt s

/-- A loaded address names code: the checked map finds a code-shaped
    section there. -/
def codeStelle (bild : Bild) (bias a : Nat) : Bool :=
  match abteilFinden bild.abschnitte bias a with
  | none => false
  | some s => istCodeAbschnitt s

/-- DATA PLACE IS WRITABLE: a data place carries the section's write
    permission through the loaded memory. -/
theorem datenStelle_schreibbar (bild : Bild) (bias a : Nat) (s : Abschnitt)
    (hfind : abteilFinden bild.abschnitte bias a = some s)
    (hdat : istDatenAbschnitt s = true) :
    ladenSchreibbar bild bias a = true := by
  have hperm := geladenSchreibbar_fund bild bias a s hfind
  simp only [istDatenAbschnitt, Bool.and_eq_true] at hdat
  rw [hperm, hdat.1]

/-- CODE PLACE IS EXECUTABLE: a code place carries execute permission. -/
theorem codeStelle_ausfuehrbar (bild : Bild) (bias a : Nat) (s : Abschnitt)
    (hfind : abteilFinden bild.abschnitte bias a = some s)
    (hcode : istCodeAbschnitt s = true) :
    ladenAusfuehrbar bild bias a = true := by
  have hperm := geladenAusfuehrbar_fund bild bias a s hfind
  simp only [istCodeAbschnitt, Bool.and_eq_true] at hcode
  rw [hperm, hcode.1]

/-- CODE PLACE IS NOT WRITABLE: a code place refuses write permission. -/
theorem codeStelle_nicht_schreibbar (bild : Bild) (bias a : Nat)
    (s : Abschnitt)
    (hfind : abteilFinden bild.abschnitte bias a = some s)
    (hcode : istCodeAbschnitt s = true) :
    ladenSchreibbar bild bias a = false := by
  have hperm := geladenSchreibbar_fund bild bias a s hfind
  cases h1 : s.schreibbar <;> cases h2 : s.ausfuehrbar <;>
    simp_all [istCodeAbschnitt]

/-! ## 2. Physical disjointness from the checked mapping.

    No unexplained noninterference premise: `CodeFremd` for a data store
    is derived from the image validator's own verdict — pairwise disjoint
    mapped virtual intervals (`paarweise (virtReich bias)`) plus stable
    section lookup at the fetch window and the store footprint — with
    explicit no-wrap bounds. Load bias and aliasing are handled because
    every address below is a LOADED sum (`bias + vaddr + offset`); a bare
    file offset or unbiased base never names a byte (see
    `bias_alias_beispiel`). A selected-region variant reuses the accepted
    `RegionSeparation` verdict instead of the image map. -/

/-- ALIASING NOTE: distinct `(bias, vaddr)` pairs load to the same byte.
    Every premise below therefore uses loaded sums, never a bare base. -/
theorem bias_alias_beispiel : 0x100000 + 0x1000 = 0 + 0x101000 := by
  decide

/- `Vektor.addrOff_nat` (machine addition is Nat addition under an
    explicit bound) is reused below; no second lemma is declared here. -/

/-- The checked map only finds sections whose biased range holds the
    address: a successful lookup carries its interval membership. -/
theorem abteilFinden_innen (secs : List Abschnitt) (bias a : Nat)
    (s : Abschnitt)
    (h : abteilFinden secs bias a = some s) :
    bias + s.vaddr ≤ a ∧ a < bias + s.vaddr + s.memLen := by
  induction secs with
  | nil => simp [abteilFinden] at h
  | cons t rest ih =>
    simp only [abteilFinden] at h
    by_cases hc : bias + t.vaddr ≤ a ∧ a < bias + t.vaddr + t.memLen
    · rw [if_pos hc] at h
      cases h
      exact hc
    · rw [if_neg hc] at h
      exact ih h

/-- MAPPING TO FOREIGNNESS: the fetch window lives in one section, the
    store footprint in another, and the validator's pairwise verdict keeps
    the mapped intervals apart — so the store is foreign to the code
    window. Every premise is used: membership for the two lookups, `hne`
    for distinctness, `hpaar` for the interval split, the stability
    hypotheses for containment, and the bounds against modular aliasing. -/
theorem codeFremd_von_abbildung (s : Zustand) (a : Adresse) (bild : Bild)
    (bias : Nat) (sc sd : Abschnitt)
    (hmc : sc ∈ bild.abschnitte) (hmd : sd ∈ bild.abschnitte)
    (hne : abschnittAlsRegion bias sc ≠ abschnittAlsRegion bias sd)
    (hpaar : paarweise (virtReich bias) bild.abschnitte = true)
    (hrip : ∀ i : Nat, i < fetchCap →
      abteilFinden bild.abschnitte bias (s.rip.toNat + i) = some sc)
    (hstore : ∀ k : Nat, k < 8 →
      abteilFinden bild.abschnitte bias (a.toNat + k) = some sd)
    (hripNF : s.rip.toNat + fetchCap ≤ 2 ^ 64)
    (hANF : a.toNat + 8 ≤ 2 ^ 64) :
    CodeFremd s a := by
  have htrenn := paarweise_virt_trennung bias bild.abschnitte hpaar
  have hmem1 : abschnittAlsRegion bias sc ∈
      bild.abschnitte.map (abschnittAlsRegion bias) :=
    List.mem_map.mpr ⟨sc, hmc, rfl⟩
  have hmem2 : abschnittAlsRegion bias sd ∈
      bild.abschnitte.map (abschnittAlsRegion bias) :=
    List.mem_map.mpr ⟨sd, hmd, rfl⟩
  have hreg := allePaareDisjunkt_mem _ htrenn _ _ hmem1 hmem2 hne
  have hsplit : bias + sc.vaddr + sc.memLen ≤ bias + sd.vaddr ∨
      bias + sd.vaddr + sd.memLen ≤ bias + sc.vaddr := by
    unfold regionDisjunkt abschnittAlsRegion at hreg
    simp only [decide_eq_true_eq] at hreg
    exact hreg
  intro i hi k hk he
  have e1 : (addrOff s.rip i).toNat = s.rip.toNat + i :=
    addrOff_nat _ _ (by have hlt := s.rip.isLt; omega)
  have e2 : (addrOff a k).toNat = a.toNat + k :=
    addrOff_nat _ _ (by have hlt := a.isLt; omega)
  have h1 := abteilFinden_innen bild.abschnitte bias (s.rip.toNat + i) sc
    (hrip i hi)
  have h2 := abteilFinden_innen bild.abschnitte bias (a.toNat + k) sd
    (hstore k hk)
  have he2 := congrArg BitVec.toNat he
  rw [e1, e2] at he2
  omega

/-- REGION TO FOREIGNNESS: the fetch window lies in one accepted region,
    the store footprint in a disjoint one — so the store is foreign to the
    code window. Reuses the accepted interval bridge. -/
theorem codeFremd_von_regionen (s : Zustand) (a : Adresse)
    (rc rd : Region)
    (hd : regionDisjunkt rc rd = true)
    (hrip : rc.basis ≤ s.rip.toNat ∧
      s.rip.toNat + fetchCap ≤ rc.basis + rc.len)
    (hstore : rd.basis ≤ a.toNat ∧ a.toNat + 8 ≤ rd.basis + rd.len)
    (hripNF : s.rip.toNat + fetchCap ≤ 2 ^ 64)
    (hANF : a.toNat + 8 ≤ 2 ^ 64) :
    CodeFremd s a := by
  have h15 : fetchCap = 15 := rfl
  apply codeFremd_von_intervallen s a (by omega) (by omega)
  unfold regionDisjunkt at hd
  simp only [decide_eq_true_eq] at hd
  omega

/-! ## 3. Preservation under a permitted data store.

    A permitted store is a successful `write64` whose footprint is foreign
    to the code window (foreignness derived in §2, never assumed). Fetch,
    decode and code bytes then survive through the accepted
    `CodeImmutability` frame. -/

/-- FETCH PRESERVED after a permitted data store. -/
theorem geholt_nach_erlaubtem_schreiben (s : Zustand) (m' : Speicher)
    (a : Adresse) (v : Wort)
    (hwr : write64 s.speicher a v = some m') (hdis : CodeFremd s a) :
    geholt { s with speicher := m' } = geholt s :=
  geholt_nach_fremd_schreiben s m' a v hwr hdis

/-- DECODE PRESERVED after a permitted data store. -/
theorem fetchDekodiert_nach_erlaubtem_schreiben (s : Zustand) (m' : Speicher)
    (a : Adresse) (v : Wort)
    (hwr : write64 s.speicher a v = some m') (hdis : CodeFremd s a) :
    fetchDekodiert { s with speicher := m' } = fetchDekodiert s :=
  fetchDekodiert_nach_fremd_schreiben s m' a v hwr hdis

/-- CODE BYTES STAY after a permitted data store. -/
theorem codeBytes_nach_erlaubtem_schreiben (s : Zustand) (m' : Speicher)
    (a : Adresse) (v : Wort) (i : Nat)
    (hwr : write64 s.speicher a v = some m') (hdis : CodeFremd s a)
    (hi : i < (geholt s).length) :
    m'.bytes (addrOff s.rip i) = s.speicher.bytes (addrOff s.rip i) :=
  codeBytes_bleiben s m' a v i hwr hdis hi

/-! ## 4. A patched branch keeps executing after a real data store.

    The relocated jump site (checked `PatchSite` over loaded sums, with
    its load bias) still steps to its intended mapped target after an
    actual `write64` elsewhere: fetch equality and the execute-permission
    prefix are transported across the store, then the accepted
    patch-and-redecode execution runs. The metadata only selects the
    bytes; fetch, decode and step run on actual memory. -/

/-- PATCHED BRANCH CONTINUES: `byteschritt` after the permitted data
    store reaches the relocation target. -/
theorem patchSite_sprung_nach_datenschreiben (ps : PatchSite)
    (d : BitVec 32)
    (hdisp : dispSigned d = ps.disp)
    (hgleich : (ps.ziel : Int) = (siteStart ps : Int) +
      (relocLen ps.art : Int) + ps.disp)
    (hfit : rel32Passt ps.disp = true)
    (hnext : siteNext ps < 2 ^ 64)
    (hziel : ps.ziel < 2 ^ 64)
    (hart : ps.art = .sprung)
    (z : Zustand) (suffix : List Byte)
    (a : Adresse) (v : Wort) (m' : Speicher)
    (hwr : write64 z.speicher a v = some m')
    (hdis : CodeFremd z a)
    (hwin : geholt z = relocBytes .sprung d ++ suffix)
    (hexe : ausfuehrbarN z.speicher z.rip
      (relocBytes .sprung d).length = true)
    (hrip : z.rip = BitVec.ofNat 64 (siteStart ps)) :
    byteschritt { z with speicher := m' } =
      .weiter { { z with speicher := m' } with
        rip := BitVec.ofNat 64 ps.ziel } := by
  have hg : geholt { z with speicher := m' } = geholt z :=
    geholt_nach_fremd_schreiben z m' a v hwr hdis
  have hexe' : ausfuehrbarN m' ({ z with speicher := m' } : Zustand).rip
      (relocBytes .sprung d).length = true := by
    have hkeep := ausfuehrbarN_nach_schreiben z.speicher m' a z.rip v
      (relocBytes .sprung d).length hwr
    rw [hkeep]
    exact hexe
  have hwin' : geholt { z with speicher := m' } =
      relocBytes .sprung d ++ suffix := by
    rw [hg]
    exact hwin
  have hrip' : ({ z with speicher := m' } : Zustand).rip =
      BitVec.ofNat 64 (siteStart ps) := by
    dsimp only
    exact hrip
  exact patchSite_sprung_schritt ps d hdisp hgleich hfit hnext hziel hart
    _ _ hwin' hexe' hrip'

/-! ## 5. Refusals: overlap, write-executable, permission.

    An overlapping store is never foreign (`an_rip_nicht_fremd`, generic);
    what it breaks is proved by the producer `ueberlapp_geaendert_zeuge`
    (a real store onto the code byte changes the fetch). A store into a
    code footprint of an accepted image is refused by permission
    (`codeStelle_schreiben_verweigert`, via `write64_verweigert`), and a
    writable code section is refused by the image check (concrete W^X
    refusal in §6). -/

/-- OVERLAP IS NEVER FOREIGN: a store at the instruction pointer shares
    byte zero of the window with byte zero of the footprint. -/
theorem an_rip_nicht_fremd (s : Zustand) : ¬ CodeFremd s s.rip := by
  intro h
  have h0 := h 0 (by decide) 0 (by decide)
  exact h0 rfl

/-- EIGHT-BYTE CODE FOOTPRINT IS NOT WRITABLE: every byte of a footprint
    inside one code-shaped section refuses write permission. -/
theorem codeStelle_schreibbar8_falsch (bild : Bild) (bias : Nat)
    (a : Adresse) (sc : Abschnitt)
    (hstab : ∀ k : Nat, k < 8 →
      abteilFinden bild.abschnitte bias (a.toNat + k) = some sc)
    (hcode : istCodeAbschnitt sc = true)
    (hfree : ∀ k : Nat, k < 8 →
      (addrOff a k).toNat = a.toNat + k) :
    schreibbar8 (geladen bild bias) a = false := by
  have each : ∀ k : Nat, k < 8 →
      (geladen bild bias).schreibbar (addrOff a k) = false := by
    intro k hk
    show ladenSchreibbar bild bias (addrOff a k).toNat = false
    rw [hfree k hk]
    exact codeStelle_nicht_schreibbar bild bias _ sc (hstab k hk) hcode
  have e0 := each 0 (by decide)
  have e1 := each 1 (by decide)
  have e2 := each 2 (by decide)
  have e3 := each 3 (by decide)
  have e4 := each 4 (by decide)
  have e5 := each 5 (by decide)
  have e6 := each 6 (by decide)
  have e7 := each 7 (by decide)
  unfold schreibbar8
  rw [e0, e1, e2, e3, e4, e5, e6, e7]
  decide

/-- PERMISSION REFUSAL: a store into a code footprint is refused — memory
    is unchanged by construction (`write64_verweigert`). -/
theorem codeStelle_schreiben_verweigert (bild : Bild) (bias : Nat)
    (a : Adresse) (v : Wort) (sc : Abschnitt)
    (hstab : ∀ k : Nat, k < 8 →
      abteilFinden bild.abschnitte bias (a.toNat + k) = some sc)
    (hcode : istCodeAbschnitt sc = true)
    (hfree : ∀ k : Nat, k < 8 →
      (addrOff a k).toNat = a.toNat + k) :
    write64 (geladen bild bias) a v = none :=
  write64_verweigert _ _ _
    (codeStelle_schreibbar8_falsch bild bias a sc hstab hcode hfree)

/-! ## 6. Joint witness: a relocated branch surviving a real data store.

    One accepted image under a nonzero load bias: five file bytes
    (`jump +16`) in a sixteen-byte executable section (the BSS tail covers
    the whole 15-byte fetch window), eight writable data bytes elsewhere,
    entry at the loaded sum. A real nonzero `write64` into the data
    section preserves fetch/decode and the branch still reaches its
    relocation target, while the byte observably changes; a store into the
    code footprint and a writable code section are refused. Source
    non-degeneracy (a function writing a table, a reached memory-changing
    run) rides along as explicit conjuncts; no claim is made that source
    ownership proves target disjointness (that bridge stays an open cut). -/

/-- Frame code section: `jump +16` file bytes, BSS tail covering the whole
    fetch window, executable and never writable. -/
def rahmenCode : Abschnitt :=
  { dateiOff := 0, dateiLen := 5, vaddr := 0x1000, memLen := 16,
    lesbar := true, schreibbar := false, ausfuehrbar := true, ausr := 4096 }

/-- Frame data section: eight writable bytes, never executable. -/
def rahmenDaten : Abschnitt :=
  { dateiOff := 5, dateiLen := 8, vaddr := 0x2000, memLen := 8,
    lesbar := true, schreibbar := true, ausfuehrbar := false, ausr := 4096 }

/-- Frame file: `jump +16` then eight zero data bytes. -/
def rahmenDatei : List Byte :=
  [natByte 233, natByte 16, natByte 0, natByte 0, natByte 0,
    natByte 0, natByte 0, natByte 0, natByte 0, natByte 0,
    natByte 0, natByte 0, natByte 0]

/-- Frame image: code plus data under checked base `0x100000`; the entry
    names the loaded sum, never base + offset. -/
def rahmenBild : Bild :=
  { datei := rahmenDatei
    abschnitte := [rahmenCode, rahmenDaten]
    reloks := []
    eintraege := [0x101000]
    modus := .param 0x100000 }

/-- Frame site: bias `0x100000`, base `0x1000`, jump +16 to `0x101015`. -/
def rahmenSite : PatchSite := ⟨0x100000, 0x1000, 0, .sprung, 16, 0x101015⟩

/-- Frame start state: loaded image, `rip` at the biased site start. -/
def rahmenStart : Zustand :=
  bildZustand rahmenBild 0x100000 (BitVec.ofNat 64 0x101000) ketteReg
    witnessFlags

/-- ACCEPTANCE: the frame image validates under profile 48. -/
theorem rahmenBild_wohlgeformt :
    wohlgeformt .p48 rahmenBild = true := by
  decide

/-- ACCEPTANCE: the checked site admits the biased forward jump. -/
theorem rahmen_patchSite_ok : patchSiteOk rahmenSite = true := by
  decide

/-- The frame code section is code-shaped. -/
theorem rahmen_code_code : istCodeAbschnitt rahmenCode = true := by
  decide

/-- The frame data section is data-shaped. -/
theorem rahmen_daten_daten : istDatenAbschnitt rahmenDaten = true := by
  decide

/-- The frame's mapped virtual intervals are pairwise disjoint. -/
theorem rahmen_paar :
    paarweise (virtReich 0x100000) rahmenBild.abschnitte = true := by
  decide

/-- The frame's code and data regions differ as checked regions. -/
theorem rahmen_reg_ungleich :
    abschnittAlsRegion 0x100000 rahmenCode ≠
      abschnittAlsRegion 0x100000 rahmenDaten := by
  decide

/-- The frame's loaded start address is the loaded sum. -/
theorem rahmen_rip_summe : rahmenStart.rip.toNat = 0x101000 := by
  decide

/-- FOREIGNNESS, DERIVED: the data store is foreign to the code window,
    through the checked mapping — no assumed noninterference. -/
theorem rahmen_fremd :
    CodeFremd rahmenStart (BitVec.ofNat 64 0x102000) := by
  apply codeFremd_von_abbildung rahmenStart _ rahmenBild 0x100000
    rahmenCode rahmenDaten (by decide) (by decide) rahmen_reg_ungleich
    rahmen_paar _ _ (by decide) (by decide)
  · intro i hi
    rw [rahmen_rip_summe]
    have h15 : fetchCap = 15 := rfl
    have hi15 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨
        i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨
        i = 14 := by omega
    rcases hi15 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro k hk
    have e : (BitVec.ofNat 64 0x102000).toNat = 0x102000 := by decide
    rw [e]
    have hk8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
        k = 7 := by omega
    rcases hk8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## 7. Store, fetch and continued branch on the frame image. -/

/-- The frame data cell is writable for eight bytes. -/
theorem rahmen_schreibbar8 :
    schreibbar8 (geladen rahmenBild 0x100000)
      (BitVec.ofNat 64 0x102000) = true := by
  decide

/-- The frame data cell is readable for eight bytes. -/
theorem rahmen_lesbar8 :
    lesbar8 (geladen rahmenBild 0x100000)
      (BitVec.ofNat 64 0x102000) = true := by
  decide

/-- The frame data cell reads zero before the store. -/
theorem rahmen_byte_null :
    (geladen rahmenBild 0x100000).bytes (BitVec.ofNat 64 0x102000) =
      BitVec.ofNat 8 0 := by
  decide

/-- MEMORY CHANGE: a nonzero store into the frame data cell reaches,
    reads back and observably changes the byte. -/
theorem rahmen_schreibt :
    ∃ m' : Speicher,
      write64 (geladen rahmenBild 0x100000) (BitVec.ofNat 64 0x102000)
        42 = some m' ∧
      read64 m' (BitVec.ofNat 64 0x102000) = some 42 ∧
      m'.bytes (BitVec.ofNat 64 0x102000) ≠
        (geladen rahmenBild 0x100000).bytes
          (BitVec.ofNat 64 0x102000) := by
  have hwr : write64 (geladen rahmenBild 0x100000)
      (BitVec.ofNat 64 0x102000) 42 =
      some { geladen rahmenBild 0x100000 with
        bytes := writeBytes (geladen rahmenBild 0x100000)
          (BitVec.ofNat 64 0x102000) 42 } := by
    unfold write64
    rw [if_pos rahmen_schreibbar8]
  refine ⟨_, hwr,
    read64_nach_write64 _ _ _ _ hwr rahmen_lesbar8, ?_⟩
  have hhit := writeBytesN_hit (geladen rahmenBild 0x100000)
    (BitVec.ofNat 64 0x102000) 42 8 0 (by decide) (by decide)
  rw [addrOff_null] at hhit
  show writeBytes (geladen rahmenBild 0x100000) (BitVec.ofNat 64 0x102000)
      42 (BitVec.ofNat 64 0x102000) ≠ _
  unfold writeBytes
  rw [hhit, rahmen_byte_null]
  decide

/-- FETCHED WINDOW: the frame start fetches the relocated jump bytes plus
    ten BSS zeros through the checked mapping. -/
theorem rahmen_geholt :
    geholt rahmenStart =
      relocBytes .sprung (BitVec.ofNat 32 16) ++
        List.replicate 10 (BitVec.ofNat 8 0) := by
  decide

/-- The consumed jump prefix is executable on the frame start. -/
theorem rahmen_hexe :
    ausfuehrbarN rahmenStart.speicher rahmenStart.rip
      (relocBytes .sprung (BitVec.ofNat 32 16)).length = true := by
  decide

/-- CONTINUED BRANCH: after any permitted data store at the frame data
    cell, the byte step still reaches the relocation target `0x101015`. -/
theorem rahmen_sprung_bleibt (m' : Speicher)
    (hwr : write64 rahmenStart.speicher (BitVec.ofNat 64 0x102000) 42 =
      some m') :
    byteschritt { rahmenStart with speicher := m' } = .weiter
      { { rahmenStart with speicher := m' } with
        rip := BitVec.ofNat 64 0x101015 } := by
  exact patchSite_sprung_nach_datenschreiben rahmenSite
    (BitVec.ofNat 32 16) (by decide) (by decide) (by decide) (by decide)
    (by decide) rfl rahmenStart _ _ _ _ hwr rahmen_fremd rahmen_geholt
    rahmen_hexe rfl

/-! ## 8. Planted refusals on the frame image. -/

/-- PERMISSION REFUSAL on the frame: a store into the code footprint
    (eight bytes from `0x101000`, inside the code section) is refused. -/
theorem rahmen_code_schreiben_verweigert :
    write64 (geladen rahmenBild 0x100000) (BitVec.ofNat 64 0x101000)
      42 = none := by
  apply codeStelle_schreiben_verweigert rahmenBild 0x100000 _ _
    rahmenCode _ rahmen_code_code _
  · intro k hk
    have hk8 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
        k = 7 := by omega
    rcases hk8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro k hk
    exact addrOff_nat _ _ (by
      have hlt : (BitVec.ofNat 64 0x101000).toNat = 0x101000 := by decide
      omega)

/-- Writable code section: refused by the checked image mapping. -/
def rahmenBildWx : Bild :=
  { rahmenBild with
    abschnitte := [{ rahmenCode with schreibbar := true }, rahmenDaten] }

/-- W^X REFUSAL on the frame: writable code is not an accepted image. -/
theorem rahmenBildWx_verweigert :
    wohlgeformt .p48 rahmenBildWx = false := by
  decide

/-- OVERLAP INSTANCE on the frame: a store at the frame `rip` is never
    foreign to its own code window. -/
theorem rahmen_an_rip_nicht_fremd :
    ¬ CodeFremd rahmenStart rahmenStart.rip :=
  an_rip_nicht_fremd rahmenStart

/-! ## 9. Joint witness: acceptance, site, source duties, store frame,
    continued branch and refusals. -/

/-- JOINT WITNESS: the frame image is accepted, the biased site is
    admitted, some source function writes a table (non-degenerate: table
    `konto` with writer `setze`), the reached instruction run observably
    changed memory, a real data store preserves fetch/decode, the patched
    branch still reaches its target, the stored byte observably changed,
    and the code-store and writable-code shapes are refused. -/
theorem rahmen_zeuge :
    wohlgeformt .p48 rahmenBild = true ∧
    patchSiteOk rahmenSite = true ∧
    (zeugenU.fns.get ⟨0, by decide⟩).schreibt = ["konto"] ∧
    ((lauf zeugeProg zeugeZustand).map
      (fun s => s.speicher.bytes (BitVec.ofNat 64 8192)) =
      some (BitVec.ofNat 8 42)) ∧
    (∃ m' : Speicher,
      write64 rahmenStart.speicher (BitVec.ofNat 64 0x102000) 42 =
        some m' ∧
      read64 m' (BitVec.ofNat 64 0x102000) = some 42 ∧
      geholt { rahmenStart with speicher := m' } = geholt rahmenStart ∧
      fetchDekodiert { rahmenStart with speicher := m' } =
        fetchDekodiert rahmenStart ∧
      byteschritt { rahmenStart with speicher := m' } = .weiter
        { { rahmenStart with speicher := m' } with
          rip := BitVec.ofNat 64 0x101015 } ∧
      m'.bytes (BitVec.ofNat 64 0x102000) ≠
        rahmenStart.speicher.bytes (BitVec.ofNat 64 0x102000)) ∧
    write64 (geladen rahmenBild 0x100000) (BitVec.ofNat 64 0x101000) 42 =
      none ∧
    wohlgeformt .p48 rahmenBildWx = false := by
  refine ⟨rahmenBild_wohlgeformt, rahmen_patchSite_ok, zeugenU_schreibt,
    zeuge_speicher_aendert_sich.2.1, ?_, rahmen_code_schreiben_verweigert,
    rahmenBildWx_verweigert⟩
  obtain ⟨m', hwr, hrd, hchg⟩ := rahmen_schreibt
  have hwr' : write64 rahmenStart.speicher (BitVec.ofNat 64 0x102000) 42 =
      some m' := hwr
  have hrd' : read64 m' (BitVec.ofNat 64 0x102000) = some 42 := hrd
  have hchg' : m'.bytes (BitVec.ofNat 64 0x102000) ≠
      rahmenStart.speicher.bytes (BitVec.ofNat 64 0x102000) := hchg
  refine ⟨m', hwr', hrd',
    geholt_nach_erlaubtem_schreiben _ _ _ _ hwr' rahmen_fremd,
    fetchDekodiert_nach_erlaubtem_schreiben _ _ _ _ hwr' rahmen_fremd,
    rahmen_sprung_bleibt m' hwr', hchg'⟩

/- CUTS:
    Proved here, over the ACTUAL accepted vocabulary (`Bild.wohlgeformt`,
    `geladen`/`abteilFinden`, `Speicher.write64`, `Byteschritt.geholt`,
    `fetchDekodiert`, `byteschritt`, `CodeImmutability.CodeFremd` and the
    `RelocatedExecution` patch-and-redecode correspondence):
    - section shapes with W^X agreement and checked-place permission facts
      (§1);
    - physical disjointness DERIVED from the checked mapping
      (`codeFremd_von_abbildung`: pairwise `virtReich` verdict plus stable
      lookups plus explicit no-wrap bounds) or from selected-region
      separation (`codeFremd_von_regionen`); load bias and aliasing handled
      by loaded sums throughout (`bias_alias_beispiel`);
    - fetch/decode/code-byte preservation under a permitted store (§3);
    - a patched jump site continuing to its relocation target after an
      actual data store (`patchSite_sprung_nach_datenschreiben`, §4);
    - generic overlap non-foreignness plus code-footprint permission
      refusal (§5);
    - a joint biased-image witness: acceptance, admitted site, memory
      change with read-back, preserved fetch/decode, continued branch,
      planted code-store and W^X refusals, with source non-degeneracy
      conjuncts (§§6–9).
    NOT proved here, and not claimed:
    - No source correspondence: nothing here claims the image is the
      emitted form of any source program, or that duties, contracts, costs
      or locks refine anything. The source conjuncts in `rahmen_zeuge`
      reuse the existing writer/reached-run facts as non-degeneracy
      evidence only; a source-layout to target-disjointness bridge stays
      an explicit open cut.
    - No call/conditional continuation after a store: only the
      unconditional jump is connected (`patchSite_ruf_schritt` and the
      conditional legs are the analogous consumer instantiations).
    - No whole-binary theorem: one site at its final layout only;
      multi-site convergence and the full `valX86` closing theorem stay
      with the consumer.
    - No hardware correspondence: everything runs over the model
      `Speicher` function, not silicon; caches, TLBs, store buffers and
      self-modifying-code coherence stay with the TSO bridge.
    - No concurrency claim: every step is sequential over one `Speicher`;
      the TSO/GX bridge stays with its owner.
    - Overlapping stores that WOULD change the fetch are proved by the
      producer `ueberlapp_geaendert_zeuge` over non-image (writable and
      executable) memory; no accepted image admits that shape (W^X).
-/

#print axioms istCodeAbschnitt
#print axioms istDatenAbschnitt
#print axioms istCodeAbschnitt_wx
#print axioms istDatenAbschnitt_wx
#print axioms probe_code_code
#print axioms probe_daten_daten
#print axioms daten_nicht_code
#print axioms datenStelle_schreibbar
#print axioms codeStelle_ausfuehrbar
#print axioms codeStelle_nicht_schreibbar
#print axioms bias_alias_beispiel
#print axioms abteilFinden_innen
#print axioms codeFremd_von_abbildung
#print axioms codeFremd_von_regionen
#print axioms geholt_nach_erlaubtem_schreiben
#print axioms fetchDekodiert_nach_erlaubtem_schreiben
#print axioms codeBytes_nach_erlaubtem_schreiben
#print axioms patchSite_sprung_nach_datenschreiben
#print axioms an_rip_nicht_fremd
#print axioms codeStelle_schreibbar8_falsch
#print axioms codeStelle_schreiben_verweigert
#print axioms rahmenBild_wohlgeformt
#print axioms rahmen_patchSite_ok
#print axioms rahmen_code_code
#print axioms rahmen_daten_daten
#print axioms rahmen_paar
#print axioms rahmen_reg_ungleich
#print axioms rahmen_rip_summe
#print axioms rahmen_fremd
#print axioms rahmen_schreibbar8
#print axioms rahmen_lesbar8
#print axioms rahmen_byte_null
#print axioms rahmen_schreibt
#print axioms rahmen_geholt
#print axioms rahmen_hexe
#print axioms rahmen_sprung_bleibt
#print axioms rahmen_code_schreiben_verweigert
#print axioms rahmenBildWx_verweigert
#print axioms rahmen_an_rip_nicht_fremd
#print axioms rahmen_zeuge

end Gabbro.Grammatik.X86
