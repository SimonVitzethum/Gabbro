/-
  File:      Grammatik/X86/SourceCodeFrame.lean
  Subject:   Represented source data stores leave decoded code alone (lane 634).

  Consumer of the accepted SourceMemory570 representation interface
  (`repOk`, `zahlWort`, `RepSlot`, `rep_schritt_bleibt` over the real
  `execStmt` table write) and the accepted ImageStoreFrame602 mapping
  frame (`codeFremd_von_abbildung`, fetch/decode preservation over real
  `write64`). A represented source data-store step (one `Stmt.assignSlot`
  through `execStmt` plus its matching target word write) cannot change
  the decoded executable bytes or the next fetch when the checked
  code/data mapping (pairwise `virtReich` verdict), section permission
  shapes (code executable/never-writable, data writable/never-executable)
  and explicit no-wrap bounds hold. Foreignness is DERIVED from the
  mapping in every main result, never assumed; the unchanged-memory facts
  come from the actual `write64`/`write8/16/32` store frames, never from an
  assumed-unchanged premise. Narrow, unaligned and multi-byte stores are
  connected through a width-generic foreignness notion; spanning,
  guard-crossing, wrap-around, overlap and writable-code shapes are
  refused by name (SM-SPAN, SM-SCHUTZ, SM-UMBRUCH, SM-UEBERLAPP, SM-WX).
  OS protection machinery is user/binding logic with contracts; this
  frame proves nothing about silicon or arbitrary virtual-memory
  behaviour. Full source-to-final-loaded-bytes validation stays OPEN.
-/
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.Parser.Uebersetze
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Regionen
import Grammatik.X86.TableLayout
import Grammatik.X86.Byteschritt
import Grammatik.X86.CodeImmutability
import Grammatik.X86.SourceMemory
import Grammatik.X86.ImageStoreFrame
import Grammatik.X86.Bild
import Grammatik.X86.RegionSeparation
import Grammatik.X86.OverlapRefusal

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze

/-- Width-generic code foreignness: every byte of the whole possible
    fetch window (`fetchCap` at `rip`) differs from every byte of the
    `n`-byte store footprint at `a`. `n = 8` is exactly `CodeFremd`. -/
def CodeFremdN (s : Zustand) (a : Adresse) (n : Nat) : Prop :=
  ∀ i : Nat, i < fetchCap → ∀ k : Nat, k < n →
    addrOff s.rip i ≠ addrOff a k

/-! ## 1. Width-generic foreignness and fetch frame.

    `CodeFremdN` with `n = 8` is `CodeFremd` by unfolding; the interval
    bridge below derives it from Nat order plus explicit no-wrap bounds on
    both sides, so modular aliasing near the top of the address space can
    never slip through (`umbruch_alias` in the producer). -/

/-- `CodeFremdN` at width 8 is `CodeFremd`. -/
theorem codeFremdN_acht (s : Zustand) (a : Adresse) :
    CodeFremdN s a 8 ↔ CodeFremd s a := by
  rfl

/-- INTERVAL TO GENERIC FOREIGNNESS: Nat-interval disjointness plus
    explicit no-wrap on the fetch window and on the `n`-byte footprint
    gives `CodeFremdN`. Every premise is used: `hrip`/`hA` place machine
    addition as Nat addition, `h` splits the intervals. -/
theorem codeFremdN_von_intervallen (s : Zustand) (a : Adresse) (n : Nat)
    (hrip : s.rip.toNat + fetchCap ≤ 2 ^ 64)
    (hA : a.toNat + n ≤ 2 ^ 64)
    (h : s.rip.toNat + fetchCap ≤ a.toNat ∨
      a.toNat + n ≤ s.rip.toNat) :
    CodeFremdN s a n := by
  have h15 : fetchCap = 15 := rfl
  rw [h15] at hrip h
  intro i hi k hk he
  rw [h15] at hi
  have hripNat := s.rip.isLt
  have haNat := a.isLt
  have e1 : (addrOff s.rip i).toNat = s.rip.toNat + i := by
    unfold addrOff
    have hi64 : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, hi64,
      Nat.mod_eq_of_lt (by omega : s.rip.toNat + i < 2 ^ 64)]
  have e2 : (addrOff a k).toNat = a.toNat + k := by
    unfold addrOff
    have hk64 : k % 2 ^ 64 = k := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, hk64,
      Nat.mod_eq_of_lt (by omega : a.toNat + k < 2 ^ 64)]
  have he2 := congrArg BitVec.toNat he
  rw [e1, e2] at he2
  omega

/-- FETCH FRAME, WIDTH-GENERIC: the executable-prefix fetch reads only
    its window, so any store that replaces `bytes` outside an `n`-byte
    footprint foreign to the window leaves the fetch unchanged. The
    permission equality and the byte frame are the exact facts each
    successful `write8/16/32/64` supplies; nothing about the store is
    assumed beyond them. -/
theorem holeFetchAux_nach_fremdN (m m' : Speicher) (a w : Adresse)
    (n : Nat) (off cap : Nat)
    (hperm : m'.ausfuehrbar = m.ausfuehrbar)
    (hframe : ∀ x : Adresse, (∀ k : Nat, k < n → x ≠ addrOff w k) →
      m'.bytes x = m.bytes x)
    (hdis : ∀ i : Nat, i < cap → ∀ k : Nat, k < n →
      addrOff a (off + i) ≠ addrOff w k) :
    holeFetchAux m' a off cap = holeFetchAux m a off cap := by
  induction cap generalizing off with
  | zero => rfl
  | succ ncap ih =>
    have hexe : m'.ausfuehrbar (addrOff a off) =
        m.ausfuehrbar (addrOff a off) := by rw [hperm]
    simp only [holeFetchAux, hexe]
    by_cases hc : m.ausfuehrbar (addrOff a off) = true
    · rw [if_pos hc, if_pos hc]
      have hbyte : m'.bytes (addrOff a off) = m.bytes (addrOff a off) :=
        hframe _ (fun k hk => by
          have h0 := hdis 0 (by omega) k hk
          rwa [Nat.add_zero] at h0)
      rw [hbyte]
      congr 1
      apply ih
      intro i hi k hk
      have h := hdis (i + 1) (Nat.succ_lt_succ hi) k hk
      have he : off + 1 + i = off + (i + 1) := by omega
      rw [← he] at h
      exact h
    · rw [if_neg hc, if_neg hc]

/-- EXECUTE PERMISSION AGREEMENT: two memories with equal execute
    fields agree on every `ausfuehrbarN` prefix. Used for the decode
    leg of every narrow store. -/
theorem ausfuehrbarN_gleich (m m' : Speicher)
    (hperm : m'.ausfuehrbar = m.ausfuehrbar) (b : Adresse) (n : Nat) :
    ausfuehrbarN m' b n = ausfuehrbarN m b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ausfuehrbarN, ih]
    rw [hperm]

/-! ## 2. Narrow-store preservation (1/2/4-byte forms).

    Real `write8`/`write16`/`write32` steps: fetch and decode survive a
    successful narrow store foreign to the code window in the matching
    width. Alignment plays no role here — an unaligned narrow store is
    still byte-exact — so unaligned shapes are admitted by these lemmas
    and refused only where the selected contract/profile demands
    alignment (see `OverlapRefusal.zugriffOk` and §4 below). -/

/-- FETCH PRESERVED after a successful foreign 1-byte store. -/
theorem geholt_nach_write8_fremd (s : Zustand) (m' : Speicher)
    (a : Adresse) (v : Wort)
    (hwr : write8 s.speicher a v = some m') (hdis : CodeFremdN s a 1) :
    geholt { s with speicher := m' } = geholt s := by
  have hperm := write8_erhaelt_berechtigungen _ _ _ _ hwr
  unfold geholt CodeFremdN at *
  apply holeFetchAux_nach_fremdN s.speicher m' s.rip a 1 0 fetchCap
    hperm.2.2 _ _
  · intro x hx
    exact write8_rahmen s.speicher m' a x v hwr hx
  · intro i hi k hk
    simpa using hdis i hi k hk

/-- DECODE PRESERVED after a successful foreign 1-byte store. -/
theorem fetchDekodiert_nach_write8_fremd (s : Zustand) (m' : Speicher)
    (a : Adresse) (v : Wort)
    (hwr : write8 s.speicher a v = some m') (hdis : CodeFremdN s a 1) :
    fetchDekodiert { s with speicher := m' } = fetchDekodiert s := by
  have hg : geholt { s with speicher := m' } = geholt s :=
    geholt_nach_write8_fremd s m' a v hwr hdis
  have hperm := write8_erhaelt_berechtigungen _ _ _ _ hwr
  have hexe : ∀ n, ausfuehrbarN m' s.rip n =
      ausfuehrbarN s.speicher s.rip n :=
    fun n => ausfuehrbarN_gleich s.speicher m' hperm.2.2 s.rip n
  unfold fetchDekodiert
  rw [hg]
  dsimp only
  simp only [hexe]

/-- FETCH PRESERVED after a successful foreign 2-byte store. -/
theorem geholt_nach_write16_fremd (s : Zustand) (m' : Speicher)
    (a : Adresse) (v : Wort)
    (hwr : write16 s.speicher a v = some m') (hdis : CodeFremdN s a 2) :
    geholt { s with speicher := m' } = geholt s := by
  have hperm := write16_erhaelt_berechtigungen _ _ _ _ hwr
  unfold geholt CodeFremdN at *
  apply holeFetchAux_nach_fremdN s.speicher m' s.rip a 2 0 fetchCap
    hperm.2.2 _ _
  · intro x hx
    exact write16_rahmen s.speicher m' a x v hwr hx
  · intro i hi k hk
    simpa using hdis i hi k hk

/-- DECODE PRESERVED after a successful foreign 2-byte store. -/
theorem fetchDekodiert_nach_write16_fremd (s : Zustand) (m' : Speicher)
    (a : Adresse) (v : Wort)
    (hwr : write16 s.speicher a v = some m') (hdis : CodeFremdN s a 2) :
    fetchDekodiert { s with speicher := m' } = fetchDekodiert s := by
  have hg : geholt { s with speicher := m' } = geholt s :=
    geholt_nach_write16_fremd s m' a v hwr hdis
  have hperm := write16_erhaelt_berechtigungen _ _ _ _ hwr
  have hexe : ∀ n, ausfuehrbarN m' s.rip n =
      ausfuehrbarN s.speicher s.rip n :=
    fun n => ausfuehrbarN_gleich s.speicher m' hperm.2.2 s.rip n
  unfold fetchDekodiert
  rw [hg]
  dsimp only
  simp only [hexe]

/-- FETCH PRESERVED after a successful foreign 4-byte store. -/
theorem geholt_nach_write32_fremd (s : Zustand) (m' : Speicher)
    (a : Adresse) (v : Wort)
    (hwr : write32 s.speicher a v = some m') (hdis : CodeFremdN s a 4) :
    geholt { s with speicher := m' } = geholt s := by
  have hperm := write32_erhaelt_berechtigungen _ _ _ _ hwr
  unfold geholt CodeFremdN at *
  apply holeFetchAux_nach_fremdN s.speicher m' s.rip a 4 0 fetchCap
    hperm.2.2 _ _
  · intro x hx
    exact write32_rahmen s.speicher m' a x v hwr hx
  · intro i hi k hk
    simpa using hdis i hi k hk

/-- DECODE PRESERVED after a successful foreign 4-byte store. -/
theorem fetchDekodiert_nach_write32_fremd (s : Zustand) (m' : Speicher)
    (a : Adresse) (v : Wort)
    (hwr : write32 s.speicher a v = some m') (hdis : CodeFremdN s a 4) :
    fetchDekodiert { s with speicher := m' } = fetchDekodiert s := by
  have hg : geholt { s with speicher := m' } = geholt s :=
    geholt_nach_write32_fremd s m' a v hwr hdis
  have hperm := write32_erhaelt_berechtigungen _ _ _ _ hwr
  have hexe : ∀ n, ausfuehrbarN m' s.rip n =
      ausfuehrbarN s.speicher s.rip n :=
    fun n => ausfuehrbarN_gleich s.speicher m' hperm.2.2 s.rip n
  unfold fetchDekodiert
  rw [hg]
  dsimp only
  simp only [hexe]

/-- UNALIGNED POSITIVE PROBE: a 1-byte store at the unaligned address
    8196 (provably not 8-aligned) succeeds inside the data cell, is
    foreign to the code window at 4096 through the interval bridge, and
    preserves fetch and decode while observably changing the byte.
    Alignment is no fetch-preservation premise. -/
theorem unversetzt_byte_bleibt :
    ∃ m' : Speicher,
      write8 ketteStart.speicher (BitVec.ofNat 64 8196) 7 = some m' ∧
      addrAusgerichtet (BitVec.ofNat 64 8196) 8 = false ∧
      CodeFremdN ketteStart (BitVec.ofNat 64 8196) 1 ∧
      geholt { ketteStart with speicher := m' } = geholt ketteStart ∧
      fetchDekodiert { ketteStart with speicher := m' } =
        fetchDekodiert ketteStart ∧
      m'.bytes (BitVec.ofNat 64 8196) ≠
        ketteStart.speicher.bytes (BitVec.ofNat 64 8196) := by
  have hsch : schreibbarN ketteSpeicher (BitVec.ofNat 64 8196) 1 = true := by
    decide
  have hwr : write8 ketteStart.speicher (BitVec.ofNat 64 8196) 7 =
      some { ketteSpeicher with
        bytes := writeBytesN ketteSpeicher (BitVec.ofNat 64 8196) 7 1 } := by
    show write8 ketteSpeicher (BitVec.ofNat 64 8196) 7 = some _
    unfold write8
    rw [if_pos hsch]
  have hfremd : CodeFremdN ketteStart (BitVec.ofNat 64 8196) 1 := by
    apply codeFremdN_von_intervallen _ _ 1 (by decide) (by decide)
    exact Or.inl (by decide)
  have hhit : writeBytesN ketteSpeicher (BitVec.ofNat 64 8196) 7 1
      (BitVec.ofNat 64 8196) = wortByte 7 0 := by
    have h := writeBytesN_hit ketteSpeicher (BitVec.ofNat 64 8196) 7 1 0
      (by decide) (by decide)
    rwa [addrOff_null] at h
  have halt : ketteSpeicher.bytes (BitVec.ofNat 64 8196) =
      BitVec.ofNat 8 0 := by
    decide
  refine ⟨_, hwr, probe_unversetzt_8196, hfremd,
    geholt_nach_write8_fremd _ _ _ _ hwr hfremd,
    fetchDekodiert_nach_write8_fremd _ _ _ _ hwr hfremd, ?_⟩
  show writeBytesN ketteSpeicher (BitVec.ofNat 64 8196) 7 1
      (BitVec.ofNat 64 8196) ≠ ketteStart.speicher.bytes (BitVec.ofNat 64 8196)
  rw [hhit]
  show wortByte 7 0 ≠ ketteSpeicher.bytes (BitVec.ofNat 64 8196)
  rw [halt]
  decide

/-! ## 3. Main connection: a represented source data store leaves code alone.

    The source leg is the real `execStmt` table write plus its matching
    target word write (`rep_schritt_bleibt`); the target leg derives
    foreignness from the checked image mapping (`codeFremd_von_abbildung`)
    and runs the actual store frame. The permission shapes contribute the
    checked W^X verdicts. No premise states an unchanged memory; every
    unchanged byte is derived from the successful store. -/

/-- MAIN FRAME: one represented source data-store step (real `execStmt`
    `assignSlot` plus matching target `write64`) preserves the fetched
    window, the decode outcome and every fetched code byte whenever the
    checked code/data mapping (pairwise mapped-interval verdict), the
    section permission shapes and the explicit no-wrap bounds hold — and
    establishes the representation at the written slot with read-back.
    Every premise is used: the source premises through
    `rep_schritt_bleibt`, the mapping through the derived foreignness,
    `hsMem` to transport the store, the shapes through W^X. -/
theorem quellDaten_schritt_laesst_code {D : Deklaration} {V : Vertrag D}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (t : D.Tab) (f : D.Feld t)
    (lo hi : Int) (hT : D.typ t f = .int lo hi)
    (base len off : Nat)
    (hOk : repOk (D.typ t f) base len off = true)
    (i : Expr D Γ Λ (.index (D.count t)))
    (e : Expr D Γ Λ (D.typ t f))
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (σ : World D) (ρ : Env D Γ)
    (σL : World D) (hLese : σL = σ.lese Λ (i.orte ++ e.orte))
    (k : Int) (v : Zahl lo hi)
    (hk : (eval σL i σL ρ).n = k)
    (hv : (cast (congrArg (Wert D) hT) (eval σL e σL ρ) :
      Wert D (.int lo hi)) = v)
    (a : Adresse) (m m' : Speicher)
    (σ' : World D) (ρ' : Env D Γ)
    (hExec : execStmt O passes R (Stmt.assignSlot (l := l) t f i e hw hL) σ ρ =
      .ok σ' ρ')
    (hTgt : write64 m a (zahlWort v) = some m')
    (hRd : lesbar8 m a = true)
    (s : Zustand) (hsMem : s.speicher = m)
    (bild : Bild) (bias : Nat) (sc sd : Abschnitt)
    (hmc : sc ∈ bild.abschnitte) (hmd : sd ∈ bild.abschnitte)
    (hne : abschnittAlsRegion bias sc ≠ abschnittAlsRegion bias sd)
    (hpaar : paarweise (virtReich bias) bild.abschnitte = true)
    (hcode : istCodeAbschnitt sc = true)
    (hdat : istDatenAbschnitt sd = true)
    (hrip : ∀ j : Nat, j < fetchCap →
      abteilFinden bild.abschnitte bias (s.rip.toNat + j) = some sc)
    (hstore : ∀ q : Nat, q < 8 →
      abteilFinden bild.abschnitte bias (a.toNat + q) = some sd)
    (hripNF : s.rip.toNat + fetchCap ≤ 2 ^ 64)
    (hANF : a.toNat + 8 ≤ 2 ^ 64) :
    RepSlot t k f lo hi hT a m' σ' ∧
      (∃ w, read64 m' a = some w ∧ wortZahl lo hi w = some v) ∧
      geholt { s with speicher := m' } = geholt s ∧
      fetchDekodiert { s with speicher := m' } = fetchDekodiert s ∧
      (∀ j : Nat, j < (geholt s).length →
        m'.bytes (addrOff s.rip j) = s.speicher.bytes (addrOff s.rip j)) ∧
      wxOk sc = true ∧ wxOk sd = true := by
  have hRep := rep_schritt_bleibt O passes R t f lo hi hT base len off hOk
    i e hw hL σ ρ σL hLese k v hk hv a m m' σ' ρ' hExec hTgt hRd
  have hFremd := codeFremd_von_abbildung s a bild bias sc sd hmc hmd hne
    hpaar hrip hstore hripNF hANF
  have hwr : write64 s.speicher a (zahlWort v) = some m' := by
    rw [hsMem]
    exact hTgt
  have hwx1 : wxOk sc = true := istCodeAbschnitt_wx sc hcode
  have hwx2 : wxOk sd = true := istDatenAbschnitt_wx sd hdat
  refine ⟨hRep.1, hRep.2, ?_, ?_, ?_, hwx1, hwx2⟩
  · exact geholt_nach_erlaubtem_schreiben s m' a (zahlWort v) hwr hFremd
  · exact fetchDekodiert_nach_erlaubtem_schreiben s m' a (zahlWort v) hwr
      hFremd
  · intro j hj
    exact codeBytes_nach_erlaubtem_schreiben s m' a (zahlWort v) j hwr
      hFremd hj

/-! ## 4. Named refusals: the exact self-modifying/permission cases.

    SM-WX: a section both writable and executable is refused by the
    checked image verdict (generic over sections). SM-SPAN: an 8-byte
    store whose footprint crosses a section end is refused by permission
    (memory unchanged by construction). SM-SCHUTZ: a footprint crossing
    into the unmapped guard past the data end is not contained in any
    carrier. SM-UMBRUCH: at the top of the address space the no-wrap
    bound fails, so no interval-disjointness verdict applies.
    SM-UEBERLAPP (a store at `rip` is never foreign) is the generic
    producer `an_rip_nicht_fremd`, cited in the joint witness. -/

/-- SM-WX (generic): a writable and executable section meets no image
    check. Both premises are used. -/
theorem wx_schreibbar_code_verweigert (s : Abschnitt)
    (hwr : s.schreibbar = true) (hexe : s.ausfuehrbar = true) :
    wxOk s = false := by
  simp [wxOk, hwr, hexe]

/-- SM-SPAN (data end): an 8-byte store at `0x102004` crosses the end of
    the eight-byte data section (`0x102000 .. 0x102008`), so write
    permission fails and the store is refused with memory unchanged by
    construction. -/
theorem datenende_spanne_verweigert :
    write64 (geladen rahmenBild 0x100000) (BitVec.ofNat 64 0x102004) 42 =
      none := by
  apply write64_verweigert _ _ _
  decide

/-- SM-SPAN (code end): an 8-byte store at `0x10100C` starts inside the
    executable code section (`0x101000 .. 0x101010`, never writable) and
    crosses its end, so write permission fails and the store is refused
    with memory unchanged by construction. -/
theorem codeende_spanne_verweigert :
    write64 (geladen rahmenBild 0x100000) (BitVec.ofNat 64 0x10100C) 42 =
      none := by
  apply write64_verweigert _ _ _
  decide

/-- SM-SCHUTZ (guard): an 8-byte footprint at `0x102006` crosses the end
    of the data carrier into the unmapped guard, so the checker admits
    it against no carrier extent. -/
theorem schutz_fuss_aussen :
    fussEnthalten (Fuss (natAdresse 0x102006))
      (wortTraeger 0x102000) = false := by
  decide

/-- SM-UMBRUCH (wrap): at the top of the address space the no-wrap bound
    fails, so no Nat-interval disjointness verdict covers a store there —
    modular aliasing can never be argued away. -/
theorem umbruch_kein_rahmen :
    ¬ OhneUmbruch (BitVec.ofNat 64 (2 ^ 64 - 1)) := by
  unfold OhneUmbruch
  decide

/-! ## 5. Joint witness: source write and target store, both memory-changing.

    One table that the witness function writes, one reached `execStmt`
    step moving the source slot `0 → 42`, one real target word write at
    the laid-out data address moving the byte `0 → 42`, preserved
    fetch/decode on the accepted frame image, and the planted refusals.
    SM-UEBERLAPP rides as the generic producer `an_rip_nicht_fremd`. -/

/-- JOINT WITNESS for `quellDaten_schritt_laesst_code`: every premise
    holds jointly — checked admission, writer contract, evaluated index
    and value, the reached source step, the matching target store with
    read permission, the checked mapping verdict with its section
    membership and permission shapes — and so do the representation with
    read-back, the preserved fetch/decode, the memory changes on both
    sides, and the overlap, code-store, span and W^X refusals. -/
theorem quellDaten_schritt_laesst_code_zeuge :
    ∃ (σ' : World witD) (ρ' : Env witD []) (m' : Speicher),
      repOk (witD.typ () ()) 0x102000 8 0 = true ∧
      witV.schreibt () = true ∧
      (eval witSL witI witSL Env.nil).n = 0 ∧
      (cast (congrArg (Wert witD) witHT)
        (eval witSL witE witSL Env.nil) :
        Wert witD (.int 0 100)) = witVal ∧
      execStmt witO 0 witR
        (Stmt.assignSlot (l := false) () () witI witE witHw witHL)
        witSigma Env.nil = .ok σ' ρ' ∧
      write64 (geladen rahmenBild 0x100000) (slotAddr 0x102000 0)
        (zahlWort witVal) = some m' ∧
      lesbar8 (geladen rahmenBild 0x100000)
        (slotAddr 0x102000 0) = true ∧
      paarweise (virtReich 0x100000) rahmenBild.abschnitte = true ∧
      RepSlot () 0 () 0 100 witHT (slotAddr 0x102000 0) m' σ' ∧
      (∃ w, read64 m' (slotAddr 0x102000 0) = some w ∧
        wortZahl 0 100 w = some witVal) ∧
      geholt { rahmenStart with speicher := m' } = geholt rahmenStart ∧
      fetchDekodiert { rahmenStart with speicher := m' } =
        fetchDekodiert rahmenStart ∧
      (witSigma.slots () 0 ()).n = 0 ∧
      (σ'.slots () 0 ()).n = 42 ∧
      m'.bytes (slotAddr 0x102000 0) ≠
        (geladen rahmenBild 0x100000).bytes (slotAddr 0x102000 0) ∧
      ¬ CodeFremd rahmenStart rahmenStart.rip ∧
      write64 (geladen rahmenBild 0x100000) (BitVec.ofNat 64 0x101000)
        42 = none ∧
      write64 (geladen rahmenBild 0x100000) (BitVec.ofNat 64 0x102004)
        42 = none ∧
      wohlgeformt .p48 rahmenBild = true := by
  have hOk : repOk (witD.typ () ()) 0x102000 8 0 = true := by
    rw [witHT]
    decide
  have hsch : schreibbar8 (geladen rahmenBild 0x100000)
      (slotAddr 0x102000 0) = true := by
    decide
  have hles : lesbar8 (geladen rahmenBild 0x100000)
      (slotAddr 0x102000 0) = true := by
    decide
  have hTgt : write64 (geladen rahmenBild 0x100000)
      (slotAddr 0x102000 0) (zahlWort witVal) =
      some { geladen rahmenBild 0x100000 with
        bytes := writeBytes (geladen rahmenBild 0x100000)
          (slotAddr 0x102000 0) (zahlWort witVal) } := by
    unfold write64
    rw [if_pos hsch]
  have hExecFull : ∃ σ' ρ', execStmt witO 0 witR
      (Stmt.assignSlot (l := false) () () witI witE witHw witHL)
      witSigma Env.nil = .ok σ' ρ' := by
    simp only [execStmt]
    exact ⟨_, _, rfl⟩
  obtain ⟨σ', ρ', hExec⟩ := hExecFull
  have hrip : ∀ j : Nat, j < fetchCap →
      abteilFinden rahmenBild.abschnitte 0x100000
        (rahmenStart.rip.toNat + j) = some rahmenCode := by
    intro j hj
    rw [rahmen_rip_summe]
    have h15 : fetchCap = 15 := rfl
    have hj15 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨
        j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨
        j = 14 := by omega
    rcases hj15 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have eA : (slotAddr 0x102000 0).toNat = 0x102000 := by
    decide
  have hstore : ∀ q : Nat, q < 8 →
      abteilFinden rahmenBild.abschnitte 0x100000
        ((slotAddr 0x102000 0).toNat + q) = some rahmenDaten := by
    intro q hq
    rw [eA]
    have hq8 : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨
        q = 7 := by omega
    rcases hq8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hMain := quellDaten_schritt_laesst_code witO 0 witR () () 0 100
    witHT 0x102000 8 0 hOk witI witE witHw witHL witSigma Env.nil witSL
    rfl 0 witVal rfl rfl _ _ _ σ' ρ' hExec hTgt hles rahmenStart rfl
    rahmenBild 0x100000 rahmenCode rahmenDaten (by decide) (by decide)
    rahmen_reg_ungleich rahmen_paar rahmen_code_code rahmen_daten_daten
    hrip hstore (by decide) (by decide)
  have hByte : writeBytes (geladen rahmenBild 0x100000)
      (slotAddr 0x102000 0) (zahlWort witVal) (slotAddr 0x102000 0) =
      wortByte (zahlWort witVal) 0 := by
    have h := writeBytesN_hit (geladen rahmenBild 0x100000)
      (slotAddr 0x102000 0) (zahlWort witVal) 8 0 (by decide) (by decide)
    rw [addrOff_null] at h
    unfold writeBytes
    exact h
  have hDataByte : (geladen rahmenBild 0x100000).bytes
      (slotAddr 0x102000 0) = BitVec.ofNat 8 0 := by
    decide
  have hBytes : ({ geladen rahmenBild 0x100000 with
      bytes := writeBytes (geladen rahmenBild 0x100000)
        (slotAddr 0x102000 0) (zahlWort witVal) } : Speicher).bytes
      (slotAddr 0x102000 0) ≠
      (geladen rahmenBild 0x100000).bytes (slotAddr 0x102000 0) := by
    show writeBytes (geladen rahmenBild 0x100000) (slotAddr 0x102000 0)
      (zahlWort witVal) (slotAddr 0x102000 0) ≠ _
    rw [hByte, hDataByte]
    decide
  refine ⟨σ', ρ', _, hOk, witHw, rfl, rfl, hExec, hTgt, hles, rahmen_paar,
    hMain.1, hMain.2.1, hMain.2.2.1, hMain.2.2.2.1, rfl, ?hAfter, hBytes,
    an_rip_nicht_fremd rahmenStart, rahmen_code_schreiben_verweigert,
    datenende_spanne_verweigert, rahmenBild_wohlgeformt⟩
  case hAfter =>
    cases hExec
    rfl

/- CUTS:
    Proved here, over the ACTUAL accepted vocabulary (`execStmt` table
    writes, `repOk`/`RepSlot`/`rep_schritt_bleibt`, `write64/8/16/32`
    with their permission checks and store frames, `geholt`,
    `fetchDekodiert`, `codeFremd_von_abbildung`, `geladen`,
    `abteilFinden`, `paarweise (virtReich _)`):
    - width-generic code foreignness with its Nat-interval bridge and
      explicit no-wrap bounds (§1);
    - fetch/decode preservation for real 1/2/4-byte stores plus an
      unaligned positive probe (§2);
    - the main frame: one represented source data-store step preserves
      fetch, decode and every fetched code byte under the checked
      mapping, permission shapes and bounds, with representation and
      read-back (§3);
    - named self-modifying/permission refusals SM-WX (generic),
      SM-SPAN at both section ends, SM-SCHUTZ (guard), SM-UMBRUCH
      (wrap), SM-UEBERLAPP via the generic producer (§4);
    - a joint witness with source slot change `0 → 42`, target byte
      change, preserved fetch/decode and all planted refusals (§5).
    NOT proved here, and not claimed:
    - No validator soundness: `valX86_sound` and the generic
      source-to-final-loaded-bytes closing theorem stay OPEN; this file
      covers one `assignSlot` shape on one `.int` slot, not whole units.
    - No source correspondence for narrow stores: §2 is target-only;
      only the 8-byte leg carries a `RepSlot` through `rep_schritt_bleibt`.
    - No concurrency claim: every step is sequential over one `Speicher`;
      per-access TSO/GX refinement stays with the TSO bridge.
    - No hardware claim: everything runs over the model `Speicher`
      function, not silicon; caches, TLBs, store buffers and
      self-modifying-code coherence stay open.
    - No OS/loader claim: the image mapping is a checked premise about
      numbers; the protection mechanism that enforces it at runtime is
      user/binding logic with contracts, never granted here.
    - No int->ptr conversion: slot addresses are target-side
      `natAdresse` computations over accepted layout bases, never source
      values cast to pointers.
-/

#print axioms CodeFremdN
#print axioms codeFremdN_acht
#print axioms codeFremdN_von_intervallen
#print axioms holeFetchAux_nach_fremdN
#print axioms ausfuehrbarN_gleich
#print axioms geholt_nach_write8_fremd
#print axioms fetchDekodiert_nach_write8_fremd
#print axioms geholt_nach_write16_fremd
#print axioms fetchDekodiert_nach_write16_fremd
#print axioms geholt_nach_write32_fremd
#print axioms fetchDekodiert_nach_write32_fremd
#print axioms unversetzt_byte_bleibt
#print axioms quellDaten_schritt_laesst_code
#print axioms wx_schreibbar_code_verweigert
#print axioms datenende_spanne_verweigert
#print axioms codeende_spanne_verweigert
#print axioms schutz_fuss_aussen
#print axioms umbruch_kein_rahmen
#print axioms quellDaten_schritt_laesst_code_zeuge

end Gabbro.Grammatik.X86
