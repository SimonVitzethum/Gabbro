/-
  File:      Grammatik/X86/BridgeWrite.lean
  Subject:   Projected TSO stores to source W writes (admitted word profile).

  Lane 573 (wave B, Lean-first): consumer of the ACCEPTED `TSOHistory`
  (`histVon`/`sichtVon`) and `SourceMemory` (`RepSlot`/`rep_schritt_bleibt`)
  interfaces over the canonical `TSO`/`Speicher` vocabulary. Issue is
  proved invisible (stutter); a single byte flush is proved NOT a carrier
  write (tearing guard via `wort_fuss_reisst`); the guarded whole-word
  install is tied to the real source slot-write transition through
  `rep_schritt_bleibt` (derived from `execStmt`, never assumed). FIFO
  order is retained and foreign-drain limits are proved refusals. The
  full per-access `SchrittW` simulation stays an explicit OPEN obstruction
  (byte vs carrier granularity, needs per-rule O-access decomposition).
-/
import Grammatik.X86.TSOHistory
import Grammatik.X86.SourceMemory
import Grammatik.X86.WordAtomicity

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik
open Speichermodell

/-! ## 1. Issue is invisible: stutter at word and carrier level. -/

/-- An issued (buffered, unflushed) byte store changes no canonical word
    observation: the issue step keeps `s.mem` byte-identical
    (`issue_kein_speicher`), so every `read64` read-back is unchanged.
    Visibility needs a flush; issuing alone is stutter. -/
theorem issue_beobachtet_bleibt (s s' : TSOZustand) (c : Nat)
    (a b : Adresse) (v : Byte) (w : Wort)
    (h : issueByte s c a v = some s')
    (hrd : read64 s.mem b = some w) :
    read64 s'.mem b = some w := by
  unfold issueByte at h
  by_cases hc : s.mem.schreibbar a = true
  · rw [if_pos hc] at h
    cases h
    exact hrd
  · rw [if_neg hc] at h
    cases h

/-- An issued byte store preserves the source representation of every
    admitted carrier: `RepSlot` reads `read64` over canonical memory,
    which the issue leaves untouched. Every premise is used: `hm` moves
    between the TSO memory and the representation memory, `hRep` is the
    carried fact, `h` is the stutter step. -/
theorem issue_rep_bleibt {D : Deklaration} (t : D.Tab) (k : Int)
    (f : D.Feld t) (lo hi : Int) (hT : D.typ t f = .int lo hi)
    (a : Adresse) (m : Speicher) (σ : World D)
    (s s' : TSOZustand) (c : Nat) (x : Adresse) (v : Byte)
    (hm : s.mem = m)
    (hRep : RepSlot t k f lo hi hT a m σ)
    (h : issueByte s c x v = some s') :
    RepSlot t k f lo hi hT a s'.mem σ := by
  unfold issueByte at h
  by_cases hc : s.mem.schreibbar x = true
  · rw [if_pos hc] at h
    cases h
    rw [hm]
    exact hRep
  · rw [if_neg hc] at h
    cases h

/-! ## 2. One flush moves at most one byte: the word guard is necessary. -/

/-- A single oldest-entry flush changes at most ONE canonical address:
    two distinct addresses cannot both change. Hence no single flush
    installs a full 8-byte word whose bytes differ in two places: the
    whole-word claim needs the atomicity guard (empty buffer, alignment,
    full-footprint permissions), never a byte-issue sequence. -/
theorem flush_nur_ein_byte (s s' : TSOZustand) (c : Nat)
    (e : TSOEintrag) (rest : List TSOEintrag)
    (h : flushKern s c = some s') (he : s.puffer c = e :: rest)
    (x y : Adresse) (hne : x ≠ y)
    (hx : s'.mem.bytes x ≠ s.mem.bytes x)
    (hy : s'.mem.bytes y ≠ s.mem.bytes y) : False := by
  have hx' : x = e.addr := by
    by_cases hxe : x = e.addr
    · exact hxe
    · exact absurd (flush_rahmen s s' c h e rest he x hxe) hx
  have hy' : y = e.addr := by
    by_cases hye : y = e.addr
    · exact hye
    · exact absurd (flush_rahmen s s' c h e rest he y hye) hy
  exact hne (hx'.trans hy'.symm)

/-- The two tearing addresses sit inside ONE word footprint: `sbX = 0`
    is byte 0 of the word at `0`, `sbY = 1` is byte 1. -/
theorem riss_im_fuss : sbX ∈ Fuss (0 : Adresse) ∧ sbY ∈ Fuss (0 : Adresse) := by
  have h0 : addrOff (0 : Adresse) 0 = sbX := by decide
  have h1 : addrOff (0 : Adresse) 1 = sbY := by decide
  refine ⟨?_, ?_⟩
  · rw [← h0, ← schreibEreignisse_acht]
    rw [schreibEreignisse_mem]
    exact ⟨0, by decide, rfl⟩
  · rw [← h1, ← schreibEreignisse_acht]
    rw [schreibEreignisse_mem]
    exact ⟨1, by decide, rfl⟩

/-- **TEARING REFUSAL (proved):** after the first flush of two separately
    issued footprint bytes, the two bytes of the word at `0` are mixed:
    byte 0 is the new value while byte 1 still reads the pre-flush byte.
    No single source value was installed; a validator admitting only
    whole-word installs refuses this intermediate state. -/
theorem riss_gemischt_verweigert :
    wortRiss3.mem.bytes sbX = sbEins ∧
      wortRiss3.mem.bytes sbY = wortRiss2.mem.bytes sbY ∧
      wortRiss3.mem.bytes sbX ≠ wortRiss3.mem.bytes sbY := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## 3. Guarded whole-word install meets the real source write. -/

/-- **BRIDGE (positive):** one actual source table-write step
    (`Stmt.assignSlot` through `execStmt`) together with the matching
    guarded target word install establishes the representation at the
    written slot, and the installed bytes parse back to the source
    value (`wortZahl` roundtrip). The word atomicity guard
    (`WortGuard`: empty own buffer, 8-alignment, full-footprint
    readability/writability) is CHECKED, never assumed: its readability
    feeds the source step, and all four guard facts are re-concluded for
    the consumer. The source transition is DERIVED via
    `rep_schritt_bleibt` (which unfolds `execStmt`); no simulation
    premise is taken. Visibility vs issuing: only the installed word
    (`write64`, what a fully drained word packet / the LOCK path
    achieves) is visible; the buffered issues behind it are stutter
    (§1). Every premise is used. -/
theorem bruecke_schritt_rep {D : Deklaration} {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)}
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
    (s : TSOZustand) (c : Nat) (hG : WortGuard s c a) (hm : s.mem = m) :
    RepSlot t k f lo hi hT a m' σ' ∧
      (∃ w, read64 m' a = some w ∧ wortZahl lo hi w = some v) ∧
      s.puffer c = [] ∧ ausgerichtet8 a = true ∧
      lesbar8 m a = true ∧ schreibbar8 m a = true := by
  obtain ⟨hbuf, hali, hles, hwrS⟩ := hG
  rw [hm] at hles hwrS
  have hMain := rep_schritt_bleibt O passes R t f lo hi hT
    base len off hOk i e hw hL σ ρ σL hLese k v hk hv a m m' σ' ρ' hExec hTgt hles
  exact ⟨hMain.1, hMain.2, hbuf, hali, hles, hwrS⟩

/-! ## 4. FIFO modification order with stutter bookkeeping. -/

/-- **FIFO + STUTTER:** after two same-core issues from an empty buffer
    and one flush, the OLDER value is the committed readable byte at the
    first address (per-core FIFO flush order reaches the projected
    history), while the YOUNGER byte still reads its pre-flush value:
    it is stutter, invisible until its own flush (§1). The safe
    direction for W: W admits any fresh-timestamp order, so every TSO
    FIFO order is an admissible W choice, never the reverse. -/
theorem bruecke_fifo_stutter (s s1 s2 s3 : TSOZustand) (c : Nat)
    (a b : Adresse) (v w : Byte)
    (h1 : issueByte s c a v = some s1)
    (h2 : issueByte s1 c b w = some s2)
    (hempty : s.puffer c = [])
    (hne : a ≠ b)
    (h3 : flushKern s2 c = some s3) :
    s3.mem.bytes a = v ∧ s3.mem.bytes b = s2.mem.bytes b ∧
      Lesbar (histVon s3) (sichtVon s3 c) a
        ⟨1, v, Sicht.null⟩ := by
  have hPaket := paket_reisst s s1 s2 s3 c a b v w h1 h2 hempty h3 hne
  have hHist := fifo_hist_konsistent s s1 s2 s3 c a b v w h1 h2 hempty h3
  exact ⟨hPaket.1, hPaket.2, hHist⟩

/-! ## 5. Foreign stores stay invisible: proved refusal. -/

/-- **FOREIGN-DRAIN REFUSAL (proved):** a locally fence-ready core
    coexists with a foreign forwarded read past canonical memory, and
    the forwarded value is NOT the committed word: core 1 forwards its
    own pending `7` at address `0` while canonical memory still reads
    the word `0`. A local fence/drain publishes nothing foreign; only
    flushes publish, and only the acting core's own. Any carrier claim
    built on a foreign buffered value is refused by this shape. -/
theorem bruecke_fremd_kein_wort :
    ∃ (s : TSOZustand) (w : Wort),
      s.puffer 1 ≠ [] ∧ zaunBereit s 0 = true ∧
      loadByte s 1 0 = some (BitVec.ofNat 8 7) ∧
      read64 s.mem 0 = some w ∧
      (BitVec.ofNat 8 7) ≠ wortByte w 0 := by
  refine ⟨⟨zeugenSpeicher,
    fun d => if d = 1 then [⟨(0 : Adresse), BitVec.ofNat 8 7⟩] else []⟩,
    0, by decide, by decide, by decide, by decide, by decide⟩

/-! ## 6. Joint witnesses. -/

/-- **JOINT WITNESS for `bruecke_schritt_rep`:** every premise holds
    jointly on the witness declaration `witD` (one table that the
    witness function writes) with the TSO guard state
    `⟨witM, fun _ => []⟩` (empty buffers, aligned word, full
    permissions) standing over the same memory `witM` — and so does
    the conclusion, with a reached memory-changing run on both sides
    (source slot `0 → 42`, target bytes changed). -/
theorem bruecke_schritt_rep_zeuge :
    ∃ (σ' : World witD) (ρ' : Env witD []) (m' : Speicher),
      repOk (witD.typ () ()) 4096 16 0 = true ∧
      execStmt witO 0 witR
        (Stmt.assignSlot (l := false) () () witI witE witHw witHL)
        witSigma Env.nil = .ok σ' ρ' ∧
      write64 witM witA (zahlWort witVal) = some m' ∧
      (∃ s : TSOZustand, ∃ c : Nat, WortGuard s c witA ∧ s.mem = witM) ∧
      RepSlot () 0 () 0 100 witHT witA m' σ' ∧
      (∃ w, read64 m' witA = some w ∧ wortZahl 0 100 w = some witVal) ∧
      (witSigma.slots () 0 ()).n = 0 ∧
      (σ'.slots () 0 ()).n = 42 ∧
      witM.bytes witA ≠ m'.bytes witA := by
  obtain ⟨σ', ρ', m', hOk, _, _, _, hExec, hTgt, _, _, _, hBefore, hAfter,
    hBytes⟩ := rep_schritt_bleibt_zeuge
  have hG : WortGuard (⟨witM, fun _ => []⟩ : TSOZustand) 0 witA :=
    ⟨rfl, by decide, by decide, by decide⟩
  have hMain := bruecke_schritt_rep witO 0 witR () () 0 100 witHT
    4096 16 0 hOk witI witE witHw witHL witSigma Env.nil witSL rfl
    0 witVal rfl rfl witA witM m' σ' ρ' hExec hTgt _ 0 hG rfl
  exact ⟨σ', ρ', m', hOk, hExec, hTgt, ⟨_, 0, hG, rfl⟩,
    hMain.1, hMain.2.1, hBefore, hAfter, hBytes⟩

/-- **JOINT TWO-CORE WITNESS:** from the empty start, two issues on
    different cores reach `sbNach2` (both cores load the stale `0`),
    flushing core 0 observably changes the canonical byte at `sbX` —
    AND, on the same word vocabulary, the admitted source slot write
    `0 → 42` lands its representation with a changed target word.
    Non-degenerate on both sides: two cores with real buffered stores
    plus one table that its function writes. -/
theorem bruecke_zeuge_gelenk :
    TSOErreichbar sbStart sbNach2 ∧
    loadByte sbNach2 0 sbY = some 0 ∧ loadByte sbNach2 1 sbX = some 0 ∧
    flushKern sbNach2 0 = some sbGespült ∧
    sbNach2.mem.bytes sbX ≠ sbGespült.mem.bytes sbX ∧
    Speichermodell.Lesbar (histVon sbGespült) (sichtVon sbGespült 0) sbX
      ⟨1, sbEins, Speichermodell.Sicht.null⟩ ∧
    (∃ (σ' : World witD) (m' : Speicher),
      RepSlot () 0 () 0 100 witHT witA m' σ' ∧
      (∃ w, read64 m' witA = some w ∧ wortZahl 0 100 w = some witVal) ∧
      (witSigma.slots () 0 ()).n = 0 ∧ (σ'.slots () 0 ()).n = 42 ∧
      witM.bytes witA ≠ m'.bytes witA) := by
  obtain ⟨hReach, hL0, hL1, hFl, hChg, hLes⟩ := hist_zeuge_gelenk
  obtain ⟨σ', _, m', _, _, _, _, _, _, _, hRep, hRt, hBefore, hAfter,
    hBytes⟩ := rep_schritt_bleibt_zeuge
  exact ⟨hReach, hL0, hL1, hFl, hChg, hLes, σ', m',
    hRep, hRt, hBefore, hAfter, hBytes⟩

/-! ## 7. OBSTRUCTION: what is NOT bridged here. -/

/-- The admitted carrier profile: exactly the `SourceMemory` fragment
    (one `.int lo hi` slot with `0 <= lo`, `hi < 2 ^ 64`, 8-byte slot
    inside its layout entry). Anything else — sums, floats, bools,
    globals, atomics, gates, pointers, overlapping or torn footprints,
    foreign buffered values — is refused by `repOk`/`WortGuard`/the
    tearing and foreign lemmas above, never silently admitted. -/
def BrueckenProfil (ty : Ty) (base len off : Nat) : Bool :=
  repOk ty base len off

/-- The profile decides exactly the admitted shape: the witness slot
    is admitted, a `bool` field is refused. -/
theorem brueckenProfil_zeuge :
    BrueckenProfil (.int 0 100) 4096 16 0 = true ∧
      BrueckenProfil .bool 4096 16 0 = false := by
  decide

/- CUTS:
    - Admitted profile only (`BrueckenProfil` = `repOk`): one
      `.int lo hi` slot (`0 <= lo`, `hi < 2 ^ 64`) as one LE 8-byte
      word installed atomically under `WortGuard`. Sums, floats,
      bools, globals, statics, arenas, atomics, gates and function
      pointers have no representation; torn footprints and foreign
      buffered values are refused (`riss_gemischt_verweigert`,
      `bruecke_fremd_kein_wort`, `flush_nur_ein_byte`).
    - Single-slot writes only: `bruecke_schritt_rep` covers one
      `Stmt.assignSlot` step plus its matching guarded `write64`
      (what a fully drained word packet / the LOCK path achieves);
      byte-issue sequences are stutter (`issue_rep_bleibt`) until
      flushed, and a single flush is never a carrier write.
    - NO per-access `SchrittW` (`wahl`/`neu`) construction here: a W
      write installs ONE message carrying the whole post-step carrier
      value (`MaschineW.histS`), while a TSO flush installs one byte;
      assembling one `SchrittW` from a drained byte packet needs the
      per-rule access-list decomposition (O-access, ~70 `RufSchrittG`
      rules, pattern `exchange_liest_schreibt`) of TSO-GX-BRUECKE.md
      §5, owned by the follow-up bridge. The byte-instantiated
      `Lesbar`/`Frisch` facts (`bruecke_fifo_stutter`,
      `spülen_baut_frische_nachricht`) do NOT transfer to
      carrier-granular `Frisch`: that transfer is the OPEN leg.
    - No W/GX run induction, no lowering map, no lock/start/join,
      fence, interrupt, MMIO or timing claim; `valX86_sound` and the
      source-to-final-bytes closing theorem stay OPEN.
    - No source, checker, contract, budget or goal change; no new
      executor, no second IR, no guessed ISA beyond the accepted
      pilot vocabulary.
-/

#print axioms issue_beobachtet_bleibt
#print axioms issue_rep_bleibt
#print axioms flush_nur_ein_byte
#print axioms riss_im_fuss
#print axioms riss_gemischt_verweigert
#print axioms bruecke_schritt_rep
#print axioms bruecke_fifo_stutter
#print axioms bruecke_fremd_kein_wort
#print axioms bruecke_schritt_rep_zeuge
#print axioms bruecke_zeuge_gelenk
#print axioms BrueckenProfil
#print axioms brueckenProfil_zeuge

end Gabbro.Grammatik.X86
