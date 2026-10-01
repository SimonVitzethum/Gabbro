/-
  File:      Grammatik/X86/WordAtomicity.lean
  Subject:   Aligned whole-word observation guard and composed frame/read-back
             facts over the canonical LOCK path (no new executor).

  Lane 421 (continuous reserve): thin consumer layer over the ACCEPTED
  `Speicher` / `TSO` / `LockedOps` vocabulary. The only whole-word atomic
  update is the accepted `lockSchritt` XADD shape; this module adds NO new
  transition, NO byte-issue sequence claimed atomic, and NO source RMW
  closure. It contributes: (1) one reusable admission guard `WortGuard`
  grouping the LOCK preconditions for lowering/validator consumers;
  (2) word-level observation `WortBeobachtet`; (3) composed lemmas
  (single-transition read-back, disjoint-word stability) proved by APPLYING
  the accepted lemmas; (4) concrete refusals; (5) a word-level tearing
  witness applying `paket_reisst`; (6) the explicit OPEN bridge
  (`WortNachW` empty). Per-byte TSO is not multi-byte atomicity.
-/
import Grammatik.X86.LockedOps
import Grammatik.X86.TSO

namespace Gabbro.Grammatik.X86

/-- Admission guard for one aligned whole-word LOCK update on core `c`:
    the own store buffer is empty (the LOCK form bypasses it), the word
    address carries the declared 8-alignment, and the full footprint is
    readable and writable. Consumer: lowering/validator admit exactly this
    shape; anything else is refused by `lockSchritt` itself. -/
def WortGuard (s : TSOZustand) (c : Nat) (a : Adresse) : Prop :=
  s.puffer c = [] ∧ ausgerichtet8 a = true ∧
    lesbar8 s.mem a = true ∧ schreibbar8 s.mem a = true

/-- Word observation: canonical memory holds `v` at the word `a`. -/
def WortBeobachtet (m : Speicher) (a : Adresse) (v : Wort) : Prop :=
  read64 m a = some v

/-! ## 1. Single-transition observation: the LOCK word update reads back. -/

/-- A successful aligned LOCK add installs exactly one new word, observed
    by an immediate read-back: no byte-wise intermediate state is visible
    at the word level. Proved by composing the accepted step equation with
    the accepted sequential read-after-write; every premise pins one guard
    of `lockSchritt` or of the read-back. -/
theorem wort_schritt_liest_zurueck (s s' : TSOZustand) (c : Nat) (a : Adresse)
    (delta alt : Wort) (m' : Speicher) (ev : LockEreignis)
    (hbuf : s.puffer c = [])
    (hrd : read64 s.mem a = some alt)
    (hali : ausgerichtet8 a = true)
    (hwr : write64 s.mem a (alt + delta) = some m')
    (hles : lesbar8 s.mem a = true)
    (hstep : lockSchritt (.xadd64 a delta) c s = some (s', ev)) :
    WortBeobachtet s'.mem a (alt + delta) := by
  rw [lockSchritt_xadd_erfolg s c a delta alt m' hbuf hrd hali hwr] at hstep
  cases hstep
  show read64 m' a = some (alt + delta)
  exact read64_nach_write64 s.mem m' a (alt + delta) hwr hles

/-! ## 2. Permission extraction: a successful word access pins its guard. -/

/-- A successful word read pins full readability of the footprint:
    `read64` checks `lesbar8` by construction. -/
theorem read64_braucht_lesbar (m : Speicher) (a : Adresse) (v : Wort)
    (h : read64 m a = some v) : lesbar8 m a = true := by
  unfold read64 at h
  by_cases hc : lesbar8 m a = true
  · exact hc
  · rw [if_neg hc] at h
    cases h

/-- A successful word store pins full writability of the footprint:
    `write64` checks `schreibbar8` by construction. -/
theorem write64_braucht_schreibbar (m : Speicher) (a : Adresse) (v : Wort)
    (m' : Speicher) (h : write64 m a v = some m') :
    schreibbar8 m a = true := by
  unfold write64 at h
  by_cases hc : schreibbar8 m a = true
  · exact hc
  · rw [if_neg hc] at h
    cases h

/-- The LOCK preconditions, grouped as one admission guard for
    lowering/validator consumers: every premise pins one guard of
    `lockSchritt`, and readability/writability are derived from the
    successful accesses, not assumed. -/
theorem wort_guard_aus_voraussetzungen (s : TSOZustand) (c : Nat)
    (a : Adresse) (delta alt : Wort) (m' : Speicher)
    (hbuf : s.puffer c = [])
    (hrd : read64 s.mem a = some alt)
    (hali : ausgerichtet8 a = true)
    (hwr : write64 s.mem a (alt + delta) = some m') :
    WortGuard s c a := by
  refine ⟨hbuf, hali, ?_, ?_⟩
  · exact read64_braucht_lesbar s.mem a alt hrd
  · exact write64_braucht_schreibbar s.mem a (alt + delta) m' hwr

/-! ## 3. Frame: a disjoint word survives the LOCK step; outside bytes stay. -/

/-- A successful LOCK add leaves a disjoint word observation unchanged:
    proved by composing the accepted step equation with the accepted
    sequential disjoint read frame. -/
theorem wort_bleibt_unter_disjunkt (s s' : TSOZustand) (c : Nat)
    (a b : Adresse) (delta alt : Wort) (m' : Speicher) (ev : LockEreignis)
    (old : Wort)
    (hbuf : s.puffer c = [])
    (hrd : read64 s.mem a = some alt)
    (hali : ausgerichtet8 a = true)
    (hwr : write64 s.mem a (alt + delta) = some m')
    (hdis : Disjunkt a b)
    (hread : read64 s.mem b = some old)
    (hstep : lockSchritt (.xadd64 a delta) c s = some (s', ev)) :
    read64 s'.mem b = some old := by
  rw [lockSchritt_xadd_erfolg s c a delta alt m' hbuf hrd hali hwr] at hstep
  cases hstep
  show read64 m' b = some old
  rw [read64_rahmen s.mem m' a b (alt + delta) hwr hdis]
  exact hread

/-- A successful LOCK add changes no byte outside its footprint. -/
theorem wort_rahmen_byte (s s' : TSOZustand) (c : Nat) (a x : Adresse)
    (delta alt : Wort) (m' : Speicher) (ev : LockEreignis)
    (hbuf : s.puffer c = [])
    (hrd : read64 s.mem a = some alt)
    (hali : ausgerichtet8 a = true)
    (hwr : write64 s.mem a (alt + delta) = some m')
    (haussen : ∀ k : Nat, k < 8 → x ≠ addrOff a k)
    (hstep : lockSchritt (.xadd64 a delta) c s = some (s', ev)) :
    s'.mem.bytes x = s.mem.bytes x := by
  rw [lockSchritt_xadd_erfolg s c a delta alt m' hbuf hrd hali hwr] at hstep
  cases hstep
  exact write64_rahmen s.mem m' a x (alt + delta) hwr haussen

/-! ## 4. Refusals: misalignment, full buffer and refused store. -/

/-- A LOCK add without the declared alignment is refused: the step is
    `none`, never a silent byte-wise split. -/
theorem lock_verweigert_ohne_ausrichtung (s : TSOZustand) (c : Nat)
    (a : Adresse) (delta alt : Wort)
    (hbuf : s.puffer c = [])
    (hrd : read64 s.mem a = some alt)
    (hali : ausgerichtet8 a = false) :
    lockSchritt (.xadd64 a delta) c s = none := by
  have hb : (s.puffer c).isEmpty = true := by rw [hbuf]; rfl
  unfold lockSchritt
  simp [hb, hrd, hali]

/-- A LOCK add with a nonempty own buffer is refused: the LOCK form
    bypasses the buffer only when it is empty. -/
theorem lock_verweigert_bei_vollem_puffer (s : TSOZustand) (c : Nat)
    (a : Adresse) (delta : Wort)
    (hne : s.puffer c ≠ []) :
    lockSchritt (.xadd64 a delta) c s = none := by
  have hb : (s.puffer c).isEmpty = false := by
    cases h : s.puffer c with
    | nil => exact absurd h hne
    | cons _ _ => rfl
  unfold lockSchritt
  simp [hb]

/-- A LOCK add whose install store is refused installs nothing: the step
    is `none`, so no partial word becomes visible. -/
theorem lock_verweigert_ohne_schreibrecht (s : TSOZustand) (c : Nat)
    (a : Adresse) (delta alt : Wort)
    (hbuf : s.puffer c = [])
    (hrd : read64 s.mem a = some alt)
    (hali : ausgerichtet8 a = true)
    (hnowr : write64 s.mem a (alt + delta) = none) :
    lockSchritt (.xadd64 a delta) c s = none := by
  have hb : (s.puffer c).isEmpty = true := by rw [hbuf]; rfl
  unfold lockSchritt
  simp [hb, hrd, hali, hnowr]

/-! ## 5. Tearing: a byte-wise word install is not atomic. -/

/-- Two bytes inside one word footprint, issued separately, flush one at
    a time: after the first flush the first byte is new while the second
    still reads the pre-flush byte. A genuine specialization of the
    accepted `paket_reisst` to the word footprint (distinctness from the
    accepted `addrOff_ne8`), never an atomicity claim. Consumer: any
    lowering that emits a word store as byte issues must fence/drain
    between them; the LOCK path of §1 is the only atomic word update. -/
theorem wort_fuss_reisst (s s1 s2 s3 : TSOZustand) (c : Nat) (a : Adresse)
    (v w : Byte)
    (h1 : issueByte s c (addrOff a 0) v = some s1)
    (h2 : issueByte s1 c (addrOff a 1) w = some s2)
    (hempty : s.puffer c = [])
    (h3 : flushKern s2 c = some s3) :
    s3.mem.bytes (addrOff a 0) = v ∧
      s3.mem.bytes (addrOff a 1) = s2.mem.bytes (addrOff a 1) := by
  have hne : addrOff a 0 ≠ addrOff a 1 :=
    addrOff_ne8 (by decide) (by decide) (by decide)
  exact paket_reisst s s1 s2 s3 c (addrOff a 0) (addrOff a 1) v w
    h1 h2 hempty h3 hne

/-- After core 0 additionally issues the second footprint byte. -/
def wortRiss2 : TSOZustand :=
  ⟨sbNach1.mem,
    pufferSetze sbNach1.puffer 0 (sbNach1.puffer 0 ++ [⟨sbY, sbEins⟩])⟩

/-- After core 0 flushes its oldest entry (the first byte). -/
def wortRiss3 : TSOZustand :=
  ⟨{ wortRiss2.mem with
      bytes := fun x => if x = sbX then sbEins else wortRiss2.mem.bytes x },
    pufferSetze wortRiss2.puffer 0 [⟨sbY, sbEins⟩]⟩

/-- Concrete tearing witness over real canonical bytes, single core: two
    issued bytes flush one at a time, so after the first flush the first
    byte is new while the second still reads the pre-flush byte, and the
    flush observably changed memory. -/
theorem wort_fuss_reisst_zeuge :
    ∃ s1 s2 s3 : TSOZustand,
    issueByte sbStart 0 sbX sbEins = some s1 ∧
    issueByte s1 0 sbY sbEins = some s2 ∧
    flushKern s2 0 = some s3 ∧
    s3.mem.bytes sbX = sbEins ∧
    s3.mem.bytes sbY = s2.mem.bytes sbY ∧
    s2.mem.bytes sbX ≠ s3.mem.bytes sbX := by
  have h2 : issueByte sbNach1 0 sbY sbEins = some wortRiss2 := by rfl
  have h3 : flushKern wortRiss2 0 = some wortRiss3 := by rfl
  have ht := paket_reisst sbStart sbNach1 wortRiss2 wortRiss3 0
    sbX sbY sbEins sbEins sb_schritt1 h2 rfl h3 sbX_ne_sbY
  have hchg : wortRiss2.mem.bytes sbX ≠ wortRiss3.mem.bytes sbX := by
    decide
  exact ⟨sbNach1, wortRiss2, wortRiss3, sb_schritt1, h2, h3,
    ht.1, ht.2, hchg⟩

/-! ## 6. Stated non-claim: no source/hardware bridge is proved here. -/

/-- No per-access refinement of the LOCK word update into a source or
    hardware model is proved here: the type of such a claim is empty.
    The TSO bridge owns it. -/
inductive WortNachW : TSOZustand → Prop

/-- Every bridge claim is void inside this module. -/
theorem kein_wort_nach_w (s : TSOZustand) : ¬ WortNachW s := by
  intro h
  cases h

/-! ## 7. Joint witnesses: reached, memory-changing, non-degenerate. -/

/-- Joint witness for `wort_schritt_liest_zurueck`: all its premises hold
    together on the concrete first LOCK step (word 0 at `lockAddr`,
    delta 5), the step reads back the installed word, and canonical
    memory observably changed. -/
theorem wort_schritt_liest_zurueck_zeuge :
    lockStart.puffer 0 = [] ∧ read64 lockStart.mem lockAddr = some 0 ∧
    ausgerichtet8 lockAddr = true ∧ lesbar8 lockStart.mem lockAddr = true ∧
    ∃ m' : Speicher, write64 lockStart.mem lockAddr (0 + 5) = some m' ∧
      ∃ s' : TSOZustand, ∃ ev : LockEreignis,
      lockSchritt (.xadd64 lockAddr 5) 0 lockStart = some (s', ev) ∧
      WortBeobachtet s'.mem lockAddr (0 + 5) ∧
      lockStart.mem.bytes lockAddr ≠ s'.mem.bytes lockAddr := by
  have hrd : read64 lockStart.mem lockAddr = some 0 := by decide
  have hali : ausgerichtet8 lockAddr = true := by decide
  have hwr : write64 lockStart.mem lockAddr (0 + 5) = some lockNach1.mem := by
    rfl
  have hchg : lockStart.mem.bytes lockAddr ≠ lockNach1.mem.bytes lockAddr := by
    decide
  exact ⟨rfl, hrd, hali, rfl, lockNach1.mem, hwr, lockNach1, lockEv1,
    lock_schritt1,
    wort_schritt_liest_zurueck lockStart lockNach1 0 lockAddr 5 0
      lockNach1.mem lockEv1 rfl hrd hali hwr rfl lock_schritt1,
    hchg⟩

/-- A second word address, one page above `lockAddr`. -/
def wortFern : Adresse := BitVec.ofNat 64 8192

/-- The second word footprint is disjoint from the first: Nat-interval
    disjointness under no-wrap on both sides. -/
theorem wort_fern_disjunkt : Disjunkt lockAddr wortFern := by
  have hA : lockAddr.toNat + 8 ≤ 2 ^ 64 := by decide
  have hB : wortFern.toNat + 8 ≤ 2 ^ 64 := by decide
  have h : lockAddr.toNat + 8 ≤ wortFern.toNat := by decide
  exact disjunkt_von_intervallen lockAddr wortFern hA hB (Or.inl h)

/-- Joint witness for `wort_bleibt_unter_disjunkt`: the first LOCK step
    preserves the second word observation (still 0) while observably
    changing the first word's bytes. -/
theorem wort_bleibt_unter_disjunkt_zeuge :
    Disjunkt lockAddr wortFern ∧
    read64 lockStart.mem wortFern = some 0 ∧
    read64 lockNach1.mem wortFern = some 0 ∧
    lockStart.mem.bytes lockAddr ≠ lockNach1.mem.bytes lockAddr := by
  have h1 : read64 lockStart.mem wortFern = some 0 := by decide
  have h2 : read64 lockNach1.mem wortFern = some 0 := by decide
  have hchg : lockStart.mem.bytes lockAddr ≠ lockNach1.mem.bytes lockAddr := by
    decide
  exact ⟨wort_fern_disjunkt, h1, h2, hchg⟩

/-- Joint refusal witness for `lock_verweigert_ohne_ausrichtung`: address
    4097 is misaligned, reads fine, and the LOCK step is refused. -/
theorem lock_verweigert_ohne_ausrichtung_zeuge :
    ∃ a : Adresse, ausgerichtet8 a = false ∧
    read64 lockStart.mem a = some 0 ∧
    lockSchritt (.xadd64 a 5) 0 lockStart = none := by
  have hrd : read64 lockStart.mem (BitVec.ofNat 64 4097) = some 0 := by decide
  have hali : ausgerichtet8 (BitVec.ofNat 64 4097) = false := by decide
  exact ⟨BitVec.ofNat 64 4097, hali, hrd,
    lock_verweigert_ohne_ausrichtung lockStart 0 _ 5 0 rfl hrd hali⟩

/-- Joint refusal witness for `lock_verweigert_bei_vollem_puffer`: core 1
    holds a pending store, so its LOCK step is refused while core 0 stays
    fence-ready. -/
theorem lock_verweigert_bei_vollem_puffer_zeuge :
    zaunStart.puffer 1 ≠ [] ∧
    lockSchritt (.xadd64 lockAddr 5) 1 zaunStart = none := by
  exact ⟨zaun_start_fremd,
    lock_verweigert_bei_vollem_puffer zaunStart 1 lockAddr 5
      zaun_start_fremd⟩

/- CUTS:
    - New work only: `WortGuard` groups the accepted LOCK preconditions;
      `WortBeobachtet` names the word read-back; every lemma composes an
      accepted step equation with an accepted sequential frame/read-back
      fact. No new transition, no second executor, no byte-issue sequence
      claimed atomic.
    - The only whole-word atomic update is the accepted `lockSchritt`
      XADD shape under its declared guards (empty own buffer,
      `ausgerichtet8`, readable and writable footprint). Any other shape
      is refused (`lock_verweigert_*`); the refusals say nothing about
      addresses the checker never admits.
    - Per-byte TSO is not multi-byte atomicity: `wort_fuss_reisst`
      (applying the accepted `paket_reisst`) shows a byte-wise word
      install tears, even inside one footprint.
    - No W/GX refinement: `WortNachW` is empty (`kein_wort_nach_w`); any
      source RMW lowering correspondence and any per-access TSO
      simulation stay with the bridge.
    - No hardware claim: no cycle bound, no silicon correspondence for
      the alignment profile, no fence/drain timing; failure-as-`none`
      is safety-only, no progress or liveness follows.
    - No fetch/decode/ABI/image claim: the guard takes an `Adresse`
      directly, not decoded bytes; codec coverage, relocation, entry
      and the closing validator stay with their owners.
    - No source, checker, contract, budget or goal change: nothing here
      speaks about `Vertrag`, `Stmt`, duties or `gabbro_ziel`.
-/

#print axioms WortGuard
#print axioms WortBeobachtet
#print axioms wort_schritt_liest_zurueck
#print axioms read64_braucht_lesbar
#print axioms write64_braucht_schreibbar
#print axioms wort_guard_aus_voraussetzungen
#print axioms wort_bleibt_unter_disjunkt
#print axioms wort_rahmen_byte
#print axioms lock_verweigert_ohne_ausrichtung
#print axioms lock_verweigert_bei_vollem_puffer
#print axioms lock_verweigert_ohne_schreibrecht
#print axioms wort_fuss_reisst
#print axioms wort_fuss_reisst_zeuge
#print axioms kein_wort_nach_w
#print axioms wort_schritt_liest_zurueck_zeuge
#print axioms wortFern
#print axioms wortRiss2
#print axioms wortRiss3
#print axioms wort_fern_disjunkt
#print axioms wort_bleibt_unter_disjunkt_zeuge
#print axioms lock_verweigert_ohne_ausrichtung_zeuge
#print axioms lock_verweigert_bei_vollem_puffer_zeuge

#print axioms WortGuard

end Gabbro.Grammatik.X86
