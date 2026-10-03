/-
  File:      Grammatik/X86/ComposeAtomicLedger.lean
  Subject:   Atomic-ledger closing: every shared atomic access closes to its
             ledger entry (ordering, RMW field, success/failure); unlogged
             shared access refuses.

  Lane 838 (composition closing): composes ONLY already-accepted modules --
  `LockedOps` (`lockSchritt`, `casSchritt`, `LockEreignis`, `RmwForm`,
  `lock_xadd_atomar`, `mfence_ordnung`, `cas_erfolg_schreibt`,
  `cas_fehlschlag_stottert`, two-core/memory-changing witnesses),
  `WordAtomicity` (`WortGuard`), `ReleaseAcquire` (`ReleaseSchreiben`,
  `freigabe_braucht_flush`, `zaun_erwerb_liest_kanonisch`), `TSOHistory`
  (`hist_zeuge_gelenk`, reached run), and the source `Ordnung`
  (`entspannt`/`freigabe`) of `Speichermodell.Sicht`. No new executor, no
  new decoder, no source/checker/goal change.
-/
import Grammatik.X86.LockedOps
import Grammatik.X86.WordAtomicity
import Grammatik.X86.ReleaseAcquire
import Grammatik.X86.TSOHistory

namespace Gabbro.Grammatik.X86

/-- Shared atomic access: the shape the ledger closes. Loads and stores
    carry their ordering; both RMW forms carry `freigabe` (acq_rel, the
    accepted release/acquire over-approximation of `seq_cst`); a fence is
    address-free. -/
inductive AtomZugriff where
  | lese (a : Adresse) (o : Speichermodell.Ordnung)
  | schreibe (a : Adresse) (v : Wort) (o : Speichermodell.Ordnung)
  | xadd (a : Adresse) (delta : Wort)
  | cas (a : Adresse) (erwartet neu : Wort)
  | zaun
  deriving DecidableEq, Repr

/-- One ledger entry: address (`none` for a fence), ordering, RMW field,
    outcome (`none` for a load, which installs nothing, and for a CAS
    attempt whose outcome the step has not decided yet). -/
structure LedgerEintrag where
  addr : Option Adresse
  ord : Speichermodell.Ordnung
  istRmw : Bool
  erfolg : Option Bool
  deriving DecidableEq, Repr

/-- The ledger entry of one shared atomic access: loads carry their
    ordering with no outcome; stores carry success; both RMW forms carry
    `freigabe` with the RMW field set; XADD always succeeds; a CAS attempt
    records no outcome yet (the step decides it, see `ledgerCasOk`); a
    fence is address-free release order. -/
def ledgerEintrag : AtomZugriff → LedgerEintrag
  | .lese a o => ⟨some a, o, false, none⟩
  | .schreibe a _ o => ⟨some a, o, false, some true⟩
  | .xadd a _ => ⟨some a, .freigabe, true, some true⟩
  | .cas a _ _ => ⟨some a, .freigabe, true, none⟩
  | .zaun => ⟨none, .freigabe, false, some true⟩

/-- The decided CAS entry: the attempt's address and RMW field with the
    runtime outcome the accepted `casSchritt` returned. -/
def ledgerCasOk (a : Adresse) (ok : Bool) : LedgerEintrag :=
  ⟨some a, .freigabe, true, some ok⟩

/-- Decided closing check: the entry carries the access's address,
    ordering and RMW field. A CAS attempt accepts any recorded outcome
    (the step, not the attempt, decides success); every other form pins
    its outcome. -/
def ledgerDeckt : AtomZugriff → LedgerEintrag → Bool
  | .lese a o, e =>
    decide (e.addr = some a ∧ e.ord = o ∧ e.istRmw = false ∧ e.erfolg = none)
  | .schreibe a _ o, e =>
    decide (e.addr = some a ∧ e.ord = o ∧ e.istRmw = false ∧ e.erfolg = some true)
  | .xadd a _, e =>
    decide (e.addr = some a ∧ e.ord = .freigabe ∧ e.istRmw = true ∧ e.erfolg = some true)
  | .cas a _ _, e =>
    decide (e.addr = some a ∧ e.ord = .freigabe ∧ e.istRmw = true)
  | .zaun, e =>
    decide (e.addr = none ∧ e.ord = .freigabe ∧ e.istRmw = false ∧ e.erfolg = some true)

/-! ## 1. Every access closes to its own ledger entry (decided). -/

/-- A load closes to its entry. -/
theorem lese_schliesst (a : Adresse) (o : Speichermodell.Ordnung) :
    ledgerDeckt (.lese a o) (ledgerEintrag (.lese a o)) = true := by
  unfold ledgerDeckt ledgerEintrag
  simp

/-- A store closes to its entry. -/
theorem schreibe_schliesst (a : Adresse) (v : Wort) (o : Speichermodell.Ordnung) :
    ledgerDeckt (.schreibe a v o) (ledgerEintrag (.schreibe a v o)) = true := by
  unfold ledgerDeckt ledgerEintrag
  simp

/-- An XADD closes to its entry. -/
theorem xadd_schliesst (a : Adresse) (delta : Wort) :
    ledgerDeckt (.xadd a delta) (ledgerEintrag (.xadd a delta)) = true := by
  unfold ledgerDeckt ledgerEintrag
  simp

/-- A CAS attempt closes to its entry (whatever outcome the step records). -/
theorem cas_schliesst (a : Adresse) (erwartet neu : Wort) (ok : Bool) :
    ledgerDeckt (.cas a erwartet neu) (ledgerCasOk a ok) = true := by
  unfold ledgerDeckt ledgerCasOk
  simp

/-- A fence closes to its entry. -/
theorem zaun_schliesst :
    ledgerDeckt .zaun (ledgerEintrag .zaun) = true := by
  unfold ledgerDeckt ledgerEintrag
  simp

/-! ## 2. Producer connections: accepted steps fill the ledger fields. -/

/-- XADD closing through the accepted step: a successful locked add fills
    the ledger RMW entry (release order, RMW set, success) and the
    accepted event carries the same RMW shape with the observed and
    installed words. Every premise pins one guard of `lockSchritt`. -/
theorem xadd_eintrag_aus_schritt (s s' : TSOZustand) (c : Nat) (a : Adresse)
    (delta alt : Wort) (m' : Speicher) (ev : LockEreignis)
    (hbuf : s.puffer c = [])
    (hrd : read64 s.mem a = some alt)
    (hali : ausgerichtet8 a = true)
    (hwr : write64 s.mem a (alt + delta) = some m')
    (hstep : lockSchritt (.xadd64 a delta) c s = some (s', ev)) :
    (ledgerEintrag (.xadd a delta)).istRmw = true ∧
      (ledgerEintrag (.xadd a delta)).erfolg = some true ∧
      (ledgerEintrag (.xadd a delta)).ord = .freigabe ∧
      ev.istRmw = true ∧ ev.gelesen = some alt ∧
      ev.geschrieben = some (alt + delta) := by
  obtain ⟨hrmw, _, _, hgal, hneu, _, _, _, _⟩ :=
    lock_xadd_atomar s s' c a delta alt m' ev hbuf hrd hali hwr hstep
  exact ⟨rfl, rfl, rfl, hrmw, hgal, hneu⟩

/-- CAS-success closing through the accepted step: a successful attempt
    fills the ledger RMW entry with success and observably installs the
    new word. Every premise pins one guard of `casSchritt` or the
    read-back. -/
theorem cas_erfolg_eintrag_aus_schritt (s s' : TSOZustand) (c : Nat)
    (a : Adresse) (erwartet neu alt : Wort) (m' : Speicher)
    (hbuf : s.puffer c = [])
    (hrd : read64 s.mem a = some alt)
    (hali : ausgerichtet8 a = true)
    (hgleich : (alt == erwartet) = true)
    (hwr : write64 s.mem a neu = some m')
    (hles : lesbar8 s.mem a = true)
    (hstep : casSchritt a erwartet neu c s = some (s', true))
    (hne : neu ≠ alt) :
    (ledgerCasOk a true).istRmw = true ∧
      (ledgerCasOk a true).erfolg = some true ∧
      (ledgerCasOk a true).ord = .freigabe ∧
      read64 s'.mem a = some neu ∧
      read64 s.mem a ≠ read64 s'.mem a := by
  obtain ⟨hrb, hdiff, _, _⟩ :=
    cas_erfolg_schreibt s s' c a erwartet neu alt m'
      hbuf hrd hali hgleich hwr hles hstep hne
  exact ⟨rfl, rfl, rfl, hrb, hdiff⟩

/-- CAS-failure closing through the accepted step: a failed attempt fills
    the ledger RMW entry with failure and stutters (no byte moves, no
    buffer moves). Every premise pins one guard of `casSchritt`. -/
theorem cas_fehlschlag_eintrag_aus_schritt (s s' : TSOZustand) (c : Nat)
    (a : Adresse) (erwartet neu alt : Wort) (bok : Bool)
    (hbuf : s.puffer c = [])
    (hrd : read64 s.mem a = some alt)
    (hali : ausgerichtet8 a = true)
    (hfehl : (alt == erwartet) = false)
    (hstep : casSchritt a erwartet neu c s = some (s', bok)) :
    (ledgerCasOk a bok).istRmw = true ∧
      (ledgerCasOk a bok).erfolg = some false ∧
      s'.mem.bytes = s.mem.bytes ∧ s'.puffer = s.puffer := by
  obtain ⟨hbytes, hpuffer, hbok⟩ :=
    cas_fehlschlag_stottert s s' c a erwartet neu alt bok
      hbuf hrd hali hfehl hstep
  rw [hbok]
  exact ⟨rfl, rfl, hbytes, hpuffer⟩

/-- Fence closing through the accepted step: a successful fence fills the
    address-free ledger entry and afterwards no address forwards from the
    acting core's buffer. Both premises pin the guards of `lockSchritt`. -/
theorem zaun_eintrag_aus_schritt (s s' : TSOZustand) (c : Nat)
    (ev : LockEreignis)
    (hstep : lockSchritt .mfence c s = some (s', ev))
    (hbuf : s.puffer c = []) :
    (ledgerEintrag .zaun).addr = none ∧
      (ledgerEintrag .zaun).ord = .freigabe ∧
      ev.istZaun = true ∧ ev.istRmw = false ∧
      (∀ a, neuestens (s'.puffer c) a = none) := by
  obtain ⟨_, _, hzaun, hrmw, hleer⟩ :=
    mfence_ordnung s s' c ev hstep hbuf
  exact ⟨rfl, rfl, hzaun, hrmw, hleer⟩

/-- Ordering closing through the accepted facts: a release store is
    invisible to a foreign core until its drain, while a fence-ready
    acquire load observes canonical memory -- and both ledger entries
    carry the release/acquire order. Every premise is used. -/
theorem ordnung_eintrag_aus_schritt (s s' : TSOZustand) (c d : Nat)
    (a : Adresse) (v : Byte) (w : Wort)
    (h : issueByte s c a v = some s')
    (hne : d ≠ c)
    (hmiss : neuestens (s.puffer d) a = none)
    (hrd : s.mem.lesbar a = true)
    (t : TSOZustand) (e : Nat)
    (hzaun : zaunBereit t e = true)
    (hrd2 : t.mem.lesbar a = true) :
    (ledgerEintrag (.schreibe a w .freigabe)).ord = .freigabe ∧
      (ledgerEintrag (.lese a .freigabe)).ord = .freigabe ∧
      loadByte s' d a = some (s.mem.bytes a) ∧
      loadByte t e a = some (t.mem.bytes a) := by
  exact ⟨rfl, rfl,
    freigabe_braucht_flush s s' c d a v h hne hmiss hrd,
    zaun_erwerb_liest_kanonisch t e a hzaun hrd2⟩

/-! ## 3. Refusal: unlogged shared access is refused. -/

/-- Ledger lookup: the first entry the access closes to, if any. -/
def ledgerFindt (es : List LedgerEintrag) (z : AtomZugriff) :
    Option LedgerEintrag :=
  es.find? (ledgerDeckt z)

/-- An empty ledger logs nothing: every shared atomic access refuses. -/
theorem ohne_eintrag_verweigert (z : AtomZugriff) :
    ledgerFindt [] z = none := by
  rfl

/-- PLANTED REFUSAL (ordering): a relaxed-only ledger refuses an acquire
    load at the same address -- the order field must match. -/
theorem falsche_ordnung_verweigert (a : Adresse) :
    ledgerFindt [⟨some a, .entspannt, false, none⟩]
      (.lese a .freigabe) = none := by
  unfold ledgerFindt ledgerDeckt
  simp

/-- PLANTED REFUSAL (RMW field): a ledger holding only the plain-store
    entry refuses an XADD at the same address -- a split store is never
    an RMW (`rmw_nur_mit_lock`, accepted). -/
theorem kein_rmw_ohne_lock_verweigert (a : Adresse) (delta : Wort)
    (v : Wort) :
    ledgerFindt [ledgerEintrag (.schreibe a v .freigabe)]
      (.xadd a delta) = none := by
  unfold ledgerFindt ledgerDeckt ledgerEintrag
  simp

/-- POSITIVE: a logged XADD is found with its entry. -/
theorem xadd_eintrag_gefunden (a : Adresse) (delta : Wort) :
    ledgerFindt [ledgerEintrag (.xadd a delta)] (.xadd a delta) =
      some (ledgerEintrag (.xadd a delta)) := by
  unfold ledgerFindt
  simp [xadd_schliesst a delta]

/-! ## 4. The closing composition. -/

/-- ATOMIC-LEDGER CLOSING: every shared atomic access closes to its
    ledger entry -- XADD fills the RMW/success/order fields beside the
    accepted event, CAS success installs observably, CAS failure stutters
    with failure recorded, a fence leaves no forwarding, release/acquire
    order matches the accepted target facts -- and unlogged access
    refuses. Each conjunct applies one accepted producer lemma over
    arbitrary admitted inputs; nothing is re-proved here. -/
theorem ComposeAtomicLedger_verbindung :
    (∀ (s s' : TSOZustand) (c : Nat) (a : Adresse) (delta alt : Wort)
      (m' : Speicher) (ev : LockEreignis),
      s.puffer c = [] → read64 s.mem a = some alt →
      ausgerichtet8 a = true → write64 s.mem a (alt + delta) = some m' →
      lockSchritt (.xadd64 a delta) c s = some (s', ev) →
      (ledgerEintrag (.xadd a delta)).istRmw = true ∧
        (ledgerEintrag (.xadd a delta)).erfolg = some true ∧
        (ledgerEintrag (.xadd a delta)).ord = .freigabe ∧
        ev.istRmw = true ∧ ev.gelesen = some alt ∧
        ev.geschrieben = some (alt + delta)) ∧
    (∀ (s s' : TSOZustand) (c : Nat) (a : Adresse)
      (erwartet neu alt : Wort) (m' : Speicher),
      s.puffer c = [] → read64 s.mem a = some alt →
      ausgerichtet8 a = true → (alt == erwartet) = true →
      write64 s.mem a neu = some m' → lesbar8 s.mem a = true →
      casSchritt a erwartet neu c s = some (s', true) → neu ≠ alt →
      (ledgerCasOk a true).istRmw = true ∧
        (ledgerCasOk a true).erfolg = some true ∧
        (ledgerCasOk a true).ord = .freigabe ∧
        read64 s'.mem a = some neu ∧
        read64 s.mem a ≠ read64 s'.mem a) ∧
    (∀ (s s' : TSOZustand) (c : Nat) (a : Adresse)
      (erwartet neu alt : Wort) (bok : Bool),
      s.puffer c = [] → read64 s.mem a = some alt →
      ausgerichtet8 a = true → (alt == erwartet) = false →
      casSchritt a erwartet neu c s = some (s', bok) →
      (ledgerCasOk a bok).istRmw = true ∧
        (ledgerCasOk a bok).erfolg = some false ∧
        s'.mem.bytes = s.mem.bytes ∧ s'.puffer = s.puffer) ∧
    (∀ (s s' : TSOZustand) (c : Nat) (ev : LockEreignis),
      lockSchritt .mfence c s = some (s', ev) → s.puffer c = [] →
      (ledgerEintrag .zaun).addr = none ∧
        (ledgerEintrag .zaun).ord = .freigabe ∧
        ev.istZaun = true ∧ ev.istRmw = false ∧
        (∀ a, neuestens (s'.puffer c) a = none)) ∧
    (∀ (s s' : TSOZustand) (c d : Nat) (a : Adresse) (v : Byte)
      (w : Wort),
      issueByte s c a v = some s' → d ≠ c →
      neuestens (s.puffer d) a = none → s.mem.lesbar a = true →
      ∀ (t : TSOZustand) (e : Nat),
      zaunBereit t e = true → t.mem.lesbar a = true →
      (ledgerEintrag (.schreibe a w .freigabe)).ord = .freigabe ∧
        (ledgerEintrag (.lese a .freigabe)).ord = .freigabe ∧
        loadByte s' d a = some (s.mem.bytes a) ∧
        loadByte t e a = some (t.mem.bytes a)) ∧
    (∀ z : AtomZugriff, ledgerFindt [] z = none) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s s' c a delta alt m' ev hbuf hrd hali hwr hstep
    exact xadd_eintrag_aus_schritt s s' c a delta alt m' ev
      hbuf hrd hali hwr hstep
  · intro s s' c a erwartet neu alt m' hbuf hrd hali hgleich hwr hles hstep hne
    exact cas_erfolg_eintrag_aus_schritt s s' c a erwartet neu alt m'
      hbuf hrd hali hgleich hwr hles hstep hne
  · intro s s' c a erwartet neu alt bok hbuf hrd hali hfehl hstep
    exact cas_fehlschlag_eintrag_aus_schritt s s' c a erwartet neu alt bok
      hbuf hrd hali hfehl hstep
  · intro s s' c ev hstep hbuf
    exact zaun_eintrag_aus_schritt s s' c ev hstep hbuf
  · intro s s' c d a v w h hne hmiss hrd t e hzaun hrd2
    exact ordnung_eintrag_aus_schritt s s' c d a v w h hne hmiss hrd t e
      hzaun hrd2
  · intro z
    exact ohne_eintrag_verweigert z

/-! ## 5. Joint witness: reached, two-core, memory-changing. -/

/-- JOINT WITNESS for `ComposeAtomicLedger_verbindung`: a reached
    two-issue run whose flush observably changes canonical memory; a
    two-core locked-add pair changing one word from 0 to 12; installing
    and stuttering CAS steps; a fence beside a foreign pending store; a
    release store invisible to the foreign core with a fence-ready
    acquire beside it; and the empty ledger refusing. Non-degenerate:
    real buffered stores, real RMW events, memory-changing steps. -/
theorem ComposeAtomicLedger_verbindung_zeuge :
    (TSOErreichbar sbStart sbNach2 ∧
      sbNach2.mem.bytes sbX ≠ sbGespült.mem.bytes sbX) ∧
    (∃ s0 s1 s2 : TSOZustand, ∃ e1 e2 : LockEreignis,
      lockSchritt (.xadd64 lockAddr 5) 0 s0 = some (s1, e1) ∧
      lockSchritt (.xadd64 lockAddr 7) 1 s1 = some (s2, e2) ∧
      e1.kern ≠ e2.kern ∧ e1.istRmw = true ∧ e2.istRmw = true ∧
      s0.mem.bytes lockAddr ≠ s2.mem.bytes lockAddr) ∧
    (∃ s' : TSOZustand, casSchritt lockAddr 0 9 0 lockStart = some (s', true) ∧
      read64 s'.mem lockAddr = some 9) ∧
    (casSchritt lockAddr 5 9 0 lockStart = some (lockStart, false)) ∧
    (∃ s s' : TSOZustand, ∃ ev : LockEreignis,
      s.puffer 0 = [] ∧ lockSchritt .mfence 0 s = some (s', ev) ∧
      s'.puffer 1 ≠ [] ∧ ev.istZaun = true) ∧
    (loadByte sbNach1 1 sbX = some (sbStart.mem.bytes sbX) ∧
      loadByte sbStart 0 sbX = some (sbStart.mem.bytes sbX)) ∧
    (ledgerFindt [] (.xadd lockAddr 5) = none) := by
  refine ⟨⟨hist_zeuge_gelenk.1, sb_flush_aendert_speicher⟩,
    locked_add_zwei_kerne, cas_erfolg_zeuge, cas_fehlschlag_zeuge,
    mfence_ordnung_zeuge, ⟨?_, ?_⟩, ohne_eintrag_verweigert _⟩
  · exact freigabe_braucht_flush sbStart sbNach1 0 1 sbX sbEins
      sb_schritt1 (by decide) rfl (by decide)
  · exact zaun_erwerb_liest_kanonisch sbStart 0 sbX
      ((zaunBereit_iff_leer sbStart 0).mpr rfl) (by decide)

/- CUTS:
    - No new executor, decoder, memory or source model: `AtomZugriff`,
      `LedgerEintrag`, `ledgerEintrag`/`ledgerCasOk`, `ledgerDeckt` and
      `ledgerFindt` are pure compositions over the accepted
      `lockSchritt`/`casSchritt`/`issueByte`/`loadByte`/`flushKern`
      vocabulary; every step fact is an application of an accepted
      lemma (`lock_xadd_atomar`, `cas_erfolg_schreibt`,
      `cas_fehlschlag_stottert`, `mfence_ordnung`,
      `freigabe_braucht_flush`, `zaun_erwerb_liest_kanonisch`).
    - No per-access W/GX refinement: closing an access to its ledger
      entry is not a `SchrittW` simulation (byte vs carrier
      granularity, per-rule O-access decomposition). Owned by bridge
      lanes 573 (`BridgeWrite`) and 574 (`BridgeRead`), recorded OPEN
      in their CUTS; this module hands them addressed, ordered,
      RMW-tagged, outcome-recorded accesses.
    - No source-carrier admission link: `AtomZugriff` is not connected
      to the source `GeteiltV` admission (`AtomicPayload`, lane 350).
      Follow-up: exhibit the address map from ledger entries to
      admitted shared atomics.
    - No fetch/decode linkage: the ledger takes addresses, not decoded
      bytes. Consumers: fetched LOCK paths of lanes 776
      (`LockCmpxchgSuccess`), 778 (`LockXaddFetch`), 779
      (`XchgOrderNeed`) and the retry discipline of lane 784
      (`CasRetryBound`).
    - No tearing claim at this layer: single byte issues still tear
      (`paket_reisst`, `riss_gemischt_verweigert`, accepted); only the
      guarded LOCK word update is one ledger RMW entry.
    - No hardware time, fairness or progress: `lockKosten`/`casKosten`
      shapes are reused only as data, never as cycle bounds; failure
      stutter is safety-only.
    - No source, checker, contract, budget or goal change: nothing here
      speaks about `Vertrag`, `Stmt`, duties or `gabbro_ziel`.
-/

#print axioms lese_schliesst
#print axioms schreibe_schliesst
#print axioms xadd_schliesst
#print axioms cas_schliesst
#print axioms zaun_schliesst
#print axioms xadd_eintrag_aus_schritt
#print axioms cas_erfolg_eintrag_aus_schritt
#print axioms cas_fehlschlag_eintrag_aus_schritt
#print axioms zaun_eintrag_aus_schritt
#print axioms ordnung_eintrag_aus_schritt
#print axioms ohne_eintrag_verweigert
#print axioms falsche_ordnung_verweigert
#print axioms kein_rmw_ohne_lock_verweigert
#print axioms xadd_eintrag_gefunden
#print axioms ComposeAtomicLedger_verbindung
#print axioms ComposeAtomicLedger_verbindung_zeuge

end Gabbro.Grammatik.X86
