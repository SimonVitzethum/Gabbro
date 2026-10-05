/-
  File:      Grammatik/X86/PipelineAtomics.lean
  Subject:   Pipeline: source shared-atomic reads/writes, fences and lock
              sections onto TSO target forms.

  Lane 1163: lowers a small source atomic vocabulary (`AtomQuelle`) to
  target forms (`ZielOp`): plain aligned MOV (`Befehl.load64/store64`,
  `Codec.encode`) for relaxed/acquire loads and release stores under the
  NAMED hardware assumption `TSOPlainRegel` (discharged against the
  accepted TSO model), LOCK-prefixed RMW and MFENCE (`LockForm`,
  `encodeLock`, reused) otherwise. Per-access correspondence reuses the
  accepted step facts (`effAddr_load/store_schritt`, `lockSchritt`,
  `casSchritt`, `mfenceDrain`, `ladeWort8`, `wLesbar_aus_gruppe`) with
  ledger closing (`ledgerDeckt`); no fairness or retry bound is claimed.
  Unsupported shapes are REFUSED, never guessed. No second IR, no second
  source interpreter, no optimiser change.
-/
import Grammatik.X86.Pipeline
import Grammatik.X86.ComposeAtomicLedger
import Grammatik.X86.BridgeRead
import Grammatik.X86.MfenceDrainOwn
import Grammatik.X86.LockedInstructionExecution
import Grammatik.X86.EffectiveAddress

namespace Gabbro.Grammatik.X86.PipelineAtomics

open Gabbro.Grammatik
open Gabbro.Grammatik.X86

/-- Source atomic op: shared-atomic read/write with ordering, fence,
    word RMW (expected value in rax for CAS, as hardware compares
    against rax), and lock sections (fence-bracketed bodies). -/
inductive AtomQuelle where
  | lese (a : Adresse) (o : Speichermodell.Ordnung) (dst base : Register) (disp : BitVec 32)
  | schreibe (a : Adresse) (o : Speichermodell.Ordnung) (base src : Register) (disp : BitVec 32)
  | zaun
  | xadd (src base : Register) (disp : BitVec 32)
  | cas (src base : Register) (disp : BitVec 32)
  | sperre (innen : List AtomQuelle)
  deriving Repr

/-- Target op: plain MOV (pilot word load/store) or a LOCK form. -/
inductive ZielOp where
  | movLoad (dst base : Register) (disp : BitVec 32)
  | movStore (base src : Register) (disp : BitVec 32)
  | lock (f : LockForm)
  deriving DecidableEq, Repr

/-! ## 1. Lowering: plain MOV for loads/stores, LOCK/MFENCE otherwise.

    Relaxed and acquire loads and release stores lower to plain aligned
    MOV (`load64`/`store64`): on x86-TSO loads are not reordered with
    loads and stores not with stores, so no fence is needed for these
    orders (the exact rule is the named assumption `TSOPlainRegel` of
    §2). `seq_cst` stays modelled as release/acquire (the accepted
    over-approximation of `ReleaseAcquire`: no total order claimed).
    Fences lower to MFENCE, RMW to LOCK XADD / LOCK CMPXCHG, lock
    sections to MFENCE-bracketed bodies. Nested lock sections are
    REFUSED (no lock-order claim is made here). -/

/-- Canonical bytes of one target op: the pilot encoder for plain MOV,
    `encodeLock` for LOCK forms (both reused, never redefined). -/
def zielBytes : ZielOp → List Byte
  | .movLoad dst base disp => encode (.load64 dst base disp)
  | .movStore base src disp => encode (.store64 base src disp)
  | .lock f => encodeLock f

/-- Lower one body op (no lock sections inside): every shape but
    `sperre` lowers; `sperre` is refused here (nested locks). -/
def senkEinzeln : AtomQuelle → Option ZielOp
  | .lese _ _ dst base disp => some (.movLoad dst base disp)
  | .schreibe _ _ base src disp => some (.movStore base src disp)
  | .zaun => some (.lock .mfence)
  | .xadd src base disp => some (.lock (.xadd64 src base disp))
  | .cas src base disp => some (.lock (.cmpxchg64 src base disp))
  | .sperre _ => none

/-- Lower a body: each element singly; any refusal refuses the body. -/
def senkListe : List AtomQuelle → Option (List ZielOp)
  | [] => some []
  | q :: qs =>
    match senkEinzeln q, senkListe qs with
    | some t, some ts => some (t :: ts)
    | _, _ => none

/-- Lower one source atomic op: single ops go singly, a lock section
    becomes the MFENCE entry, the lowered body, the MFENCE exit. -/
def senkAtom : AtomQuelle → Option (List ZielOp)
  | .lese _ _ dst base disp => some [.movLoad dst base disp]
  | .schreibe _ _ base src disp => some [.movStore base src disp]
  | .zaun => some [.lock .mfence]
  | .xadd src base disp => some [.lock (.xadd64 src base disp)]
  | .cas src base disp => some [.lock (.cmpxchg64 src base disp)]
  | .sperre innen =>
    match senkListe innen with
    | some ts => some ([.lock .mfence] ++ ts ++ [.lock .mfence])
    | none => none

/-- Decided validator: `ts` is accepted for `q` exactly when the
    lowering produces it. Bytes are checked data, never trusted. -/
def valAtom (q : AtomQuelle) (ts : List ZielOp) : Bool :=
  match senkAtom q with
  | some ts' => decide (ts' = ts)
  | none => false

/-- A load lowers to its plain MOV. -/
theorem senk_lese (a : Adresse) (o : Speichermodell.Ordnung)
    (dst base : Register) (disp : BitVec 32) :
    senkAtom (.lese a o dst base disp) = some [.movLoad dst base disp] := rfl

/-- A store lowers to its plain MOV. -/
theorem senk_schreibe (a : Adresse) (o : Speichermodell.Ordnung)
    (base src : Register) (disp : BitVec 32) :
    senkAtom (.schreibe a o base src disp) = some [.movStore base src disp] := rfl

/-- A fence lowers to MFENCE. -/
theorem senk_zaun : senkAtom .zaun = some [.lock .mfence] := rfl

/-- Fetch-add lowers to LOCK XADD. -/
theorem senk_xadd (src base : Register) (disp : BitVec 32) :
    senkAtom (.xadd src base disp) = some [.lock (.xadd64 src base disp)] := rfl

/-- Compare-exchange lowers to LOCK CMPXCHG. -/
theorem senk_cas (src base : Register) (disp : BitVec 32) :
    senkAtom (.cas src base disp) = some [.lock (.cmpxchg64 src base disp)] := rfl

/-- A lock section lowers to the MFENCE-bracketed body. -/
theorem senk_sperre (innen : List AtomQuelle) (innere : List ZielOp)
    (h : senkListe innen = some innere) :
    senkAtom (.sperre innen) = some ([.lock .mfence] ++ innere ++ [.lock .mfence]) := by
  simp only [senkAtom, h]

/-- A body ending in a nested lock section is REFUSED. -/
theorem senkListe_mit_sperre (innen : List AtomQuelle) (aussen : List AtomQuelle) :
    senkListe (innen ++ [.sperre aussen]) = none := by
  induction innen with
  | nil => rfl
  | cons q qs ih =>
    have h2 : senkListe (qs ++ [.sperre aussen]) = none := ih
    simp only [List.cons_append, senkListe, h2]
    cases senkEinzeln q <;> rfl

/-- A nested lock section is REFUSED. -/
theorem sperre_verschachtelt_verweigert (innen aussen : List AtomQuelle) :
    senkAtom (.sperre (innen ++ [.sperre aussen])) = none := by
  simp only [senkAtom, senkListe_mit_sperre]

/-- The validator accepts exactly the lowered targets. -/
theorem valAtom_korrekt (q : AtomQuelle) (ts : List ZielOp) :
    valAtom q ts = true ↔ senkAtom q = some ts := by
  unfold valAtom
  cases h : senkAtom q with
  | none => simp [h]
  | some ts' => simp only [h, decide_eq_true_eq, Option.some.injEq]

/-- Every lowered plain MOV is straight-line pilot code. -/
theorem zielOp_gerade : ∀ (t : ZielOp),
    (match t with
    | .movLoad dst base disp => Pipeline.gerade (.load64 dst base disp) = true
    | .movStore base src disp => Pipeline.gerade (.store64 base src disp) = true
    | .lock _ => True) := by
  intro t
  cases t with
  | movLoad dst base disp => rfl
  | movStore base src disp => rfl
  | lock f => exact True.intro

/-- Plain MOV bytes decode back (pilot round trip, reused). -/
theorem zielBytes_movLoad_rundweg (dst base : Register) (disp : BitVec 32)
    (suffix : List Byte) :
    decode (zielBytes (.movLoad dst base disp) ++ suffix) =
      some (⟨.load64 dst base disp, (zielBytes (.movLoad dst base disp)).length⟩, suffix) := by
  unfold zielBytes
  exact roundtrip (.load64 dst base disp) suffix

/-- LOCK bytes decode back (locked round trip, reused). -/
theorem zielBytes_lock_rundweg (f : LockForm) (suffix : List Byte) :
    decodeLock (zielBytes (.lock f) ++ suffix) =
      some (LockAnweisung.ok f (zielBytes (.lock f)).length, suffix) := by
  unfold zielBytes
  exact roundtripLock f suffix

/-! ## 2. The NAMED hardware assumption: the plain-MOV reordering rule.

    On x86-TSO only Store→Load may reorder; loads are not reordered
    with loads and stores not with stores (Intel SDM Vol. 3A §9.2,
    summarized by the accepted TSO model). Hence a relaxed or acquire
    load and a release store lower to a plain aligned MOV: the three
    packaged facts are (a) a release store is invisible off-core until
    its drain, (b) a fence-ready load observes canonical memory, (c) a
    drained store is visible through its own drain, (d) the issuing core
    observes its own store with no fence. `TSOPlainRegel_gilt`
    discharges the assumption against the accepted model, so every
    per-access theorem below cites the NAME and never the silicon. -/

/-- The plain-MOV reordering rule, as one named assumption. -/
structure TSOPlainRegel : Prop where
  unsichtbar : ∀ (s s' : TSOZustand) (c d : Nat) (a : Adresse) (v : Byte),
    issueByte s c a v = some s' → d ≠ c →
    neuestens (s.puffer d) a = none → s.mem.lesbar a = true →
    loadByte s' d a = some (s.mem.bytes a)
  zaunLiest : ∀ (s : TSOZustand) (c : Nat) (a : Adresse),
    zaunBereit s c = true → s.mem.lesbar a = true →
    loadByte s c a = some (s.mem.bytes a)
  drainSichtbar : ∀ (s s1 s2 : TSOZustand) (c : Nat) (a : Adresse) (v : Byte),
    s.puffer c = [] → issueByte s c a v = some s1 →
    flushKern s1 c = some s2 → s2.mem.bytes a = v
  eigenSichtbar : ∀ (s s' : TSOZustand) (c : Nat) (a : Adresse) (v : Byte),
    issueByte s c a v = some s' → s.mem.lesbar a = true →
    loadByte s' c a = some v

/-- The named rule HOLDS of the accepted TSO model. -/
theorem TSOPlainRegel_gilt : TSOPlainRegel :=
  ⟨freigabe_braucht_flush, zaun_erwerb_liest_kanonisch,
    freigabe_flush_sichtbar, load_nach_issue⟩

/-- Fence readiness is the empty own buffer (reused, not restated). -/
theorem zaunBereit_aus_leer (s : TSOZustand) (c : Nat)
    (hbuf : s.puffer c = []) : zaunBereit s c = true :=
  (zaunBereit_iff_leer s c).mpr hbuf

/-! ## 3. Per-access correspondence: loads.

    A lowered relaxed/acquire load runs the pilot `load64` step on the
    effective address AND agrees with the TSO group load under the named
    rule: with an empty own buffer the group observes canonical memory,
    which is exactly what the step read. The ledger closes the access. -/

/-- **LOAD CORRESPONDENCE.** The lowered plain MOV reads the word at the
    effective address into the destination, keeps memory, agrees with
    the TSO group load under `TSOPlainRegel`, and closes the ledger.
    Every premise pins one guard; the named rule is cited, never the
    silicon. -/
theorem lese_korrekt (q : AtomQuelle) (ts : List ZielOp)
    (s s' : Zustand) (t : TSOZustand) (c : Nat)
    (a : Adresse) (o : Speichermodell.Ordnung)
    (dst base : Register) (disp : BitVec 32) (w : Wort)
    (hq : q = .lese a o dst base disp)
    (hSen : senkAtom q = some ts)
    (heff : effAddr s base disp = a)
    (hmem : t.mem = s.speicher)
    (hbuf : t.puffer c = [])
    (hRd : lesbar8 s.speicher a = true)
    (hrd : read64 s.speicher a = some w)
    (hstep : schritt (Pipeline.kanon (.load64 dst base disp)) s = some s')
    (hRegel : TSOPlainRegel) :
    s'.register dst = w ∧ s'.speicher = s.speicher ∧
      ladeWort8 t c a = read64 s.speicher a ∧
      ts = [.movLoad dst base disp] ∧
      ledgerDeckt (.lese a o) (ledgerEintrag (.lese a o)) = true := by
  subst hq
  rw [senk_lese] at hSen
  cases hSen
  have hrd' : read64 s.speicher (effAddr s base disp) = some w := heff ▸ hrd
  obtain ⟨hreg, hspeicher, -⟩ := effAddr_load_schritt _ s s' dst base disp w
    (laengeOk_encode _) rfl hrd' hstep
  have hRd' : lesbar8 t.mem a = true := by rw [hmem]; exact hRd
  have hzaun := zaunBereit_aus_leer t c hbuf
  have hL : ∀ i : Fin 8,
      loadByte t c (addrOff a i.val) = some ((readBytes t.mem a) i) := by
    intro i
    exact hRegel.zaunLiest t c _ hzaun
      (lesbar8_hit t.mem a i.val hRd' i.isLt)
  have hGrp := ladeWort8_aus_lesungen t c a (readBytes t.mem a) hL
  have hRdT : read64 t.mem a = some (bytesWort (readBytes t.mem a)) := by
    unfold read64
    rw [if_pos hRd']
  have hEq : ladeWort8 t c a = read64 s.speicher a := by
    have hGrp2 : ladeWort8 t c a = read64 t.mem a := hGrp.trans hRdT.symm
    rw [← hmem]
    exact hGrp2
  exact ⟨hreg, hspeicher, hEq, rfl, lese_schliesst a o⟩

/-! ## 4. Per-access correspondence: stores.

    A lowered release store runs the pilot `store64` step on the
    effective address. Under the named rule the issued footprint byte
    stays invisible off-core until its drain while the issuing core
    observes it at once. The ledger closes the access. -/

/-- **STORE CORRESPONDENCE.** The lowered plain MOV writes exactly the
    footprint bytes, the issued byte is invisible off-core until
    flushed and visible on-core at once (both under `TSOPlainRegel`),
    and the ledger closes. Byte 0 links the issued byte to the stored
    word (`wortByte`). -/
theorem schreibe_korrekt (q : AtomQuelle) (ts : List ZielOp)
    (s s' : Zustand) (t t' : TSOZustand) (c d : Nat) (m : Speicher)
    (a : Adresse) (o : Speichermodell.Ordnung)
    (base src : Register) (disp : BitVec 32) (b0 : Byte)
    (hq : q = .schreibe a o base src disp)
    (hSen : senkAtom q = some ts)
    (heff : effAddr s base disp = a)
    (hwr : write64 s.speicher a (s.register src) = some m)
    (hstep : schritt (Pipeline.kanon (.store64 base src disp)) s = some s')
    (hb : b0 = wortByte (s.register src) 0)
    (hIssue : issueByte t c (addrOff a 0) b0 = some t')
    (hne : d ≠ c)
    (hmiss : neuestens (t.puffer d) (addrOff a 0) = none)
    (hrd : t.mem.lesbar (addrOff a 0) = true)
    (hRegel : TSOPlainRegel) :
    (∀ x, s'.speicher.bytes x ≠ s.speicher.bytes x → x ∈ Fuss a) ∧
      loadByte t' d (addrOff a 0) = some (t.mem.bytes (addrOff a 0)) ∧
      loadByte t' c (addrOff a 0) = some (wortByte (s.register src) 0) ∧
      ts = [.movStore base src disp] ∧
      ledgerDeckt (.schreibe a (s.register src) o)
        (ledgerEintrag (.schreibe a (s.register src) o)) = true := by
  subst hq
  rw [senk_schreibe] at hSen
  cases hSen
  have hwr' : write64 s.speicher (effAddr s base disp) (s.register src) =
      some m := heff ▸ hwr
  obtain ⟨hfuss, -, -⟩ := effAddr_store_schritt _ s s' base src disp m
    (laengeOk_encode _) rfl hwr' hstep
  rw [heff] at hfuss
  refine ⟨hfuss, hRegel.unsichtbar t t' c d _ b0 hIssue hne hmiss hrd, ?_,
    rfl, schreibe_schliesst _ _ _⟩
  rw [← hb]
  exact hRegel.eigenSichtbar t t' c _ b0 hIssue hrd

/-! ## 5. Per-access correspondence: fences.

    A lowered fence is the decoded MFENCE byte form running the
    own-buffer drain: afterwards the own buffer is empty and
    fence-ready, every foreign buffer is intact, and later loads on the
    acting core observe canonical memory. Draining another core is NOT
    claimed. -/

/-- **FENCE CORRESPONDENCE.** The lowered MFENCE bytes decode to the
    fence form and drain the own buffer with the full local frame. -/
theorem zaun_korrekt (q : AtomQuelle) (ts : List ZielOp)
    (t t' : TSOZustand) (c : Nat) (rest : List Byte)
    (hq : q = .zaun)
    (hSen : senkAtom q = some ts)
    (hdec : decodeLock pinMfence = some (LockAnweisung.ok .mfence 3, rest))
    (hbuf : t.puffer c = [])
    (hdrain : mfenceDrain t c = some t') :
    t'.puffer c = [] ∧ zaunBereit t' c = true ∧
      (∀ d : Nat, d ≠ c → t'.puffer d = t.puffer d) ∧
      (∀ a : Adresse, t'.mem.lesbar a = true →
        loadByte t' c a = some (t'.mem.bytes a)) ∧
      lockSchritt .mfence c t =
        some (t, ⟨c, [], [], none, none, false, true⟩) ∧
      ts = [.lock .mfence] ∧
      mfenceSchrittAusBytes pinMfence t c = some t' ∧
      ledgerDeckt .zaun (ledgerEintrag .zaun) = true := by
  subst hq
  rw [senk_zaun] at hSen
  cases hSen
  have hbyte : mfenceSchrittAusBytes pinMfence t c = some t' := by
    unfold mfenceSchrittAusBytes
    rw [hdec]
    exact hdrain
  exact ⟨mfenceDrain_leert t t' c hdrain,
    mfenceDrain_bereit t t' c hdrain,
    fun d hd => mfenceDrain_fremd t t' c hd hdrain,
    fun a hrd => mfenceDrain_ordnung t t' c hdrain a hrd,
    lockSchritt_mfence_erfolg t c hbuf, rfl, hbyte, zaun_schliesst⟩

/-- The byte step equation behind the fence correspondence. -/
theorem zaun_byteseite (t t' : TSOZustand) (c : Nat)
    (hdrain : drainVoll t c = some t') :
    mfenceSchrittAusBytes pinMfence t c = some t' :=
  mfenceSchrittAusBytes_ok t t' c [] pin_lock_mfence_decodiert hdrain

/-! ## 6. Per-access correspondence: RMW.

    Lowered fetch-add and compare-exchange run the accepted locked steps
    on canonical memory with the full atomicity frame. The
    register-address binding of the byte forms (which base/disp names
    which address) is NOT proved here: it is the stated open gap, and
    the fetched byte runs stay with the reused pins. -/

/-- **XADD CORRESPONDENCE.** The lowered LOCK XADD grows the word by the
    delta with the single-RMW event, keeps every outside byte, decodes
    from its canonical bytes, and closes the ledger. -/
theorem xadd_korrekt (q : AtomQuelle) (ts : List ZielOp)
    (t t' : TSOZustand) (c : Nat)
    (a : Adresse) (delta alt : Wort) (m' : Speicher) (ev : LockEreignis)
    (src base : Register) (disp : BitVec 32)
    (hq : q = .xadd src base disp)
    (hSen : senkAtom q = some ts)
    (hbuf : t.puffer c = [])
    (hrd : read64 t.mem a = some alt)
    (hali : ausgerichtet8 a = true)
    (hwr : write64 t.mem a (alt + delta) = some m')
    (hstep : lockSchritt (.xadd64 a delta) c t = some (t', ev)) :
    ev.istRmw = true ∧ ev.lesen = Fuss a ∧ ev.schreiben = Fuss a ∧
      ev.gelesen = some alt ∧ ev.geschrieben = some (alt + delta) ∧
      (∀ x, (∀ k : Nat, k < 8 → x ≠ addrOff a k) →
        t'.mem.bytes x = t.mem.bytes x) ∧
      ts = [.lock (.xadd64 src base disp)] ∧
      decodeLock (zielBytes (.lock (.xadd64 src base disp))) =
        some (LockAnweisung.ok (.xadd64 src base disp)
          (zielBytes (.lock (.xadd64 src base disp))).length, []) ∧
      ledgerDeckt (.xadd a delta) (ledgerEintrag (.xadd a delta)) = true := by
  subst hq
  rw [senk_xadd] at hSen
  cases hSen
  obtain ⟨hrmw, hles, hschr, hgelesen, hgeschr, -, -, -, hrahmen⟩ :=
    lock_xadd_atomar t t' c a delta alt m' ev hbuf hrd hali hwr hstep
  have hrt := zielBytes_lock_rundweg (.xadd64 src base disp) []
  simp only [List.append_nil] at hrt
  exact ⟨hrmw, hles, hschr, hgelesen, hgeschr, hrahmen, rfl, hrt,
    xadd_schliesst a delta⟩

/-- **CAS SUCCESS CORRESPONDENCE.** The lowered LOCK CMPXCHG installs
    the new word, observably changes the read-back, keeps every outside
    byte, decodes from its canonical bytes, and closes the ledger with
    the decided outcome. -/
theorem cas_korrekt_erfolg (q : AtomQuelle) (ts : List ZielOp)
    (t t' : TSOZustand) (c : Nat)
    (a : Adresse) (erwartet neu alt : Wort) (m' : Speicher)
    (src base : Register) (disp : BitVec 32)
    (hq : q = .cas src base disp)
    (hSen : senkAtom q = some ts)
    (hbuf : t.puffer c = [])
    (hrd : read64 t.mem a = some alt)
    (hali : ausgerichtet8 a = true)
    (hgleich : (alt == erwartet) = true)
    (hwr : write64 t.mem a neu = some m')
    (hles : lesbar8 t.mem a = true)
    (hne : neu ≠ alt)
    (hstep : casSchritt a erwartet neu c t = some (t', true)) :
    read64 t'.mem a = some neu ∧
      (∀ x, (∀ k : Nat, k < 8 → x ≠ addrOff a k) →
        t'.mem.bytes x = t.mem.bytes x) ∧
      ts = [.lock (.cmpxchg64 src base disp)] ∧
      decodeLock (zielBytes (.lock (.cmpxchg64 src base disp))) =
        some (LockAnweisung.ok (.cmpxchg64 src base disp)
          (zielBytes (.lock (.cmpxchg64 src base disp))).length, []) ∧
      ledgerDeckt (.cas a erwartet neu) (ledgerCasOk a true) = true := by
  subst hq
  rw [senk_cas] at hSen
  cases hSen
  obtain ⟨hrb, -, -, hrahmen⟩ := cas_erfolg_schreibt t t' c a erwartet neu alt
    m' hbuf hrd hali hgleich hwr hles hstep hne
  have hrt := zielBytes_lock_rundweg (.cmpxchg64 src base disp) []
  simp only [List.append_nil] at hrt
  exact ⟨hrb, hrahmen, rfl, hrt, cas_schliesst a erwartet neu true⟩

/-- **CAS FAILURE CORRESPONDENCE.** A failed comparison stutters (the
    accepted step performs no install); the ledger records the decided
    `false`. The byte machine's write-back (which additionally pins
    write permission) stays with the reused adapter
    `lockVoll_cmpxchg_fehlschlag_adapter`, cited, not restated. -/
theorem cas_korrekt_fehlschlag (q : AtomQuelle) (ts : List ZielOp)
    (t t' : TSOZustand) (c : Nat)
    (a : Adresse) (erwartet neu alt : Wort)
    (src base : Register) (disp : BitVec 32)
    (hq : q = .cas src base disp)
    (hSen : senkAtom q = some ts)
    (hbuf : t.puffer c = [])
    (hrd : read64 t.mem a = some alt)
    (hali : ausgerichtet8 a = true)
    (hfehl : (alt == erwartet) = false)
    (hstep : casSchritt a erwartet neu c t = some (t', false)) :
    t' = t ∧
      ts = [.lock (.cmpxchg64 src base disp)] ∧
      decodeLock (zielBytes (.lock (.cmpxchg64 src base disp))) =
        some (LockAnweisung.ok (.cmpxchg64 src base disp)
          (zielBytes (.lock (.cmpxchg64 src base disp))).length, []) ∧
      ledgerDeckt (.cas a erwartet neu) (ledgerCasOk a false) = true := by
  subst hq
  rw [senk_cas] at hSen
  cases hSen
  have heq := casSchritt_fehlschlag t c a erwartet neu alt hbuf hrd hali hfehl
  rw [heq] at hstep
  cases hstep
  have hrt := zielBytes_lock_rundweg (.cmpxchg64 src base disp) []
  simp only [List.append_nil] at hrt
  exact ⟨rfl, rfl, hrt, cas_schliesst a erwartet neu false⟩

/-! ## 7. Lock sections: fence-bracketed bodies.

    A lock section lowers to the MFENCE entry, the lowered body, the
    MFENCE exit. Entry makes later loads canonical (acquire side),
    exit drains prior stores to visibility (release side); foreign
    buffers survive all three phases. The inner run's foreign frame is
    an explicit premise (per-step framing of arbitrary inner runs is
    OPEN, see CUTS). -/

/-- Reached runs chain: the recorded steps of the second run extend the
    first. Reused shape, proved once here. -/
theorem erreichbar_kette (s0 s1 s2 : TSOZustand)
    (h1 : TSOErreichbar s0 s1) (h2 : TSOErreichbar s1 s2) :
    TSOErreichbar s0 s2 := by
  induction h2 with
  | start => exact h1
  | schritt _ hstep ih => exact .schritt ih hstep

/-- **LOCK-SECTION CORRESPONDENCE.** Entry and exit drains empty the own
    buffer and fence it, every foreign buffer ends as it began, and the
    whole bracket is one reached run. -/
theorem sperre_korrekt (innen : List AtomQuelle) (innere : List ZielOp)
    (s0 s1 s2 s3 : TSOZustand) (c : Nat)
    (hIn : senkListe innen = some innere)
    (hEintritt : mfenceDrain s0 c = some s1)
    (hMitte : TSOErreichbar s1 s2)
    (hRahmen : ∀ d : Nat, d ≠ c → s2.puffer d = s1.puffer d)
    (hAustritt : mfenceDrain s2 c = some s3) :
    senkAtom (.sperre innen) =
        some ([.lock .mfence] ++ innere ++ [.lock .mfence]) ∧
      s3.puffer c = [] ∧ zaunBereit s3 c = true ∧
      (∀ d : Nat, d ≠ c → s3.puffer d = s0.puffer d) ∧
      TSOErreichbar s0 s3 := by
  have hSen := senk_sperre innen innere hIn
  have r1 : TSOErreichbar s0 s1 :=
    mfenceDrain_erreichbar_von s0 s0 s1 c .start hEintritt
  have r2 : TSOErreichbar s0 s2 := erreichbar_kette s0 s1 s2 r1 hMitte
  have r3 : TSOErreichbar s0 s3 :=
    mfenceDrain_erreichbar_von s0 s2 s3 c r2 hAustritt
  refine ⟨hSen, mfenceDrain_leert s2 s3 c hAustritt,
    mfenceDrain_bereit s2 s3 c hAustritt, ?_, r3⟩
  intro d hd
  rw [mfenceDrain_fremd s2 s3 c hd hAustritt, hRahmen d hd,
    mfenceDrain_fremd s0 s1 c hd hEintritt]

/-! ## 8. GX legs: what is proved per access toward the source.

    The committed group read simulates a source W read (the `lies`
    consequent for a real recording G step is DERIVED through the
    reused `wLesbar_aus_gruppe`), and a plain-carrier value survives
    every atomic environment of the rely (`havoc_erhaelt_gruppenwert`).
    No full `SchrittW` is derived here: `schwach_ist_gX` is cited, not
    applied -- exactly the boundary `BridgeRead` records. -/

/-- **GX READ LEG.** A lowered plain load at a represented slot parses
    to exactly the source slot value and derives the `lies` consequent
    for every recording G step. -/
theorem gx_lese_korrekt {D : Deklaration} {t : D.Tab} {k : Int}
    {f : D.Feld t} {lo hi : Int} {hT : D.typ t f = .int lo hi}
    {a : Adresse} {s : TSOZustand} {c0 : Nat}
    {σw : World D} {σ : Gabbro.Grammatik.Speicher D}
    {W : RufMaschineW D} {u : Faden} {M'' : RufMaschineG D} {n : Nat}
    (q : AtomQuelle) (zt : List ZielOp)
    (o : Speichermodell.Ordnung) (dst base : Register) (disp : BitVec 32)
    (hq : q = .lese a o dst base disp)
    (hSen : senkAtom q = some zt)
    (v : Zahl lo hi)
    (hRep : RepSlot t k f lo hi hT a s.mem σw)
    (hMiss : ∀ i : Nat, i < 8 → neuestens (s.puffer c0) (addrOff a i) = none)
    (hRd : lesbar8 s.mem a = true)
    (hLo : 0 ≤ lo) (hHi : hi < 2 ^ 64)
    (w : Wort) (hWort : ladeWort8 s c0 a = some w)
    (hv : (cast (congrArg (Wert D) hT) (σw.slots t k f)) = v)
    (hMem : (⟨n, σw.speicher, Speichermodell.Sicht.null⟩ : NachrichtW D) ∈
      W.hist (.inl t))
    (hProj : W.sicht u (.inl t) ≤ sichtVon s c0 a)
    (hTs : sichtVon s c0 a ≤ n)
    (hTraeger : TraegerGleich σ σw.speicher (.inl t)) :
    zt = [.movLoad dst base disp] ∧
      wortZahl lo hi w = some v ∧
      ledgerDeckt (.lese a o) (ledgerEintrag (.lese a o)) = true ∧
      (LiestG (mitSpeicher W.g σ) M'' u (.inl t) →
        Speichermodell.Lesbar W.hist (W.sicht u) (.inl t)
          (⟨n, σw.speicher, Speichermodell.Sicht.null⟩ : NachrichtW D) ∧
        TraegerGleich σ
          (⟨n, σw.speicher, Speichermodell.Sicht.null⟩ : NachrichtW D).wert
          (.inl t)) := by
  subst hq
  rw [senk_lese] at hSen
  cases hSen
  obtain ⟨hval, hlie⟩ := wLesbar_aus_gruppe v hRep hMiss hRd hLo hHi w
    hWort hv hMem hProj hTs hTraeger
  exact ⟨rfl, hval, lese_schliesst a o, hlie⟩

/-- **RELY STABILITY LEG.** A plain-carrier value read through a lowered
    load survives every atomic environment of the rely. -/
theorem rely_stabil {D : Deklaration}
    {T : D.Tab ⊕ D.Glob → Prop} {A : AUmwelt D} (hA : HavocA T A)
    {t : D.Tab} {k : Int} {f : D.Feld t} {lo hi : Int}
    {hT : D.typ t f = .int lo hi} {v : Zahl lo hi}
    (q : AtomQuelle) (zt : List ZielOp)
    (a : Adresse) (o : Speichermodell.Ordnung)
    (dst base : Register) (disp : BitVec 32)
    (hq : q = .lese a o dst base disp)
    (hSen : senkAtom q = some zt)
    (hTnot : ¬ T (.inl t))
    {X : List (D.Tab ⊕ D.Glob)} {σw : World D}
    (hV : (cast (congrArg (Wert D) hT) (σw.speicher.slots t k f)) = v) :
    (cast (congrArg (Wert D) hT) (((A X σw).speicher.slots) t k f)) = v ∧
      zt = [.movLoad dst base disp] ∧
      ledgerDeckt (.lese a o) (ledgerEintrag (.lese a o)) = true := by
  subst hq
  rw [senk_lese] at hSen
  cases hSen
  have hstab : (cast (congrArg (Wert D) hT)
      (((A X σw).speicher.slots) t k f)) = v :=
    havoc_erhaelt_gruppenwert (hT := hT) hA hTnot hV
  exact ⟨hstab, rfl, lese_schliesst a o⟩
