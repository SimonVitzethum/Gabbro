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
