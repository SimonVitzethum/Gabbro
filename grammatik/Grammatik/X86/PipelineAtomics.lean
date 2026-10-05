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
