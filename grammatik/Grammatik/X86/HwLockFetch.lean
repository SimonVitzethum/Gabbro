/-
  File:      Grammatik/X86/HwLockFetch.lean
  Subject:   LOCK family on the coherent machine: fetched-byte dispatch,
             narrower widths and other addressing modes as stated
             refusals, split-lock (cache-line crossing) as refusal.

  Lane 1209: follow-up of lane 1119 (`HwLockRmw.lean`). The 1119 plug
  takes a PARSED `LockAnweisung`; fetch stays with the single-core
  662 `lockByteschritt`. This module adds fetched-byte dispatch ON
  `HwMaschine` (decode from the core's fetched window, execute
  permission, `ExtendedExecution` discipline via 662 `decodeLockExt`),
  the SIB addressing mode 662 accepts, and split-lock refusal.
  Narrower widths (8/16/32-bit) and non-mod=2 modes have no 662 row:
  they are refused here at the decoder, never executed.
  The old evaluators are lifted, never redefined.
-/
import Grammatik.X86.HwLockRmw

namespace Gabbro.Grammatik.X86

/-- Fetched decode on the coherent machine: the 662 `lockFetch` on the
    core projection (actual executable bytes at the core RIP, combined
    decoder, length and execute-permission checks). -/
def hwLockFetch (m : HwMaschine) (c : Nat) :
    Option (LockAnweisung × List Byte) :=
  lockFetch (lockMaschineVonHw m c)

/-- The coherent fetch IS the 662 fetch on the projection: no second
    fetch model. -/
theorem hwLockFetch_aus_projektion (m : HwMaschine) (c : Nat) :
    hwLockFetch m c = lockFetch (lockMaschineVonHw m c) := rfl

/-! ## 2. Split-lock guard and the fetched step.

  A locked word crossing a cache line is a split lock (Intel SDM
  Vol. 3A 9.1.1: split locks may take a bus lock; with alignment
  checking they fault). This layer performs no bus transaction and
  claims no #AC control state, so the crossing shape is a stated
  admission refusal (`none`), never a fault claim. Line size 64 is a
  named silicon assumption (see CUTS). -/

/-- Cache-line size of the selected profile: 64 bytes (named silicon
    assumption). -/
def cacheLinie : Nat := 64

/-- Split-lock guard: true exactly when the 8-byte word at `tgt`
    meets two 64-byte lines. -/
def splitSperre (tgt : Adresse) : Bool :=
  decide ((tgt.toNat / cacheLinie) ≠ ((tgt.toNat + 7) / cacheLinie))

/-- The word footprint of a locked form on the coherent machine, if
    the form touches memory. -/
def lockFuss (m : HwMaschine) (c : Nat) : LockForm → Option Adresse
  | .xadd64 _ base d => some (effAddr (projZustand m c) base d)
  | .cmpxchg64 _ base d => some (effAddr (projZustand m c) base d)
  | .mfence => none

/-- One fetched LOCK step on the coherent machine: fetch from the
    core window, refuse parsed #UD, refuse split-lock words, admit
    the rest through the 1119 parsed plug. Takes only the machine:
    no caller-supplied decoded value ever becomes a trusted fetch. -/
def hwLockFetchSchritt (m : HwMaschine) (c : Nat) : Option HwMaschine :=
  match hwLockFetch m c with
  | none => none
  | some (a, _) =>
    match a with
    | .ud _ _ => none
    | .ok f _ =>
      match lockFuss m c f with
      | some tgt =>
        match splitSperre tgt with
        | true => none
        | false => hwLockSchritt m c a
      | none => hwLockSchritt m c a

/-- The fetched LOCK producer plug over `Unit`: the fetch decides,
    never the caller. -/
def adapterLockFetch : HwAdapter Unit :=
  ⟨fun m c _ => hwLockFetchSchritt m c⟩

/-! ## 3. Fetched-step equations and well-formedness.

  The fetched step is the parsed 1119 plug step wherever the fetch
  admits a non-split form; every other shape refuses. -/

/-- Fetch refusal refuses the fetched step. -/
theorem hwLockFetchSchritt_ohne_fetch (m : HwMaschine) (c : Nat)
    (h : hwLockFetch m c = none) :
    hwLockFetchSchritt m c = none := by
  unfold hwLockFetchSchritt
  simp only [h]

/-- A fetched parsed #UD never executes. -/
theorem hwLockFetchSchritt_ud (m : HwMaschine) (c : Nat) (g : LockUdGrund)
    (len : Nat) (rest : List Byte)
    (h : hwLockFetch m c = some (.ud g len, rest)) :
    hwLockFetchSchritt m c = none := by
  unfold hwLockFetchSchritt
  simp only [h]

/-- Split-lock words refuse the fetched step (stated admission
    refusal, never a fault claim). -/
theorem hwLockFetchSchritt_split (m : HwMaschine) (c : Nat)
    (f : LockForm) (len : Nat) (rest : List Byte)
    (h : hwLockFetch m c = some (.ok f len, rest))
    (tgt : Adresse) (hff : lockFuss m c f = some tgt)
    (hs : splitSperre tgt = true) :
    hwLockFetchSchritt m c = none := by
  unfold hwLockFetchSchritt
  simp only [h, hff, hs]

/-- Without split, the fetched step is exactly the parsed plug step
    on the fetched instruction. -/
theorem hwLockFetchSchritt_ohne_split (m : HwMaschine) (c : Nat)
    (f : LockForm) (len : Nat) (rest : List Byte)
    (h : hwLockFetch m c = some (.ok f len, rest))
    (hs : match lockFuss m c f with
      | some tgt => splitSperre tgt = false
      | none => True) :
    hwLockFetchSchritt m c = hwLockSchritt m c (.ok f len) := by
  unfold hwLockFetchSchritt
  cases hff : lockFuss m c f with
  | none =>
    simp only [h, hff]
  | some tgt =>
    have hs2 : splitSperre tgt = false := by
      simp only [hff] at hs
      exact hs
    simp only [h, hff, hs2]

/-- Every fetched successor preserves well-formedness: profiles are
    untouched (the 1119 re-embedding), so admission still has silicon
    behind it. -/
theorem adapterLockFetch_wf (m : HwMaschine) (c : Nat) (u : Unit)
    (m' : HwMaschine)
    (h : adapterLockFetch.schritt m c u = some m') (hwf : HwWf m) :
    HwWf m' := by
  have h2 : hwLockFetchSchritt m c = some m' := h
  cases hf : hwLockFetch m c with
  | none =>
    rw [hwLockFetchSchritt_ohne_fetch m c hf] at h2
    cases h2
  | some pr =>
    cases pr with
    | mk a rest =>
      cases a with
      | ud g len =>
        rw [hwLockFetchSchritt_ud m c g len rest hf] at h2
        cases h2
      | ok f len =>
        cases hff : lockFuss m c f with
        | none =>
          rw [hwLockFetchSchritt_ohne_split m c f len rest hf
            (by simp only [hff])] at h2
          exact adapterLockRmw_wf m c _ m' h2 hwf
        | some tgt =>
          by_cases hs : splitSperre tgt = true
          · rw [hwLockFetchSchritt_split m c f len rest hf tgt hff hs] at h2
            cases h2
          · rw [hwLockFetchSchritt_ohne_split m c f len rest hf
              (by simp only [hff]; simpa using hs)] at h2
            exact adapterLockRmw_wf m c _ m' h2 hwf

/- CUTS:
     Skeleton only: fetched decode `hwLockFetch` as the 662 fetch on
     the core projection. NOT proved here: the fetched step, split-lock
     refusal, narrower-width / other-mode refusals, agreement with the
     parsed plug, witness. See task lane 1209.
-/

#print axioms hwLockFetch_aus_projektion
