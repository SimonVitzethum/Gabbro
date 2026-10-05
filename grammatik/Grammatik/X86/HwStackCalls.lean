/-
  File:      Grammatik/X86/HwStackCalls.lean
  Subject:   Stack, call and return per core through TSO on the coherent
             machine (lane 1139).

  Lifts the accepted `Stapel`/`StackUnwind`/`CallAlign16` word effects to
  buffered byte issues (`hwWortAusgabe`/`issueListe`) and the accepted
  `read64` loads to forwarding `loadByte` observations, on `HwMaschine`.
  Push/call store through the acting core's TSO buffer; pop/ret observe
  through loads with owner-only forwarding; alignment and spill privacy
  are stated premises. No model is redefined here.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Stapel
import Grammatik.X86.TSO
import Grammatik.X86.WordAccessGrouping
import Grammatik.X86.HardwareExecution
import Grammatik.X86.StackUnwind
import Grammatik.X86.CallAlign16
import Grammatik.X86.CodeImmutability

namespace Gabbro.Grammatik.X86

/-- Stack slot of core `c`: one word below its top. -/
def stapelSlot (m : HwMaschine) (c : Nat) : Adresse :=
  (m.kerne c).register Register.rsp - BitVec.ofNat 64 8

/-- Buffered push: the word as eight TSO byte issues at the slot. -/
def stapelPush (m : HwMaschine) (c : Nat) (v : Wort) : Option HwMaschine :=
  hwWortAusgabe m c (stapelSlot m c) v

/-- Buffered call spill: the return word as eight TSO byte issues. -/
def stapelCall (m : HwMaschine) (c : Nat) (ret : Wort) : Option HwMaschine :=
  hwWortAusgabe m c (stapelSlot m c) ret

/-! ## 1. Family events and the adapter.

  Push/call issue a buffered word at the acting core's slot; pop/ret
  observe the word at a named slot without moving state; a drain moves
  one oldest entry into shared memory. The checked call gate refuses a
  misaligned call site loudly (`none`). -/

/-- Stack/call/return family events on the coherent machine. -/
inductive StapelEreignis where
  | push : Wort → StapelEreignis
  | ruf : Wort → StapelEreignis
  | pop : Adresse → StapelEreignis
  | ret : Adresse → StapelEreignis
  deriving DecidableEq, Repr

/-- Word load with owner-only forwarding over the shared TSO view:
    the eight footprint bytes reassembled little-endian. `none` = at
    least one footprint byte unreadable. -/
def stapelLadeWort (s : TSOZustand) (c : Nat) (a : Adresse) : Option Wort :=
  match loadByte s c (addrOff a 0), loadByte s c (addrOff a 1),
    loadByte s c (addrOff a 2), loadByte s c (addrOff a 3),
    loadByte s c (addrOff a 4), loadByte s c (addrOff a 5),
    loadByte s c (addrOff a 6), loadByte s c (addrOff a 7) with
  | some b0, some b1, some b2, some b3,
    some b4, some b5, some b6, some b7 =>
      some (bytesWort (fun i => if i.val = 0 then b0 else if i.val = 1 then b1
        else if i.val = 2 then b2 else if i.val = 3 then b3
        else if i.val = 4 then b4 else if i.val = 5 then b5
        else if i.val = 6 then b6 else b7))
  | _, _, _, _, _, _, _, _ => none

/-- The family adapter: push/call buffer a word, pop/ret observe one
    (state unchanged), the misaligned call refuses. -/
def stapelAdapter : HwAdapter StapelEreignis :=
  ⟨fun m c ev => match ev with
    | .push v => stapelPush m c v
    | .ruf ret =>
      if rufAlignOk (projZustand m c) then stapelCall m c ret else none
    | .pop a =>
      match stapelLadeWort (tsoAnsicht m) c a with
      | some _ => some m
      | none => none
    | .ret a =>
      match stapelLadeWort (tsoAnsicht m) c a with
      | some _ => some m
      | none => none⟩

/-- A buffered word store preserves well-formedness. -/
theorem stapelPush_wf (m : HwMaschine) (c : Nat) (v : Wort)
    (m' : HwMaschine) (h : stapelPush m c v = some m')
    (hwf : HwWf m) : HwWf m' := by
  unfold stapelPush hwWortAusgabe at h
  cases h1 : issueListe (tsoAnsicht m) c (wortEintraege (stapelSlot m c) v) with
  | none => rw [h1] at h; cases h
  | some s' =>
    rw [h1] at h
    cases h
    exact setTso_wf _ s' hwf

/-- A buffered call spill preserves well-formedness. -/
theorem stapelCall_wf (m : HwMaschine) (c : Nat) (ret : Wort)
    (m' : HwMaschine) (h : stapelCall m c ret = some m')
    (hwf : HwWf m) : HwWf m' := by
  unfold stapelCall hwWortAusgabe at h
  cases h1 : issueListe (tsoAnsicht m) c
      (wortEintraege (stapelSlot m c) ret) with
  | none => rw [h1] at h; cases h
  | some s' =>
    rw [h1] at h
    cases h
    exact setTso_wf _ s' hwf

/-- Every adapter step preserves well-formedness. -/
theorem stapelAdapter_wf (m : HwMaschine) (c : Nat) (ev : StapelEreignis)
    (m' : HwMaschine) (h : stapelAdapter.schritt m c ev = some m')
    (hwf : HwWf m) : HwWf m' := by
  cases ev with
  | push v =>
    exact stapelPush_wf m c v m' h hwf
  | ruf ret =>
    by_cases ha : rufAlignOk (projZustand m c) = true
    · have hh : stapelAdapter.schritt m c (.ruf ret) =
          stapelCall m c ret := by
        show (if rufAlignOk (projZustand m c) then stapelCall m c ret
          else none) = _
        rw [if_pos ha]
      rw [hh] at h
      exact stapelCall_wf m c ret m' h hwf
    · have hh : stapelAdapter.schritt m c (.ruf ret) = none := by
        show (if rufAlignOk (projZustand m c) then stapelCall m c ret
          else none) = _
        rw [if_neg ha]
      rw [hh] at h
      cases h
  | pop a =>
    cases hl : stapelLadeWort (tsoAnsicht m) c a with
    | none =>
      have hh : stapelAdapter.schritt m c (.pop a) = none := by
        show (match stapelLadeWort (tsoAnsicht m) c a with
          | some _ => some m | none => none) = none
        rw [hl]
      rw [hh] at h
      cases h
    | some v =>
      have hh : stapelAdapter.schritt m c (.pop a) = some m := by
        show (match stapelLadeWort (tsoAnsicht m) c a with
          | some _ => some m | none => none) = some m
        rw [hl]
      rw [hh] at h
      cases h
      exact hwf
  | ret a =>
    cases hl : stapelLadeWort (tsoAnsicht m) c a with
    | none =>
      have hh : stapelAdapter.schritt m c (.ret a) = none := by
        show (match stapelLadeWort (tsoAnsicht m) c a with
          | some _ => some m | none => none) = none
        rw [hl]
      rw [hh] at h
      cases h
    | some v =>
      have hh : stapelAdapter.schritt m c (.ret a) = some m := by
        show (match stapelLadeWort (tsoAnsicht m) c a with
          | some _ => some m | none => none) = some m
        rw [hl]
      rw [hh] at h
      cases h
      exact hwf

/-! ## 2. Agreement with the accepted word effects.

  A buffered push/call appends exactly the canonical eight entries and
  leaves shared memory alone; the entries carry exactly the sequential
  `write64` footprint bytes; an unbuffered load is the accepted
  `read64`; every buffered byte issues and every observed byte loads
  through an exact `HwSchritt` event. -/

/-- A buffered push appends exactly the canonical word entries. -/
theorem stapelPush_puffer (m : HwMaschine) (c : Nat) (v : Wort)
    (m' : HwMaschine) (h : stapelPush m c v = some m') :
    m'.puffer c = m.puffer c ++ wortEintraege (stapelSlot m c) v :=
  hwWortAusgabe_puffer m c (stapelSlot m c) v m' h

/-- A buffered push changes no shared-memory byte. -/
theorem stapelPush_kein_speicher (m : HwMaschine) (c : Nat) (v : Wort)
    (m' : HwMaschine) (h : stapelPush m c v = some m') (x : Adresse) :
    m'.mem.bytes x = m.mem.bytes x :=
  hwWortAusgabe_kein_speicher m c (stapelSlot m c) v m' h x

/-- A buffered call spill appends exactly the canonical word entries. -/
theorem stapelCall_puffer (m : HwMaschine) (c : Nat) (ret : Wort)
    (m' : HwMaschine) (h : stapelCall m c ret = some m') :
    m'.puffer c = m.puffer c ++ wortEintraege (stapelSlot m c) ret :=
  hwWortAusgabe_puffer m c (stapelSlot m c) ret m' h

/-- A buffered call spill changes no shared-memory byte. -/
theorem stapelCall_kein_speicher (m : HwMaschine) (c : Nat) (ret : Wort)
    (m' : HwMaschine) (h : stapelCall m c ret = some m') (x : Adresse) :
    m'.mem.bytes x = m.mem.bytes x :=
  hwWortAusgabe_kein_speicher m c (stapelSlot m c) ret m' h x

/-- BYTE ECHO: every canonical entry carries its sequential store byte:
    the buffered word and the `write64` footprint agree byte for byte.
    The old evaluator's store is lifted, never redefined. -/
theorem stapelEcho_schreiben (m : Speicher) (a : Adresse) (v : Wort)
    (k : Nat) (hk : k < 8) :
    writeBytes m a v (addrOff a k) = wortByte v k :=
  writeBytesN_hit m a v 8 k hk (Nat.le_refl 8)

/-- Every canonical entry sits at its footprint address with its word
    byte: the issued list is exactly the eight addressed bytes. -/
theorem wortEintraege_mem (a : Adresse) (v : Wort) (e : TSOEintrag)
    (h : e ∈ wortEintraege a v) :
    ∃ k, k < 8 ∧ e = ⟨addrOff a k, wortByte v k⟩ := by
  simp only [wortEintraege, List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hbot
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨2, by decide, rfl⟩
  · exact ⟨3, by decide, rfl⟩
  · exact ⟨4, by decide, rfl⟩
  · exact ⟨5, by decide, rfl⟩
  · exact ⟨6, by decide, rfl⟩
  · exact ⟨7, by decide, rfl⟩
  · cases hbot

/-- UNBUFFERED LOAD IS THE ACCEPTED LOAD: with no pending entry at any
    footprint byte, the forwarding load is exactly `read64`. Every
    premise is used: each readability premise feeds one byte load, each
    no-entry premise feeds the same byte. -/
theorem stapelLadeWort_still (s : TSOZustand) (c : Nat) (a : Adresse)
    (hn0 : neuestens (s.puffer c) (addrOff a 0) = none)
    (hn1 : neuestens (s.puffer c) (addrOff a 1) = none)
    (hn2 : neuestens (s.puffer c) (addrOff a 2) = none)
    (hn3 : neuestens (s.puffer c) (addrOff a 3) = none)
    (hn4 : neuestens (s.puffer c) (addrOff a 4) = none)
    (hn5 : neuestens (s.puffer c) (addrOff a 5) = none)
    (hn6 : neuestens (s.puffer c) (addrOff a 6) = none)
    (hn7 : neuestens (s.puffer c) (addrOff a 7) = none)
    (hles : ∀ k, k < 8 → s.mem.lesbar (addrOff a k) = true) :
    stapelLadeWort s c a = read64 s.mem a := by
  have hles8 : lesbar8 s.mem a = true := by
    have h0 := hles 0 (by decide)
    have h1 := hles 1 (by decide)
    have h2 := hles 2 (by decide)
    have h3 := hles 3 (by decide)
    have h4 := hles 4 (by decide)
    have h5 := hles 5 (by decide)
    have h6 := hles 6 (by decide)
    have h7 := hles 7 (by decide)
    simp [lesbar8, h0, h1, h2, h3, h4, h5, h6, h7]
  unfold stapelLadeWort
  rw [load_ohne_eintrag s c _ hn0 (hles 0 (by decide)),
    load_ohne_eintrag s c _ hn1 (hles 1 (by decide)),
    load_ohne_eintrag s c _ hn2 (hles 2 (by decide)),
    load_ohne_eintrag s c _ hn3 (hles 3 (by decide)),
    load_ohne_eintrag s c _ hn4 (hles 4 (by decide)),
    load_ohne_eintrag s c _ hn5 (hles 5 (by decide)),
    load_ohne_eintrag s c _ hn6 (hles 6 (by decide)),
    load_ohne_eintrag s c _ hn7 (hles 7 (by decide))]
  show some (bytesWort (fun i : Fin 8 => if i.val = 0
    then s.mem.bytes (addrOff a 0) else if i.val = 1
    then s.mem.bytes (addrOff a 1) else if i.val = 2
    then s.mem.bytes (addrOff a 2) else if i.val = 3
    then s.mem.bytes (addrOff a 3) else if i.val = 4
    then s.mem.bytes (addrOff a 4) else if i.val = 5
    then s.mem.bytes (addrOff a 5) else if i.val = 6
    then s.mem.bytes (addrOff a 6) else s.mem.bytes (addrOff a 7))) =
    read64 s.mem a
  unfold read64
  rw [if_pos hles8]
  simp only [bytesWort, readBytes]
  have r0 : ((0 : Fin 8).val) = 0 := rfl
  have r1 : ((1 : Fin 8).val) = 1 := rfl
  have r2 : ((2 : Fin 8).val) = 2 := rfl
  have r3 : ((3 : Fin 8).val) = 3 := rfl
  have r4 : ((4 : Fin 8).val) = 4 := rfl
  have r5 : ((5 : Fin 8).val) = 5 := rfl
  have r6 : ((6 : Fin 8).val) = 6 := rfl
  have r7 : ((7 : Fin 8).val) = 7 := rfl
  rw [r0, r1, r2, r3, r4, r5, r6, r7]
  simp

end Gabbro.Grammatik.X86
