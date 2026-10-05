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

/-! ## 3. Exact byte embedding into `HwSchritt`.

  Every buffered byte is one `gibAus` event, every observed byte one
  `lade` event: the family rides the coherent machine step for step,
  never beside it. -/

/-- A buffered stack byte IS a machine store-issue event. -/
theorem stapelByte_ausgabe (m : HwMaschine) (c : Nat) (a : Adresse)
    (b : Byte) (s' : TSOZustand)
    (h : issueByte (tsoAnsicht m) c a b = some s') :
    HwSchritt m (setTso m s') (.schreibAusgabe c a b) :=
  .gibAus c a b s' h

/-- An observed stack byte IS a machine load event. -/
theorem stapelByte_beob (m : HwMaschine) (c : Nat) (a : Adresse)
    (b : Byte) (h : loadByte (tsoAnsicht m) c a = some b) :
    HwSchritt m m (.leseBeob c a b) :=
  .lade c a b h

/-- Machine-step reachability: the reflexive-transitive closure of
    `HwSchritt` over a silent event trace. -/
inductive HwStern : HwMaschine → HwMaschine → Prop where
  | refl (m : HwMaschine) : HwStern m m
  | step (m m1 m2 : HwMaschine) (e : HwEreignis) :
      HwSchritt m m1 e → HwStern m1 m2 → HwStern m m2

/-- A folded word issue is a chain of machine store-issue steps: the
    buffered word reaches the machine in eight `HwSchritt` events. -/
theorem issueListe_stern (m : HwMaschine) (c : Nat) (l : List TSOEintrag)
    (s s' : TSOZustand) (h : issueListe s c l = some s') :
    HwStern (setTso m s) (setTso m s') := by
  induction l generalizing s with
  | nil =>
    simp only [issueListe] at h
    cases h
    exact .refl _
  | cons e rest ih =>
    unfold issueListe at h
    cases h1 : issueByte s c e.addr e.wert with
    | none =>
      rw [h1] at h
      cases h
    | some s1 =>
      rw [h1] at h
      have ihh := ih s1 h
      have hstep : HwSchritt (setTso m s) (setTso m s1)
          (.schreibAusgabe c e.addr e.wert) := by
        apply HwSchritt.gibAus c e.addr e.wert s1
        rw [setTso_ansicht]
        exact h1
      exact .step _ _ _ _ hstep ihh

/-- A buffered push reaches the machine in eight store-issue steps. -/
theorem stapelPush_stern (m : HwMaschine) (c : Nat) (v : Wort)
    (m' : HwMaschine) (h : stapelPush m c v = some m') :
    HwStern m m' := by
  unfold stapelPush hwWortAusgabe at h
  cases h1 : issueListe (tsoAnsicht m) c
      (wortEintraege (stapelSlot m c) v) with
  | none =>
    rw [h1] at h
    cases h
  | some s' =>
    rw [h1] at h
    cases h
    have hs := issueListe_stern m c (wortEintraege (stapelSlot m c) v)
      (tsoAnsicht m) s' h1
    have hrefl : setTso m (tsoAnsicht m) = m := by
      cases m with
      | mk mem kerne puffer hw bereit => rfl
    rw [hrefl] at hs
    exact hs

/-- A buffered call spill reaches the machine in eight steps. -/
theorem stapelCall_stern (m : HwMaschine) (c : Nat) (ret : Wort)
    (m' : HwMaschine) (h : stapelCall m c ret = some m') :
    HwStern m m' := by
  unfold stapelCall hwWortAusgabe at h
  cases h1 : issueListe (tsoAnsicht m) c
      (wortEintraege (stapelSlot m c) ret) with
  | none =>
    rw [h1] at h
    cases h
  | some s' =>
    rw [h1] at h
    cases h
    have hs := issueListe_stern m c (wortEintraege (stapelSlot m c) ret)
      (tsoAnsicht m) s' h1
    have hrefl : setTso m (tsoAnsicht m) = m := by
      cases m with
      | mk mem kerne puffer hw bereit => rfl
    rw [hrefl] at hs
    exact hs

/-! ## 4. Duties and refusals.

  The call gate is the accepted alignment duty as a stated premise: an
  aligned site buffers the return word, a misaligned site refuses
  loudly. The spill-privacy duty keeps the sequential fetch: a slot
  spill foreign to the code window preserves the fetched bytes through
  the accepted preservation lemma. A guard slot refuses the issue, an
  unreadable slot refuses the observation. -/

/-- ALIGNED CALL PASSES: at an aligned call site the adapter buffers
    the return word. The alignment premise discharges the gate. -/
theorem stapelRuf_ausgerichtet (m : HwMaschine) (c : Nat) (ret : Wort)
    (hali : rufAlignOk (projZustand m c) = true) :
    stapelAdapter.schritt m c (.ruf ret) = stapelCall m c ret := by
  show (if rufAlignOk (projZustand m c) then stapelCall m c ret
    else none) = _
  rw [if_pos hali]

/-- MISALIGNED CALL REFUSES: at a misaligned call site the adapter
    loudly refuses instead of spilling. The misalignment feeds the
    gate directly. -/
theorem stapelRuf_fehlalign (m : HwMaschine) (c : Nat) (ret : Wort)
    (hmis : rufAlignOk (projZustand m c) = false) :
    stapelAdapter.schritt m c (.ruf ret) = none := by
  show (if rufAlignOk (projZustand m c) then stapelCall m c ret
    else none) = _
  simp [hmis]

/-- A successful pop observation moves no state. -/
theorem stapelAdapter_pop_still (m : HwMaschine) (c : Nat) (a : Adresse)
    (v : Wort) (h : stapelLadeWort (tsoAnsicht m) c a = some v) :
    stapelAdapter.schritt m c (.pop a) = some m := by
  show (match stapelLadeWort (tsoAnsicht m) c a with
    | some _ => some m | none => none) = _
  rw [h]

/-- A successful return observation moves no state. -/
theorem stapelAdapter_ret_still (m : HwMaschine) (c : Nat) (a : Adresse)
    (v : Wort) (h : stapelLadeWort (tsoAnsicht m) c a = some v) :
    stapelAdapter.schritt m c (.ret a) = some m := by
  show (match stapelLadeWort (tsoAnsicht m) c a with
    | some _ => some m | none => none) = _
  rw [h]

/-- SPILL PRIVACY KEEPS THE FETCH: the sequential shadow of a slot
    store foreign to the code window preserves the fetched bytes, by
    the accepted preservation lemma. The privacy premise is the
    disjointness the lemma consumes. -/
theorem stapelSpill_fetch_bleibt (s : Zustand) (a : Adresse) (v : Wort)
    (m' : Speicher) (hwr : write64 s.speicher a v = some m')
    (hpriv : CodeFremd s a) :
    geholt { s with speicher := m' } = geholt s :=
  geholt_nach_fremd_schreiben s m' a v hwr hpriv

/-- A refused first byte refuses the whole word fold. -/
theorem issueListe_cons_none (s : TSOZustand) (c : Nat) (e : TSOEintrag)
    (rest : List TSOEintrag)
    (h : issueByte s c e.addr e.wert = none) :
    issueListe s c (e :: rest) = none := by
  unfold issueListe
  rw [h]

/-- GUARD PUSH REFUSES: a slot whose first byte is not writable admits
    no buffered push. The denial fails the very first byte issue, so
    the whole word fold refuses. -/
theorem stapelPush_wache (m : HwMaschine) (c : Nat) (v : Wort)
    (hguard : m.mem.schreibbar (stapelSlot m c) = false) :
    stapelPush m c v = none := by
  unfold stapelPush hwWortAusgabe
  have hfirst : issueByte (tsoAnsicht m) c (addrOff (stapelSlot m c) 0)
      (wortByte v 0) = none :=
    issue_verweigert _ _ _ _ (by rw [addrOff_null]; exact hguard)
  have hcons : wortEintraege (stapelSlot m c) v =
      ⟨addrOff (stapelSlot m c) 0, wortByte v 0⟩ ::
      [⟨addrOff (stapelSlot m c) 1, wortByte v 1⟩,
       ⟨addrOff (stapelSlot m c) 2, wortByte v 2⟩,
       ⟨addrOff (stapelSlot m c) 3, wortByte v 3⟩,
       ⟨addrOff (stapelSlot m c) 4, wortByte v 4⟩,
       ⟨addrOff (stapelSlot m c) 5, wortByte v 5⟩,
       ⟨addrOff (stapelSlot m c) 6, wortByte v 6⟩,
       ⟨addrOff (stapelSlot m c) 7, wortByte v 7⟩] := rfl
  have hfold : issueListe (tsoAnsicht m) c
      (⟨addrOff (stapelSlot m c) 0, wortByte v 0⟩ ::
      [⟨addrOff (stapelSlot m c) 1, wortByte v 1⟩,
       ⟨addrOff (stapelSlot m c) 2, wortByte v 2⟩,
       ⟨addrOff (stapelSlot m c) 3, wortByte v 3⟩,
       ⟨addrOff (stapelSlot m c) 4, wortByte v 4⟩,
       ⟨addrOff (stapelSlot m c) 5, wortByte v 5⟩,
       ⟨addrOff (stapelSlot m c) 6, wortByte v 6⟩,
       ⟨addrOff (stapelSlot m c) 7, wortByte v 7⟩]) = none :=
    issueListe_cons_none _ _ _ _ hfirst
  rw [hcons, hfold]

/-- GUARD CALL REFUSES: a slot whose first byte is not writable admits
    no buffered call spill, for the same first-byte reason. -/
theorem stapelCall_wache (m : HwMaschine) (c : Nat) (ret : Wort)
    (hguard : m.mem.schreibbar (stapelSlot m c) = false) :
    stapelCall m c ret = none := by
  unfold stapelCall hwWortAusgabe
  have hfirst : issueByte (tsoAnsicht m) c (addrOff (stapelSlot m c) 0)
      (wortByte ret 0) = none :=
    issue_verweigert _ _ _ _ (by rw [addrOff_null]; exact hguard)
  have hcons : wortEintraege (stapelSlot m c) ret =
      ⟨addrOff (stapelSlot m c) 0, wortByte ret 0⟩ ::
      [⟨addrOff (stapelSlot m c) 1, wortByte ret 1⟩,
       ⟨addrOff (stapelSlot m c) 2, wortByte ret 2⟩,
       ⟨addrOff (stapelSlot m c) 3, wortByte ret 3⟩,
       ⟨addrOff (stapelSlot m c) 4, wortByte ret 4⟩,
       ⟨addrOff (stapelSlot m c) 5, wortByte ret 5⟩,
       ⟨addrOff (stapelSlot m c) 6, wortByte ret 6⟩,
       ⟨addrOff (stapelSlot m c) 7, wortByte ret 7⟩] := rfl
  have hfold : issueListe (tsoAnsicht m) c
      (⟨addrOff (stapelSlot m c) 0, wortByte ret 0⟩ ::
      [⟨addrOff (stapelSlot m c) 1, wortByte ret 1⟩,
       ⟨addrOff (stapelSlot m c) 2, wortByte ret 2⟩,
       ⟨addrOff (stapelSlot m c) 3, wortByte ret 3⟩,
       ⟨addrOff (stapelSlot m c) 4, wortByte ret 4⟩,
       ⟨addrOff (stapelSlot m c) 5, wortByte ret 5⟩,
       ⟨addrOff (stapelSlot m c) 6, wortByte ret 6⟩,
       ⟨addrOff (stapelSlot m c) 7, wortByte ret 7⟩]) = none :=
    issueListe_cons_none _ _ _ _ hfirst
  rw [hcons, hfold]

/-- UNREADABLE POP REFUSES: a slot whose first byte is not readable
    admits no pop observation. The denial fails the first byte load. -/
theorem stapelPop_unlesbar (s : TSOZustand) (c : Nat) (a : Adresse)
    (hguard : s.mem.lesbar (addrOff a 0) = false) :
    stapelLadeWort s c a = none := by
  unfold stapelLadeWort
  have hfirst : loadByte s c (addrOff a 0) = none :=
    load_verweigert s c (addrOff a 0) hguard
  rw [hfirst]

/-- UNREADABLE RETURN REFUSES: the same first-byte denial refuses the
    return observation. -/
theorem stapelRet_unlesbar (s : TSOZustand) (c : Nat) (a : Adresse)
    (hguard : s.mem.lesbar (addrOff a 0) = false) :
    stapelLadeWort s c a = none :=
  stapelPop_unlesbar s c a hguard

/-! ## 5. Joint witness: two cores, buffered push, forward, drain.

  Core 0 (aligned top at 8192, running at 4096) buffers word 42 at its
  slot 8184; core 0 forwards it while core 1 (misaligned top at 8184)
  still reads zero; after core 0 drains, shared memory holds 42 for
  both cores. The drain observably changes memory (0 becomes 42). -/

/-- Witness bytes: zeroed everywhere. -/
def witBytes (_ : Adresse) : Byte := BitVec.ofNat 8 0

/-- Witness data permission: sixteen stack bytes at 8176. -/
def witDaten (a : Adresse) : Bool :=
  decide (8176 ≤ a.toNat ∧ a.toNat < 8192)

/-- Witness code permission: fifteen bytes at 4096. -/
def witCode (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4111)

/-- Witness shared memory: zeroed bytes, stack RW, code X-only. -/
def witMem : Speicher :=
  { bytes := witBytes, lesbar := witDaten,
    schreibbar := witDaten, ausfuehrbar := witCode }

/-- Witness core-0 registers: aligned top at 8192, `rax` holding 9. -/
def witReg0 : Register → Wort := fun q =>
  if q = Register.rsp then BitVec.ofNat 64 8192
  else if q = Register.rax then BitVec.ofNat 64 9
  else BitVec.ofNat 64 0

/-- Witness core-1 registers: misaligned top at 8184. -/
def witReg1 : Register → Wort := fun q =>
  if q = Register.rsp then BitVec.ofNat 64 8184
  else BitVec.ofNat 64 0

/-- Witness core data: core 0 runs at 4096, core 1 idles at 8192. -/
def witKern : Nat → HwKern
  | 0 => ⟨witReg0, zeugeFlags, BitVec.ofNat 64 4096,
      (fun _ => BitVec.ofNat 128 0), kontextReset⟩
  | _ => ⟨witReg1, zeugeFlags, BitVec.ofNat 64 8192,
      (fun _ => BitVec.ofNat 128 0), kontextReset⟩

/-- Witness start machine: shared memory, two cores, empty buffers,
    full silicon with OS vector state. -/
def witM0 : HwMaschine :=
  ⟨witMem, witKern, fun _ => [], basisHw, fun _ => basisBereit⟩

/-- Witness slot address: one word below core 0's top. -/
def witSlotAddr : Adresse := BitVec.ofNat 64 8184

/-- Witness pushed word. -/
def witWort : Wort := BitVec.ofNat 64 42

/-- Witness zero word. -/
def witNull : Wort := BitVec.ofNat 64 0

/-- Core 0 buffers word 42 at its slot. -/
def witPush : Option HwMaschine := stapelPush witM0 0 witWort

/-- Buffered entry count on core 0 after the push. -/
def witBufLen : Option Nat :=
  match witPush with
  | some m1 => some (m1.puffer 0).length
  | none => none

/-- Shared-memory byte at the slot right after the push. -/
def witMemStill : Option Byte :=
  match witPush with
  | some m1 => some (m1.mem.bytes witSlotAddr)
  | none => none

/-- Core 0 observes its own buffered word (forwarding). -/
def witLoadEigen : Option (Option Wort) :=
  match witPush with
  | some m1 => some (stapelLadeWort (tsoAnsicht m1) 0 witSlotAddr)
  | none => none

/-- Core 1 observes the old word (no foreign forwarding). -/
def witLoadFremd : Option (Option Wort) :=
  match witPush with
  | some m1 => some (stapelLadeWort (tsoAnsicht m1) 1 witSlotAddr)
  | none => none

/-- Core 0 drains its oldest entry, eight times chained. -/
def witD1 : Option TSOZustand :=
  match witPush with
  | some m1 => flushKern (tsoAnsicht m1) 0
  | none => none

def witD2 : Option TSOZustand :=
  match witD1 with
  | some s => flushKern s 0
  | none => none

def witD3 : Option TSOZustand :=
  match witD2 with
  | some s => flushKern s 0
  | none => none

def witD4 : Option TSOZustand :=
  match witD3 with
  | some s => flushKern s 0
  | none => none

def witD5 : Option TSOZustand :=
  match witD4 with
  | some s => flushKern s 0
  | none => none

def witD6 : Option TSOZustand :=
  match witD5 with
  | some s => flushKern s 0
  | none => none

def witD7 : Option TSOZustand :=
  match witD6 with
  | some s => flushKern s 0
  | none => none

def witD8 : Option TSOZustand :=
  match witD7 with
  | some s => flushKern s 0
  | none => none

/-- Shared memory after the full drain. -/
def witNachFlush : Option Speicher :=
  match witD8 with
  | some s => some s.mem
  | none => none

/-- The word read from shared memory after the drain. -/
def witNachRead : Option (Option Wort) :=
  match witNachFlush with
  | some mem => some (read64 mem witSlotAddr)
  | none => none

/-- Core 1 reads the drained word from shared memory. -/
def witFremdNachFlush : Option (Option Wort) :=
  match witD8 with
  | some s => some (stapelLadeWort s 1 witSlotAddr)
  | none => none

/-- Guard witness memory: nothing is writable. -/
def witGuardMem : Speicher :=
  { bytes := witBytes, lesbar := witDaten,
    schreibbar := fun _ => false, ausfuehrbar := witCode }

/-- Guard witness machine: same cores, write-protected memory. -/
def witGuardM0 : HwMaschine :=
  ⟨witGuardMem, witKern, fun _ => [], basisHw, fun _ => basisBereit⟩

/-- Dark witness memory: nothing is readable. -/
def witDarkMem : Speicher :=
  { bytes := witBytes, lesbar := fun _ => false,
    schreibbar := witDaten, ausfuehrbar := witCode }

/-! ## 6. Witness facts and the joint `_zeuge`.

  Every duty premise holds on the witness: core 0 is aligned, core 1
  is misaligned, the slot spill is foreign to the code window, the
  guard denies the first slot byte, the dark page denies the read.
  The run is non-degenerate: two cores touch the slot, the drain
  observably changes shared memory from 0 to 42. -/

/-- The witness machine is well-formed: full silicon admits all. -/
theorem wit_wf : HwWf witM0 := by
  intro c f _
  cases f <;> rfl

/-- Core 0's slot is one word below its top: address 8184. -/
theorem wit_slot : stapelSlot witM0 0 = witSlotAddr := by
  decide

/-- Core 0 sits at an aligned call site. -/
theorem wit_align0 : rufAlignOk (projZustand witM0 0) = true := by
  decide

/-- Core 1 sits at a misaligned call site. -/
theorem wit_misalign1 : rufAlignOk (projZustand witM0 1) = false := by
  decide

/-- The slot spill is foreign to core 0's code window. -/
theorem wit_priv : CodeFremd (projZustand witM0 0) (stapelSlot witM0 0) := by
  rw [wit_slot]
  apply codeFremd_von_intervallen
  · decide
  · decide
  · exact Or.inl (by decide)

/-- The push buffers exactly eight entries on core 0. -/
theorem wit_puffer8 : witBufLen = some 8 := by
  decide

/-- The push leaves the shared slot byte at zero. -/
theorem wit_mem_still : witMemStill = some (BitVec.ofNat 8 0) := by
  decide

/-- Forwarding: core 0 reads its own unflushed word 42. -/
theorem wit_weiterleitung :
    witLoadEigen = some (some witWort) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem wit_fremd_alt :
    witLoadFremd = some (some witNull) := by
  decide

/-- The drain changes shared memory: the slot reads 42. -/
theorem wit_spuelung_aendert_speicher :
    witNachRead = some (some witWort) := by
  decide

/-- After the drain core 1 observes the new word. -/
theorem wit_fremd_neu :
    witFremdNachFlush = some (some witWort) := by
  decide

/-- The slot starts zeroed: the run really changes memory. -/
theorem wit_anfang_null :
    witMem.bytes witSlotAddr = BitVec.ofNat 8 0 := by
  decide

/-- Core 1's buffer holds no entry at the slot's first byte. -/
theorem wit_fremd_kein_eintrag :
    neuestens ((tsoAnsicht witM0).puffer 1) (addrOff witSlotAddr 0) =
      none := by
  decide

/-- The slot's first byte is readable on the witness. -/
theorem wit_slot_lesbar :
    (tsoAnsicht witM0).mem.lesbar (addrOff witSlotAddr 0) = true := by
  decide

/-- Every slot footprint byte is readable on the witness. -/
theorem wit_slot_lesbar_all (k : Nat) (hk : k < 8) :
    (tsoAnsicht witM0).mem.lesbar (addrOff witSlotAddr k) = true := by
  have haddr : (addrOff witSlotAddr k).toNat = 8184 + k := by
    unfold addrOff witSlotAddr
    rw [BitVec.toNat_add]
    have e1 : (BitVec.ofNat 64 8184).toNat = 8184 := by
      rw [BitVec.toNat_ofNat]
    have e2 : (BitVec.ofNat 64 k).toNat = k := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    rw [e1, e2]
    exact Nat.mod_eq_of_lt (by omega)
  show witDaten (addrOff witSlotAddr k) = true
  unfold witDaten
  rw [decide_eq_true_eq]
  omega

/-- Unbuffered foreign load is the accepted load on the witness. -/
theorem wit_still_beispiel :
    stapelLadeWort (tsoAnsicht witM0) 1 witSlotAddr =
      read64 (tsoAnsicht witM0).mem witSlotAddr :=
  stapelLadeWort_still _ _ _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    wit_slot_lesbar_all

/-- The guard denies the first slot byte. -/
theorem wit_guard_dicht :
    witGuardM0.mem.schreibbar (stapelSlot witGuardM0 0) = false := by
  decide

/-- Guard push refuses on the witness. -/
theorem wit_guard_push_verweigert :
    stapelPush witGuardM0 0 witWort = none := by
  decide

/-- The dark page denies the first slot byte. -/
theorem wit_dark_dicht :
    witDarkMem.lesbar (addrOff witSlotAddr 0) = false := by
  decide

/-- Dark pop refuses on the witness. -/
theorem wit_dark_pop_verweigert :
    stapelLadeWort ⟨witDarkMem, fun _ => []⟩ 0 witSlotAddr = none := by
  decide

/-- Misaligned call refuses on the witness. -/
theorem wit_ruf_fehlalign_verweigert :
    stapelAdapter.schritt witM0 1
      (.ruf (BitVec.ofNat 64 4101)) = none := by
  decide

/-- Aligned call buffers on the witness. -/
theorem wit_ruf_ausgerichtet_puffert :
    stapelAdapter.schritt witM0 0
      (.ruf (BitVec.ofNat 64 4101)) =
      stapelCall witM0 0 (BitVec.ofNat 64 4101) :=
  stapelRuf_ausgerichtet _ _ _ wit_align0

/-- JOINT WITNESS: every duty premise holds jointly on a reached,
    non-degenerate two-core run -- aligned push with owner-only
    forwarding, foreign zero, drain changing shared memory 0 to 42,
    foreign observation of the drained word -- beside the planted
    guard, dark-read and misaligned-call refusals. -/
theorem stapelTso_zeuge :
    HwWf witM0 ∧
      rufAlignOk (projZustand witM0 0) = true ∧
      rufAlignOk (projZustand witM0 1) = false ∧
      CodeFremd (projZustand witM0 0) (stapelSlot witM0 0) ∧
      witBufLen = some 8 ∧
      witMemStill = some (BitVec.ofNat 8 0) ∧
      witLoadEigen = some (some witWort) ∧
      witLoadFremd = some (some witNull) ∧
      witNachRead = some (some witWort) ∧
      witFremdNachFlush = some (some witWort) ∧
      witMem.bytes witSlotAddr = BitVec.ofNat 8 0 ∧
      witGuardM0.mem.schreibbar (stapelSlot witGuardM0 0) = false ∧
      stapelPush witGuardM0 0 witWort = none ∧
      witDarkMem.lesbar (addrOff witSlotAddr 0) = false ∧
      stapelLadeWort ⟨witDarkMem, fun _ => []⟩ 0 witSlotAddr = none ∧
      stapelAdapter.schritt witM0 1
        (.ruf (BitVec.ofNat 64 4101)) = none := by
  exact ⟨wit_wf, wit_align0, wit_misalign1, wit_priv, wit_puffer8,
    wit_mem_still, wit_weiterleitung, wit_fremd_alt,
    wit_spuelung_aendert_speicher, wit_fremd_neu, wit_anfang_null,
    wit_guard_dicht, wit_guard_push_verweigert, wit_dark_dicht,
    wit_dark_pop_verweigert, wit_ruf_fehlalign_verweigert⟩

end Gabbro.Grammatik.X86
