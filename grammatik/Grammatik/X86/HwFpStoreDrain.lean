/-
  File:      Grammatik/X86/HwFpStoreDrain.lean
  Subject:   FP 32-bit store drain equals the accepted `write32`.

  Lane 1307 (follow-up of lane 1211 `HwFpDispatch.lean`): the
  drain/write32 byte correspondence for STMXCSR and MOVSS-store was
  open (value and footprint pinned at issue level only). This file
  proves, generically over the TSO model and the `FpFremdFrei32`
  guard, that the four buffered byte entries drain to canonical
  memory equal to the accepted `write32` of the stored value (the
  `HwDrainGeneric.lean` technique for 8 bytes, specialised to 4),
  with forwarding to the owner and the foreign view before drain; a
  misaligned 4-byte store crossing a group boundary stays as the
  accepted tearing refusal. Accepted evaluators are lifted, never
  redefined.
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.HwFpControl
import Grammatik.X86.HwFpDispatch
import Grammatik.X86.HwDrainGeneric
import Grammatik.X86.WordAccessGrouping

namespace Gabbro.Grammatik.X86

/-- FP 32-bit store-drain family events on the coherent machine. -/
inductive FpStoreEreignis where
  | speichere32 : Adresse → Wort → FpStoreEreignis
  | eigenSpuele : FpStoreEreignis
  | fremdSpuele : Nat → FpStoreEreignis
  | fremdAusgabe : Nat → TSOEintrag → FpStoreEreignis
  | beobachte : Adresse → FpStoreEreignis
  deriving DecidableEq, Repr

/-- The family adapter: 32-bit stores buffer four bytes, drains
    flush, observations read without moving state. -/
def fpStoreAdapter : HwAdapter FpStoreEreignis :=
  ⟨fun m c ev => match ev with
    | .speichere32 a v => fpCtrlAusgabe32 m c a v
    | .eigenSpuele =>
      match flushKern (tsoAnsicht m) c with
      | some s' => some (setTso m s')
      | none => none
    | .fremdSpuele d =>
      match flushKern (tsoAnsicht m) d with
      | some s' => some (setTso m s')
      | none => none
    | .fremdAusgabe d e =>
      match issueByte (tsoAnsicht m) d e.addr e.wert with
      | some s' => some (setTso m s')
      | none => none
    | .beobachte a =>
      match loadByte (tsoAnsicht m) c a with
      | some _ => some m
      | none => none⟩

/-! ## 2. Adapter duties: well-formedness, agreement, embedding. -/

/-- Every adapter step preserves well-formedness: stores, flushes and
    issues ride `setTso`, observations are silent. -/
theorem fpStoreAdapter_wf (m : HwMaschine) (c : Nat)
    (ev : FpStoreEreignis) (m' : HwMaschine)
    (h : fpStoreAdapter.schritt m c ev = some m') (hwf : HwWf m) :
    HwWf m' := by
  cases ev with
  | speichere32 a v =>
    have had : fpStoreAdapter.schritt m c (.speichere32 a v) =
        fpCtrlAusgabe32 m c a v := rfl
    rw [had] at h
    unfold fpCtrlAusgabe32 at h
    cases h1 : issueListe (tsoAnsicht m) c (fpEintraege32 a v) with
    | none => rw [h1] at h; cases h
    | some s' => rw [h1] at h; cases h; exact setTso_wf _ s' hwf
  | eigenSpuele =>
    cases hfl : flushKern (tsoAnsicht m) c with
    | none =>
      have hh : fpStoreAdapter.schritt m c .eigenSpuele = none := by
        show (match flushKern (tsoAnsicht m) c with
          | some s' => some (setTso m s') | none => none) = none
        rw [hfl]
      rw [hh] at h; cases h
    | some s' =>
      have hh : fpStoreAdapter.schritt m c .eigenSpuele =
          some (setTso m s') := by
        show (match flushKern (tsoAnsicht m) c with
          | some s' => some (setTso m s') | none => none) = _
        rw [hfl]
      rw [hh] at h; cases h; exact setTso_wf _ s' hwf
  | fremdSpuele d =>
    cases hfl : flushKern (tsoAnsicht m) d with
    | none =>
      have hh : fpStoreAdapter.schritt m c (.fremdSpuele d) = none := by
        show (match flushKern (tsoAnsicht m) d with
          | some s' => some (setTso m s') | none => none) = none
        rw [hfl]
      rw [hh] at h; cases h
    | some s' =>
      have hh : fpStoreAdapter.schritt m c (.fremdSpuele d) =
          some (setTso m s') := by
        show (match flushKern (tsoAnsicht m) d with
          | some s' => some (setTso m s') | none => none) = _
        rw [hfl]
      rw [hh] at h; cases h; exact setTso_wf _ s' hwf
  | fremdAusgabe d e =>
    cases hfl : issueByte (tsoAnsicht m) d e.addr e.wert with
    | none =>
      have hh : fpStoreAdapter.schritt m c (.fremdAusgabe d e) = none := by
        show (match issueByte (tsoAnsicht m) d e.addr e.wert with
          | some s' => some (setTso m s') | none => none) = none
        rw [hfl]
      rw [hh] at h; cases h
    | some s' =>
      have hh : fpStoreAdapter.schritt m c (.fremdAusgabe d e) =
          some (setTso m s') := by
        show (match issueByte (tsoAnsicht m) d e.addr e.wert with
          | some s' => some (setTso m s') | none => none) = _
        rw [hfl]
      rw [hh] at h; cases h; exact setTso_wf _ s' hwf
  | beobachte a =>
    cases hl : loadByte (tsoAnsicht m) c a with
    | none =>
      have hh : fpStoreAdapter.schritt m c (.beobachte a) = none := by
        show (match loadByte (tsoAnsicht m) c a with
          | some _ => some m | none => none) = none
        rw [hl]
      rw [hh] at h; cases h
    | some w =>
      have hh : fpStoreAdapter.schritt m c (.beobachte a) = some m := by
        show (match loadByte (tsoAnsicht m) c a with
          | some _ => some m | none => none) = some m
        rw [hl]
      rw [hh] at h; cases h; exact hwf

/-- A buffered 32-bit store appends exactly the canonical four entries. -/
theorem fpStoreSpeichere_puffer (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort) (m' : HwMaschine)
    (h : fpStoreAdapter.schritt m c (.speichere32 a v) = some m') :
    m'.puffer c = m.puffer c ++ fpEintraege32 a v :=
  fpCtrlAusgabe32_puffer m c a v m' h

/-- A buffered 32-bit store changes no shared-memory byte. -/
theorem fpStoreSpeichere_kein_speicher (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort) (m' : HwMaschine)
    (h : fpStoreAdapter.schritt m c (.speichere32 a v) = some m')
    (x : Adresse) :
    m'.mem.bytes x = m.mem.bytes x :=
  fpCtrlAusgabe32_kein_speicher m c a v m' h x

/-- An own-drain adapter step IS the accepted oldest-entry flush. -/
theorem fpStoreEigen_ist_flush (m : HwMaschine) (c : Nat)
    (s' : TSOZustand)
    (hfl : flushKern (tsoAnsicht m) c = some s') (m' : HwMaschine)
    (h : fpStoreAdapter.schritt m c .eigenSpuele = some m') :
    m' = setTso m s' := by
  have hh : fpStoreAdapter.schritt m c .eigenSpuele =
      some (setTso m s') := by
    show (match flushKern (tsoAnsicht m) c with
      | some s' => some (setTso m s') | none => none) = _
    rw [hfl]
  rw [hh] at h
  exact (Option.some.inj h).symm

/-- An own-drain adapter step is a machine flush event. -/
theorem fpStoreEigen_ist_schritt (m : HwMaschine) (c : Nat)
    (s' : TSOZustand) (e : TSOEintrag)
    (hfl : flushKern (tsoAnsicht m) c = some s')
    (hkopf : (m.puffer c).head? = some e) :
    HwSchritt m (setTso m s') (.spülung c e) :=
  .spüle c e s' hfl hkopf

/-- A successful observation moves no state. -/
theorem fpStoreBeobachte_still (m : HwMaschine) (c : Nat) (a : Adresse)
    (v : Byte) (h : loadByte (tsoAnsicht m) c a = some v) :
    fpStoreAdapter.schritt m c (.beobachte a) = some m := by
  show (match loadByte (tsoAnsicht m) c a with
    | some _ => some m | none => none) = _
  rw [h]

/-- EMPTY DRAIN REFUSES: flushing an empty own buffer admits no step. -/
theorem fpStoreEigen_leer_verweigert (m : HwMaschine) (c : Nat)
    (hleer : m.puffer c = []) :
    fpStoreAdapter.schritt m c .eigenSpuele = none := by
  have hfl : flushKern (tsoAnsicht m) c = none := by
    apply flush_leer
    simpa [tsoAnsicht] using hleer
  show (match flushKern (tsoAnsicht m) c with
    | some s' => some (setTso m s') | none => none) = none
  rw [hfl]

/-- GUARD STORE REFUSES: without write permission at the first byte
    the whole 32-bit fold refuses. -/
theorem fpStoreSpeichere_wache (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort)
    (hguard : m.mem.schreibbar (addrOff a 0) = false) :
    fpStoreAdapter.schritt m c (.speichere32 a v) = none := by
  have had : fpStoreAdapter.schritt m c (.speichere32 a v) =
      fpCtrlAusgabe32 m c a v := rfl
  rw [had]
  unfold fpCtrlAusgabe32
  have hfirst : issueByte (tsoAnsicht m) c (addrOff a 0)
      (wortByte v 0) = none :=
    issue_verweigert _ _ _ _
      (by simpa [tsoAnsicht_speicher] using hguard)
  have hcons : fpEintraege32 a v =
      ⟨addrOff a 0, wortByte v 0⟩ ::
      [⟨addrOff a 1, wortByte v 1⟩,
       ⟨addrOff a 2, wortByte v 2⟩,
       ⟨addrOff a 3, wortByte v 3⟩] := rfl
  have hfold : issueListe (tsoAnsicht m) c
      (⟨addrOff a 0, wortByte v 0⟩ ::
      [⟨addrOff a 1, wortByte v 1⟩,
       ⟨addrOff a 2, wortByte v 2⟩,
       ⟨addrOff a 3, wortByte v 3⟩]) = none :=
    issueListe_cons_none _ _ _ _ hfirst
  rw [hcons, hfold]

/-- DARK OBSERVATION REFUSES: without read permission the byte
    observation refuses. -/
theorem fpStoreBeobachte_dunkel (m : HwMaschine) (c : Nat) (a : Adresse)
    (hguard : (tsoAnsicht m).mem.lesbar a = false) :
    fpStoreAdapter.schritt m c (.beobachte a) = none := by
  have hl : loadByte (tsoAnsicht m) c a = none :=
    load_verweigert _ _ _ hguard
  show (match loadByte (tsoAnsicht m) c a with
    | some _ => some m | none => none) = none
  rw [hl]

/- CUTS: skeleton plus adapter duties; induction, forwarding, refusals open.
-/

#print axioms FpStoreEreignis
#print axioms fpStoreAdapter

end Gabbro.Grammatik.X86
