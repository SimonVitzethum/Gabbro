/-
  File:      Grammatik/X86/HwDrainGeneric.lean
  Subject:   Generic drain-equals-write64 induction on the coherent machine
             (lane 1207, follow-up of lane 1185 `HwForwardingGeneric`).

  Lifts the accepted word drain (`DrainSpur`, `WortGruppe`, `FremdFrei`,
  `flushKern`, `wortEintraege`) to a generic induction: draining the
  eight buffered entries of a word store, in any interleaving with
  foreign flushes/issues satisfying `FremdFrei`, installs exactly the
  `write64` footprint bytes, with the visited states exactly the stated
  prefixes. A foreign overlapping flush breaks it (counter-witness).
  No model is redefined here.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.TSO
import Grammatik.X86.WordAccessGrouping
import Grammatik.X86.HwStackCalls
import Grammatik.X86.HardwareExecution

namespace Gabbro.Grammatik.X86

/-! ## 1. Family events and the adapter. -/

/-- Generic drain family events on the coherent machine. -/
inductive DrainEreignis where
  | speichere : Adresse → Wort → DrainEreignis
  | eigenSpuele : DrainEreignis
  | fremdSpuele : Nat → DrainEreignis
  | fremdAusgabe : Nat → TSOEintrag → DrainEreignis
  | beobachte : Adresse → DrainEreignis
  deriving DecidableEq, Repr

/-- The family adapter: word stores buffer, drains flush, observations
    read without moving state. -/
def drainAdapter : HwAdapter DrainEreignis :=
  ⟨fun m c ev => match ev with
    | .speichere a v => hwWortAusgabe m c a v
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
      match stapelLadeWort (tsoAnsicht m) c a with
      | some _ => some m
      | none => none⟩

/-! ## 2. Adapter duties: well-formedness, agreement, embedding. -/

/-- Every adapter step preserves well-formedness: stores, flushes and
    issues ride `setTso`, observations are silent. -/
theorem drainAdapter_wf (m : HwMaschine) (c : Nat) (ev : DrainEreignis)
    (m' : HwMaschine) (h : drainAdapter.schritt m c ev = some m')
    (hwf : HwWf m) : HwWf m' := by
  cases ev with
  | speichere a v =>
    have had : drainAdapter.schritt m c (.speichere a v) =
        hwWortAusgabe m c a v := rfl
    rw [had] at h
    unfold hwWortAusgabe at h
    cases h1 : issueListe (tsoAnsicht m) c (wortEintraege a v) with
    | none => rw [h1] at h; cases h
    | some s' => rw [h1] at h; cases h; exact setTso_wf _ s' hwf
  | eigenSpuele =>
    cases hfl : flushKern (tsoAnsicht m) c with
    | none =>
      have hh : drainAdapter.schritt m c .eigenSpuele = none := by
        show (match flushKern (tsoAnsicht m) c with
          | some s' => some (setTso m s') | none => none) = none
        rw [hfl]
      rw [hh] at h; cases h
    | some s' =>
      have hh : drainAdapter.schritt m c .eigenSpuele =
          some (setTso m s') := by
        show (match flushKern (tsoAnsicht m) c with
          | some s' => some (setTso m s') | none => none) = _
        rw [hfl]
      rw [hh] at h; cases h; exact setTso_wf _ s' hwf
  | fremdSpuele d =>
    cases hfl : flushKern (tsoAnsicht m) d with
    | none =>
      have hh : drainAdapter.schritt m c (.fremdSpuele d) = none := by
        show (match flushKern (tsoAnsicht m) d with
          | some s' => some (setTso m s') | none => none) = none
        rw [hfl]
      rw [hh] at h; cases h
    | some s' =>
      have hh : drainAdapter.schritt m c (.fremdSpuele d) =
          some (setTso m s') := by
        show (match flushKern (tsoAnsicht m) d with
          | some s' => some (setTso m s') | none => none) = _
        rw [hfl]
      rw [hh] at h; cases h; exact setTso_wf _ s' hwf
  | fremdAusgabe d e =>
    cases hfl : issueByte (tsoAnsicht m) d e.addr e.wert with
    | none =>
      have hh : drainAdapter.schritt m c (.fremdAusgabe d e) = none := by
        show (match issueByte (tsoAnsicht m) d e.addr e.wert with
          | some s' => some (setTso m s') | none => none) = none
        rw [hfl]
      rw [hh] at h; cases h
    | some s' =>
      have hh : drainAdapter.schritt m c (.fremdAusgabe d e) =
          some (setTso m s') := by
        show (match issueByte (tsoAnsicht m) d e.addr e.wert with
          | some s' => some (setTso m s') | none => none) = _
        rw [hfl]
      rw [hh] at h; cases h; exact setTso_wf _ s' hwf
  | beobachte a =>
    cases hl : stapelLadeWort (tsoAnsicht m) c a with
    | none =>
      have hh : drainAdapter.schritt m c (.beobachte a) = none := by
        show (match stapelLadeWort (tsoAnsicht m) c a with
          | some _ => some m | none => none) = none
        rw [hl]
      rw [hh] at h; cases h
    | some w =>
      have hh : drainAdapter.schritt m c (.beobachte a) = some m := by
        show (match stapelLadeWort (tsoAnsicht m) c a with
          | some _ => some m | none => none) = some m
        rw [hl]
      rw [hh] at h; cases h; exact hwf

/-- A buffered word store appends exactly the canonical eight entries. -/
theorem drainSpeichere_puffer (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort) (m' : HwMaschine)
    (h : drainAdapter.schritt m c (.speichere a v) = some m') :
    m'.puffer c = m.puffer c ++ wortEintraege a v :=
  hwWortAusgabe_puffer m c a v m' h

/-- A buffered word store changes no shared-memory byte. -/
theorem drainSpeichere_kein_speicher (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort) (m' : HwMaschine)
    (h : drainAdapter.schritt m c (.speichere a v) = some m')
    (x : Adresse) :
    m'.mem.bytes x = m.mem.bytes x :=
  hwWortAusgabe_kein_speicher m c a v m' h x

/-- An own-drain adapter step IS the accepted oldest-entry flush. -/
theorem drainEigen_ist_flush (m : HwMaschine) (c : Nat)
    (s' : TSOZustand)
    (hfl : flushKern (tsoAnsicht m) c = some s') (m' : HwMaschine)
    (h : drainAdapter.schritt m c .eigenSpuele = some m') :
    m' = setTso m s' := by
  have hh : drainAdapter.schritt m c .eigenSpuele =
      some (setTso m s') := by
    show (match flushKern (tsoAnsicht m) c with
      | some s' => some (setTso m s') | none => none) = _
    rw [hfl]
  rw [hh] at h
  exact (Option.some.inj h).symm

/-- An own-drain adapter step is a machine flush event. -/
theorem drainEigen_ist_schritt (m : HwMaschine) (c : Nat)
    (s' : TSOZustand) (e : TSOEintrag)
    (hfl : flushKern (tsoAnsicht m) c = some s')
    (hkopf : (m.puffer c).head? = some e) :
    HwSchritt m (setTso m s') (.spülung c e) :=
  .spüle c e s' hfl hkopf

/-- A successful observation moves no state. -/
theorem drainBeobachte_still (m : HwMaschine) (c : Nat) (a : Adresse)
    (w : Wort) (h : stapelLadeWort (tsoAnsicht m) c a = some w) :
    drainAdapter.schritt m c (.beobachte a) = some m := by
  show (match stapelLadeWort (tsoAnsicht m) c a with
    | some _ => some m | none => none) = _
  rw [h]

/-- EMPTY DRAIN REFUSES: flushing an empty own buffer admits no step. -/
theorem drainEigen_leer_verweigert (m : HwMaschine) (c : Nat)
    (hleer : m.puffer c = []) :
    drainAdapter.schritt m c .eigenSpuele = none := by
  have hfl : flushKern (tsoAnsicht m) c = none := by
    apply flush_leer
    simpa [tsoAnsicht] using hleer
  show (match flushKern (tsoAnsicht m) c with
    | some s' => some (setTso m s') | none => none) = none
  rw [hfl]

/-- GUARD STORE REFUSES: without write permission at the first byte
    the whole word fold refuses. -/
theorem drainSpeichere_wache (m : HwMaschine) (c : Nat)
    (a : Adresse) (v : Wort)
    (hguard : m.mem.schreibbar (addrOff a 0) = false) :
    drainAdapter.schritt m c (.speichere a v) = none := by
  have had : drainAdapter.schritt m c (.speichere a v) =
      hwWortAusgabe m c a v := rfl
  rw [had]
  unfold hwWortAusgabe
  have hfirst : issueByte (tsoAnsicht m) c (addrOff a 0)
      (wortByte v 0) = none :=
    issue_verweigert _ _ _ _
      (by simpa [addrOff_null, tsoAnsicht_speicher] using hguard)
  have hcons : wortEintraege a v =
      ⟨addrOff a 0, wortByte v 0⟩ ::
      [⟨addrOff a 1, wortByte v 1⟩,
       ⟨addrOff a 2, wortByte v 2⟩,
       ⟨addrOff a 3, wortByte v 3⟩,
       ⟨addrOff a 4, wortByte v 4⟩,
       ⟨addrOff a 5, wortByte v 5⟩,
       ⟨addrOff a 6, wortByte v 6⟩,
       ⟨addrOff a 7, wortByte v 7⟩] := rfl
  have hfold : issueListe (tsoAnsicht m) c
      (⟨addrOff a 0, wortByte v 0⟩ ::
      [⟨addrOff a 1, wortByte v 1⟩,
       ⟨addrOff a 2, wortByte v 2⟩,
       ⟨addrOff a 3, wortByte v 3⟩,
       ⟨addrOff a 4, wortByte v 4⟩,
       ⟨addrOff a 5, wortByte v 5⟩,
       ⟨addrOff a 6, wortByte v 6⟩,
       ⟨addrOff a 7, wortByte v 7⟩]) = none :=
    issueListe_cons_none _ _ _ _ hfirst
  rw [hcons, hfold]

/-- DARK OBSERVATION REFUSES: without read permission at the first
    byte the whole word observation refuses. -/
theorem drainBeobachte_dunkel (s : TSOZustand) (c : Nat) (a : Adresse)
    (hguard : s.mem.lesbar (addrOff a 0) = false) :
    stapelLadeWort s c a = none :=
  stapelPop_unlesbar s c a hguard

/- CUTS:
   Skeleton only: adapter defined, induction and witnesses open.
-/

#print axioms drainAdapter

end Gabbro.Grammatik.X86
