/-
  File:      Grammatik/X86/TsoGxStart.lean
  Subject:   Start-anchored bridged run for the GX refinement (lane 1253).

  Follow-up of the three bridged fragment kinds (`TsoRunInduction`:
  no-read store, committed read, forwarded read): those start their W
  run at a hand-built fragment machine, never at `RufStartG`, so they
  carry no joint start-anchored witness. This module proves the
  entry/call prefix from `RufStartG` reaches the fragment head on the
  accepted non-degenerate witness program (`eP`: `haupt` calls
  `setze`, which writes table `konto`), reusing the accepted
  entry/call step lemmas (`w_rufEnde`, `w_blatt`) and the accepted
  joint witness (`ziel_ort_einfaden_zeuge`). No new machine, no new
  executor, no silicon claim.
-/
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtEinfadenZeuge
import Grammatik.X86.Bruecke.TsoRunInduction

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The start anchor: the G start machine of the witness program. -/
def startAnker : RufMaschineG eD := RufStartG eP eSp eInit

/-- The start anchor reaches itself in zero steps. -/
theorem startAnker_refl : RufErreichbarG eP eO 0 startAnker startAnker :=
  .start

/-- The anchor unfolds to the accepted start machine. -/
theorem startAnker_gleich : startAnker = RufStartG eP eSp eInit := rfl

/-- Entry/call prefix step 1 (reused `w_rufEnde`): the call of `setze`
    from `haupt` fires on the start machine, reaching a machine whose
    head is the `setze` body. Entry world, arguments and ghost entry
    event are exactly the accepted ones; nothing is redefined. -/
theorem startCall_erreichbar :
    ∃ M1 : RufMaschineG eD,
      RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M1 := by
  have h00 : (RufStartG eP eSp eInit).faeden 0 = ⟨[], ⟨eHaupt, .nil, eSp.welt [],
      ⟨false, [], [], .nil, .ende eRumpfHaupt⟩⟩, [],
      [RufEreignisF.eintritt eHaupt .nil (eSp.welt [])]⟩ := rfl
  have hoff0 : offen ((RufStartG eP eSp eInit).faeden 0).spur = [] := rfl
  obtain ⟨M1, s1, hZ1⟩ := w_rufEnde (P := eP) (O := eO) (passes := 0) h00
    eSetze .nil eHpSetze rfl
    (.cons (.call ePruefe .nil eHpPruefe rfl) (.ret .keine List.Perm.nil))
    .nil rfl (ehg0 hoff0).heldIn
  exact ⟨M1, .schritt _ _ 0 .start s1⟩

/-- Fragment-head prefix (reused `w_blatt`): the `assignSlot` writing
    `konto[0] = 5` fires inside the entered `setze` frame, reaching a
    machine two steps from the start. The fragment head is therefore
    reached from `RufStartG` by entry/call prefix execution alone;
    the three bridged fragment kinds consume this head. -/
theorem fragmentKopf_erreichbar :
    ∃ M2 : RufMaschineG eD,
      RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M2 := by
  have h00 : (RufStartG eP eSp eInit).faeden 0 = ⟨[], ⟨eHaupt, .nil, eSp.welt [],
      ⟨false, [], [], .nil, .ende eRumpfHaupt⟩⟩, [],
      [RufEreignisF.eintritt eHaupt .nil (eSp.welt [])]⟩ := rfl
  have hoff0 : offen ((RufStartG eP eSp eInit).faeden 0).spur = [] := rfl
  obtain ⟨M1, s1, hZ1⟩ := w_rufEnde (P := eP) (O := eO) (passes := 0) h00
    eSetze .nil eHpSetze rfl
    (.cons (.call ePruefe .nil eHpPruefe rfl) (.ret .keine List.Perm.nil))
    .nil rfl (ehg0 hoff0).heldIn
  have hoff1 : offen (M1.faeden 0).spur = [] := by
    rw [hZ1.spur, (Erw.lese _ _ _).offen]; exact hoff0
  obtain ⟨M2, s2, hZ2⟩ := w_blatt (P := eP) (O := eO) (passes := 0) hZ1.1
    _ _ _ rfl rfl (ehg0 (eoff_z hZ1 hoff1)).heldIn _ _
    (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  exact ⟨M2, .schritt _ _ 0 (.schritt _ _ 0 .start s1) s2⟩

/-- The three bridged fragment kinds (reused `fragArt_abgedeckt_oder_drain`):
    every fragment kind is a no-read store, a committed read, a forwarded
    read, or drain-only progress (which the run induction refuses a W
    step). The prefix above feeds the head these kinds consume. -/
theorem startBrueckenArten (a : FragArt) :
    a = .store ∨ a = .loadCommit ∨ a = .loadFwd ∨ a = .drain :=
  fragArt_abgedeckt_oder_drain a

/-- JOINT WITNESS (`startFragment_zeuge`): every premise holds jointly
    on the accepted `eP` run -- a reached machine from `RufStartG`, the
    start world at `konto[0] = 0`, a table (`konto`) that `setze` writes,
    and a logged `pruefe` entry whose world carries `konto[0] = 5` by the
    accepted theorem. Non-degenerate: a written table and a reached run
    whose memory observably changed (`0` at the start, `5` at the entry
    world). The `schreibt` fact is `rfl` on the witness signature. -/
theorem startFragment_zeuge :
    ∃ M : RufMaschineG eD,
      RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M ∧
      (eSp.slots () 0 ()).n = 0 ∧
      (eD.signatur eSetze).schreibt () = true ∧
      ∃ (rho : Env eD (eD.params ePruefe)) (s0 : World eD),
        RufEreignisF.eintritt ePruefe rho s0 ∈ (M.faeden 0).log ∧
        ReqAmEintritt eP ePruefe s0 rho ∧
        (s0.slots () 0 ()).n = 5 := by
  obtain ⟨M, hr, h0, rho, s0, hm, hreq, h5⟩ := ziel_ort_einfaden_zeuge
  exact ⟨M, hr, h0, rfl, rho, s0, hm, hreq, h5⟩

/- CUTS:
  Proved here: the start anchor (`startAnker`, `startAnker_refl`,
  `startAnker_gleich`); the entry/call prefix reaching the fragment
  head from `RufStartG` (`startCall_erreichbar` via the accepted
  `w_rufEnde`, `fragmentKopf_erreichbar` via the accepted `w_blatt`
  with `execStmt_assignSlot`); the bridged-kind enumeration
  (`startBrueckenArten` via the accepted `fragArt_abgedeckt_oder_drain`:
  no-read store, committed read, forwarded read, drain-only progress);
  the joint non-degenerate witness (`startFragment_zeuge` via the
  accepted `ziel_ort_einfaden_zeuge` plus the `rfl` write fact): a
  reached run from `RufStartG` with a written table and an observable
  memory change (`0` at the start, `5` at the logged entry world).
  NOT proved here, and not claimed:
  - No `TsoGxRefine.lean` exists on this master (lane 1215 is not
    integrated): there is no accepted refinement statement to compose
    with, so no cross-module refinement simulation is claimed; the
    prefix leg above is the piece the task names as missing.
  - No per-access TSO-to-W/GX simulation is constructed here: the
    `BrueckenLauf` run induction over `witD`/`ctM` is reused by
    reference only (`startBrueckenArten` names its kinds); joining the
    `eP` prefix run with a `witD` bridged run needs a cross-declaration
    lowering certificate, which stays OPEN.
  - No byte-level entry/call linkage: `PipelineEntry.prolog_lauf` and
    `StackExecution.geholt_verschachtelt_wiederhergestellt` live on the
    byte machine (`Zustand`, `laufBytes`); the prefix here is
    source-level (`RufSchrittG` from `RufStartG`). The byte-to-source
    entry connection stays OPEN with the pipeline owners.
  - No new hardware or software assumptions: the only gates are the
    accepted entry/call step guards; no silicon, timing, fairness or
    progress claim.
-/

#print axioms startAnker
#print axioms startAnker_refl
#print axioms startAnker_gleich
#print axioms startCall_erreichbar
#print axioms fragmentKopf_erreichbar
#print axioms startBrueckenArten
#print axioms startFragment_zeuge

end Gabbro.Grammatik.X86
