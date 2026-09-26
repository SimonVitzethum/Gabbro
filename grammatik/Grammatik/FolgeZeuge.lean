/-
  File:      Grammatik/FolgeZeuge.lean
  Subject:   WITNESSES for the order leg (`FolgeG`, OFFEN O1 L50/L52, Opus agent G,
             2026-09-26).

  The fixture is the sequential program `eP` of ZielOrtEinfadenZeuge.lean:

      setze()   konto[0] = 5; return            ensures konto[0] == 5
      pruefe()  return                          REQUIRES konto[0] == 5
      haupt()   setze(); pruefe(); return       thread 0; every other thread idles

  `setze` plays the flush, `pruefe` the reply, `haupt` the service:
  * `Φ50` -- L50's shape: every ENTRY of `pruefe` directly behind a RETURN of `setze`;
  * `Φ52` -- L52's shape: every return of `haupt`, and the end of a thread started in
    `haupt`, directly behind a return of `pruefe`.
  Both pass the static check (`eP_folge50`, `eP_folge52`).

  * `folge50_zeuge` -- NON-DEGENERACY of the leg: on a reached run of four steps (call
    `setze`, its write of `5` into the table the start left at `0`, its return, call `pruefe`)
    the newest log event is the entry of `pruefe` and the one directly behind it the return of
    `setze`, the entry world carries the flush's write (`konto[0] = 5`, by the contract leg),
    and the leg holds there -- the ordered event OCCURS, the claim is not vacuous.
  * `folge52_zeuge` -- one step further (`pruefe` returns) thread 0 is FINISHED in `haupt`,
    and BY THE LEG its log ends directly behind the return of `pruefe`.
  * `eP2` swaps the two calls (`pruefe(); setze(); return`). The static check REFUSES it
    (`eP2_folge50_falsch`), and on a reached run the order FAILS while "both happened" holds
    (`folge50_gegen`): the premise of the leg is needed, and `flush ∧ reply` is weaker.
-/
import Grammatik.ZielOrtEinfadenZeuge
import Grammatik.FolgeBeweis

namespace Gabbro.Grammatik

/-! ## 1. The two order specifications, and the check on `eP` -/

/-- L50's shape on the fixture: `pruefe` (the reply) only directly behind `setze` (the flush). -/
def Φ50 : Folge eD where
  vor := fun g => match (g : EFn) with | .setze => true | _ => false
  ruf := fun g => match (g : EFn) with | .pruefe => true | _ => false
  ind := fun _ => true
  ende := fun _ => false

/-- L52's shape on the fixture: `haupt` (the service) ends only directly behind `pruefe` (the
    reply). -/
def Φ52 : Folge eD where
  vor := fun g => match (g : EFn) with | .pruefe => true | _ => false
  ruf := fun _ => false
  ind := fun _ => true
  ende := fun g => match (g : EFn) with | .haupt => true | _ => false

theorem eP_folge50 : FolgeOk eP Φ50 :=
  ⟨fun f => by cases f <;> rfl, fun _ _ => rfl⟩

theorem eP_folge52 : FolgeOk eP Φ52 :=
  ⟨fun f => by cases f <;> rfl, fun _ _ => rfl⟩

/-! ## 2. The run of `eP`: the ordered events occur -/

/-- **NON-DEGENERACY (L50).** A reached machine whose newest log event is the ENTRY of `pruefe`
    and the next the RETURN of `setze`, after `setze` changed memory (`konto[0]`: `0` at the
    start, `5` at the entry world of `pruefe`), and the order leg holds there BY THE THEOREM. -/
theorem folge50_zeuge : ∃ M : RufMaschineG eD,
    RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M ∧ (eSp.slots () 0 ()).n = 0 ∧
    (∃ (r1 : Env eD (eD.params ePruefe)) (w1 : World eD) (r2 : Env eD (eD.params eSetze))
      (v2 : ErgVal eD (eD.erg eSetze)) (a2 b2 : World eD) (rest : List (RufEreignisF eD)),
      (M.faeden 0).log = RufEreignisF.eintritt ePruefe r1 w1 ::
        RufEreignisF.rueck eSetze r2 v2 a2 b2 :: rest ∧ (w1.slots () 0 ()).n = 5) ∧
    Pflichtig Φ50 ((M.faeden 0).log.head?.getD (RufEreignisF.eintritt eHaupt .nil (eSp.welt []))) = true ∧
    FolgeLog Φ50 (M.faeden 0).log := by
  have h00 : (RufStartG eP eSp eInit).faeden 0 = ⟨[], ⟨eHaupt, .nil, eSp.welt [],
      ⟨false, [], [], .nil, .ende eRumpfHaupt⟩⟩, [],
      [RufEreignisF.eintritt eHaupt .nil (eSp.welt [])]⟩ := rfl
  have hoff0 : offen ((RufStartG eP eSp eInit).faeden 0).spur = [] := rfl
  obtain ⟨M1, s1, hZ1⟩ := w_rufEnde (P := eP) (O := eO) (passes := 0) h00 eSetze .nil eHpSetze rfl
    (.cons (.call ePruefe .nil eHpPruefe rfl) (.ret .keine List.Perm.nil)) .nil rfl (ehg0 hoff0).heldIn
  have hoff1 : offen (M1.faeden 0).spur = [] := by
    rw [hZ1.spur, (Erw.lese _ _ _).offen]; exact hoff0
  obtain ⟨M2, s2, hZ2⟩ := w_blatt (P := eP) (O := eO) (passes := 0) hZ1.1
    _ _ _ rfl rfl (ehg0 (eoff_z hZ1 hoff1)).heldIn _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff2 : offen (M2.faeden 0).spur = [] := by
    rw [hZ2.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans hoff1
  obtain ⟨M3, s3, hG3⟩ := w_rueckP (P := eP) (O := eO) (passes := 0) hZ2.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (ehg0 (eoff_z hZ2 hoff2)).heldIn
  have hoff3 : offen (M3.faeden 0).spur = [] := by
    rw [hG3.1]
    exact ((Erw.lese _ _ _).offen).trans hoff2
  obtain ⟨M4, s4, hZ4⟩ := w_rufEnde (P := eP) (O := eO) (passes := 0) hG3.1 ePruefe .nil eHpPruefe
    rfl (.ret .keine List.Perm.nil) .nil rfl (ehg0 (eoff_g hG3 hoff3)).heldIn
  have hr4 : RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M4 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3) s4
  have hlog : ∃ (r1 : Env eD (eD.params ePruefe)) (w1 : World eD) (r2 : Env eD (eD.params eSetze))
      (v2 : ErgVal eD (eD.erg eSetze)) (a2 b2 : World eD) (rest : List (RufEreignisF eD)),
      (M4.faeden 0).log = RufEreignisF.eintritt ePruefe r1 w1 ::
        RufEreignisF.rueck eSetze r2 v2 a2 b2 :: rest := by
    rw [hZ4.1]
    exact ⟨_, _, _, _, _, _, _, rfl⟩
  obtain ⟨r1, w1, r2, v2, a2, b2, rest, hl⟩ := hlog
  have hm : RufEreignisF.eintritt ePruefe r1 w1 ∈ (M4.faeden 0).log := by
    rw [hl]; exact List.mem_cons_self
  have hreq := ((eP_zertifiziert M4 hr4).1 0 _ hm).1 _ _ _ rfl
  refine ⟨M4, hr4, rfl, ⟨r1, w1, r2, v2, a2, b2, rest, hl, of_decide_eq_true hreq⟩, ?_,
    (folgeG_erreichbar eSp eInit hr4 Φ50 eP_folge50 0).1⟩
  rw [hl]
  rfl

/-- **NON-DEGENERACY (L52).** One step further `pruefe` returns: thread 0 is FINISHED in its
    start function `haupt` (empty stack, head at its `return`), and BY THE THEOREM its log ends
    directly behind a return of `pruefe` -- the reply went out before the service ended. -/
theorem folge52_zeuge : ∃ M : RufMaschineG eD,
    RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M ∧ FertigG M 0 ∧
    (M.faeden 0).kopf.f = eHaupt ∧ Armiert Φ52 (M.faeden 0).log = true := by
  have h00 : (RufStartG eP eSp eInit).faeden 0 = ⟨[], ⟨eHaupt, .nil, eSp.welt [],
      ⟨false, [], [], .nil, .ende eRumpfHaupt⟩⟩, [],
      [RufEreignisF.eintritt eHaupt .nil (eSp.welt [])]⟩ := rfl
  have hoff0 : offen ((RufStartG eP eSp eInit).faeden 0).spur = [] := rfl
  obtain ⟨M1, s1, hZ1⟩ := w_rufEnde (P := eP) (O := eO) (passes := 0) h00 eSetze .nil eHpSetze rfl
    (.cons (.call ePruefe .nil eHpPruefe rfl) (.ret .keine List.Perm.nil)) .nil rfl (ehg0 hoff0).heldIn
  have hoff1 : offen (M1.faeden 0).spur = [] := by
    rw [hZ1.spur, (Erw.lese _ _ _).offen]; exact hoff0
  obtain ⟨M2, s2, hZ2⟩ := w_blatt (P := eP) (O := eO) (passes := 0) hZ1.1
    _ _ _ rfl rfl (ehg0 (eoff_z hZ1 hoff1)).heldIn _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff2 : offen (M2.faeden 0).spur = [] := by
    rw [hZ2.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans hoff1
  obtain ⟨M3, s3, hG3⟩ := w_rueckP (P := eP) (O := eO) (passes := 0) hZ2.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (ehg0 (eoff_z hZ2 hoff2)).heldIn
  have hoff3 : offen (M3.faeden 0).spur = [] := by
    rw [hG3.1]
    exact ((Erw.lese _ _ _).offen).trans hoff2
  obtain ⟨M4, s4, hZ4⟩ := w_rufEnde (P := eP) (O := eO) (passes := 0) hG3.1 ePruefe .nil eHpPruefe
    rfl (.ret .keine List.Perm.nil) .nil rfl (ehg0 (eoff_g hG3 hoff3)).heldIn
  have hoff4 : offen (M4.faeden 0).spur = [] := by
    rw [hZ4.spur, (Erw.lese _ _ _).offen]; exact hoff3
  obtain ⟨M5, s5, hG5⟩ := w_rueckP (P := eP) (O := eO) (passes := 0) hZ4.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (ehg0 (eoff_z hZ4 hoff4)).heldIn
  have hr5 : RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M5 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1)
      s2) s3) s4) s5
  have hF : FertigG M5 0 := by
    unfold FertigG
    rw [hG5.1]
    exact ⟨rfl, rfl⟩
  have hf : (M5.faeden 0).kopf.f = eHaupt := by rw [hG5.1]
  refine ⟨M5, hr5, hF, hf, ?_⟩
  have := (folgeG_erreichbar eSp eInit hr5 Φ52 eP_folge52 0).2 hF.1 hF.2 (by rw [hf]; rfl)
  exact this

/-! ## 3. The counter-program: the premise is needed, and the conjunction is weaker -/

/-- `haupt` with the calls swapped: `pruefe(); setze(); return`. -/
def eRumpfHaupt2 : Endblock eD (vertragVon eD eHaupt) false [] [] :=
  .cons (.call ePruefe .nil eHpPruefe rfl) (.cons (.call eSetze .nil eHpSetze rfl)
    (.ret .keine List.Perm.nil))

def eP2 : Programm eD where
  invariante := eP.invariante
  requires := eP.requires
  ensures := eP.ensures
  rumpf
    | .setze => eRumpfSetze
    | .pruefe => eRumpfPruefe
    | .haupt => eRumpfHaupt2
    | .ruhe => eRumpfRuhe

/-- **The static check refuses the swapped program**: `pruefe` stands behind no call. -/
theorem eP2_folge50_falsch : ¬ FolgeOk eP2 Φ50 := fun h => by
  have := h.1 eHaupt
  revert this
  decide

/-- **Without the premise the order fails, while "both happened" holds.** On a reached run of
    the swapped program (call `pruefe`, its return, call `setze`, its write, its return) the
    log holds an entry of `pruefe` AND a return of `setze` -- the conjunction `flush ∧ reply`
    -- and it is NOT ordered: the entry of `pruefe` stands directly behind the start entry. -/
theorem folge50_gegen : ∃ M : RufMaschineG eD,
    RufErreichbarG eP2 eO 0 (RufStartG eP2 eSp eInit) M ∧
    (∃ ev ∈ (M.faeden 0).log, Pflichtig Φ50 ev = true) ∧
    (∃ ev ∈ (M.faeden 0).log, Armiert Φ50 [ev] = true) ∧
    ¬ FolgeLog Φ50 (M.faeden 0).log := by
  have h00 : (RufStartG eP2 eSp eInit).faeden 0 = ⟨[], ⟨eHaupt, .nil, eSp.welt [],
      ⟨false, [], [], .nil, .ende eRumpfHaupt2⟩⟩, [],
      [RufEreignisF.eintritt eHaupt .nil (eSp.welt [])]⟩ := rfl
  have hoff0 : offen ((RufStartG eP2 eSp eInit).faeden 0).spur = [] := rfl
  obtain ⟨M1, s1, hZ1⟩ := w_rufEnde (P := eP2) (O := eO) (passes := 0) h00 ePruefe .nil
    eHpPruefe rfl (.cons (.call eSetze .nil eHpSetze rfl) (.ret .keine List.Perm.nil)) .nil rfl
    (ehg0 hoff0).heldIn
  have hoff1 : offen (M1.faeden 0).spur = [] := by
    rw [hZ1.spur, (Erw.lese _ _ _).offen]; exact hoff0
  obtain ⟨M2, s2, hG2⟩ := w_rueckP (P := eP2) (O := eO) (passes := 0) hZ1.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (ehg0 (eoff_z hZ1 hoff1)).heldIn
  have hoff2 : offen (M2.faeden 0).spur = [] := by
    rw [hG2.1]
    exact ((Erw.lese _ _ _).offen).trans hoff1
  obtain ⟨M3, s3, hZ3⟩ := w_rufEnde (P := eP2) (O := eO) (passes := 0) hG2.1 eSetze .nil eHpSetze
    rfl (.ret .keine List.Perm.nil) .nil rfl (ehg0 (eoff_g hG2 hoff2)).heldIn
  have hoff3 : offen (M3.faeden 0).spur = [] := by
    rw [hZ3.spur, (Erw.lese _ _ _).offen]; exact hoff2
  obtain ⟨M4, s4, hZ4⟩ := w_blatt (P := eP2) (O := eO) (passes := 0) hZ3.1
    _ _ _ rfl rfl (ehg0 (eoff_z hZ3 hoff3)).heldIn _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff4 : offen (M4.faeden 0).spur = [] := by
    rw [hZ4.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans hoff3
  obtain ⟨M5, s5, hG5⟩ := w_rueckP (P := eP2) (O := eO) (passes := 0) hZ4.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (ehg0 (eoff_z hZ4 hoff4)).heldIn
  have hr5 : RufErreichbarG eP2 eO 0 (RufStartG eP2 eSp eInit) M5 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1)
      s2) s3) s4) s5
  refine ⟨M5, hr5, ?_, ?_, ?_⟩
  · rw [hG5.1]
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)), rfl⟩
  · rw [hG5.1]
    exact ⟨_, List.mem_cons_self, rfl⟩
  · rw [hG5.1]
    intro h
    exact Bool.false_ne_true (h.2.2.2.1 (by simp) rfl)

#print axioms Gabbro.Grammatik.folge50_zeuge
#print axioms Gabbro.Grammatik.folge52_zeuge
#print axioms Gabbro.Grammatik.folge50_gegen

end Gabbro.Grammatik
