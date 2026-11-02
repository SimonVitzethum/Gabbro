module
public import Grammatik.Proben.InvZeuge.Teil1a

public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtInv
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section



namespace Gabbro.Grammatik

/-- Thread `0` runs `haupt`, every other thread `nichts`. -/
def ivInit : Faden → Σ f : ivD.Fn, Env ivD (ivD.params f) :=
  fun t => if t = 0 then ⟨ivHaupt, .nil⟩ else ⟨ivNichts, .nil⟩

theorem ivInit_sonst {t : Faden} (ht : t ≠ 0) : ivInit t = ⟨ivNichts, .nil⟩ := if_neg ht

theorem ivStart (setze : Endblock ivD (vertragVon ivD ivSetze) false [] ivL) :
    StartGut (ivP setze) ivSp ivInit := by
  intro t
  by_cases ht : t = 0
  · subst ht; rfl
  · rw [ivInit_sonst ht]; rfl

theorem ivInit_exklusiv : StartExklusiv (D := ivD) ivInit := by
  intro t u htu L hL hL'
  by_cases ht : t = 0
  · have hu : u ≠ 0 := fun h => htu (ht.trans h.symm)
    rw [ivInit_sonst hu] at hL'
    exact absurd hL' List.not_mem_nil
  · rw [ivInit_sonst ht] at hL
    exact absurd hL List.not_mem_nil

theorem ivPgut_frag : programmImFragmentG ivPgut ivFs = true := by decide
theorem ivPschlecht_frag : programmImFragmentG ivPschlecht ivFs = true := by decide
theorem ivPgut_fuss : fussSperreB ivPgut (SperrInv.leer ivD) ivFs = true := by decide
theorem ivPschlecht_fuss : fussSperreB ivPschlecht (SperrInv.leer ivD) ivFs = true := by decide


/-! ## 4. The obligations -/

theorem iv_koerper_nichts (setze : Endblock ivD (vertragVon ivD ivSetze) false [] ivL) :
    KoerperGutS (ivP setze) 0 (axWahr ivD) (SperrInv.leer ivD) ivNichts := by
  have hr : (ivP setze).rumpf ivNichts = ivRumpfNichts := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [ivRumpfNichts, execEndH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [ivRumpfNichts, execEndH] at hrun
    cases hrun

theorem iv_koerper_gut : KoerperGutS ivPgut 0 (axWahr ivD) (SperrInv.leer ivD) ivSetze := by
  have hr : ivPgut.rumpf ivSetze = ivRumpfGut := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [ivRumpfGut, ivS0, ivS1, ivSchreib, ivRetS, execEndH, execStmtH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [ivRumpfGut, ivS0, ivS1, ivSchreib, ivRetS, execEndH, execStmtH] at hrun
    cases hrun

theorem iv_koerper_schlecht : KoerperGutS ivPschlecht 0 (axWahr ivD) (SperrInv.leer ivD) ivSetze := by
  have hr : ivPschlecht.rumpf ivSetze = ivRumpfSchlecht := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [ivRumpfSchlecht, ivS0, ivSchreib, ivRetS, execEndH, execStmtH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [ivRumpfSchlecht, ivS0, ivSchreib, ivRetS, execEndH, execStmtH] at hrun
    cases hrun

theorem iv_koerper_haupt (setze : Endblock ivD (vertragVon ivD ivSetze) false [] ivL) :
    KoerperGutS (ivP setze) 0 (axWahr ivD) (SperrInv.leer ivD) ivHaupt := by
  have hr : (ivP setze).rumpf ivHaupt = ivRumpfHaupt := rfl
  refine ⟨fun O' _ _ _ U _ R hR hOV σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R hR hOL σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [ivRumpfHaupt, ivRuf, execEndH] at hrun
    rcases execStmtH_call_fall (S := SperrInv.leer ivD) (O := O') (U := U) (passes := 0)
      (R := torRuf (ivP setze) R) (l := false) (Γ := []) ivSetze .nil ivHp rfl σ ρ with
      ⟨σ1, v1, _, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · simp only [ivHauptRest, ivH0, ivH1, ivSchreib, ivRetH, execEndH, execStmtH] at hrun
      cases hrun
    · cases hrun
      exact hOV _ _ _ _ he1 g rfl
    · cases hrun
  · rw [hr] at hrun
    simp only [ivRumpfHaupt, ivRuf, execEndH] at hrun
    rcases execStmtH_call_fall (S := SperrInv.leer ivD) (O := O') (U := U) (passes := 0)
      (R := R) (l := false) (Γ := []) ivSetze .nil ivHp rfl σ ρ with
      ⟨σ1, v1, _, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · simp only [ivHauptRest, ivH0, ivH1, ivSchreib, ivRetH, execEndH, execStmtH] at hrun
      cases hrun
    · cases hrun
      exact hOL _ _ _ _ he1
    · cases hrun

theorem ivPgut_koerper : ∀ f : ivD.Fn, KoerperGutS ivPgut 0 (axWahr ivD) (SperrInv.leer ivD) f
  | .haupt => iv_koerper_haupt _
  | .setze => iv_koerper_gut
  | .nichts => iv_koerper_nichts _

theorem ivPschlecht_koerper :
    ∀ f : ivD.Fn, KoerperGutS ivPschlecht 0 (axWahr ivD) (SperrInv.leer ivD) f
  | .haupt => iv_koerper_haupt _
  | .setze => iv_koerper_schlecht
  | .nichts => iv_koerper_nichts _

theorem iv_inv_gut : InvGutS ivPgut 0 (axWahr ivD) (SperrInv.leer ivD) ivSetze := by
  intro O' _ _ _ U _ R _ _ σ ρ _ σ' v hrun
  have hr : ivPgut.rumpf ivSetze = ivRumpfGut := rfl
  rw [hr] at hrun
  simp only [ivRumpfGut, ivS0, ivS1, ivSchreib, ivRetS, execEndH, execStmtH] at hrun
  cases hrun
  intro i _ _
  cases i
  simp only [InvHaelt, World.lese, World.merke, World.schreibSlot, World.storeSlot, ivIdx, ivWert,
  List.map_append, List.append_assoc, eval, Zahl.weiter, dite_eq_ite, List.cons_append, List.nil_append, ivPgut, ivP,
  ivInv, Int.reduceEq, ↓reduceIte, ite_self]
  rfl

theorem iv_inv_haupt (setze : Endblock ivD (vertragVon ivD ivSetze) false [] ivL) :
    InvGutS (ivP setze) 0 (axWahr ivD) (SperrInv.leer ivD) ivHaupt := by
  intro O' _ _ _ U _ R _ _ σ ρ _ σ' v hrun
  have hr : (ivP setze).rumpf ivHaupt = ivRumpfHaupt := rfl
  rw [hr] at hrun
  simp only [ivRumpfHaupt, ivRuf, execEndH] at hrun
  rcases execStmtH_call_fall (S := SperrInv.leer ivD) (O := O') (U := U) (passes := 0)
    (R := R) (l := false) (Γ := []) ivSetze .nil ivHp rfl σ ρ with
    ⟨σ1, v1, _, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
  · simp only [ivHauptRest, ivH0, ivH1, ivSchreib, ivRetH, execEndH, execStmtH] at hrun
    cases hrun
    intro i _ _
    cases i
    simp only [InvHaelt, World.lese, World.merke, World.schreibSlot, World.storeSlot, ivIdx, ivWert,
  List.map_append, List.append_assoc, eval, Zahl.weiter, dite_eq_ite, List.cons_append, List.nil_append, ivP, ivInv,
  Int.reduceEq, ↓reduceIte, ite_self]
    rfl
  · cases hrun
  · cases hrun

theorem iv_inv_nichts (setze : Endblock ivD (vertragVon ivD ivSetze) false [] ivL) :
    InvGutS (ivP setze) 0 (axWahr ivD) (SperrInv.leer ivD) ivNichts :=
  invGutS_ohne fun _ _ => rfl

theorem ivPgut_inv : ∀ f : ivD.Fn, InvGutS ivPgut 0 (axWahr ivD) (SperrInv.leer ivD) f
  | .haupt => iv_inv_haupt _
  | .setze => iv_inv_gut
  | .nichts => iv_inv_nichts _

/-! ## 5. The correct program is certified -/

/-- **`ivPgut` is certified by `ziel_ort_sperre_inv`**: every premise,
    the new obligation included. -/
theorem ivPgut_zertifiziert : ∀ M : RufMaschineG ivD,
    RufErreichbarG ivPgut ivO 0 (RufStartG ivPgut ivSp ivInit) M →
      (VertragAmOrtG ivPgut M ∧ SperrInvG (SperrInv.leer ivD) M ∧ KeinLogikHaltG ivO 0 M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG ivPgut ivO 0 M t M') ∧
      InvAmOrtG ivPgut M :=
  ziel_ort_sperre_inv ivPgut ivO 0 (axWahr ivD) (SperrInv.leer ivD) ivFs ivSp ivInit ivO_gut
    ivO_lokal (axVertragO_wahr ivO) axEnsLokal_wahr sperrInvOk_leer ivFs_voll ivPgut_frag
    ivPgut_fuss ivPgut_koerper (ivStart _) (fun _ => rfl) ivInit_exklusiv ivPgut_inv

/-- **The broken program was certified by `ziel_ort_sperre`** (every
    premise holds: its contracts are `true`) -- the gap this section closes. -/
theorem ivPschlecht_alt : ∀ M : RufMaschineG ivD,
    RufErreichbarG ivPschlecht ivO 0 (RufStartG ivPschlecht ivSp ivInit) M →
      VertragAmOrtG ivPschlecht M ∧ SperrInvG (SperrInv.leer ivD) M ∧ KeinLogikHaltG ivO 0 M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG ivPschlecht ivO 0 M t M' :=
  ziel_ort_sperre ivPschlecht ivO 0 (axWahr ivD) (SperrInv.leer ivD) ivFs ivSp ivInit ivO_gut
    ivO_lokal (axVertragO_wahr ivO) axEnsLokal_wahr sperrInvOk_leer ivFs_voll ivPschlecht_frag
    ivPschlecht_fuss ivPschlecht_koerper (ivStart _) (fun _ => rfl) ivInit_exklusiv

/-! ## 6. The broken program is refuted -/

/-- The identity environment move meets `HavocOk` of the empty family. -/
theorem iv_havoc : HavocOk (SperrInv.leer ivD) (fun _ σ => σ) :=
  fun _ _ => ⟨rfl, fun c _ => traegerGleich_refl _ c, rfl⟩

/-- **The new obligation fails for the broken `setze`**: from the zero
    memory its body returns with `konto[0] = 5`, `konto[1] = 0`. -/
theorem ivPschlecht_nicht_invGutS :
    ¬ InvGutS ivPschlecht 0 (axWahr ivD) (SperrInv.leer ivD) ivSetze := by
  intro h
  have h3 := h ivO (gutO_rahmenO ivO_gut) ivO_lokal (axVertragO_wahr ivO) (fun _ σ => σ) iv_havoc
    (rufAusV []) (rufAusV_rahmen (vertraegeOkR_nil ivPschlecht))
    (rufAusV_ohneVorbedingung (vertraegeOkR_nil ivPschlecht).1) (ivSp.welt []) .nil rfl _ _ rfl ()
    (List.mem_singleton.mpr rfl) rfl
  revert h3
  simp only [InvHaelt, World.lese, World.merke, World.schreibSlot, World.storeSlot, Speicher.welt, ivSp, ivIdx,
  ivWert, List.map_append, List.append_nil, eval, Zahl.weiter, List.cons_append, List.nil_append, ivPschlecht, ivP,
  ivInv, ↓reduceIte, Int.reduceEq, imp_false, Bool.not_eq_true]
  decide

theorem ivM0_faden0 (setze : Endblock ivD (vertragVon ivD ivSetze) false [] ivL) :
    (RufStartG (ivP setze) ivSp ivInit).faeden 0 =
    ⟨[], ⟨ivHaupt, .nil, ivSp.welt [], ⟨false, [], ivL, .nil, .ende ivRumpfHaupt⟩⟩,
      startSpur ivHaupt, [RufEreignisF.eintritt ivHaupt .nil (ivSp.welt [])]⟩ := by rfl

theorem ivOffen0 : offen (startSpur (D := ivD) ivHaupt) = [()] := by rfl

theorem ivHeld {s : List (Ereignis ivD)} (h : offen s = [()]) : HeldIn ivL (offen s) :=
  fun L _ => by cases L; rw [h]; exact List.mem_singleton.mpr rfl

/-- **The new conclusion fails on a machine of `ivPschlecht` reachable in
    three steps** (thread 0: `haupt` calls `setze`, `setze` writes slot `0`
    and returns): the logged return of `setze` breaks the invariant. -/
theorem ivPschlecht_verletzt : ∃ M : RufMaschineG ivD,
    RufErreichbarG ivPschlecht ivO 0 (RufStartG ivPschlecht ivSp ivInit) M ∧
    ¬ InvAmOrtG ivPschlecht M := by
  obtain ⟨M1, s1, hZ1⟩ := w_rufEnde (P := ivPschlecht) (O := ivO) (passes := 0)
    (ivM0_faden0 ivRumpfSchlecht) ivSetze .nil ivHp rfl ivHauptRest .nil rfl (ivHeld ivOffen0)
  have hoff1 : offen (M1.faeden 0).spur = [()] := by
    rw [hZ1.spur, (Erw.lese _ _ _).offen]; exact ivOffen0
  have e1 := hZ1.1
  obtain ⟨M2, s2, hZ2⟩ := w_blatt (P := ivPschlecht) (O := ivO) (passes := 0) e1 ivS0 ivRetS .nil
    rfl rfl (by rw [← e1]; exact ivHeld hoff1) _ _ rfl
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff2 : offen (M2.faeden 0).spur = [()] := by
    rw [hZ2.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans
      (by rw [← hZ1.welt] at *; exact hoff1)
  have e2 := hZ2.1
  obtain ⟨M3, s3, hG3⟩ := w_rueckP (P := ivPschlecht) (O := ivO) (passes := 0) e2 _ _ rfl
    (PopArt.wie rfl) .empty (List.Perm.refl _) _ rfl
    (by show HeldIn ivL _; rw [← e2]; exact ivHeld hoff2)
  refine ⟨M3, .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3, fun h => ?_⟩
  have h3 := h 0 _ (by rw [hG3.1]; exact List.mem_cons_self) _ _ _ _ _ rfl ()
    (List.mem_singleton.mpr rfl) rfl
  revert h3
  rw [hZ2.welt, hZ1.welt]
  simp only [InvHaelt, World.lese, World.merke, World.schreibSlot, World.storeSlot, RufMaschineG.weltVon,
  Speicher.welt, RufStartG, ivSp, ivP, ivInv, ivIdx, ivWert, List.map_append, List.append_assoc, eval, Zahl.weiter,
  List.cons_append, List.nil_append, ivPschlecht, ↓reduceIte, Int.reduceEq, imp_false, Bool.not_eq_true]
  decide

/-! ## 7. The correct program on a reached run -/

end Gabbro.Grammatik
