module

public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtInv
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge
public import Grammatik.Proben.InvZeuge.Teil1

@[expose] public section

namespace Gabbro.Grammatik

/-- **`ivGut_zeuge`**: on a machine of `ivPgut` reached in four steps
    (thread 0: `haupt` calls `setze`, `setze` writes both slots and
    returns), the logged return of `setze` meets the invariant it owes BY
    THE THEOREM (`ivPgut_zertifiziert`), at a world whose two slots hold
    `5`. -/
theorem ivGut_zeuge : ∃ M : RufMaschineG ivD,
    RufErreichbarG ivPgut ivO 0 (RufStartG ivPgut ivSp ivInit) M ∧
    ∃ (v : ErgVal ivD (ivD.erg ivSetze)) (s0 s1 : World ivD),
      RufEreignisF.rueck ivSetze .nil v s0 s1 ∈ (M.faeden 0).log ∧
      InvAmRueck ivPgut ivSetze s1 ∧
      (s1.slots () 0 ()).n = 5 ∧ (s1.slots () 1 ()).n = 5 := by
  obtain ⟨M1, s1, hZ1⟩ := w_rufEnde (P := ivPgut) (O := ivO) (passes := 0)
    (ivM0_faden0 ivRumpfGut) ivSetze .nil ivHp rfl ivHauptRest .nil rfl (ivHeld ivOffen0)
  have hoff1 : offen (M1.faeden 0).spur = [()] := by
    rw [hZ1.spur, (Erw.lese _ _ _).offen]; exact ivOffen0
  have e1 := hZ1.1
  obtain ⟨M2, s2, hZ2⟩ := w_blatt (P := ivPgut) (O := ivO) (passes := 0) e1 ivS0 (.cons ivS1 ivRetS)
    .nil rfl rfl (by rw [← e1]; exact ivHeld hoff1) _ _ rfl
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff2 : offen (M2.faeden 0).spur = [()] := by
    rw [hZ2.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans
      (by rw [← hZ1.welt] at *; exact hoff1)
  have e2 := hZ2.1
  obtain ⟨M3, s3, hZ3⟩ := w_blatt (P := ivPgut) (O := ivO) (passes := 0) e2 ivS1 ivRetS
    .nil rfl rfl (by rw [← e2]; exact ivHeld hoff2) _ _ rfl
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff3 : offen (M3.faeden 0).spur = [()] := by
    rw [hZ3.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans
      (by rw [← hZ2.welt] at *; exact hoff2)
  have e3 := hZ3.1
  obtain ⟨M4, s4, hG4⟩ := w_rueckP (P := ivPgut) (O := ivO) (passes := 0) e3 _ _ rfl
    (PopArt.wie rfl) .empty (List.Perm.refl _) _ rfl
    (by show HeldIn ivL _; rw [← e3]; exact ivHeld hoff3)
  have hr4 : RufErreichbarG ivPgut ivO 0 (RufStartG ivPgut ivSp ivInit) M4 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3) s4
  obtain ⟨v, a, b, hm, hb⟩ : ∃ (v : ErgVal ivD (ivD.erg ivSetze)) (a b : World ivD),
      RufEreignisF.rueck ivSetze .nil v a b ∈ (M4.faeden 0).log ∧
      b = (M3.weltVon 0).lese ivL [] := by
    rw [hG4.1]; exact ⟨_, _, _, List.mem_cons_self, rfl⟩
  refine ⟨M4, hr4, v, a, b, hm, (ivPgut_zertifiziert M4 hr4).2 0 _ hm _ _ _ _ _ rfl, ?_, ?_⟩
  · rw [hb, hZ3.welt, hZ2.welt, hZ1.welt]
    simp only [World.lese, World.merke, World.schreibSlot, World.storeSlot, RufMaschineG.weltVon, Speicher.welt,
  RufStartG, ivSp, ivIdx, ivWert, List.map_append, List.append_assoc, eval, Zahl.weiter, List.cons_append,
  List.nil_append, dite_eq_ite, List.map_nil, Int.reduceEq, ↓reduceIte, ite_self]
    rfl
  · rw [hb, hZ3.welt, hZ2.welt, hZ1.welt]
    simp only [World.lese, World.merke, World.schreibSlot, World.storeSlot, RufMaschineG.weltVon, Speicher.welt,
  RufStartG, ivSp, ivIdx, ivWert, List.map_append, List.append_assoc, eval, Zahl.weiter, List.cons_append,
  List.nil_append, dite_eq_ite, List.map_nil, ↓reduceIte, Int.reduceEq]
    rfl

/-! ## CUTS:

  What is proved: on a declaration with one table invariant, the correct
  program meets every premise of `ziel_ort_sperre_inv`
  (`ivPgut_zertifiziert`) and its reached run logs a return of `setze` at
  which the invariant holds by the theorem (`ivGut_zeuge`); the broken
  program, which `ziel_ort_sperre` certifies (`ivPschlecht_alt`), fails
  the new obligation (`ivPschlecht_nicht_invGutS`) and the new conclusion
  on a reached machine (`ivPschlecht_verletzt`).

  What is NOT covered: the root frame's return is not a logged event (G
  logs returns at pops only), so an invariant owed by a thread's start
  function is not checked at the end of the thread; `haupt` re-establishes
  the invariant itself only to meet `InvGutS`. -/

#print axioms ivPgut_zertifiziert
#print axioms ivPschlecht_alt
#print axioms ivPschlecht_nicht_invGutS
#print axioms ivPschlecht_verletzt
#print axioms ivGut_zeuge

end Gabbro.Grammatik
