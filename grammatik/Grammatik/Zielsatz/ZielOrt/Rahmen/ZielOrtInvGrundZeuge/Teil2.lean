module

public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtInvGrund
public import Grammatik.Proben.InvZeuge
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtInvGrundZeuge.Teil1

@[expose] public section

namespace Gabbro.Grammatik

/-- **The new obligation fails for the broken `setze`**: from the zero
    memory its body leaves by the reason with `konto[0] = 5`,
    `konto[1] = 0`. -/
theorem igPschlecht_nicht_invGutGrund :
    ¬ Zielsatz.InvGutGrund igPschlecht 0 (axWahr igD) (SperrInv.leer igD) igSetze := by
  intro h
  have h3 := h igO (gutO_rahmenO igO_gut) igO_lokal (axVertragO_wahr igO) (fun _ σ => σ) ig_havoc
    (rufAusV []) (rufAusV_rahmen (vertraegeOkR_nil igPschlecht))
    (rufAusV_ohneVorbedingung (vertraegeOkR_nil igPschlecht).1) (igSp.welt []) .nil rfl _ _ rfl ()
    (List.mem_singleton.mpr rfl) rfl
  revert h3
  simp only [InvHaelt, World.schreibSlot, World.merke, World.storeSlot, World.lese, Speicher.welt, igSp, igIdx, igWert, List.map_append, List.append_nil, eval, Zahl.weiter, List.cons_append, List.nil_append, igPschlecht, igP, igInv, ↓reduceIte, Int.reduceEq, imp_false, Bool.not_eq_true]
  decide

/-! ## 6. The runs -/

theorem igM0_faden0 (setze : Endblock igD (vertragVon igD igSetze) false [] igL) :
    (RufStartG (igP setze) igSp igInit).faeden 0 =
    ⟨[], ⟨igHaupt, .nil, igSp.welt [], ⟨false, [], igL, .nil, .ende igRumpfHaupt⟩⟩,
      startSpur igHaupt, [RufEreignisF.eintritt igHaupt .nil (igSp.welt [])]⟩ := by rfl

theorem igHeld {s : List (Ereignis igD)} (h : offen s = [()]) : HeldIn igL (offen s) :=
  fun L _ => by cases L; rw [h]; exact List.mem_singleton.mpr rfl

/-- **The run to the reason return of `setze`**, for either body: `haupt`
    unfolds `breaking` (1, 2), calls `setze` through `let … else` (3),
    `setze` writes slot `0` (4). -/
theorem igVorlauf (setze : Endblock igD (vertragVon igD igSetze) false [] igL) :
    ∃ (M3 : RufMaschineG igD) (s0 : World igD) (log : List (RufEreignisF igD)),
      RufErreichbarG (igP setze) igO 0 (RufStartG (igP setze) igSp igInit) M3 ∧
      M3.faeden 0 = ⟨[⟨igHaupt, .nil, igSp.welt [],
          ⟨false, [], igL, .nil, .wartetSonst (τ := .bool) (igD.gruende igSetze) igErr .nil
            (.dann .nil (.ende igTail))⟩⟩],
        ⟨igSetze, .nil, s0, ⟨false, [], igL, .nil, .ende setze⟩⟩,
        s0.spur, log⟩ ∧
      M3.weltVon 0 = s0 ∧ offen s0.spur = [()] ∧
      s0.slots = igSp.slots := by
  obtain ⟨M1, s1, hZ1⟩ := w_endeEntf (P := igP setze) (O := igO) (passes := 0)
    (igM0_faden0 setze) (.breaking () igB) igTail .nil rfl rfl
  obtain ⟨M2, s2, hZ2⟩ := w_breaking (P := igP setze) (O := igO) (passes := 0) hZ1.1 () igB .nil
    (.ende igTail) .nil rfl
  have hoff2 : offen (M1.weltVon 0).spur = [()] := by
    rw [hZ1.welt]
    rfl
  obtain ⟨M3, s3, hZ3⟩ := w_bindCallElse (P := igP setze) (O := igO) (passes := 0) hZ2.1 igSetze
    .nil rfl igHp (by decide) igErr .nil (.dann .nil (.ende igTail)) .nil rfl (igHeld hoff2)
  refine ⟨M3, _, _, .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3,
    hZ3.1, hZ3.welt, ?_, ?_⟩
  · show offen ((M2.weltVon 0).lese igL []).spur = [()]
    rw [(Erw.lese _ _ _).offen, hZ2.welt]
    exact hoff2
  · show ((M2.weltVon 0).lese igL []).slots = igSp.slots
    rw [hZ2.welt, hZ1.welt]
    rfl

/-- **The new conclusion fails on a machine of `igPschlecht` reachable in
    five steps** (thread 0: `haupt` unfolds `breaking`, calls `setze`
    through `let … else`, `setze` writes slot `0` and leaves by the
    reason): the logged reason return of `setze` breaks the invariant --
    while `igPschlecht_alt` certified the program. -/
theorem igPschlecht_verletzt : ∃ M : RufMaschineG igD,
    RufErreichbarG igPschlecht igO 0 (RufStartG igPschlecht igSp igInit) M ∧
    ¬ Zielsatz.InvAmGrundG igPschlecht M := by
  obtain ⟨M3, s0, log, hr3, hz3, hw3, hoff3, hsl3⟩ := igVorlauf igRumpfSchlecht
  obtain ⟨M4, s4, hZ4⟩ := w_blatt (P := igPschlecht) (O := igO) (passes := 0) hz3 igS0 igGrund
    .nil rfl rfl (igHeld hoff3) _ _ rfl
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff4 : offen (M4.faeden 0).spur = [()] := by
    rw [hZ4.spur]
    exact ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen.trans
      (by rw [hw3]; exact hoff3)
  obtain ⟨M5, s5, hG5⟩ := w_rueckGrundP (P := igPschlecht) (O := igO) (passes := 0) hZ4.1 _ _ rfl
    (PopGrund.sonst igErr .nil (.dann .nil (.ende igTail)) .nil rfl) ⟨0, Nat.zero_lt_one⟩
    (List.Perm.refl igL) .nil rfl (by rw [← hZ4.1]; exact igHeld hoff4)
  refine ⟨M5, .schritt _ _ _ (.schritt _ _ _ hr3 s4) s5, fun h => ?_⟩
  have h3 := h 0 _ (by rw [hG5.1]; exact List.mem_cons_self) _ _ _ _ _ rfl ()
    (List.mem_singleton.mpr rfl) rfl
  revert h3
  rw [hZ4.welt, hw3]
  simp only [InvHaelt, World.schreibSlot, World.merke, World.storeSlot, World.lese, hsl3, igSp, igIdx, igWert, List.map_append, List.append_assoc, eval, Zahl.weiter, List.cons_append, List.nil_append, igPschlecht, igP, igInv, ↓reduceIte, Int.reduceEq, imp_false, Bool.not_eq_true]
  rfl

/-- **`igGut_zeuge`**: on a machine of `igPgut` reached in six steps
    (thread 0: `haupt` calls `setze` through `let … else`, `setze` writes
    both slots and leaves by the reason), the logged reason return of
    `setze` meets the invariant it owes BY THE THEOREM
    (`igPgut_zertifiziert`), at a world whose two slots hold `5`. -/
theorem igGut_zeuge : ∃ M : RufMaschineG igD,
    RufErreichbarG igPgut igO 0 (RufStartG igPgut igSp igInit) M ∧
    ∃ (r : Fin (igD.gruende igSetze)) (s0 s1 : World igD),
      RufEreignisF.why igSetze .nil r s0 s1 ∈ (M.faeden 0).log ∧
      InvAmRueck igPgut igSetze s1 ∧
      (s1.slots () 0 ()).n = 5 ∧ (s1.slots () 1 ()).n = 5 := by
  obtain ⟨M3, s0, log, hr3, hz3, hw3, hoff3, hsl3⟩ := igVorlauf igRumpfGut
  obtain ⟨M4, s4, hZ4⟩ := w_blatt (P := igPgut) (O := igO) (passes := 0) hz3 igS0 (.cons igS1 igGrund)
    .nil rfl rfl (igHeld hoff3) _ _ rfl
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff4 : offen (M4.faeden 0).spur = [()] := by
    rw [hZ4.spur]
    exact ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen.trans
      (by rw [hw3]; exact hoff3)
  have e4 := hZ4.1
  obtain ⟨M5, s5, hZ5⟩ := w_blatt (P := igPgut) (O := igO) (passes := 0) e4 igS1 igGrund
    .nil rfl rfl (by rw [← e4]; exact igHeld hoff4) _ _ rfl
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff5 : offen (M5.faeden 0).spur = [()] := by
    rw [hZ5.spur]
    exact ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen.trans
      hoff4
  obtain ⟨M6, s6, hG6⟩ := w_rueckGrundP (P := igPgut) (O := igO) (passes := 0) hZ5.1 _ _ rfl
    (PopGrund.sonst igErr .nil (.dann .nil (.ende igTail)) .nil rfl) ⟨0, Nat.zero_lt_one⟩
    (List.Perm.refl igL) .nil rfl (by rw [← hZ5.1]; exact igHeld hoff5)
  have hr6 : RufErreichbarG igPgut igO 0 (RufStartG igPgut igSp igInit) M6 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ hr3 s4) s5) s6
  obtain ⟨r, a, b, hm, hb⟩ : ∃ (r : Fin (igD.gruende igSetze)) (a b : World igD),
      RufEreignisF.why igSetze .nil r a b ∈ (M6.faeden 0).log ∧ b = M5.weltVon 0 := by
    rw [hG6.1]; exact ⟨_, _, _, List.mem_cons_self, rfl⟩
  refine ⟨M6, hr6, r, a, b, hm, (igPgut_zertifiziert M6 hr6).2 0 _ hm _ _ _ _ _ rfl, ?_, ?_⟩
  · rw [hb, hZ5.welt, hZ4.welt, hw3]
    simp only [World.schreibSlot, World.merke, World.storeSlot, World.lese, hsl3, igSp, igIdx, igWert, List.map_append, List.append_assoc, eval, Zahl.weiter, List.cons_append, List.nil_append, dite_eq_ite, Int.reduceEq, ↓reduceIte, ite_self]
    rfl
  · rw [hb, hZ5.welt, hZ4.welt, hw3]
    simp only [World.schreibSlot, World.merke, World.storeSlot, World.lese, hsl3, igSp, igIdx, igWert, List.map_append, List.append_assoc, eval, Zahl.weiter, List.cons_append, List.nil_append, dite_eq_ite, ↓reduceIte, Int.reduceEq]
    rfl

#print axioms Gabbro.Grammatik.igPgut_frag
#print axioms Gabbro.Grammatik.igPgut_fuss
#print axioms Gabbro.Grammatik.igHaupt_fall
#print axioms Gabbro.Grammatik.igPgut_koerper
#print axioms Gabbro.Grammatik.igPschlecht_koerper
#print axioms Gabbro.Grammatik.igPgut_inv
#print axioms Gabbro.Grammatik.igPschlecht_inv
#print axioms Gabbro.Grammatik.igPgut_invGrund
#print axioms Gabbro.Grammatik.igPgut_zertifiziert
#print axioms Gabbro.Grammatik.igPschlecht_alt
#print axioms Gabbro.Grammatik.igPschlecht_nicht_invGutGrund
#print axioms Gabbro.Grammatik.igVorlauf
#print axioms Gabbro.Grammatik.igPschlecht_verletzt
#print axioms Gabbro.Grammatik.igGut_zeuge

end Gabbro.Grammatik
