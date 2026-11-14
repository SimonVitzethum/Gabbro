module

public import Grammatik.Logik.Fortschritt.KostenG
public import Grammatik.Proben.InvZeuge.Teil1
public import Grammatik.Zielsatz.Kern.Spec.Teil1

@[expose] public section

namespace Gabbro.Grammatik

/-! A writer restores two slots and owes their equality invariant. Its old
    body-only price was 7; the equality with its two loads adds exactly 5.
    This fixture also exercises the declared-cost consumer and `ZeitAb`. -/

instance c05_fn_deq : DecidableEq ivD.Fn := inferInstanceAs (DecidableEq IvFn)

/-- The same body, at zero and at its actual return-predicate price. -/
theorem kostenEpilog_zeuge :
    schuldet (D := ivD) ivSetze () = true ∧
    kostenEpilog ivPgut ivSetze = kostenExpr ivInv ∧
    kostenExpr ivInv = 5 ∧
    kostenEnd 0 (fun _ => 0) 0 (ivPgut.rumpf ivSetze) = 7 ∧
    kostenTief ivPgut 0 1 ivSetze = 7 + kostenExpr ivInv ∧
    7 < kostenTief ivPgut 0 1 ivSetze := by
  decide

/-- All declarations cover the body and every value-return epilogue. -/
def c05Decl : ivD.Fn → Nat
  | .haupt => 25
  | .setze => 12
  | .nichts => 1

theorem kostenEpilog_deklaration_zeuge :
    kostenPasst ivPgut 0 c05Decl ivFs = true ∧
    kostenPasst ivPgut 0 (fun g => if g = ivSetze then 7 else c05Decl g) ivFs = false := by
  decide

/-- A reached writer frame takes three own steps (two writes and the
    value return). Entry, admission and activity hold together; both the
    computed and declared bounds apply, and `ZeitAb` holds at that entry. -/
theorem kostenEpilog_rahmen_zeuge :
    ∃ (M1 M4 : RufMaschineG ivD) (rho : Env ivD (ivD.params ivSetze)) (s0 : World ivD)
      (run : SegLauf ivPgut ivO 0 M1 M4),
      Eintritt ivPgut 0 ivSetze rho s0 1 M1 ∧
      rufTief ivPgut 1 ivSetze = true ∧
      aktivVor 0 1 run ∧
      segZaehle run 0 = 3 ∧
      segZaehle run 0 ≤ kostenTief ivPgut 0 1 ivSetze ∧
      segZaehle run 0 ≤ c05Decl ivSetze ∧
      Zielsatz.ZeitAb ivPgut ivO 0 M1 := by
  obtain ⟨M1, s1, hZ1⟩ := w_rufEnde (P := ivPgut) (O := ivO) (passes := 0)
    (ivM0_faden0 ivRumpfGut) ivSetze .nil ivHp rfl ivHauptRest .nil rfl (ivHeld ivOffen0)
  have hoff1 : offen (M1.faeden 0).spur = [()] := by
    rw [hZ1.spur, (Erw.lese _ _ _).offen]
    exact ivOffen0
  have e1 := hZ1.1
  obtain ⟨M2, s2, hZ2⟩ := w_blatt (P := ivPgut) (O := ivO) (passes := 0) e1 ivS0
    (.cons ivS1 ivRetS) .nil rfl rfl (by rw [← e1]; exact ivHeld hoff1) _ _ rfl
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
  obtain ⟨M4, s4, _⟩ := w_rueckP (P := ivPgut) (O := ivO) (passes := 0) e3 _ _ rfl
    (PopArt.wie rfl) .empty (List.Perm.refl _) _ rfl
    (by show HeldIn ivL _; rw [← e3]; exact ivHeld hoff3)
  let run : SegLauf ivPgut ivO 0 M1 M4 :=
    .schritt _ _ 0 (.schritt _ _ 0 (.schritt _ _ 0 .start s2) s3) s4
  have hE : Eintritt ivPgut 0 ivSetze _ _ 1 M1 :=
    ⟨by rw [e1], by rw [e1]; rfl⟩
  have hadm : rufTief ivPgut 1 ivSetze = true := by decide
  have hA : aktivVor 0 1 run := by
    simp only [run, aktivVor, true_and]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [e1]
      simp only [List.length_cons]
      omega
    · rw [e2]
      simp only [List.length_cons]
      omega
    · rw [e3]
      simp only [List.length_cons]
      omega
  refine ⟨M1, M4, _, _, run, hE, hadm, hA, rfl,
    frame_schritte_beschraenkt ivPgut ivO 0 0 ivSetze 0 hadm hE run hA,
    kosten_passt_deklaration ivPgut ivO 0 c05Decl ivFs
      kostenEpilog_deklaration_zeuge.1 0 ivSetze (ivFs_voll _) hE run hA, ?_⟩
  intro f g n rho s0 k hadm hE M2 run hA
  exact frame_schritte_beschraenkt ivPgut ivO 0 f g n hadm hE run hA

#print axioms kostenEpilog_zeuge
#print axioms kostenEpilog_deklaration_zeuge
#print axioms kostenEpilog_rahmen_zeuge

end Gabbro.Grammatik
