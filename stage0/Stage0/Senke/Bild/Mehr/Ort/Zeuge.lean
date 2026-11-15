/-
  File:      stage0/Stage0/Senke/Bild/Mehr/Ort/Zeuge.lean
  Subject:   Witnesses of the commit of one memory statement (package MT2) and of one segment (MT3) on the call fixture `t4`: thread `0` starts
             the callee `t4G` (`konto[0] := 5; return 3`) at the start machine. All premises of `randG_ort` hold
             jointly -- the write `konto[0] := 5` is a memory statement whose carriers lie in `C` (every carrier),
             it ends normally, machine G stands at the boundary in front of it, the current machine holds the
             thread's frame and a world agreeing on `C` -- and machine G's thread takes the write's steps to the
             boundary in front of `return 3`, at a world agreeing with the sequential one on `C`.
-/
module
public import Stage0.Senke.Bild.Mehr.Ort.Segment
public import Stage0.Senke.Bild.Rek.Zeuge
@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Gabbro.Grammatik Gabbro.Stage0.Senke Gabbro.Stage0.Senke.BildLauf

/-- Every thread starts the callee `t4G`. -/
def zeugeInitG : Faden → Σ g : t4D.Fn, Env t4D (t4D.params g) := fun _ => ⟨t4G, Env.nil⟩

/-- Every carrier of the fixture. -/
def zeugeAlleC : t4D.Tab ⊕ t4D.Glob → Prop := fun _ => True

/-- **The commit, all premises jointly.** -/
theorem randG_ort_zeuge :
    ∃ (σ1 : World t4D) (N' : RufMaschineG t4D) (σ1' : World t4D),
      execStmt t4O 0 keinRuf t4GSchreib (t4Sp.welt []) Env.nil = .ok σ1 Env.nil ∧
      RufLaufG t4P t4O 0 0 (RufStartG t4P t4Sp zeugeInitG) N' ∧
      RandG 0 [] t4G Env.nil (t4Sp.welt []) (fun _ => False) t4GRest N' σ1' Env.nil ∧
      OrtGleich zeugeAlleC σ1 σ1' := by
  have h0 : RandG 0 [] t4G Env.nil (t4Sp.welt []) (fun _ => False) (t4P.rumpf t4G)
      (RufStartG t4P t4Sp zeugeInitG) (t4Sp.welt []) Env.nil :=
    randG_start t4P t4Sp (init := zeugeInitG) (thr := 0) (f := t4G) (rho := Env.nil) (fun _ => False) rfl rfl
      (fun _ _ => rfl)
  rw [t4GRumpf_eq] at h0
  obtain ⟨σ1, hex⟩ : ∃ σ1 : World t4D,
      execStmt t4O 0 keinRuf t4GSchreib (t4Sp.welt []) Env.nil = .ok σ1 Env.nil := ⟨_, rfl⟩
  have hs : StmtR (fun _ => False) (fun _ => False) true t4GSchreib :=
    StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)
  have hC : OrtPrem zeugeAlleC t4GSchreib := ⟨trivial, fun _ _ => trivial⟩
  obtain ⟨N', σ1', hl, hR, hσ1, _⟩ := randG_ort (rufOk_leer t4P t4O 0 0 (fun _ => False) keinRuf) hs hC hex h0
    (OrtGleich.refl _) rfl rfl (fun _ h => (h : False).elim)
  exact ⟨σ1, N', σ1', hex, hl, hR, hσ1⟩

/-- **The commit of a segment, all premises jointly**: the callee's body up to `return 3` is one segment (the write
    `konto[0] := 5`), and machine G's thread commits it from the start machine. -/
theorem randG_segment_zeuge :
    ∃ (σ1 : World t4D) (N' : RufMaschineG t4D) (σ1' : World t4D),
      Segment t4O 0 keinRuf (fun _ => False) (fun _ => False) zeugeAlleC (t4P.rumpf t4G) (t4Sp.welt []) Env.nil
        t4GRest σ1 Env.nil ∧
      RufLaufG t4P t4O 0 0 (RufStartG t4P t4Sp zeugeInitG) N' ∧
      RandG 0 [] t4G Env.nil (t4Sp.welt []) (fun _ => False) t4GRest N' σ1' Env.nil ∧
      OrtGleich zeugeAlleC σ1 σ1' := by
  have h0 : RandG 0 [] t4G Env.nil (t4Sp.welt []) (fun _ => False) (t4P.rumpf t4G)
      (RufStartG t4P t4Sp zeugeInitG) (t4Sp.welt []) Env.nil :=
    randG_start t4P t4Sp (init := zeugeInitG) (thr := 0) (f := t4G) (rho := Env.nil) (fun _ => False) rfl rfl
      (fun _ _ => rfl)
  obtain ⟨σ1, hex⟩ : ∃ σ1 : World t4D,
      execStmt t4O 0 keinRuf t4GSchreib (t4Sp.welt []) Env.nil = .ok σ1 Env.nil := ⟨_, rfl⟩
  have hs : StmtR (fun _ => False) (fun _ => False) true t4GSchreib :=
    StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)
  have hC : OrtPrem zeugeAlleC t4GSchreib := ⟨trivial, fun _ _ => trivial⟩
  have hk : Segment t4O 0 keinRuf (fun _ => False) (fun _ => False) zeugeAlleC (t4P.rumpf t4G) (t4Sp.welt [])
      Env.nil t4GRest σ1 Env.nil := by
    rw [t4GRumpf_eq]
    exact .schritt t4GSchreib t4GRest t4GRest _ σ1 σ1 Env.nil Env.nil Env.nil hs hC hex (.halt _ _ _)
  obtain ⟨N', σ1', hl, hR, hσ1, _⟩ := randG_segment_ein (rufOk_leer t4P t4O 0 0 (fun _ => False) keinRuf) hk h0
    (OrtGleich.refl _) rfl rfl (fun _ h => (h : False).elim)
  exact ⟨σ1, N', σ1', hk, hl, hR, hσ1⟩

end Gabbro.Stage0.Senke.BildMehr
