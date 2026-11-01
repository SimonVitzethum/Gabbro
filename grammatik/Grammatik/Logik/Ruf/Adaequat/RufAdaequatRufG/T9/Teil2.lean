module

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T8
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T9.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-- The bind witness up to its waiting state: `endeEntf`, `dannIteWahr`,
    `dannBindCall` -- the caller frame of `t4B` now WAITS (`wartet`) below
    the callee frame of `t4G`. -/
theorem t4B_wartet :
    ∃ M3 : RufMaschineG t4D, RufLaufG t4P t4O 0 0 (t4M t4B t4BRumpf) M3 ∧
      ∃ caller : RufRahmenG t4D, (M3.faeden 0).stapel = [caller, t4Unten] ∧
        caller.f = t4B ∧ caller.wartend = true ∧ (M3.faeden 0).kopf.f = t4G := by
  have hZ0 : ZustandG (t4M t4B t4BRumpf) 0 [t4Unten] t4B Env.nil (t4Sp.welt []) []
      (Env.nil : Env t4D []) (.ende t4BRumpf) ((t4M t4B t4BRumpf).weltVon 0) := ⟨rfl, rfl⟩
  obtain ⟨M1, hs1, hZ1⟩ := w_endeEntf (P := t4P) (O := t4O) (passes := 0) hZ0.1
    (.ite .tru t4BindBlock .nil) (.ret (.val (t4Lit 9 (by decide) (by decide))) List.Perm.nil)
    Env.nil rfl rfl
  obtain ⟨M2, hs2, hZ2⟩ := w_iteWahr (P := t4P) (O := t4O) (passes := 0) hZ1.1
    .tru t4BindBlock .nil .nil
    (.ende (.ret (.val (t4Lit 9 (by decide) (by decide))) List.Perm.nil)) Env.nil rfl rfl
    (fun L => nomatch L)
  obtain ⟨M3, hs3, hZ3⟩ := w_bindCall (P := t4P) (O := t4O) (passes := 0) hZ2.1
    t4G .nil rfl (t4Hp t4B) rfl (.cons (.assignSlot () () t4Idx1x (.var .here) rfl t4Darf) .nil)
    (.dann .nil (.ende (.ret (.val (t4Lit 9 (by decide) (by decide))) List.Perm.nil))) Env.nil
    rfl (fun L => nomatch L)
  refine ⟨M3, RufLaufG.schritt hs1 (RufLaufG.schritt hs2 (RufLaufG.einzeln hs3)), _,
    by rw [hZ3.1], rfl, rfl, by rw [hZ3.1]⟩

/-- **AGREEMENT (formerly the finding `befund_wartet`).** On the bind
    witness, from the state in which the caller of `t4B` WAITS below the
    callee: no machine reachable by steps of the thread has a waiting head
    (the verbatim pops can no longer restore the waiting caller; the
    deadlock run is gone), and the sequential semantics returns `9`. -/
theorem wartet_einig :
    (∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4B).erg),
      execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4BRumpf ((t4M t4B t4BRumpf).weltVon 0) Env.nil =
        .zurueck σ' v ∧ (show Zahl 0 100 from v).n = 9) ∧
    ∃ M3 : RufMaschineG t4D, RufLaufG t4P t4O 0 0 (t4M t4B t4BRumpf) M3 ∧
      (∃ caller : RufRahmenG t4D, (M3.faeden 0).stapel = [caller, t4Unten] ∧
        caller.f = t4B ∧ caller.wartend = true) ∧
      ∀ M' : RufMaschineG t4D, RufLaufG t4P t4O 0 0 M3 M' →
        ∀ g, (M'.faeden g).kopf.wartend = false := by
  refine ⟨⟨_, _, rfl, rfl⟩, ?_⟩
  obtain ⟨M3, hl3, caller, hst, hf, hw, _⟩ := t4B_wartet
  refine ⟨M3, hl3, ⟨caller, hst, hf, hw⟩, ?_⟩
  intro M' hl g
  exact (rufLaufG_sauber (hl3.trans hl) (t4M_sauber t4B t4BRumpf) g).kopf_wartend


/-! ## 13. NOTE: the machine realises `rufRumpf`, not `rufAt`

    The program semantics `exec` calls through `rufAt`, which checks the
    callee's `requires` (and `ensures`, and the owed invariants) and READS
    their places. The machine checks no contract (booked in
    `RufMaschineG.lean`'s CUTS). So G agrees with `exec` only where every
    contract holds and reads nothing -- a design cut of G, not a defect of
    its steps, shown here on the plain witness with `requires false`. -/

/-- The plain witness program with every `requires` false. -/
def t4Pk : Programm t4D :=
  { t4P with requires := fun _ => .fls }

theorem befund_vertrag :
    execEnd t4O 0 (rufAt t4Pk t4O 0 2) t4FRumpf ((t4M t4F t4FRumpf).weltVon 0) Env.nil =
      .logik (.vorbedingung t4G) ∧
    ∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4F).erg),
      execEnd t4O 0 (rufRumpf t4Pk t4O 0 1) t4FRumpf ((t4M t4F t4FRumpf).weltVon 0) Env.nil =
        .zurueck σ' v ∧
      ∃ (M' : RufMaschineG t4D) (ext : List (RufEreignisF t4D)),
        RufLaufG t4Pk t4O 0 0 (t4M t4F t4FRumpf) M' ∧
        M'.faeden 0 = ⟨[], t4Unten, σ'.spur,
          RufEreignisF.rueck t4F Env.nil v (t4Sp.welt []) σ' :: (ext ++ [])⟩ := by
  refine ⟨rfl, ?_⟩
  have hex : ∃ (σ' : World t4D) (v : ErgVal t4D (vertragVon t4D t4F).erg),
      execEnd t4O 0 (rufRumpf t4Pk t4O 0 1) t4FRumpf ((t4M t4F t4FRumpf).weltVon 0) Env.nil =
        .zurueck σ' v := ⟨_, _, rfl⟩
  obtain ⟨σ', v, hex⟩ := hex
  have hG : Tief t4Pk (fun _ => False) 1 t4G :=
    show EndR (fun _ => False) (Tief t4Pk (fun _ => False) 0) t4GRumpf from
      EndR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) (EndR.ret _ _)
  have hb : EndR (fun _ => False) (Tief t4Pk (fun _ => False) 1) t4FRumpf :=
    EndR.cons _ _ (StmtR.call _ t4G rfl hG)
      (EndR.cons _ _ (StmtR.blatt _ (BlattG.assignSlot _ _ _ _ _ _)) (EndR.ret _ _))
  obtain ⟨M', ext, hl, hf, _, _⟩ := rufG_adaequat_ruf t4Pk t4O 0 1 (t4M t4F t4FRumpf) 0 t4F
    Env.nil (t4Sp.welt []) t4Unten [] [] [] Env.nil t4FRumpf (fun _ => False) hb rfl rfl t4_held
    (t4_frei t4F t4FRumpf) σ' v hex
  exact ⟨σ', v, hex, M', ext, hl, hf⟩



end Gabbro.Grammatik
