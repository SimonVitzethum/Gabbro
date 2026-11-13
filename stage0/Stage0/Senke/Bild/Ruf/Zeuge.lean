/-
  File:      stage0/Stage0/Senke/Bild/Ruf/Zeuge.lean
  Subject:   Witness of package P3 (the image theorem admits calls) on the call fixture `t4` of `RufAdaequatRufG`:
             the plain caller `g(); konto[1] := 7; return 9` with ONE call of the callee `konto[0] := 5; return 3`,
             contracts `true`, no locks, the read-blind fixture oracle. Jointly:
             * the oracle carries the named property (`leseblindOK_t4O`);
             * the call obligation up to read events holds for `rufAt` at depth 1 with the callees admitted there
               (`rufOk_gleich_tief`), and the callee IS admitted (`t4G_tief`), so the callee set is not empty;
             * the body's decomposed prefix takes the call as ONE step under the image's handler `rufAt 1`, in a frame
               `rumpfRahmen` of the fixture (`Zerlegung`, the premise `hk` of `Emitted.bild_ziel_tief`);
             * machine G, at the start machine with the start world, realises that call step from the sequential
               world after a read of `konto` -- a DIFFERENT world, `≈` to the start world (`lesegleich_zeuge`) -- and
               stands behind the call at a world `≈` to the sequential one (`randGL_schritt`).
             The call step reuses the symbolic callee return; no image or memory evaluation.
-/
module
public import Stage0.Senke.Bild.Ruf.RufOkGleich
public import Stage0.Senke.Bild.Gleich.RufAtZeuge
public import Stage0.Senke.Bild.Prolog
public import Stage0.Senke.Bild.StartG
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T8a
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Stage0.Senke

/-! ## The named oracle property is satisfiable -/

/-- The fixture's oracle carries the named property. -/
theorem leseblindOK_t4O : LeseblindOK t4O :=
  leseblindOK_von leseblind_t4O

/-- Every declaration has an oracle with the named property (the oracle that ignores the trace). -/
theorem leseblindOK_still (D : Deklaration) : LeseblindOK (stillesOrakel D) :=
  leseblindOK_von (leseblind_still D)

/-! ## The fixture, split at its call -/

/-- The call of the plain caller: `g();`. -/
def t4Ruf : Stmt t4D (vertragVon t4D t4F) false [] [] (nach t4D t4G []) :=
  .call t4G .nil (t4Hp t4F) rfl

/-- What remains of the plain caller behind the call: `konto[1] := 7; return 9`. -/
def t4FRest : Endblock t4D (vertragVon t4D t4F) false [] (nach t4D t4G []) :=
  .cons (.assignSlot () () t4Idx1 (t4Lit 7 (by decide) (by decide)) rfl t4Darf)
    (.ret (.val (t4Lit 9 (by decide) (by decide))) List.Perm.nil)

theorem t4FRumpf_eq : t4FRumpf = .cons t4Ruf t4FRest := rfl

/-- One thread start for every thread: the plain caller with no arguments. -/
def zeugeInit : Faden → Σ g : t4D.Fn, Env t4D (t4D.params g) :=
  fun _ => ⟨t4F, Env.nil⟩

/-- A layout of the fixture's world (the decomposed prefix does not read it). -/
def zeugeLay : Lay t4D where
  col := fun _ _ => 0
  ga := fun g => nomatch g
  lo := 0
  hi := 0
  tor := fun a => nomatch a
  byte := fun _ => none

/-- The frame of the plain caller's body at depth 2: callees run as `rufAt 1`. -/
abbrev zeugeRahmen : BodyFrame t4D :=
  rumpfRahmen zeugeLay t4O 0 t4P (fun _ => 0) (fun _ => []) 0 1 t4F 0 0 0 0 0 (t4Sp.welt []) Env.nil [] ([], 0)

/-! ## The witness -/

/-- **P3 witness, all premises jointly, with ONE call.** The call obligation up to read events for `rufAt 1` and the
    callees admitted at depth 1 (`t4G` among them); the decomposed prefix of the caller's body that takes the call as
    one step under `rufAt 1` from the read world `zeugeWeltL`; and machine G, from the start machine at the start
    world `zeugeWelt` (`≈` to `zeugeWeltL`, not equal), running the call by steps of thread `0` to the boundary behind
    it, at a world `≈` to the sequential world behind the call. -/
theorem bild_ruf_zeuge :
    LeseblindOK t4O ∧ Tief t4P (fun _ => False) 1 t4G ∧
    RufOkGleich t4P t4O 0 0 (fun _ => False) (rufAt t4P t4O 0 1) (Tief t4P (fun _ => False) 1) ∧
    ∃ (σ1 σm1 : World t4D) (M' : RufMaschineG t4D),
      Zerlegung zeugeRahmen (fun _ => False) (Tief t4P (fun _ => False) 1) t4FRumpf zeugeWeltL Env.nil
        t4FRest σ1 Env.nil ∧
      RufLaufG t4P t4O 0 0 (RufStartG t4P t4Sp zeugeInit) M' ∧ WeltGleich σ1 σm1 ∧
      RandG 0 [] t4F Env.nil (t4Sp.welt []) (fun _ => False) t4FRest M' σm1 Env.nil := by
  have hRuf : RufOkGleich t4P t4O 0 0 (fun _ => False) (rufAt t4P t4O 0 1) (Tief t4P (fun _ => False) 1) :=
    rufOk_gleich_tief leseblind_t4O 0 (fun _ => False) 1
  obtain ⟨σ1, v, hG⟩ := t4G_ruf_kehrt zeugeWeltL
  have hex : execStmt t4O 0 (rufAt t4P t4O 0 1) t4Ruf zeugeWeltL Env.nil = .ok σ1 Env.nil := by
    -- Keep the read world folded so the symbolic handler return matches.
    simp only [t4Ruf, execStmt, Args.orte, lese_nil, evalArgs, hG]
  have hs : StmtR (fun _ => False) (Tief t4P (fun _ => False) 1) false t4Ruf :=
    StmtR.call t4Ruf t4G rfl (t4G_tief _)
  have hk : Zerlegung zeugeRahmen (fun _ => False) (Tief t4P (fun _ => False) 1) t4FRumpf zeugeWeltL Env.nil
      t4FRest σ1 Env.nil := by
    rw [t4FRumpf_eq]
    exact Zerlegung.schritt t4Ruf t4FRest t4FRest zeugeWeltL σ1 σ1 Env.nil Env.nil Env.nil hs hex
      (Zerlegung.halt t4FRest σ1 Env.nil)
  have hG : RandG 0 [] t4F Env.nil (t4Sp.welt []) (fun _ => False) (.cons t4Ruf t4FRest)
      (RufStartG t4P t4Sp zeugeInit) zeugeWelt Env.nil :=
    randG_start t4P t4Sp (init := zeugeInit) (thr := 0) (f := t4F) (rho := Env.nil) (fun _ => False) rfl rfl
      (fun _ _ => rfl)
  have hw : WeltGleich zeugeWeltL zeugeWelt := (weltGleich_lese zeugeWelt [] [.inl ()]).symm
  have hGL : RandGL 0 [] t4F Env.nil (t4Sp.welt []) (fun _ => False) (.cons t4Ruf t4FRest)
      (RufStartG t4P t4Sp zeugeInit) zeugeWeltL Env.nil :=
    ⟨zeugeWelt, hw, hG⟩
  obtain ⟨M', hl, σm1, hw1, hG'⟩ := randGL_schritt leseblind_t4O hRuf hs hex hGL
  exact ⟨leseblindOK_t4O, t4G_tief _, hRuf, σ1, σm1, M', hk, hl, hw1, hG'⟩

#print axioms bild_ruf_zeuge

end Gabbro.Stage0.Senke.BildLauf
