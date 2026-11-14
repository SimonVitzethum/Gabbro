/-
  File:      stage0/Stage0/Senke/Bild/Ruf/ZeugeHardware.lean
  Subject:   **Witness of the discharged oracle premise and of the fragment check** (reviews H1/H3, M1, partial H2) on
             the call fixture `t4P` of `RufAdaequatRufG` (four functions; the plain caller `t4F` calls `t4G`), with
             the COUNTING oracle `zaehlOrakel` (its foreign answer is the length of the trace without reads: it
             answers from the history, and a further question changes its answer, `zaehlOrakel_fragt`). Jointly:
             * the fragment check passes on the whole program by computation (`t4P_programmRB`, `rfl` over the four
               bodies -- no compiler run), so every body lies in the call fragment (`t4P_endR`) and the program has
               no foreign call (`t4P_fremdFrei`);
             * the counting oracle meets the goal theorem's hardware assumptions (`zaehl_hardware`); the program
               premise of the image theorems holds for it as for every oracle (`leseblindP_alle`), and also from the
               hardware assumptions and the check (`leseblindP_hardware`);
             * the call obligation up to read events holds for `rufAt 1` under that oracle, and machine G realises
               the call step of `t4F` from a sequential world `≈` to (and different from) its start world.
             What it does not contain (H2, what remains): an `Emitted` value. One needs a `Frontend.Source text`
             (the parser's and elaborator's proofs over a source string), the compiler's equations (`Compiled`) and
             the emission equation `Senke.bild … = .ok image`; each is a run of the compiler, so an image-level
             instance of `Emitted.bild_ziel_ruf` evaluates the front end in the kernel. Below `Emitted`, the image
             side of the fixture (`BodyFrame.Ok` with `FunSpec` for every function, `RandIR` with the lowered code
             loaded in a runner memory) is not built here either.
-/
module
public import Stage0.Senke.Bild.Ruf.Zeuge
public import Stage0.Senke.Bild.Ruf.Hardware
public import Stage0.Senke.Bild.Rek.EndRBVoll
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Stage0.Senke

/-! ## The fragment check on the fixture -/

/-- The fixture's four functions, enumerated. -/
theorem t4_voll : ∀ g : t4D.Fn, g ∈ [t4G, t4F, t4B, t4L] := by
  have h : ∀ g : Fin 4, g ∈ ([0, 1, 2, 3] : List (Fin 4)) := by decide
  exact h

/-- **The check passes on the whole fixture, by computation.** -/
theorem t4P_programmRB : programmRB t4P (fun _ => false) [t4G, t4F, t4B, t4L] = true := rfl

/-- Every body of the fixture lies in the call fragment (the premise of `tiefAlle_frag`). -/
theorem t4P_endR (A : t4D.Lock → Prop) : ∀ g : t4D.Fn, EndR A (fun _ => True) (t4P.rumpf g) :=
  endR_programmRB (fun _ => false) (fun _ h => absurd h Bool.false_ne_true) t4_voll t4P_programmRB

/-- The fixture has no foreign call. -/
theorem t4P_fremdFrei : FremdFrei t4P :=
  fremdFrei_programmRB (fun _ => false) t4_voll t4P_programmRB

/-! ## The counting oracle under the hardware assumptions -/

/-- The fixture's declared foreign ensures (there is no foreign item). -/
def zaehlQ : AxEns t4D := fun a => nomatch a

/-- **The counting oracle meets the goal theorem's hardware assumptions** on the fixture's declaration. -/
theorem zaehl_hardware [hw : RootNativeFloat.Hardware] :
    Zielsatz.HardwareAnnahmen (zaehlOrakel t4D) zaehlQ := by
  refine And.intro ?_ (And.intro (zaehlOrakel_regLokal t4D) (And.intro ?_ hw))
  · intro a
    exact nomatch a
  · intro a
    exact nomatch a

/-- The leaf callee returns under the counting oracle, with a symbolic start world (no kernel run). -/
theorem t4G_ruf_kehrt_zaehl (σ : World t4D) : ∃ (σ' : World t4D) (v : ErgVal t4D (t4D.erg t4G)),
    rufAt t4P (zaehlOrakel t4D) 0 1 t4G σ Env.nil = .ok σ' v := by
  obtain ⟨σ', v, hb⟩ : ∃ (σ' : World t4D) (v : ErgVal t4D (t4D.erg t4G)),
      execEnd (V := vertragVon t4D t4G) (zaehlOrakel t4D) 0 (rufAt t4P (zaehlOrakel t4D) 0 0)
        (t4P.rumpf t4G) σ Env.nil = .zurueck σ' v := by
    change ∃ σ' v, execEnd (V := vertragVon t4D t4G) (zaehlOrakel t4D) 0 (rufAt t4P (zaehlOrakel t4D) 0 0)
      t4GRumpf σ Env.nil = .zurueck σ' v
    simp only [t4GRumpf, execEnd, execStmt]
    exact ⟨_, _, rfl⟩
  exact ⟨σ', v, rufAt_t4D_ok_of_body rfl rfl hb⟩

/-- **P3 with the discharged premise, all jointly**: from the hardware assumptions and the fragment check alone, the
    call obligation up to read events holds for `rufAt 1` under the counting oracle (callee `t4G` admitted), and
    machine G, started at the start world, realises the caller's call step from the sequential world after a read
    of `konto`, standing behind the call at a world `≈` to the sequential one. -/
theorem zaehl_ruf_zeuge [RootNativeFloat.Hardware] :
    LeseblindP t4P (zaehlOrakel t4D) ∧ Tief t4P (fun _ => False) 1 t4G ∧
    RufOkGleich t4P (zaehlOrakel t4D) 0 0 (fun _ => False) (rufAt t4P (zaehlOrakel t4D) 0 1)
      (Tief t4P (fun _ => False) 1) ∧
    ∃ (σ1 σm1 : World t4D) (M' : RufMaschineG t4D),
      execStmt (zaehlOrakel t4D) 0 (rufAt t4P (zaehlOrakel t4D) 0 1) t4Ruf zeugeWeltL Env.nil = .ok σ1 Env.nil ∧
      RufLaufG t4P (zaehlOrakel t4D) 0 0 (RufStartG t4P t4Sp zeugeInit) M' ∧ WeltGleich σ1 σm1 ∧
      RandG 0 [] t4F Env.nil (t4Sp.welt []) (fun _ => False) t4FRest M' σm1 Env.nil := by
  have hO : LeseblindP t4P (zaehlOrakel t4D) := leseblindP_alle t4P (zaehlOrakel t4D)
  have hRuf : RufOkGleich t4P (zaehlOrakel t4D) 0 0 (fun _ => False) (rufAt t4P (zaehlOrakel t4D) 0 1)
      (Tief t4P (fun _ => False) 1) :=
    rufOk_gleich_tief hO 0 (fun _ => False) 1
  obtain ⟨σ1, v, hG⟩ := t4G_ruf_kehrt_zaehl zeugeWeltL
  have hex : execStmt (zaehlOrakel t4D) 0 (rufAt t4P (zaehlOrakel t4D) 0 1) t4Ruf zeugeWeltL Env.nil =
      .ok σ1 Env.nil := by
    -- Keep the read world folded so the symbolic handler return matches.
    simp only [t4Ruf, execStmt, Args.orte, lese_nil, evalArgs, hG]
  have hs : StmtR (fun _ => False) (Tief t4P (fun _ => False) 1) false t4Ruf :=
    StmtR.call t4Ruf t4G rfl (t4G_tief _)
  have hG : RandG 0 [] t4F Env.nil (t4Sp.welt []) (fun _ => False) (.cons t4Ruf t4FRest)
      (RufStartG t4P t4Sp zeugeInit) zeugeWelt Env.nil :=
    randG_start t4P t4Sp (init := zeugeInit) (thr := 0) (f := t4F) (rho := Env.nil) (fun _ => False) rfl rfl
      (fun _ _ => rfl)
  have hw : WeltGleich zeugeWeltL zeugeWelt := (weltGleich_lese zeugeWelt [] [.inl ()]).symm
  have hGL : RandGL 0 [] t4F Env.nil (t4Sp.welt []) (fun _ => False) (.cons t4Ruf t4FRest)
      (RufStartG t4P t4Sp zeugeInit) zeugeWeltL Env.nil :=
    ⟨zeugeWelt, hw, hG⟩
  obtain ⟨M', hl, σm1, hw1, hG'⟩ := randGL_schritt (P := t4P) hO.rs hRuf hs hex hGL
  exact ⟨hO, t4G_tief _, hRuf, σ1, σm1, M', hex, hl, hw1, hG'⟩

#print axioms zaehl_ruf_zeuge
#print axioms t4P_endR

end Gabbro.Stage0.Senke.BildLauf
