/- The t4B bind-inside-if fixture: the image half, conditional on a body image. -/
module
public import Stage0.Senke.Bild.Block.Emitted
public import Stage0.Senke.Bild.Rek.ZeugeDann
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Stage0.Senke Runner.IR Runner.Mem

variable [Kern]

/-- Image half of `bild_dann_zeuge`. Given only a valid image body boundary of the
    fixture, reach the call inside its if and prove the complete image/G call window.
    The model's joint witness supplies the terminating call; no compiler is run in
    the kernel. What remains abstract is a concrete loaded memory, its code layout,
    and the corresponding `BodyFrame.Ok`/`RandIR` premises. This is a conditional
    image witness, not a claim that those memory premises were constructed here. -/
theorem bild_block_zeuge {Y : Lay t4D} [TorOK Y t4O] [SichtOK t4O]
    {A : t4D.Fn → Nat} {C : t4D.Fn → List II} {Lm : Nat}
    (hc : BildCodes Y t4P 0 A C Lm) {fp rp cfp pc : Runner.W} {K Ks : Nat}
    {ens : List II × Nat} {m : Runner.Mem}
    (hB : (rumpfRahmen Y t4O 0 t4P A C Lm 1 t4B fp K Ks rp cfp zeugeWelt Env.nil [] ens).Ok)
    (hIR : (rumpfRahmen Y t4O 0 t4P A C Lm 1 t4B fp K Ks rp cfp zeugeWelt Env.nil [] ens).RandIR
      (t4P.rumpf t4B) pc m zeugeWelt Env.nil) :
    ∃ (n1 n2 : Nat) (pcC : Runner.W) (mC : Runner.Mem) (MC : RufMaschineG t4D)
      (σ2 : World t4D) (v : ErgVal t4D (t4D.erg t4G)),
      let B := ((rumpfRahmen Y t4O 0 t4P A C Lm 1 t4B fp K Ks rp cfp zeugeWelt Env.nil [] ens).suffix n1).suffix n2
      Star ⟨pc, fp⟩ m ⟨pcC, fp⟩ mC ∧
      RufLaufG t4P t4O 0 0 (RufStartG t4P t4Sp zeugeInitB) MC ∧
      RandDannL B 0 [] Env.nil zeugeWelt (fun _ => False) t4BindBlock
        (.dann .nil (.ende t4BRest)) pcC mC MC zeugeWeltB Env.nil ∧
      BlockFenster B Lm 0 t4G (rufWelt t4P t4G zeugeWeltB [] zeugeArgs)
        (rufEnv t4G zeugeWeltB [] zeugeArgs Env.nil) 0
        ⟨t4B, Env.nil, zeugeWelt, ⟨false, [], [], Env.nil,
          .wartet t4BindRest (.dann .nil (.ende t4BRest))⟩⟩ [] (fun _ => False)
        (t4P.rumpf t4G) (rufWelt t4P t4G zeugeWeltB [] zeugeArgs)
        (rufEnv t4G zeugeWeltB [] zeugeArgs Env.nil) pcC mC MC
        (fun pcN mN M3 => RandDannL B 0 [] Env.nil zeugeWelt (fun _ => False) t4BindRest
          (.schrumpf (.dann .nil (.ende t4BRest))) pcN mN M3 σ2 (.cons (ergWert rfl v) Env.nil)) := by
  have hG : RandGL 0 [] t4B Env.nil zeugeWelt (fun _ => False) (t4P.rumpf t4B)
      (RufStartG t4P t4Sp zeugeInitB) zeugeWelt Env.nil :=
    randGL_von (randG_start t4P t4Sp (init := zeugeInitB) (thr := 0) (f := t4B)
      (rho := Env.nil) (fun _ => False) rfl rfl (fun _ _ => rfl))
  obtain ⟨n1, n2, pcC, mC, MC, st, hl, hC⟩ := randL_ite_eintritt hB
    (show RandL _ 0 [] Env.nil zeugeWelt (fun _ => False)
      (.cons (.ite .tru t4BindBlock .nil) t4BRest) pc m
      (RufStartG t4P t4Sp zeugeInitB) zeugeWelt Env.nil from ⟨hIR, hG⟩) rfl
  obtain ⟨hg, _, _, _, σ2, v, _, _, hR, _, _, _⟩ := bild_dann_zeuge
  have hkC : Zerlegung (rufZRahmen Y t4O 0 t4P A 0 t4G (rufWelt t4P t4G zeugeWeltB [] zeugeArgs)
      (rufEnv t4G zeugeWeltB [] zeugeArgs Env.nil)) (fun _ => False) (TiefAlle t4P (fun _ => False) 0)
      (t4P.rumpf t4G) (rufWelt t4P t4G zeugeWeltB [] zeugeArgs)
      (rufEnv t4G zeugeWeltB [] zeugeArgs Env.nil) (t4P.rumpf t4G)
      (rufWelt t4P t4G zeugeWeltB [] zeugeArgs) (rufEnv t4G zeugeWeltB [] zeugeArgs Env.nil) :=
    Zerlegung.halt _ _ _
  exact ⟨n1, n2, pcC, mC, MC, σ2, v, st, hl, hC,
    randDannL_bindCall_ein_aus ((hB.suffix n1).suffix n2) hc rfl rfl rfl (by decide)
      leseblind_t4O hC hR hg hkC⟩

#print axioms bild_block_zeuge

end Gabbro.Stage0.Senke.BildLauf
