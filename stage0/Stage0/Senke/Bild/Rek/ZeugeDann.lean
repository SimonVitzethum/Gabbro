/-
  File:      stage0/Stage0/Senke/Bild/Rek/ZeugeDann.lean
  Subject:   Witness of the block-position calls (package P5, parts 6 and 7) on the bind caller `t4B` of the call
             fixture `t4`: `if true { let x = g(); konto[1] := x } else { }; return 9`, the callee `t4G`
             (`konto[0] := 5; return 3`), contracts `true`, no locks, the read-blind fixture oracle. Jointly:
             * machine G, from the start machine of `t4B`, unfolds the `if` (`endeEntf`) and takes its `then` branch
               (`dannIteWahr`), and stands at the block-position boundary in front of `let x = g()` (`RandDannGL`);
             * the call `g()` ends normally under `rufAt 1` (the symbolic return `t4G_ruf_kehrt`);
             * the callee is admitted at depth 1 with recursion (`TiefAlle`), its decomposed prefix is trivial;
             * `randDannGL_bindCall_ein_aus`: machine G descends into the callee and returns, binding the returned
               value into the rest of the block, at the block-position boundary in front of `konto[1] := x`.
             No image, no memory, no compiler.
-/
module
public import Stage0.Senke.Bild.Rek.DannRueck
public import Stage0.Senke.Bild.Rek.Zeuge
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Stage0.Senke

/-- One thread start for every thread: the bind caller `t4B` with no arguments. -/
def zeugeInitB : Faden → Σ g : t4D.Fn, Env t4D (t4D.params g) :=
  fun _ => ⟨t4B, Env.nil⟩

/-- What remains of the bind caller behind its `if`: `return 9`. -/
def t4BRest : Endblock t4D (vertragVon t4D t4B) false [] [] :=
  .ret (.val (t4Lit 9 (by decide) (by decide))) List.Perm.nil

/-- What remains of the bind block behind `let x = g()`: `konto[1] := x`. -/
def t4BindRest : Block t4D (vertragVon t4D t4B) false [.int 0 100] [] [] :=
  .cons (.assignSlot () () t4Idx1x (.var .here) rfl t4Darf) .nil

/-- The world in front of the bind block: the start world after the read of the condition `true`. -/
abbrev zeugeWeltB : World t4D := zeugeWelt.lese [] (Expr.tru : Expr t4D [] [] .bool).orte

variable [Runner.IR.Kern]

/-- **Witness of the block-position calls, all premises jointly, with a symbolic call return.** The callee is admitted at
    depth 1 by `TiefAlle`; machine G reaches, from the start machine of `t4B`, the block-position boundary in front of
    `let x = g()`; the call ends normally under `rufAt 1` with `v`; and machine G descends into the callee and returns
    to the block-position boundary in front of `konto[1] := x`, with `x` bound to `v`, at a world `≈` to the call's
    world. -/
theorem bild_dann_zeuge :
    TiefAlle t4P (fun _ => False) 1 t4G ∧
    ∃ (M2 M1 M' : RufMaschineG t4D) (σ2 : World t4D) (v : ErgVal t4D (t4D.erg t4G)),
      RufLaufG t4P t4O 0 0 (RufStartG t4P t4Sp zeugeInitB) M2 ∧
      RandDannGL 0 [] t4B Env.nil zeugeWelt (fun _ => False) t4BindBlock (.dann .nil (.ende t4BRest)) M2
        zeugeWeltB Env.nil ∧
      rufAt t4P t4O 0 1 t4G (zeugeWeltB.lese [] zeugeArgs.orte) (rufEnv t4G zeugeWeltB [] zeugeArgs Env.nil) =
        .ok σ2 v ∧
      RufLaufG t4P t4O 0 0 M2 M1 ∧ RufLaufG t4P t4O 0 0 M1 M' ∧
      RandDannGL 0 [] t4B Env.nil zeugeWelt (fun _ => False) t4BindRest (.schrumpf (.dann .nil (.ende t4BRest)))
        M' σ2 (.cons (ergWert rfl v) Env.nil) := by
  have hg : TiefAlle t4P (fun _ => False) 1 t4G := tief_tiefAlle t4P _ 1 t4G (t4G_tief _)
  -- machine G at the start of `t4B`
  have hG0 : RandG 0 [] t4B Env.nil zeugeWelt (fun _ => False) (t4P.rumpf t4B) (RufStartG t4P t4Sp zeugeInitB)
      zeugeWelt Env.nil :=
    randG_start t4P t4Sp (init := zeugeInitB) (thr := 0) (f := t4B) (rho := Env.nil) (fun _ => False) rfl rfl
      (fun _ _ => rfl)
  obtain ⟨⟨log0, hZ0⟩, hΛ0, _⟩ := hG0
  have hW0 := hZ0.welt
  -- the `if` unfolds into block position
  obtain ⟨M1, hs1, hZ1⟩ := w_endeEntf (P := t4P) (O := t4O) (passes := 0) hZ0.1
    (.ite .tru t4BindBlock .nil) t4BRest Env.nil rfl rfl
  rw [hW0] at hZ1
  have hW1 := hZ1.welt
  -- its `then` branch: the bind block, in front of `t4B`'s rest
  obtain ⟨M2, hs2, hZ2⟩ := w_iteWahr (P := t4P) (O := t4O) (passes := 0) hZ1.1 .tru t4BindBlock .nil .nil
    (.ende t4BRest) Env.nil rfl rfl hΛ0.heldIn
  rw [hW1] at hZ2
  have hl2 : RufLaufG t4P t4O 0 0 (RufStartG t4P t4Sp zeugeInitB) M2 :=
    RufLaufG.schritt hs1 (RufLaufG.einzeln hs2)
  have hD : RandDannGL 0 [] t4B Env.nil zeugeWelt (fun _ => False) t4BindBlock (.dann .nil (.ende t4BRest)) M2
      zeugeWeltB Env.nil :=
    ⟨zeugeWeltB, WeltGleich.refl _, ⟨_, hZ2⟩, heldB_lese _ hΛ0, fun _ h => False.elim h⟩
  -- reuse the leaf callee's symbolic return
  obtain ⟨σ2, v, hR⟩ : ∃ (σ2 : World t4D) (v : ErgVal t4D (t4D.erg t4G)),
      rufAt t4P t4O 0 1 t4G (zeugeWeltB.lese [] zeugeArgs.orte) (rufEnv t4G zeugeWeltB [] zeugeArgs Env.nil) =
        .ok σ2 v := t4G_ruf_kehrt _
  -- the callee's trivial decomposed prefix
  have hkC : Zerlegung (rufZRahmen zeugeLay t4O 0 t4P (fun _ => 0) 0 t4G (rufWelt t4P t4G zeugeWeltB [] zeugeArgs)
        (rufEnv t4G zeugeWeltB [] zeugeArgs Env.nil)) (fun _ => False) (TiefAlle t4P (fun _ => False) 0)
      (t4P.rumpf t4G) (rufWelt t4P t4G zeugeWeltB [] zeugeArgs) (rufEnv t4G zeugeWeltB [] zeugeArgs Env.nil)
      (t4P.rumpf t4G) (rufWelt t4P t4G zeugeWeltB [] zeugeArgs) (rufEnv t4G zeugeWeltB [] zeugeArgs Env.nil) :=
    Zerlegung.halt _ _ _
  -- in and out of the callee
  obtain ⟨M1', _, hl1, hE, hout⟩ := randDannGL_bindCall_ein_aus (P := t4P) (O := t4O) (passes := 0) (j := 0)
    (leseblind_t4O.toP t4P) hD hR hg hkC
  obtain ⟨M', hl', hD'⟩ := hout hE
  exact ⟨hg, M2, M1', M', σ2, v, hl2, hD, hR, hl1, hl', hD'⟩

#print axioms bild_dann_zeuge

end Gabbro.Stage0.Senke.BildLauf
