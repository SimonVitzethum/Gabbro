/-
  File:      stage0/Stage0/Senke/Bild/Mehr/FadenZeuge.lean
  Subject:   Witness of `fadenErreichbarX_lauf` (multi-thread image theorem, package MT2) on the chain's own witness
             `bild_dann_zeuge`: the bind caller `t4B` of the call fixture `t4` (`if true { let x = g(); konto[1] := x }
             else { }; return 9`). Machine G's thread `0` unfolds the `if`, takes its `then` branch, descends into the
             callee `g` and returns with its value -- three runs of the single-thread chain, joined -- and the thread
             machine over GX, from the start machine of `t4B` with every thread live and none joining, reaches the
             machine behind the call. The run is not empty: there thread `0` stands in front of `konto[1] := x`
             with `x` bound to the callee's value (`RandDannGL`), not at the start of the body.
-/
module
public import Stage0.Senke.Bild.Rek.ZeugeDann
public import Stage0.Senke.Bild.Mehr.Faden
@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Gabbro.Grammatik Gabbro.Stage0.Senke Gabbro.Stage0.Senke.BildLauf

variable [Runner.IR.Kern]

/-- The thread machine at the start of the bind caller: every thread live, none joining. -/
def zeugeFadenK0 : FadenMaschine t4D := ⟨RufStartG t4P t4Sp zeugeInitB, fun _ => true, fun _ => [], fun _ => 0, 0⟩

/-- **The chain's G run of one thread is a run of the thread machine over GX**, behind a call. -/
theorem fadenErreichbarX_lauf_zeuge :
    ∃ (M' : RufMaschineG t4D) (σ2 : World t4D) (ρ2 : Env t4D [.int 0 100]),
      RufLaufG t4P t4O 0 0 (RufStartG t4P t4Sp zeugeInitB) M' ∧
      RandDannGL 0 [] t4B Env.nil zeugeWelt (fun _ => False) t4BindRest (.schrumpf (.dann .nil (.ende t4BRest)))
        M' σ2 ρ2 ∧
      FadenErreichbarX t4P t4O 0 (fun _ => False) zeugeFadenK0 ⟨M', fun _ => true, fun _ => [], fun _ => 0, 0⟩ := by
  obtain ⟨_, M2, M1, M', σ2, v, hl2, _, _, hl1, hl', hD'⟩ := bild_dann_zeuge
  have hl := (hl2.trans hl1).trans hl'
  exact ⟨M', σ2, _, hl, hD', fadenErreichbarX_lauf hl rfl rfl .start⟩

end Gabbro.Stage0.Senke.BildMehr
