/-
  File:      stage0/Stage0/Senke/Bild/Gleich/Zeuge.lean
  Subject:   Witnesses of packages P0 and P1 (read-erasure equivalence, handler substitution). On the call fixture
             `t4` of `RufAdaequatRufG`: a read is invisible up to `≈` but changes the trace, a write is never erased
             (`lesegleich_zeuge`); every premise of `execEnd_lg` holds jointly with two different start worlds and two
             different handlers, without early failures (`execEnd_lg_zeuge`). For every declaration: an oracle that
             ignores the trace is read-blind (`leseblind_still`). All terms; no kernel computation.
-/
module
public import Stage0.Senke.Bild.Gleich.Ersetzung
public import Stage0.Senke.Bild.Gleich.LesegleichEig
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T8
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik

/-- An oracle that ignores the trace: a foreign call leaves the world and answers `0`, a register reads `0`, every
    publication is visible. -/
def stillesOrakel (D : Deklaration) : Orakel D where
  wirktL := fun _ σ _ => ({ σ with spur := [] }, 0)
  regLiesL := fun _ _ => 0
  regSchreib := fun _ _ => ()
  sichtbarL := fun _ _ => true

/-- **The oracle premise holds** (as for every oracle, `leseblind_alle`). -/
theorem leseblind_still (D : Deklaration) : Leseblind (stillesOrakel D) :=
  leseblind_alle _

/-- The call fixture's oracle is read-blind (the fixture has no foreign body, register or global). -/
theorem leseblind_t4O : Leseblind t4O :=
  leseblind_alle _

/-- The fixture's start world: every slot `0`, empty trace. -/
abbrev zeugeWelt : World t4D := t4Sp.welt []

/-- **P0 witness**: a read of `konto` is invisible up to `≈` but changes the trace; a write is never erased, even one
    that stores the value already there. -/
theorem lesegleich_zeuge :
    WeltGleich zeugeWelt (zeugeWelt.lese [] [.inl ()]) ∧
      (zeugeWelt.lese [] [.inl ()]).spur ≠ zeugeWelt.spur ∧
      ¬ WeltGleich zeugeWelt (zeugeWelt.schreibSlot () [] 0 () (zeugeWelt.slots () 0 ())) :=
  ⟨weltGleich_lese _ _ _, lese_echt _ _ (List.cons_ne_nil _ _), weltGleich_nicht_schreibSlot _ _ _ _ _ _⟩

/-- **P1 witness** (`execEnd_lg`): the plain caller of the fixture (`g(); konto[1] := 7; return 9`) runs under the
    body-running handler at depth 1 from the start world, and under the handler that reads `konto` before every call
    from the start world after a read of `konto`. All premises hold jointly -- the handlers are related
    (`rufRumpf_lese_vorn`), the oracle is read-blind (`leseblind_t4O`), the start worlds are `≈` and different
    (`lesegleich_zeuge`) -- and no early failure is admitted (`Er = fun _ => False`). -/
theorem execEnd_lg_zeuge :
    EndLG (fun _ => False)
      (execEnd t4O 0 (rufRumpf t4P t4O 0 1) t4FRumpf zeugeWelt Env.nil)
      (execEnd t4O 0 (fun g σ ρ => rufRumpf t4P t4O 0 1 g (σ.lese [] [.inl ()]) ρ) t4FRumpf
        (zeugeWelt.lese [] [.inl ()]) Env.nil) :=
  execEnd_lg (passes := 0)
    (rufRumpf_lese_vorn (P := t4P) (passes := 0) (Er := fun _ => False) (leseblind_t4O.toP t4P) 1 [] [.inl ()])
    leseblind_t4O.rs t4FRumpf (Or.inr leseblind_t4O.w) (weltGleich_lese _ _ _) Env.nil

end Gabbro.Stage0.Senke.BildLauf
