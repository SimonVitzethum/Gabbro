module

public import Grammatik.Isabelle.Table_Ops_Erhaltung
public import Grammatik.Isabelle.Absenkung_Parametrisch.Teil1

@[expose] public section

namespace Gabbro.Grammatik.AbsenkungParam
open Gabbro.Grammatik.TableOps
set_option linter.unusedVariables false

/-- The free-slot instance: everything of E1--E6, but no slot reads
    occupied -- the shape the S-2/S-3 witnesses need. -/
def gesundFrei : Zielsemantik (Nat → Nat) Nat Nat where
  lies := wlies
  schreib := wschreib
  ort := fun i => i
  belegtort := wbelegtort
  deute := fun w => some w
  deutebelegt := fun _ => false
  wort := fun i => i
  N := 2
  wirkung := fun s p z => updW z s p
  E1 := by
    intro z a b v h
    show updW z a v b = z b
    exact updW_diff _ _ _ _ h
  E2 := by
    intro z a v
    show updW z a v a = v
    exact updW_self _ _ _
  E3 := by
    intro s p z _ _
    rfl
  E4 := by
    intro i j _ _ h
    exact h
  E5 := by
    intro i j hi hj
    show i ≠ 10 + j
    omega
  E6 := by
    intro i _
    rfl

theorem anderer_platz_unberuehrt_zeuge :
    Ab gesund.toZielraum (gesund.wirkung 0 1 (fun _ => 5)) 1
      = Ab gesund.toZielraum (fun _ => 5) 1 :=
  anderer_platz_unberuehrt gesund 0 1 (fun _ => 5) 1
    (by decide) (by decide) (by decide)

theorem belegung_von_s_unberuehrt_zeuge : (true : Bool) = true :=
  belegung_von_s_unberuehrt gesund 0 1 (fun _ => 5)
    (by decide) (by decide)

theorem absenkung_am_belegten_platz_zeuge :
    Ab gesund.toZielraum (gesund.wirkung 0 1 (fun _ => 5))
      = Umhaengen (Ab gesund.toZielraum (fun _ => 5)) 0 1 :=
  absenkung_am_belegten_platz gesund 0 1 (fun _ => 5)
    (by decide) (by decide) (by decide)

theorem relabel_am_freien_platz_ist_wirkungslos_zeuge :
    Ab gesundFrei.toZielraum (gesundFrei.wirkung 0 1 (fun _ => 0))
      = Ab gesundFrei.toZielraum (fun _ => 0) := by
  apply relabel_am_freien_platz_ist_wirkungslos gesundFrei 0 1 (fun _ => 0)
    (by decide) (by decide)
  decide

theorem absenkung_geht_am_freien_platz_auseinander_zeuge :
    Ab gesundFrei.toZielraum (gesundFrei.wirkung 0 1 (fun _ => 0))
      ≠ Umhaengen (Ab gesundFrei.toZielraum (fun _ => 0)) 0 1 := by
  apply absenkung_geht_am_freien_platz_auseinander gesundFrei 0 1 (fun _ => 0)
    (by decide) (by decide)
  decide

theorem absenkung_relabel_zeuge :
    Ab gesund.toZielraum (gesund.wirkung 0 1 (fun _ => 5))
      = (if gesund.deutebelegt
            (gesund.lies (fun _ => 5) (gesund.belegtort 0)) = true
          then Umhaengen (Ab gesund.toZielraum (fun _ => 5)) 0 1
          else Ab gesund.toZielraum (fun _ => 5)) :=
  absenkung_relabel gesund 0 1 (fun _ => 5) (by decide) (by decide)

theorem relabel_erhaelt_wohlgeformt_zeuge
    (hwf : Wohlgeformt (Ab gesund.toZielraum (fun _ => 5)))
    (helter : Erreicht (Ab gesund.toZielraum (fun _ => 5)) 1)
    (hnicht : ¬ Ueber (Ab gesund.toZielraum (fun _ => 5)) 1 0) :
    Wohlgeformt (Ab gesund.toZielraum (gesund.wirkung 0 1 (fun _ => 5))) :=
  relabel_erhaelt_wohlgeformt gesund 0 1 (fun _ => 5)
    (by decide) (by decide) hwf helter hnicht

end Gabbro.Grammatik.AbsenkungParam
