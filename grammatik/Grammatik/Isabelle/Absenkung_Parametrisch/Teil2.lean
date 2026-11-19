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

end Gabbro.Grammatik.AbsenkungParam
