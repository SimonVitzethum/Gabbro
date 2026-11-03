module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz.T2.Teil1

@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **A body without `logik` sources meets `KeineLogik`** -- for every
    declared axiom ensures, without any reasoning about the program. -/
theorem logikFrei_keineLogik {P : Programm D} (passes : Nat) (Q : AxEns D) {f : D.Fn}
    (h : (P.rumpf f).logikFrei = true) : KeineLogik P passes Q f :=
  fun O' _ _ _ R _ hR σ ρ _ e =>
    Endblock.logikFrei_ok O' passes R (Ok := fun _ => False) (fun g σ ρ e h => hR g σ ρ e h) (P.rumpf f) h
      σ ρ e

/-- The program-level check over a member list. -/
def programmLogikFrei (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun f => (P.rumpf f).logikFrei

theorem programmLogikFrei_ok {P : Programm D} {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (h : programmLogikFrei P fs = true) (passes : Nat) (Q : AxEns D) :
    ∀ f, KeineLogik P passes Q f :=
  fun f => logikFrei_keineLogik passes Q ((List.all_eq_true.mp h) f (hvoll f))

#print axioms Gabbro.Grammatik.logikFrei_keineLogik
#print axioms Gabbro.Grammatik.programmLogikFrei_ok

/-! ## 6. The conclusion: no reachable machine is stuck at a `logik` check -/

end Gabbro.Grammatik
