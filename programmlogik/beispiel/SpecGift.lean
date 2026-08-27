import GabbroProgram
set_option autoImplicit false
open Gabbro.Body GabbroProgram

-- GIFT 1: die Spezifikation verlangt Menge 5, der Rumpf setzt 0.
def falsch_geraeumt (f : Int) (s : State) : Prop :=
  s.world (.slot "Faecher" f "menge") = .int 5

theorem gift1 (ρ : Env) (s : State) (f : Int) (hf : s.local' "f" = .int f) :
    ∃ s', finalState (exec ρ raeumen_body s) = some s' ∧ falsch_geraeumt f s' := by
  gabbro_simp [raeumen_body, falsch_geraeumt, hf]

-- GIFT 2: die Spezifikation verlangt, dass JEDES Fach unberuehrt bleibt -- auch `f`.
def falscher_rahmen (f : Int) (s s' : State) : Prop :=
  ∀ g, s'.world (.slot "Faecher" g "belegt") = s.world (.slot "Faecher" g "belegt")

theorem gift2 (ρ : Env) (s : State) (f : Int) (hf : s.local' "f" = .int f)
    (hoffen : s.world (.slot "Faecher" f "belegt") = .bool true) :
    ∃ s', finalState (exec ρ raeumen_body s) = some s' ∧ falscher_rahmen f s s' := by
  gabbro_simp [raeumen_body, falscher_rahmen, hf, hoffen]

-- GIFT 3: die Spezifikation nennt ein Feld, das es nicht gibt.
def erfundenes_feld (f : Int) (s : State) : Prop :=
  s.world (.slot "Faecher" f "gewicht") = .int 0

theorem gift3 (ρ : Env) (s : State) (f : Int) (hf : s.local' "f" = .int f) :
    ∃ s', finalState (exec ρ raeumen_body s) = some s' ∧ erfundenes_feld f s' := by
  gabbro_simp [raeumen_body, erfundenes_feld, hf]
