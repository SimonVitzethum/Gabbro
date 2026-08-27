/-  VON HAND GESCHRIEBEN. Kein Erzeuger hat diese Datei angefasst.

    Sie sagt, was ueber dem Programm gelten soll -- in Lean, mit Leans Mitteln.
    Das Programm selbst steht in `GabbroProgram`, erzeugt aus zwei `.gab`-Dateien.
-/
import GabbroProgram
set_option autoImplicit false
open Gabbro.Body GabbroProgram

/-- **Spezifikation 1** -- ein geraeumtes Fach ist leer und nicht sperrig. -/
def geraeumt (f : Int) (s : State) : Prop :=
  s.world (.slot "Faecher" f "belegt")  = .bool false
  ∧ s.world (.slot "Faecher" f "menge")   = .int 0
  ∧ s.world (.slot "Faecher" f "sperrig") = .bool false

theorem raeumen_erfuellt_geraeumt (s : State) (f : Int)
    (hf : s.local' "f" = .int f) :
    ∃ s', finalState (exec raeumen_body s) = some s' ∧ geraeumt f s' := by
  gabbro_simp [raeumen_body, geraeumt, hf]

/-- **Spezifikation 2 -- mit einem QUANTOR.** Das ist die Form, die eine `spec fn` in
    Gabbro gar nicht ausdruecken kann: `raeumen` fasst KEIN anderes Fach an. -/
def nur_dieses_fach (f : Int) (s s' : State) : Prop :=
  ∀ g, g ≠ f →
    s'.world (.slot "Faecher" g "belegt") = s.world (.slot "Faecher" g "belegt")
    ∧ s'.world (.slot "Faecher" g "menge") = s.world (.slot "Faecher" g "menge")

theorem raeumen_fasst_nichts_anderes_an (s : State) (f : Int)
    (hf : s.local' "f" = .int f) :
    ∃ s', finalState (exec raeumen_body s) = some s' ∧ nur_dieses_fach f s s' := by
  gabbro_simp [raeumen_body, nur_dieses_fach, hf]
  intro g hg
  simp [store, hg]

/-- **Spezifikation 3** -- ueber der ZWEITEN Datei, und sie nennt einen Parameter. -/
def eingelagert (f m : Int) (s : State) : Prop :=
  s.world (.slot "Faecher" f "belegt") = .bool true
  ∧ s.world (.slot "Faecher" f "menge") = .int m

theorem einlagern_erfuellt_eingelagert (s : State) (f m : Int)
    (hf : s.local' "f" = .int f) (hm : s.local' "m" = .int m) :
    ∃ s', finalState (exec einlagern_body s) = some s' ∧ eingelagert f m s' := by
  gabbro_simp [einlagern_body, eingelagert, hf, hm]
