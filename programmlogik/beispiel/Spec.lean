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

theorem raeumen_erfuellt_geraeumt (ρ : Env) (s : State) (f : Int)
    (hf : s.local' "f" = .int f) :
    ∃ s', finalState (exec ρ raeumen_body s) = some s' ∧ geraeumt f s' := by
  gabbro_simp [raeumen_body, geraeumt, hf]

/-- **Spezifikation 2 -- mit einem QUANTOR.** Das ist die Form, die eine `spec fn` in
    Gabbro gar nicht ausdruecken kann: `raeumen` fasst KEIN anderes Fach an. -/
def nur_dieses_fach (f : Int) (s s' : State) : Prop :=
  ∀ g, g ≠ f →
    s'.world (.slot "Faecher" g "belegt") = s.world (.slot "Faecher" g "belegt")
    ∧ s'.world (.slot "Faecher" g "menge") = s.world (.slot "Faecher" g "menge")

theorem raeumen_fasst_nichts_anderes_an (ρ : Env) (s : State) (f : Int)
    (hf : s.local' "f" = .int f) :
    ∃ s', finalState (exec ρ raeumen_body s) = some s' ∧ nur_dieses_fach f s s' := by
  gabbro_simp [raeumen_body, nur_dieses_fach, hf]
  intro g hg
  simp [store, hg]

/-- **Spezifikation 3** -- ueber der ZWEITEN Datei, und sie nennt einen Parameter. -/
def eingelagert (f m : Int) (s : State) : Prop :=
  s.world (.slot "Faecher" f "belegt") = .bool true
  ∧ s.world (.slot "Faecher" f "menge") = .int m

theorem einlagern_erfuellt_eingelagert (ρ : Env) (s : State) (f m : Int)
    (hf : s.local' "f" = .int f) (hm : s.local' "m" = .int m) :
    ∃ s', finalState (exec ρ einlagern_body s) = some s' ∧ eingelagert f m s' := by
  gabbro_simp [einlagern_body, eingelagert, hf, hm]

/-! ## Spezifikation 4 -- ein RUFER, bewiesen aus dem VERTRAG des Gerufenen

    `raeumen_und_merken` ruft `raeumen`. Der Beweis unten sieht den Rumpf von `raeumen`
    **nie an**: er nimmt an, was `raeumen` VERSPRICHT, und der Erzeuger hat dieses
    Versprechen als `raeumen_post` hingeschrieben.

    *Genau darum ist die Umgebung `ρ` ein Parameter des Satzes und keine Definition:* eine
    festgelegte Umgebung waere der Erzeuger, der entscheidet, was ein Gerufener tut -- und
    das ist die Entscheidung, fuer die ein Beweis da ist.

    `Env` liefert ein PAAR: den Zustand danach und das Ergebnis. Ein Gerufener kann beides,
    schreiben und zurueckgeben, und eine Umgebung, die nur den Zustand gaebe, machte
    `let n = f(a);` unaussprechbar -- 22 Rufstellen des Korpus.
-/

/-- Der Vertrag von `raeumen`, in der Form, die der RUF erzeugt. Wer ihn einloest, beweist
    ihn aus `raeumen_erfuellt_geraeumt` -- er ist keine Annahme ueber fremden Code. -/
def raeumen_haelt (ρ : Env) : Prop :=
  ∀ (w : World) (k : Int),
    (ρ "raeumen" { world := w, local' := bindAll ["f"] [.int k] (fun _ => .absent) }).1.world
      (.slot "Faecher" k "belegt") = .bool false

theorem rufer_erfuellt_aus_dem_vertrag (ρ : Env) (s : State) (f : Int)
    (hf : s.local' "f" = .int f) (hr : raeumen_haelt ρ) :
    ∃ s', finalState (exec ρ raeumen_und_merken_body s) = some s'
        ∧ s'.world (.slot "Faecher" f "belegt") = .bool false := by
  gabbro_simp [raeumen_und_merken_body, hf]
  exact hr s.world f
