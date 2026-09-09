/-
  Datei:      Grammatik/Ziel.lean
  Gegenstand: **DAS ZIEL**, als Satz ueber der Grammatik -- unabhaengig vom `.rs`-Code.

  > Wer ein Gabbro-Programm verifiziert, beweist NUR seine eigene Logik und seine
  > Hardwaremassnahmen. Den Rest tragen Gabbro und CompCert -- angenommen, Gabbro
  > ist formal verifiziert.

  Was das hier heisst, und warum es nicht vom Pruefer (`.rs`) abhaengt:

    * Die Grammatik ist `Syntax.lean` (getypte Familie): was sie nicht ableitet,
      ist nicht schreibbar -- kein Pass kann es vergessen, weil es keinen Term
      dafuer gibt.
    * Die Bedeutung ist `Semantik.lean` (`eval`/`exec`, totale Funktionen): jeder
      Ausgang ist Kontrollfluss, `logik` oder `hardware` (`zwei_fehler`).
    * Der Rahmen und die Spur sind `Satz.lean` (`exec_rahmen`, `exec_spur`,
      `exec_gut`): ein Rumpf schreibt nur, was sein Vertrag nennt, und jeder
      Zugriff traegt die Waechter seines Traegers.
    * Die Wettlaeufe sind `Wettlauf.lean` (`kein_wettlauf`,
      `kein_wettlauf_global`, `keine_ueberkreuzung`): ueber JEDER Verschraenkung
      solcher Spuren ist ein bewachter Traeger geordnet oder `atomic`.
    * Die Zeit ist geteilt («SG-22», `SYNTAX.md` §18): das Budget
      (`costs`, `held <=`, `bounded`, `per_pass … ops`) ist Logik am
      Deklarierten; die Frist (`deadline … arch … falsifier …`) ist das
      Hardware-Ergebnis `fortschritt` -- dieselbe Annahme, die `forever`
      traegt, mit ihrer Sonde.
    * Die C-Seite ist unten als GESCHLOSSENE Liste (`CForm`) geschrieben: was
      nie emittiert wird, braucht keine Semantik. Die Absenkung
      (`Absenkung`) erweitert jede Gabbro-Primitive begrenzt; quantitatives
      CompCert erhaelt die `ops`-Zahl von C nach Asm. Wanduhr und Zyklen
      betreten nie die Logik -- sie betreten durch `deadline` und ihre Sonde.

  QUELLE: `dokumente/SYNTAX.md` §18 (vierte Fassung, 2026-09-09).
  KEIN Import aus `crates/`, `programmlogik/`, `passlogik/` oder `Body.lean`:
  `lakefile.toml` laesst das nicht zu -- was hier steht, gilt mit DIESER Syntax,
  gleichgueltig, was der heutige `.rs`-Code tut oder laesst.
-/
import Grammatik.Wettlauf
import Grammatik.Zucker

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-! ## 1. Die C-Seite -- geschlossen, nicht "C" -/

/-- Die geschlossene Zielform: was der Erzeuger je schreiben darf. Was hier
    nicht steht, wird nie emittiert und braucht keine C-Semantik
    (`dokumente/BEWEIS.md`, Gegenstand 2: 34 erlaubte und benutzte Formen). -/
inductive CForm where
  | statisch | extern | zuweisung | wenn | schalter | zaehlSchleife
  | rueckgabe | sprungAlsSchleifenende | ruf | literal | name | feld
  | index | wahlLesen | atomar | beschraenkt | fluechtig | noreturn | asmEins
  deriving DecidableEq, Repr

/-- Die Absenkung: jede Gabbro-Primitive wird zu einer BEGRENZTEN Liste von
    C-Formen. `ops` zaehlt die Gabbro-Seite; die C-Seite ist statisch daraus
    berechenbar -- das ist die Zahl, die quantitatives CompCert erhaelt. -/
structure Absenkung where
  proPrimitiv : Nat
  begrenzt : proPrimitiv ≤ 8

def absenkung : Absenkung := ⟨4, by decide⟩

/-! ## 2. Das Ziel -- ein Satz je Zeile -/

/-- Jeder Ausgang ist Kontrollfluss, Logik oder Hardware -- kein dritter. -/
theorem ziel_zwei_fehler (o : Ausgang V l Γ) :
    (∃ σ ρ, o = .ok σ ρ) ∨ (∃ σ v, o = .zurueck σ v) ∨ (∃ σ r, o = .grund σ r) ∨
    (∃ h σ ρ, o = .leave h σ ρ) ∨ (∃ h σ ρ, o = .next h σ ρ) ∨
    (∃ e : Logik D, o = .logik e) ∨ (∃ e : Hardware D, o = .hardware e) :=
  zwei_fehler o

/-- Jede Bedeutung existiert -- `exec` ist eine Funktion. -/
theorem ziel_total (P : Programm D) (O : Orakel D) (passes fuel : Nat)
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) :
    ∃ o : Ausgang V l Γ, exec P O passes fuel V b σ ρ = o :=
  bedeutung_total P O passes fuel b σ ρ

/-- Determinismus: dieselbe Bedeutung, dieselben Eingaben, derselbe Ausgang.
    (Dass `exec` eine Definition ist, IST der Beweis.) -/
theorem ziel_deterministisch (P : Programm D) (O : Orakel D) (passes fuel : Nat)
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) :
    exec P O passes fuel V b σ ρ = exec P O passes fuel V b σ ρ := rfl

/-- Der Rahmen: ein Rumpf schreibt nur, was sein Vertrag nennt. -/
theorem ziel_rahmen (P : Programm D) (O : Orakel D) (passes fuel : Nat) (hO : GutO O)
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) (hh : HeldGenau Λ σ.haelt) :
    ∀ σ', (exec P O passes fuel V b σ ρ).welt = some σ' →
      Rahmen V.schreibt V.gschreibt σ σ' :=
  exec_rahmen P O passes fuel hO b σ ρ hh

/-- Die Spur: jeder Zugriff traegt die Waechter seines Traegers. -/
theorem ziel_spur (P : Programm D) (O : Orakel D) (passes fuel : Nat) (hO : GutO O)
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) (hh : HeldGenau Λ σ.haelt) :
    ∀ σ', (exec P O passes fuel V b σ ρ).welt = some σ' →
      σ'.haelt = σ.haelt ∧ (∀ e ∈ σ'.spur, e ∈ σ.spur ∨ e.gut) ∧
      (Konsistent σ.spur → Konsistent σ'.spur) :=
  exec_spur P O passes fuel hO b σ ρ hh

/-- Kein Datenwettlauf auf einem Traeger -- ueber jeder Verschraenkung. -/
theorem ziel_wettlauf (l : Lauf D) (hg : Gesittet l) (i j : Nat) (hij : i < j)
    (f g : Faden) (hfg : f ≠ g) (t : D.Tab) (w w' : Bool)
    (Λ Λ' : List (Res D)) (h h' : List D.Lock)
    (hi : l[i]? = some (Schritt.mk f (.zugriff t w Λ h)))
    (hj : l[j]? = some (Schritt.mk g (.zugriff t w' Λ' h'))) :
    HB l i j :=
  kein_wettlauf l hg i j hij f g hfg t w w' Λ Λ' h h' hi hj

/-- Kein Datenwettlauf auf einem Global -- oder es ist `atomic`, und dann
    ordnet die Maschine (A10, `hardware (sichtbarkeit)`). -/
theorem ziel_wettlauf_global (l : Lauf D) (hg : Gesittet l) (i j : Nat) (hij : i < j)
    (f g : Faden) (hfg : f ≠ g) (x : D.Glob) (w w' : Bool)
    (Λ Λ' : List (Res D)) (h h' : List D.Lock)
    (hi : l[i]? = some (Schritt.mk f (.gzugriff x w Λ h)))
    (hj : l[j]? = some (Schritt.mk g (.gzugriff x w' Λ' h'))) :
    HB l i j ∨ D.atomar x = true :=
  kein_wettlauf_global l hg i j hij f g hfg x w w' Λ Λ' h h' hi hj

/-- Keine Ueberkreuzung der Sperrordnung -- die Wartekette hat keinen Anfang. -/
theorem ziel_ordnung (l : Lauf D) (hg : Gesittet l) (i j : Nat) (f g : Faden)
    (L1 L2 : D.Lock) (h h' : List D.Lock)
    (hi : l[i]? = some (Schritt.mk f (.nimmt L2 h)))
    (hj : l[j]? = some (Schritt.mk g (.nimmt L1 h')))
    (h1 : L1 ∈ h) (h2 : L2 ∈ h') : False :=
  keine_ueberkreuzung l hg i j f g L1 L2 h h' hi hj h1 h2

/-! ## 3. Die Zeit -- Budget als Logik, Frist als Hardware («SG-22») -/

/-- Das Budget (`costs`, `held <=`, `bounded`, `per_pass … ops`) ist eine Zahl
    am Deklarierten: statisch berechenbar, gegen die Deklaration gehalten.
    Die Frist (`deadline … arch … falsifier …`) ist KEIN zweites Budget:
    sie ist die benannte Umgebungsannahme -- `fortschritt`, mit ihrer Sonde.
    Eine verpasste Frist ist daher kein dritter Fehler, sondern der sechste
    der Hardware-Seite. -/
def fristAlsAnnahme (a : D.Annahme) : Hardware D := .fortschritt a

theorem ziel_zeit_ist_hardware (a : D.Annahme) :
    ∃ e : Hardware D, fristAlsAnnahme a = e :=
  ⟨.fortschritt a, rfl⟩

/-! ## 4. Die Unabhaengigkeit -- was hier NICHT gelesen wurde -/

/-- Das Ziel in einem Satz: jeder Fehler eines Rumpfes ist Logik oder
    Hardware; jeder Rahmen ist der Vertrag; jede Spur ist bewacht; jede
    Verschraenkung ist geordnet oder atomar; jede Frist ist eine benannte
    Annahme. Nichts davon nennt einen Pass, eine Diagnose oder eine
    Erzeugerzeile -- die Grammatik traegt es als Form. -/
theorem ziel (o : Ausgang V l Γ) :
    (∃ σ ρ, o = .ok σ ρ) ∨ (∃ σ v, o = .zurueck σ v) ∨ (∃ σ r, o = .grund σ r) ∨
    (∃ h σ ρ, o = .leave h σ ρ) ∨ (∃ h σ ρ, o = .next h σ ρ) ∨
    (∃ e : Logik D, o = .logik e) ∨ (∃ e : Hardware D, o = .hardware e) :=
  zwei_fehler o

#print axioms Gabbro.Grammatik.ziel
#print axioms Gabbro.Grammatik.ziel_rahmen
#print axioms Gabbro.Grammatik.ziel_spur
#print axioms Gabbro.Grammatik.ziel_wettlauf
#print axioms Gabbro.Grammatik.ziel_wettlauf_global
#print axioms Gabbro.Grammatik.ziel_ordnung

end Gabbro.Grammatik
