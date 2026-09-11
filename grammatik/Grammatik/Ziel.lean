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
    * Die Stabilitaet ist `InterferenzAllgemein.lean` (`allgemeinStabil`):
      gueltige und schrittweise erhaltene Zusicherungen gelten an der letzten
      Welt der Kette.
    * Die Komposition ist `Komposition.lean` (`UmgebungOk`, `SchleifenOk`):
      die Ruf- und Schleifenordnung als Gestalt, noch ohne Beweis.
    * Das Geteilte ist `Geteilt.lean` (`geteilt_treu`): als ungeteilt
      Erklaertes erreicht hoechstens ein Faden -- gerechnet, nicht angenommen.
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

  GRENZEN, gemessen am 2026-09-10 (`messung/ZIEL-BEWERTUNG-2026-09-10.md`):
  kein Satz fuehrt `exec`-Spuren in `Gesittet` ueber (die Bruecke steht in
  `Wettlauf.lean` als `lauf_aus_brav`, mit W3-W5 als Prämissen); die gueltige
  sequenzielle Logik unter Verschraenkung (Owicki-Gries-Schritt) steht nirgends;
  die Frist ist hier nur benannt (`fristAlsAnnahme`) -- gemessen wird sie von
  der Sonde (`sonden/sonde_tick.c`, Probenwaehrung, kein Beweis).
-/
import Grammatik.Wettlauf
import Grammatik.Zucker
import Grammatik.InterferenzAllgemein
import Grammatik.Komposition
import Grammatik.Geteilt

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-! ## 1. Die C-Seite -- geschlossen, nicht "C" -/

/-- Die Zielformen, ueber die der Absenkungsvertrag spricht -- 19 benannte
    Gestalten, KEINE geschlossene Liste. Dass der Erzeuger nur diese schreibt,
    ist unbewiesen: `dokumente/BEWEIS.md`, Gegenstand 2, misst 64 Formen im
    Erzeugnis, davon 30 ohne Entscheid (u.a. Zeigerarithmetik an 491 Stellen).
    Wer die Liste schliesst, entscheidet die 19 (`?:` als Muster) oder nimmt
    sie aus dem Erzeuger. -/
inductive CForm where
  | statisch | extern | zuweisung | wenn | schalter | zaehlSchleife
  | rueckgabe | sprungAlsSchleifenende | ruf | literal | name | feld
  | index | wahlLesen | atomar | beschraenkt | fluechtig | noreturn | asmEins
  deriving DecidableEq, Repr

/-- Die Absenkung ALS ANNAHME: jede Gabbro-Primitive wuerde zu einer BEGRENZTEN
    Liste von C-Formen. `ops` zaehlt die Gabbro-Seite; erhalten wuerde die Zahl
    ein quantitatives CompCert (CerCo, nicht der Produktionsuebersetzer). -/
structure Absenkung where
  proPrimitiv : Nat
  begrenzt : proPrimitiv ≤ 18

/-- Die Zahl, auf der der Vertrag ruhen wuerde -- TEILGEMESSEN seit 2026-09-10
    (`messung/ABSENKUNG-MESSUNG.md`, Entscheid `messung/ABSENKUNG-SCHRANKEN-ENTSCHEID.md`):
    `17` ist das statisch gezaehlte Maximum je Gabbro-Primitiv (staerkste Zeile:
    `Schleife`/`traverse over descendants of`, `emit.rs:8523-8560`); die Schranke
    `18` ist das Maximum plus eins Kopfraum. Der Lauf ueber echte Erzeugnisse mit
    einem Lexer (`ABSENKUNG-ZAEHLUNG.md` §2) steht noch aus -- er kann das Maximum
    nur bestaetigen oder heben, nie unter `17` senken. CompCert beweist ohnehin
    Semantikerhaltung, keine Kostenerhaltung (sequenziell, rennfrei, ohne
    `__asm__`, ohne C11-`_Atomic`: 39 `_Atomic`, 120 `volatile`, 2 `__asm__` im
    eigenen Erzeugnis). -/
def absenkung : Absenkung := ⟨17, by decide⟩

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
    sie ist die benannte Umgebungsannahme -- `fortschritt`, mit ihrer Sonde. -/
def fristAlsAnnahme (a : D.Annahme) : Hardware D := .fortschritt a

/- ZURUECKGEZOGEN am 2026-09-10, und zwar der Satz, nicht die Definition:
   `ziel_zeit_ist_hardware` behauptete `∃ e, fristAlsAnnahme a = e` -- eine
   Existenzaussage ueber eine totale Funktion, die JEDER Definition gelingt.
   Nichts konnte sie beschaedigen, also mass sie nichts (dieselbe Klasse wie
   die trivialen `bedeutung_total`/`wert_total`, die der Ordner als trivial
   BESTAETIGT -- diese Zeile tat es nicht). Was bleibt, ist die Definition
   oben: die Abbildung Frist → Annahme. Gemessen wird die Frist von der Sonde
   (`sonden/sonde_tick.c`, Probenwaehrung R15/W10: Stichprobe, kein Beweis),
   nicht von einem Satz hier. -/

/-! ## 4. Die Unabhaengigkeit -- was hier NICHT gelesen wurde -/

/-- Das Ziel in einem Satz -- und zwar NUR dieser: jeder Fehler eines
    Ausgangs ist Kontrollfluss, Logik oder Hardware. Rahmen (`ziel_rahmen`),
    Spur (`ziel_spur`), Verschraenkung (`ziel_wettlauf`, `ziel_wettlauf_global`,
    `ziel_ordnung`), Fristabbildung (`fristAlsAnnahme`) und Absenkung
    (`Absenkung`, als Annahme) stehen als eigene Saetze daneben -- was hier
    stuende und dort beweist, waere ein Kommentar, der mehr behauptet als sein
    Satz. Nichts davon nennt einen Pass, eine Diagnose oder eine
    Erzeugerzeile. -/
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

/-! ## 5. The goal itself, as a theorem (Phase 5 formulation) -/

/-- **What a verified program still owes (`ziel_nutzer_last`).** Every outcome is
    control flow (`ok`, `zurueck`, `grund`, `leave`, `next`), the author's own
    logic (`logik`), or a NAMED hardware assumption (`hardware`) -- nothing else.
    That is the whole user-facing contract: prove your own logic, name your
    hardware assumptions; Gabbro and CompCert carry the rest (once Gabbro is
    verified).

    The conclusion already holds -- it is `zwei_fehler`. What does NOT yet hold
    is the road from a real run to it, so the road travels as explicit premises
    (named hypotheses, no axioms, no `sorry`). Each premise names the wave that
    discharges it; as waves land, premises turn into proofs one by one:

    * `hBridge`: every interleaving of well-formed bodies is `Gesittet`. Today
      `lauf_aus_brav` (Wettlauf.lean) derives only half of it (W1-W2 over
      suffixes); W3 (exclusion) and W5 (shared) stay premises there, and the
      per-thread state behind a real `Lauf D` is still carried as `hEin`.
    * `hSeqLogic`: valid sequential logic (`requires`/`ensures`) survives
      interleaving (Owicki-Gries step). It stands nowhere yet; `exec_rahmen`
      is the candidate premise for frame-disjointness.
    * `hProbe`: the tick probe upholds the named deadline assumption
      (`fristAlsAnnahme`, `fortschritt` with its probe). The deadline is named
      here and measured by `sonden/sonde_tick.c` (sampling, no proof).
    * `hLowering`: the lowering contract (`Absenkung`, at most 18 C forms per
      primitive) plus quantitative CompCert preserving the `ops` count. The
      count (17 measured, bound 18) is partially measured; the lexer run over
      real products is still open. -/
theorem ziel_nutzer_last (o : Ausgang V l Γ)
    (hBridge : ∀ (l : Lauf D) (voll : Faden → List (Ereignis D)),
      IstVerschraenkung l voll → Gesittet l)
    (hSeqLogic : Prop)
    (hProbe : Prop)
    (hLowering : Absenkung) :
    (∃ σ ρ, o = .ok σ ρ) ∨ (∃ σ v, o = .zurueck σ v) ∨ (∃ σ r, o = .grund σ r) ∨
    (∃ h σ ρ, o = .leave h σ ρ) ∨ (∃ h σ ρ, o = .next h σ ρ) ∨
    (∃ e : Logik D, o = .logik e) ∨ (∃ e : Hardware D, o = .hardware e) := by
  have _ := hBridge
  have _ := hSeqLogic
  have _ := hProbe
  have _ := hLowering
  exact zwei_fehler o

#print axioms Gabbro.Grammatik.ziel_nutzer_last

end Gabbro.Grammatik
