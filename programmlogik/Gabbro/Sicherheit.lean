/-
  Datei:      Gabbro/Sicherheit.lean
  Gegenstand: **DER SATZ** -- ein Rumpf, den der Pruefer annimmt, bleibt in der Semantik von
              `Body.lean` nur an den Stellen stecken, die der Schreiber selbst geschrieben
              hat: `requires` und `invariant`. Alles andere traegt die Sprache.

  Angelegt 2026-09-09. Kopfdatei zu `Sicherheit/Ausdruck.lean` und `Sicherheit/Anweisung.lean`.

  ## Die Frage, und was vorher stand

  > Erfuellt Gabbro das Ziel, dass Grammatik und Syntax ALLE Fehler abdecken, so dass der
  > einzige Fehler eines Gabbro-Programms die Logik des Nutzers sein kann?

  Der Ordner hatte darauf zwei Antworten, und keine war ein Satz ueber LAEUFE:

  * `passlogik/` -- 137 Saetze ueber die REGELN der Paesse (Bereichsverband, Wirkungshuelle,
    Rang, Terminierung). Jeder hat die Form *"wer durchgeht, erfuellt X"* ueber einem Modell
    der Regel, nicht ueber einem Programm.
  * `Gabbro/Coverage.lean` -- `the_sentence`: jede FORM der Grammatik ist getragen, angenommen
    oder abgesagt. Das ist eine Klassifikation, total nach Konstruktion; sie sagt nicht, dass
    ein angenommenes Programm nicht steckenbleibt.

  Was fehlte, ist der klassische Sicherheitssatz -- *well-typed programs don't go wrong* --
  ueber der Semantik, die dieser Ordner schon hat. `Body.lean` KENNT das Steckenbleiben
  (`Outcome.stuck`, `eval … = none`) und hatte keinen Satz, der es fuer angenommene Programme
  ausschliesst. **Der steht jetzt hier**, in der Form:

      exec ρ b s = stuck  →  Logik ρ b s

  `Logik` ist ein induktives Praedikat mit genau ZWEI Grundfaellen: ein `requires`, das an der
  Rufstelle nicht gilt, und eine `invariant`, die beim Eintritt nicht gilt -- also genau die
  Klauseln, die `Coverage.lean` `ownRequires`/`ownInvariant` nennt. Alle anderen
  Konstruktoren reichen die Stelle nur durch einen Unterblock weiter.

  ## Was der Satz sagt -- und was NICHT

  BEWIESEN (0 `sorry`, 0 eigene Axiome, kein `mathlib`):
    * `schluss_sicher`  -- ein Ausdruck, den der Pruefer annimmt, wertet zu einem Wert der
                           gerechneten Gestalt aus. Kein Nenner null, kein Bitoperator auf
                           negativer Zahl, keine Gestaltverwechslung, kein Index ausserhalb
                           `0 ..< count` (`M102`, `M103`, `M104`, `M137`, `D005`).
    * `pruefe_sicher`   -- eine Anweisung, die der Pruefer annimmt, laesst die Welt in ihrer
                           Typisierung und den Sichtbereich gehalten -- oder steht an einer
                           `Logik`-Stelle.
    * `exec_sicher`     -- der Satz, wie oben.

  ANGENOMMEN (als Praemisse am Satz, nicht als Axiom):
    (S1) `Γ` ist aus den Deklarationen abgeleitet (`Deklariert`).
    (S2) `via`-Felder sind an JEDEM Index optionsgestaltig (`KettenWohlgeformt`) -- Fund 2.
    (U1) Die Umgebung haelt die Welt und antwortet gemaess Signatur (`UmgebungOK`).
    (U2) Jede Schleife haelt ihren Sichtbereich (`SchleifenOK`).
    Beide U-Praemissen sind DERSELBE Satz eine Ebene tiefer: fuer den Rumpf des Gerufenen
    bzw. die Iteration der Schleife. Sie aus `Runs`/`RunsLoop` und `exec_sicher` zu schliessen
    ist der Programmsatz -- Schritt 2 des Plans, hier nicht gefuehrt.

  NICHT BEWIESEN, und das ist der eigentliche Ertrag -- die FUNDE:
    Fund 1  **Index und Ueberlauf sind im Modell keine Fehler.** `World := Place → Value` ist
            total: `σ (.slot c 999 f)` liefert einen Wert, egal was `count` sagt; `binop .add`
            rechnet in `Int` ohne Breite. Der Satz kann diese zwei Klassen deshalb nur als
            EIGENSCHAFT DES PRUEFERS tragen (`schluss` verlangt den Index in `0 ..< count`,
            `WF` haelt jeden Wert in seinem Bereich), nicht als ausgeschlossenen Fehlerfall
            der Semantik. *Ein Programm, das ausserhalb indiziert, bleibt in diesem Modell
            nicht stecken -- es liest.* Fuer den vollen Satz braucht `Body.lean` einen
            Fehlerausgang am Index (oder `Place` die Schranke).
    Fund 2  **`Shape.opt` traegt keinen Bereich.** `option index into T` ist im Modell ein
            `present n` mit beliebigem `n`; `chase` folgt ihm ohne Schranke aus der
            typisierten Region hinaus. Darum (S2) ueber ALLE Indizes statt `0 ..< count`.
    Fund 3  **Der Fehlerzweig von `let … else` muss enden -- und `Body.lean` verlangt es
            nicht.** `SYNTAX.md`:1029 sagt es; `step` laeuft bei einem Zweig, der abfaellt,
            mit einer Bindung ohne Wert weiter. Hier prueft `endetMitAusgang` es; ohne diese
            Bedingung ist der Satz falsch (der Zweig verliesse den Sichtbereich).
    Fund 4  **Ein `reason` hat keine `Shape`.** `Value.hasShape (.reason _) _ = false`, also
            kann ein Grund in `Typing`/`WF` nicht stehen. Der Sichtbereich hier traegt darum
            `Ge.grund` neben `Ge.form`; ein Grund in der WELT (ein `static` vom Typ `reason`)
            ist im Modell untypisierbar.
    Fund 5  **Division, Rest, Bits, Schiebungen liefern hier `.int` ohne Bereich**, waehrend
            `typen.rs` Schranken rechnet (`0 <= a/b <= a`, `x & m <= m`). `Coverage.lean`
            bucht die als `carriedByTactic` ("no general theorem stands here"). Der
            allgemeine Satz fehlt an beiden Stellen.
    Fund 6  **Die Naht.** `schluss`/`pruefe` sind ein Pruefer, den DIESE Datei schreibt, nach
            der Spezifikation -- nicht `gabbro-check`. Dass beide dasselbe annehmen, ist die
            `W16`-Klasse, und kein Satz hier beruehrt sie.

  Und ausserhalb des Modells -- was der Satz nicht einmal FORMULIEREN kann, weil `Body.lean`
  es nicht kennt: Alias (`m3.rs`: "no alias analysis"), Nebenlaeufigkeit und Speichermodell
  (A10), Terminierung (`forever` endet nicht, `S005`/`S008`/`K009` sind notwendig, nicht
  hinreichend), die Axiomschicht (`assume`/`axiom`, `unfalsifiable`), fremde Ruempfe
  (`extern`, `asm`, `entrust`), der Erzeuger und das C. Das sind keine Luecken DIESES Satzes;
  es sind die Grenzen der Semantik, ueber der er steht -- `PLAN-SICHERHEIT.md` fuehrt sie.
-/
import Gabbro.Sicherheit.Ausdruck
import Gabbro.Sicherheit.Anweisung

namespace Gabbro.Sicherheit

open Gabbro.Body

/-! ## 1. Der Satz -/

/-- **Wer stecken bleibt, bleibt an eigener Logik stecken.** Ein Rumpf, den `pruefeBlock`
    annimmt, aus einem Zustand, der in Deklaration und Sichtbereich liegt: bleibt `exec`
    stecken, so an einem `requires` oder einer `invariant` -- den beiden Grundfaellen von
    `LogikB`. -/
theorem exec_sicher (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ)
    (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape)
    (b : List Stmt) (Δ Δ' : Umgebung) (s : State)
    (hp : pruefeBlock P erg Δ b = some Δ') (hw : Welt P.D Γ s.world) (hl : WFU Δ s.local')
    (hstuck : exec ρ b s = .stuck) : LogikB ρ b s := by
  rcases pruefeBlock_sicher P Γ ρ hD hU hS erg b Δ Δ' s hp hw hl with hr | hlog
  · rw [hstuck] at hr; exact hr.elim
  · exact hlog

/-- Dieselbe Aussage als Alternative: entweder ein Ausgang mit gehaltener Welt, oder Logik. -/
theorem exec_ausgang_oder_logik (P : Programm) (Γ : Typing) (ρ : Env) (hD : Deklariert P.D Γ)
    (hU : UmgebungOK P Γ ρ) (hS : SchleifenOK P Γ ρ) (erg : Option Shape)
    (b : List Stmt) (Δ Δ' : Umgebung) (s : State)
    (hp : pruefeBlock P erg Δ b = some Δ') (hw : Welt P.D Γ s.world) (hl : WFU Δ s.local') :
    (∃ s', finalState (exec ρ b s) = some s' ∧ Welt P.D Γ s'.world) ∨ LogikB ρ b s := by
  rcases pruefeBlock_sicher P Γ ρ hD hU hS erg b Δ Δ' s hp hw hl with hr | hlog
  · left
    cases ho : exec ρ b s <;> rw [ho] at hr <;> simp only [Ergebnis] at hr
    · exact ⟨_, rfl, hr.1⟩
    · exact ⟨_, rfl, hr.1⟩
    · exact ⟨_, rfl, hr.1⟩
    · exact ⟨_, rfl, hr.1⟩
  · right; exact hlog

/-- **Die Grundfaelle von `Logik` sind genau zwei Klauseln des Schreibers.** Ein `LogikS`
    ohne Unterblock ist ein `requires` an einem Ruf oder eine `invariant` an einer Schleife
    -- nichts sonst. (Die Aussage steht als Satz, damit ein spaeterer Konstruktor, der eine
    dritte Quelle einfuehrt, hier laut faellt.) -/
theorem logik_grundfaelle (ρ : Env) (st : Stmt) (s : State) (h : LogikS ρ st s) :
    (∃ f ps as pre, st = .call f ps as pre) ∨ (∃ n f ps as pre, st = .bindCall n f ps as pre) ∨
    (∃ n f ps as pre err onErr, st = .bindCallElse n f ps as pre err onErr) ∨
    (∃ f ps as pre, st = .retCall f ps as pre) ∨ (∃ id inv body, st = .loop id inv body) ∨
    -- oder die Stelle liegt in einem Unterblock:
    (∃ c t e, st = .ite c t e) ∨ (∃ g bn onP onA, st = .onOption g bn onP onA) ∨
    (∃ g arms, st = .onReason g arms) ∨ (∃ g arms, st = .onTag g arms) ∨
    (∃ l b, st = .locked l b) ∨ (∃ i b, st = .breaking i b) := by
  cases h <;> simp

/-! ## 2. Sprechproben -- der Pruefer sagt ab, wo das Modell steckenbliebe -/

/-- Ein Beispiel-Programm ohne Deklarationen: nur Lokale. -/
def leer : Deklaration := ⟨fun _ _ => none, fun _ => 0, fun _ _ => none, fun _ => none⟩

/-- `x : u32 in 0 .. 5`. -/
def Δx : Lokal := fun n => if n = "x" then some (.intIn 0 5) else none

/-- `1 / x` mit `x in 0 .. 5`: der Nenner schliesst die Null nicht aus -- ABSAGE (`M102`). -/
example : schluss leer Δx (.bin .div (.lit (.int 1)) (.name "x")) = none := by decide

/-- Und im Modell BLIEBE es stecken: bei `x = 0` ist `eval` `none`. Das ist die Stelle, die
    die Absage verhindert. -/
example : eval ⟨fun _ => .absent, fun n => if n = "x" then .int 0 else .absent⟩
    (.bin .div (.lit (.int 1)) (.name "x")) = none := by decide

/-- `1 / y` mit `y in 1 .. 5`: angenommen, als Zahl ohne Bereich (Fund 5). -/
example : schluss leer (fun n => if n = "y" then some (.intIn 1 5) else none)
    (.bin .div (.lit (.int 1)) (.name "y")) = some .int := by decide

/-- `x + x` mit `x in 0 .. 5`: angenommen, und der Bereich ist `0 .. 10` (`M104`). -/
example : schluss leer Δx (.bin .add (.name "x") (.name "x")) = some (.intIn 0 10) := by decide

/-- `x & 3`: Bits ueber nichtnegativen Bereichen -- angenommen. `-x & 3` -- ABSAGE (`M137`). -/
example : schluss leer Δx (.bin .band (.name "x") (.lit (.int 3))) = some .int := by decide
example : schluss leer Δx (.bin .band (.un .neg (.name "x")) (.lit (.int 3))) = none := by decide

/-- `T.slots[x].f` mit `count T = 4` und `x in 0 .. 5`: ABSAGE (`M103`) -- mit `count 6`
    angenommen. -/
def tabelle (count : Int) : Deklaration :=
  ⟨fun c f => if c = "T" ∧ f = "f" then some .bool else none, fun _ => count,
   fun _ _ => none, fun _ => none⟩
example : schluss (tabelle 4) Δx (.place "T" (.name "x") "f") = none := by decide
example : schluss (tabelle 6) Δx (.place "T" (.name "x") "f") = some .bool := by decide

/-! ## 3. Die Axiome -- abgeleitet, nicht behauptet -/

#print axioms Gabbro.Sicherheit.schluss_sicher
#print axioms Gabbro.Sicherheit.pruefe_sicher
#print axioms Gabbro.Sicherheit.exec_sicher
#print axioms Gabbro.Sicherheit.logik_grundfaelle

end Gabbro.Sicherheit
