# Die Korpusschleifen — vier geschrieben, zwanzig benannt

*Gemessen am 2026-08-28, Bahn B, Schritt B5. **Und der teuerste Fund des Schritts ist keine
Invariante, sondern eine Fehlübersetzung**, die er beim Hinschreiben der ersten ausgespült
hat.*

---

## 1. Der Befund, der den Schritt umgedreht hat

Die erste Invariante — `invariant n <= 8` an `46-verneinung :: zaehle_freie` — nahm die
`loop`-Absage weg und legte darunter eine `compound-assignment` frei. Beim Nachsehen, warum
`n += 1` an einem **lokalen** Zähler dort landet, stand das hier:

```bash
ssh ki-pc-fisch-101 'cd gabbro-B && ./target/debug/gabbro lean w24-local.gab'
```

```lean
def zwei_body : List Stmt :=
  [(.bindName "n" (.lit (.int 0))),
   (.ite (.place "b" (.name "i") "belegt") [(.assignGlobal "n" (.lit (.int 2)))] []),
   (.ret (some (.name "n")))]
```

**Lies die drei Anweisungen nacheinander:** binde die *lokale* `n` auf 0 · schreibe an einen
*Weltort* namens `"n"`, den keine Deklaration kennt · gib die *lokale* `n` zurück.

> **Das Datum sagt, die Routine gebe immer 0 zurück. Sie gibt 2 zurück.** Das ist keine
> Absage und keine Vergröberung — es ist ein anderes Programm, und nichts war rot, solange es
> dastand.

`place_term` hat den Unterschied zwischen einem lokalen Namen und einem Weltort **immer**
gemacht — beim **Lesen**. Die Zuweisungsseite hat ihn nie gemacht: jedes suffixlose Ziel wurde
`.assignGlobal`. *Genau die Klasse, die dieselbe Datei drei Zeilen tiefer für die
`traverse`-Variable bucht* — „*Without this it fell through to `.global "opfer"` … That is not
a refusal but a wrong translation.*"

**Im Korpus gemessen: eine lebende Fundstelle**, `messung/abi-proben/zaehlwerk.gab ::
hole_stand` — dessen Datum sagt, die Routine gebe immer 0 zurück, während sie den Stand des
Fachs liest. Nach dem Bau: **null**.

Und die Gefahr ist nicht theoretisch: der Programmexport ist genau das Artefakt, gegen das
eine **von Hand geschriebene** Lean-Spezifikation gehalten wird (`programmlogik/beispiel/`).
*Ein Mensch hätte einen wahren Satz über ein Programm beweisen können, das niemand
geschrieben hat.*

**Geheilt**, und dazu `+=`/`-=` am Lokalen mitgenommen: die Zweideutigkeit, die der
Verbundzweig absagt, sitzt in `&=`/`|=` — Konjunktion an einer Wahrheit, Bitmaske an einer
Zahl. `+=` hat keine zweite Lesart, und `binop .add` ist `none` an allem, was keine zwei
Zahlen sind. *Ein Rumpf, der zu etwas anderem addierte, bliebe STECKEN, statt etwas zu
rechnen, das die Maschine nicht tut.*

---

## 2. Vier Invarianten, und jede sagt, was wirklich gilt

| Schleife | Invariante | woraus sie folgt |
|---|---|---|
| `46-verneinung :: zaehle_freie` | `n <= 8` | der Zähler wächst höchstens einmal je Durchgang, die Domäne hat acht Plätze |
| `19-traversierung :: aktive_zaehlen` | `n <= NSLOTS` | dieselbe Form — und genau die Schranke, die «H2.1» am 2026-08-19 von Hand bewiesen hat |
| `netz/udp-echo :: summe_1071` | `s <= 4294967295` | der Bereich des Typs — und **wörtlich die Nachbedingung** `ensures result <= 4294967295`, die eine Zeile höher steht |
| `fragmente/F10 :: kerne_zaehlen` | `tiefe <= MAXTIEFE` | der `narrow` im Rumpf **ist** der Beweis: er stellt `tiefe < MAXTIEFE` her oder verlässt die Routine, danach `+= 1` |

**Und die Aussage, die man bei drei von vieren eigentlich will, ist nicht schreibbar:**
`n == count(s in slots of w : w.slots[s].aktiv)`. Das ist «B13», und «B13» ist abgesagt
(`messung/AGGREGATION.md`). *Die Schranke ist wahr und schwächer; sie wird als das
hingeschrieben, was sie ist, und nicht als das, was fehlt.*

> **Eine Invariante ist eine Beweispflicht, keine Verzierung** — und das misst sich: das
> Pflichtenregister wächst von **70 auf 74**, weil jede geschriebene Invariante hergestellt
> und erhalten werden muss.
>
> *~~74~~ nachgezogen am 2026-08-30: das Register steht bei **75**, und der Zuwachs dieses
> Schritts ist darin unverändert enthalten — die fünf `S`-Pflichten sagen weiter mit
> `loop` ab (`messung/RUMPFKANAL-ABSAGEN.md` §2).* *Wer Invarianten schreibt, um eine Absage loszuwerden, hat sich
> vier neue Pflichten gekauft.*

---

## 3. Die zwanzig, die abgesagt bleiben — mit Grund

**Kein Beweisziel wurde geschönt.** Wo keine wahre Invariante hinschreibbar war, steht keine.

| Klasse | Schleifen | warum keine Invariante |
|---|---|---|
| **die Löschschleife** | `19 :: aktive_loeschen` | Was gilt, ist *„jeder BESUCHTE Platz ist inaktiv"* — und über die besuchte Menge gibt es keine Domäne. `forall x in slots of w : !w.slots[x].aktiv` ist **mitten in der Schleife falsch**. *Eine Invariante, die nur am Ende gilt, ist eine Nachbedingung.* |
| **die Dienstschleifen** | `04 :: dienstschleife`, `04 :: faellige_wecken`, `39 :: dienst`, `39 :: abarbeiten`, `42 :: sammeldienst` | Sie laufen unbegrenzt und ändern die Tabelle in beide Richtungen. Was über ihnen gilt, ist die **Tabelleninvariante** — und die steht schon an der Tabelle. Sie hier zu wiederholen wäre ein zweites Register über einer Sache (`W7`) |
| **die Wartestellen** | `04 :: auf_quittung_warten`, `41 :: uebertragen_lassen`, `42 :: platz_melden` | Ein `retry` wartet auf eine **Änderung von aussen**. Die Zusage ist das `progress`-Zeugnis und die Schranke, und beide stehen schon da — eine Invariante über einem Zustand, den ein anderer Faden schreibt, wäre eine Behauptung über ihn |
| **die RCU-Schleifen** | `42 :: runde_messen`, `42 :: abgleichen` | Ihr Rumpf steht in `observes` — *ein Blick, der veraltet sein DARF.* Eine Invariante über einer möglicherweise veralteten Sicht bräuchte „gültig, aber nicht aktuell" als Begriff, und den hat weder die Sprache noch das Modell |
| **die Suchschleifen** | `18 :: liegt_unter`, `39 :: erster_dringender`, `39 :: buendel_von`, `netz/udp-echo :: arp_suchen`, `F04 :: poll_used` | Sie verlassen die Schleife beim ersten Treffer. Was gilt, ist *„unter den bisher besuchten ist keiner"* — dieselbe fehlende Domäne wie bei der Löschschleife, und dazu «B10»: eine Schleifenform, die einen **Wert** liefert |
| **die Sammelschleifen** | `09 :: einsammeln`, `caprock/kapraum :: einsammeln`, `F06 :: unberuehrt`, `04 :: manifest_pruefen` | Sie sammeln über einen zweiten Träger. Die Aussage ist eine **Verbindungsinvariante mit Aggregation** — «B13», und mit ihr abgesagt |

**Vier Klassen, und drei davon zeigen auf einen benannten Eintrag:** «B13» (Aggregation),
«B10» (die wertliefernde Schleife) und die fehlende Domäne über der *besuchten* Menge. *Die
vierte — die veraltete Sicht — hat keinen Eintrag und bekommt hier ihren ersten.*

---

## 4. Was der Schritt NICHT gekauft hat

* **Er hat die Rumpfdeckung kaum bewegt: 92 → 94 von 181.** Drei der vier Invarianten legen
  nur eine andere Absage frei — `summe_1071` fällt danach an `carrier-not-a-table` (ein
  Feldzugriff `k.wort[i]` ist kein `slots`-Ort), `kerne_zaehlen` an `narrow`. **Das ist ein
  ehrlicherer Bericht und keine Deckung.**
* **Er hat keine der zwanzig geschönt.** Die Versuchung war messbar: eine Invariante, die eine
  Zahl nennt und nichts behauptet, geht durch `M133` und durch den Prüfer. *Sie stünde dann
  in der Datei und im Register, und niemand könnte sie mehr von einer echten unterscheiden.*
* **Und er hat die Ursache der drei größten Klassen nicht angefasst.** Sie sind «B13», «B10»
  und eine Domäne über der besuchten Menge — drei Konstrukte, und alle drei stehen unter
  Regel A und Tor 2. *Was dieser Schritt liefert, ist die Liste, ohne die niemand entscheiden
  kann, welches davon sich lohnt.*
