# Werkzeugkasten — Arbeitsregeln, die dieser Ordner sich erarbeitet hat

**Aufnahmebedingung:** Eine Regel kommt hier nur hinein, wenn sie aus einem **Fehler in diesem
Ordner** stammt und der Fehler benannt ist. Keine guten Vorsätze, keine übernommene Weisheit.
Wer eine Regel liest, soll den Schaden sehen können, für den sie bezahlt wurde.

> Die **Fallen**-Nummerierung (`Falle 80` …) steht in
> [`fallen-klassifikation.tsv`](fallen-klassifikation.tsv) — 100 bezahlte Caprock-Fallen,
> Quelle `CLAUDE.md`, Stand 2026-08-13. Diese Datei ist ein **gemessener Bestand mit
> genannter Quelle**; nichts wird ihr nachträglich hinzugefügt. Die `W`-Nummern hier sind
> eigene und stehen daneben, nicht darin.
>
> `Falle 80` lautet dort wörtlich: *eine Zahl, die ein Mensch parallel zur Wahrheit fuehrt*
> (Klasse `S`, `ableitung`). **W1 und W2 unten sind beide Kinder dieser Falle** — einmal im
> Messgerät, einmal in der Deklaration.

---

## W1 — Eine Deckungszahl zählt Belege, nicht Versuche

*Neben Falle 80: eine Zahl, die ein Mensch parallel zur Wahrheit führt.*

**Der Schaden.** Am 2026-08-14 wuchs der Prüfer um fünf Regeln, und ich schrieb fünf
Mutationen dazu. Die Zusammenfassungszeile druckte `37 von 37` — aus `len(MUTATIONEN)`, also
aus der Zahl der **geschriebenen** Mutationen. Gleichzeitig hatte eine ältere Mutation
(`sperre-egal`) ihren Anker verloren, weil ich die Zeile umgebaut hatte, auf die sie zielte.
Sie lief gar nicht. **Eine tote Mutation zählte als Deckung.**

**Warum das schlimmer ist als eine ungeprüfte Regel.** Ein Loch, von dem man weiss, ist ein
Posten. Eine Deckungszahl, die Löcher als Deckung zählt, **entwertet jede andere Zahl im
Ordner** — denn sie ist die Zahl, mit der man die anderen prüft. Es ist die Wunschform *im
Messgerät*.

**Die Regel.** Jede Deckungs-, Abdeckungs- oder Fortschrittszahl wird aus **verifizierten
Belegen** gebildet, nie aus der Zahl der Versuche, Einträge oder Zeilen. Wo ein Beleg
ausfallen kann (toter Anker, übersprungene Probe, nicht gebaute Fläche), muss der Ausfall die
Zahl **senken**, nicht sie unberührt lassen.

**Der Handgriff.** `mutiere-pruefer.py` zählt jetzt `gefangen` von `gültig`; ein verlorener
Anker erscheint als `ANKER FEHLT` und **fällt aus dem Nenner heraus, nicht in den Zähler**.

---

## W2 — Die Nullzusage: der Prüfer ist das Messgerät für die Zahlen, die er prüft

**Der Anlass.** Für ein neues Beispiel brauchte ich drei `costs`-Zeilen. Statt sie zu schätzen,
habe ich sie auf `1 ops` gedrückt, den Prüfer die wahren Zahlen nennen lassen (`4`, `2`, `2`)
und diese eingetragen. **Die Zahlen fielen aus dem Rumpf, nicht aus dem Wunsch.**

**Der Rückfall, der darin steckte.** Das Verfahren war richtig, der Handgriff war Handarbeit —
und Handarbeit an einer Zahl ist genau die Stelle, an der eine Zahl beginnt, parallel zur
Wahrheit zu laufen. Ein Verfahren, das Disziplin braucht, ist ein Verfahren mit Ablaufdatum.

**Die Regel.** Wo ein Pass eine deklarierte Zahl **prüft**, muss er sie auch **nennen können**.
Eine Zusage schreibt man ab, man errät sie nicht.

**Der Handgriff.** `gabbro kosten datei.gab` druckt je Funktion die gerechnete Rumpfzahl neben
der zugesagten und je `locks`-Block die gerechnete Haltezeit neben `held` bzw. `shared held`.

```
-- Stelle                                  gerechnet  zugesagt  Luft
rechte_aufloesen                           4          4         0
  rechte_aufloesen / shared held KAPPEN    4          4         0
```

**Die Spalte `Luft` ist eine Differenz, kein Urteil** — und die beiden Fälle sind
verschieden: bei `costs` ist Luft oft richtig (eine Signatur soll nicht bei jeder
Rumpfänderung brechen), bei `held` fast immer falsch, **denn die Latenzaussage rechnet mit der
Zusage, nicht mit der Rechnung**.

**Wo es wieder gebraucht wird:** `held`, `shared held` (heute schon), `per_pass bounded` —
dort mit dem bekannten Vorbehalt, dass eine eingabeabhängige Schranke keine Zahl ist, sondern
ein Term.

---

## W3 — Kein Konstrukt ohne gemessenen Bedarf

**Zweimal bezahlt.** `abi { … }` wurde gestoppt, bevor es geschrieben war. `locks ordered`
starb am Papiertest vom 2026-08-14 mit **null Prüffällen** — und die Antwort war stärker als
die Frage: es gab im ganzen Baum keine einzige Mehrfachnahme derselben Sperrklasse.

**Die Regel.** Ein Konstrukt braucht **gezählte** Fundstellen im echten Code, bevor die erste
Grammatikzeile steht. Nicht plausible, nicht erinnerte — gezählte.

**Die Probe, ob die Regel wirkt:** Der Test muss seinen eigenen Kandidaten töten dürfen. Ein
Papiertest, der nur bestätigt, ist eine Vorführung. *Derselbe Test fand statt des bestätigten
Konstrukts zwei Lücken, die auf keiner Liste standen — der Ertrag war grösser als der
Verlust.*

---

## W4 — Eine laute Übertreibung ist billiger als eine stille Ausnahme

**Der Fall.** `locks shared` steht, aber der Zeuge an der **Aufrufgrenze** braucht den
Aufrufgraphen, den es noch nicht gibt. Ohne Regel wäre die Grenze nicht bloss ungeprüft,
sondern **durchlässig**: der Gerufene schreibt exklusiv-berechtigt, der Rufer hält nur geteilt
— `H001` durch die Hintertür.

**Die Regel.** Wo eine tragende Regel ein Loch hat, das erst später richtig zu schliessen ist,
kommt die **grobe, zu strenge** Fassung davor — nicht nichts. Sie muss als Zwischenregel
**benannt** sein, mitsamt dem, was sie zu viel verbietet, und mitsamt der Prüfung, die sie
ersetzen wird.

**Warum.** Nach einer lauten Übertreibung sucht jemand — sie steht im Weg. Nach einer stillen
Ausnahme sucht niemand, denn sie sieht aus wie ein Grün.

**Der Handgriff.** `H005`: ein geteilter Block ruft keine Funktion mit `requires Held(…)`.
Punkt. Auch die einer anderen Sperre, was zu viel ist und in der Absage dransteht.

---

## W5 — Eine Zwischenregel trägt drei Teile, sonst wird sie zur Dauerregel

*W4 sagt, **dass** die grobe Fassung davorkommt. W5 sagt, **wie** sie geschrieben sein muss,
damit sie später wirklich ersetzt und nicht bloss gewohnt wird.*

**Der Anlass.** `H005` ist absichtlich zu streng. Eine zu strenge Regel ohne Ablaufvermerk
wird nach drei Monaten für die richtige gehalten — niemand weiss mehr, was sie zu viel
verbietet, also traut sich niemand, sie anzufassen. **Die Übertreibung, die W4 rechtfertigt,
ist genau das, was sie später unantastbar macht.**

**Die Regel.** Eine konservative Zwischenregel nennt in ihrer eigenen Absage:

1. **die Regel** — was sie verbietet;
2. **den Preis** — was sie zu viel verbietet, konkret, nicht als „ggf. zu streng";
3. **die Ablösung** — welche Prüfung sie ersetzen wird und was diese können muss.

**Warum in der Absage und nicht im Ticket.** Ein Ticket liest, wer aufräumt. Die Absage liest,
wer gerade dagegenläuft — und das ist derjenige, der den Preis zahlt und ihn deshalb melden
kann.

**Der Handgriff.** `H005` trägt alle drei Teile als Notizen. Bei Pass 8 wird es nicht das
letzte Mal gewesen sein.

---

## W6 — Das Weglassen einer Laufzeitprüfung ist ausschliesslich M1-begründet, nie invariantenbegründet

**Der Schaden, eine Ebene höher schon gebucht.** `5904cae`: eine Behauptung über den Baum
glätten, statt den Baum zu befunden. Derselbe Griff eine Ebene tiefer wäre: eine
Bereichsprüfung aus dem erzeugten C streichen, **weil der Beweis sagt, es könne nicht negativ
werden**.

**Die zwei Netze, und warum sie nicht dasselbe sind.**

| | woran es hängt | wer es nachrechnet |
|---|---|---|
| **M1** | am **Typ** (`u32 in 0 ..= NSLOTS`) | das Typsystem, **je Programm**, jedes Mal |
| **Invariante** | an der **Schablone**, die sie erhält | die Vertrauensfläche — einmal, für alle |

Die Verus-Vorlage `cap_space.rs` führt `refcount : nat` und beweist `oldrc >= 1` (Zeile 792)
**aus der Invariante**. Das ist richtig — und es ist **genau ein Netz**. Gabbros
`u32 in 0 ..= NSLOTS` gibt ein zweites, das **ohne** die Invariante hält; es war das, was in
der Sprechprobe als `M104` neben `D001` fiel.

**Die Regel, mechanisch, an jeder Emissionsentscheidung, die einen Beweis zitiert:**

> **Das zitierte Faktum muss aus M1 allein ableitbar sein. Sonst bleibt die Prüfung im C.**

**Warum das billiger ist als die Spezialfassung.** Die enge Form — *kein von einer Schablone
erzeugtes Feld trägt einen Typ ohne Breite* — deckt Felder. Zwischenwerte deckt sie nicht,
und künftige Konstrukte deckt sie erst recht nicht; dort geht dasselbe Loch wieder auf. W6
sitzt stattdessen **an der Entscheidung** statt am Gegenstand: **eine Zeile im
Emissionspass statt einer je Konstrukt.**

*Vorgemerkt für eine Fläche, die es noch nicht gibt.* Der Emissionspass ist nicht gebaut —
`mutiere-pruefer.py` weist ihn mit **0 Mutationen** aus. Diese Regel ist damit heute eine
**Vorabfestlegung**, keine geprüfte Zusage, und sie steht hier, damit sie beim Bauen nicht neu
erfunden werden muss. **Was 0 Mutationen hat, ist nicht gedeckt, sondern unbeschädigbar.**
