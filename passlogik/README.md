# `passlogik` — die Prüferlogik in Lean 4

*Angelegt 2026-08-25. Jede Zahl unten nennt den Befehl, der sie nachrechnet.*

> **Was das ist, und was es ausdrücklich nicht ist:** eine Formalisierung der
> **Spezifikation**, nicht der Implementierung. **Keine Zeile unter `crates/**/*.rs` ist
> beim Schreiben gelesen worden.** Die Quellen stehen je Datei im Kopf, mit
> `datei:zeile`. *Der Wert liegt genau darin: dieses Modell kann dem Rust
> WIDERSPRECHEN. Wer den Rust abschreibt, vernichtet das.*

> **Und der größere Vorbehalt zuerst — er hat zwei Hälften, und die zweite ist die
> unbequemere.**
>
> **(1) Die Naht nach außen.** Ein bewiesener Satz über einem **Modell** ist keine
> Aussage über den **Prüfer**. Was hier steht, sind die Sätze, die das Passregister
> aufschreibt — bewiesen über einer Nachbildung ihrer Regeln. **Die Naht zwischen dem
> Modell und `gabbro-check` ist von niemandem geprüft**, und sie ist die ganze
> Entfernung zwischen dieser Datei und `PROVED` in `gabbro paesse`.
>
> **(2) Die Lücke nach innen, und sie ist gemessen.** Der **Anweisungsabstieg** — was
> ein Rumpf Anweisung für Anweisung tut — steht in **keiner** der sieben Dateien und
> ist in **vieren** als Annahme gebucht (`B1`, `L1`, `P2`, `R1`). Das ist nicht
> dieselbe Aussage wie (1):
>
> > **137 Sätze über ein Modell, dessen tragende Annahme unmodelliert ist.**
>
> *Und es ist genau die Fläche, auf der im Ordner historisch die meisten Funde
> gefallen sind.* Wer diese Datei als „die Logik ist bewiesen" liest, liest über
> beide Hälften hinweg — und die zweite kann keine Anbindung an den Rust heilen,
> weil sie innerhalb des Modells liegt.

---

## Der Befehl, der alles neu baut

```bash
# Auf ki-pc-fisch-101 -- der parallele Bau hat eine Spitze von 3 385 MB und faellt
# damit ueber die lokale 1-GB-Wachhundgrenze. Siehe INSTALLATION.md.
rsync -rlpgoD --delete --exclude '.lake/' passlogik/ ki-pc-fisch-101:gabbro-lean/
ssh ki-pc-fisch-101 'cd gabbro-lean && export PATH=$HOME/.elan/bin:$PATH && lake build'
```

Lokal geht **eine einzelne Datei** (Spitze 539 MB, gemessen 2026-08-25):

```bash
cd passlogik && export PATH=$HOME/.elan/bin:$PATH && lean Passlogik/Bereich.lean
```

---

## Der Stand, in Zahlen

| | | Befehl |
|---|---:|---|
| Dateien mit Sätzen | **7** | `ls passlogik/Passlogik/` |
| Zeilen Lean | **3 240** | `wc -l passlogik/**/*.lean` |
| **Sätze** | **137** | `grep -c '^theorem' passlogik/Passlogik/*.lean` |
| davon **Hauptsätze** mit `#print axioms` an Ort und Stelle | **65** | `grep -c '#print axioms' passlogik/Passlogik/*.lean` |
| „beweist nicht"-Notizen | **54** | `grep -c 'BEWEIST NICHT\|BEWEIST AUCH NICHT'` |
| **eigene `axiom`-Deklarationen** | **0** | `grep '^axiom' passlogik/Passlogik/*.lean` |
| **`sorry`** | **0** | `grep sorry passlogik/Passlogik/*.lean` |
| `mathlib`-Abhängigkeiten | **0** | `cat passlogik/lakefile.toml` |
| Bauzeit auf `ki-pc-fisch-101` | **1,3 s** | `time lake build` |

---

## Die Axiomliste — abgeleitet, nicht gepflegt

**`Abnahme.lean` ist erzeugt** aus den `theorem`-Köpfen und ruft für **jeden** der 137
Sätze `#print axioms` auf. Die Ausgabe **ist** diese Tabelle:

```bash
ssh ki-pc-fisch-101 'cd gabbro-lean && export PATH=$HOME/.elan/bin:$PATH && lake build Abnahme'
```

| Axiomsatz | Sätze |
|---|---:|
| *keine Axiome überhaupt* | **52** |
| `propext` | 41 |
| `propext`, `Quot.sound` | 64 |
| `propext`, `Classical.choice`, `Quot.sound` | 45 |
| **`sorryAx`** | **0** |

> **Es gibt keine eigenen Axiome.** Die drei genannten sind Leans Standardaxiome — sie
> stehen unter *jedem* Lean-Beweis, der `Prop`-Extensionalität, Quotienten oder
> klassische Logik berührt, und sind nicht von dieser Arbeit eingeführt. (Die Zahlen
> zählen 202 Aufrufe: 137 in `Abnahme.lean` plus 65 an Ort und Stelle.)
>
> **`sorryAx` ist die Sprechprobe in die andere Richtung**: taucht es auf, ist ein
> Beweis nicht geführt, und `grep -c sorryAx` wird rot. Heute ist es 0.

---

## Was BEWIESEN ist

### 1. `Bereich.lean` — der Bereichsverband (M1, V1–V3), 46 Sätze

| Satz | Aussage |
|---|---|
| `add_korrekt`, `sub_korrekt`, `neg_korrekt`, **`mul_korrekt`** | das gerechnete Intervall **überdeckt** die wahre Menge. Das Produkt über die vier Ecken ist genau der Satz, den `beweise/Intervall_Aussen.thy`:149 als *„größer und noch nicht da"* offen ließ |
| `schnitt_genau`, `schnitt_ist_infimum`, `huelle_deckt_*` | Schnitt und Hülle sind Infimum und obere Schranke — **semantisch**, nicht nur an den Ecken |
| `add_monoton`, `sub_monoton`, `schnitt_monoton` | Monotonie: eine schärfere Eingabe gibt nie ein schlechteres Ergebnis |
| `echt_enger_faellt`, **`keine_unendliche_verengung`** | **Terminierung der Verengung**: das Maß `hi − lo + 1` fällt echt, also gibt es keine unendliche Kette |
| **`passt_dann_kein_ueberlauf`** | **das Überlauf-Kriterium `M104`**: sagt der Pass „passt", so liegt jeder wirkliche Wert im erklärten Zielbereich |
| `nenner_ok_dann_nicht_null` | die Division hat einen von Null verschiedenen Nenner |
| `v1_ja`, `v1_nein`, `v1_zweige_decken_ab`, `v1_verengt` | **V1**: beide Zweige verengen, und zusammen verlieren sie nichts |
| `v1_traegt_nur_stabil` | die Vorbedingung «B33» als Satz: ohne `stabil` gibt es die Prämisse *„derselbe Wert"* nicht |
| `trichotomie_bricht`, `vier_ausgaenge` | die Vorbedingung von 2026-08-18, **falsifiziert an einem Träger mit einem unvergleichbaren Element** — vier Ausgänge statt drei |
| **`v2_ge`, `v2_gt`** | **V2** — der Satz des Registers mit der größten Last und der geringsten Messung (`CONJECTURED`). *Er lässt sich nicht vergiften; beweisen lässt er sich.* |
| `v3_verengt`, `v3_braucht_erschoepfung` | V3 trägt nur unter `D005` — die Abhängigkeit steht als Prämisse |
| `fakten_ueberleben_schreiben`, `leere_fakten_immer_gueltig` | der Fakt stirbt beim Schreiben; die Schleife trägt keinen hinein |

### 2. `Wirkung.lean` — die Wirkungshülle, 21 Sätze — **der Satz mit der größten Hebelwirkung**

| Satz | Aussage |
|---|---|
| **`huelle_deckt`** | **Erfüllt jede Rufkante `Gerufener.deklariert ⊆ Rufer.deklariert` (`E008`) und deckt jede Liste den eigenen Rumpf (`E005`), so umfasst die deklarierte Menge die transitive semantische Wirkung.** Zwei **lokale** Bedingungen tragen eine **globale** Aussage |
| `zyklus_stoert_nicht` | **an einem echten Zyklus**, ausgeführt an einem Programm mit wechselseitigem Ruf. Die Induktion läuft über die **Ableitung**, nicht über den Graphen — Endlichkeit wird nirgends gebraucht |
| `sem_monoton`, **`absage_haelt_unter_unvollstaendigkeit`** | **die Hülle ist eine UNTERE Schranke**: eine Absage über der Teilsicht gilt auch über der vollen. *Das ist der Satz, der die Korrektur vom 2026-08-24 trägt* |
| `vollstaendigkeit_geht_verloren` | und was wirklich verloren geht: die **Vollständigkeit**, nicht die Widerlegung |
| `alte_pruefung_laesst_durch` | **der Fehler vom 2026-08-24 als Satz**: eine Prüfung, die am Zyklus zurückkehrt, lässt eine wirkliche Verletzung durch |
| `huelle_deckt_mit_fremden`, **`fail_open_bricht_den_satz`** | `E001`: liest ein Werkzeug eine fehlende Klausel als „keine Wirkung", passiert ein Programm, dessen fremder Rumpf schreibt |
| `grob_deckt_mehr`, **`huelle_deckt_grob`** | **der Satz gilt über der ART, nicht über der Wirkung.** Wo der Pass nur die Art vergleicht, deckt `writes a` auch `writes b` |

### 3. `Kosten.lean` — die Kostenrechnung, 22 Sätze

| Satz | Aussage |
|---|---|
| **`L1_obere_schranke`** | **`Ĉ(b) ≥ K(b, r)` für jeden Durchlauf** — Induktion über die Laufableitung, mit Kurzschluss, Zweigkette, `match`, Schleife und Ruf |
| `rekursion_bricht_die_praemisse` | **formal, warum `K001` an jeder rekursiven Funktion fiel**: die Prämisse `Ĉ(rumpf f) ≤ dekl f` erzwingt, dass der ganze übrige Rumpf null kostet |
| `L2_kleinste_belegung`, `ohne_K005_faellt_L2` | der Vergleich bei σ = 0, **und dass `K005` dafür gebraucht wird** |
| `alt_rechnet_zwei`, `neu_rechnet_sechs`, `durchlauf_kostet_sechs`, **`alte_regel_zaehlt_zu_wenig`** | **die gemessene Unterzählung um Faktor 3, maschinengeprüft.** Dieselbe Datei wie `messung/K001.md` §3, dieselben Zahlen 2 und 6 — und ein Durchlauf, der 6 kostet |
| `held_bindet_darunter`, `wartezeit_ist_summe` | `held` bindet **alles darunter**, und die Wartezeit ist die Summe (§9.3 Punkt 4) |
| `schleife_multipliziert` | Rumpf × Domänenschranke |

### 4. `Rang.lean` — die Rangordnung `H006`, 13 Sätze

| Satz | Aussage |
|---|---|
| `rang_steigt`, **`keine_verklemmung`** | **der klassische Schluss**: `r(L₁) < … < r(Lₙ) < r(L₁)` ist ein Widerspruch, also gibt es kein zirkuläres Warten |
| `kein_selbstwarten` | der Sonderfall fällt mit — er ist die Kette der Länge eins |
| `kreuz_erfuellt_lasch`, **`lasch_laesst_verklemmung_zu`** | **warum `>=` und nicht `>`**: mit gleichem Rang steht der klassische Deadlock als Modell da |
| **`null_rueckfall_verwischt`** | **`U005`, 2026-08-24**: fällt ein unbekannter Rang auf `0` zurück, sind zwei verschiedene Sperren ununterscheidbar |
| `keine_verklemmung_partiell` | die richtige Form: ein unbekannter Rang ist **kein** Rang (`H016` + `H014` als Prämissen) |
| `undeklarierte_sperren_bleiben_draussen` | §5b: die Klasse „Verklemmung" ist **größer** als der Satz |
| `rangregel_ist_nicht_notwendig` | §5c: die Regel ist hinreichend, **nicht notwendig** — eine Vollständigkeitslücke, keine Soundnesslücke |
| `kette_ohne_wiederholung` | **die Naht zu `Kosten.lean`**: der echt steigende Rang macht die gehaltene Kette wiederholungsfrei, und erst damit ist `Σ held` eine Zahl |

### 5. `Terminierung.lean` — M4, 14 Sätze

| Satz | Aussage |
|---|---|
| **`kein_unendlicher_abstieg`**, `schleife_endet` | der Kernsatz. *Das ist die ganze Mathematik der Terminierung dieser Sprache* |
| `zaehle_ein_mehr`, **`unvisited_endet`** | **was „by construction" heißt, als Rechnung**: das Maß ist die unbesuchte Restmenge |
| `decreasing_endet`, **`s005_ist_nicht_hinreichend`** | `S005` prüft, dass das Maß **genannt** wird, nicht dass es **fällt** — der Abstand als Gegenlauf |
| `consuming_endet`, **`s008_ist_nicht_hinreichend`** | dasselbe für `S008` |
| `retry_endet`, **`retry_ohne_kosten_endet_nicht`** | siehe **Fund 3** unten |
| `forever_laeuft_ewig`, `forever_traegt_kein_mass` | `forever` endet **ausdrücklich nicht** — die Aussage „jedes Programm terminiert" ist falsch, und zwar nicht aus Versehen |

### 6. `Linear.lean` — M2, 10 Sätze

| Satz | Aussage |
|---|---|
| **`pfad_zaehlt_genau`**, **`genau_einmal`** | unter Zweigabgleich und Schleifenregel verbraucht **jeder Pfad genau so oft, wie der Pass rechnet** |
| `linear_dann_affin`, **`affin_sieht_das_leck_nicht`** | **linear ist nicht affin**, und der Abstand ist genau das **Leck** |
| `unabgeglichen_faellt`, `ohne_abgleich_leck` | ohne `L104` rechnet der Pass 1, ein Pfad verbraucht 0 |
| `schleife_verbraucht_faellt`, `zwei_durchgaenge_verbrauchen_zweimal` | warum ein Wert von *vor* der Schleife im Rumpf nicht verbraucht werden darf |
| **`basisname_verwischt`** | siehe **Fund 4** unten |

### 7. `Phasen.lean` — `O001`–`O006`, 11 Sätze

| Satz | Aussage |
|---|---|
| **`fluss_geht_vorwaerts`**, `ein_schritt_kommt_voran` | der Fluss geht nie zurück, und ein Schritt kommt echt voran |
| `zusagen_komponieren` | `O004` komponiert — die Bootkette auf eine Zeile |
| `zweige_treffen_sich`, `ohne_o006_zwei_stufen` | `O006`, und was ohne es geschieht |
| `hoechstens_so_viele_schritte` | **die Ordnung ist endlich, also ist die Kette endlich** |
| `schritt_stufen_verschieden`, `kein_zweiter_durchgang` | **warum ein Schritt in einer Schleife abgelehnt wird — der Grund ist `O003`, nicht eine eigene Regel** |
| `ordnung_ist_nicht_umsonst` | *„ein linearer Wert erzwingt eine KETTE, aber nicht WELCHE"* — als Satz |

---

## Was ANGENOMMEN ist

**Es gibt keine `axiom`-Deklaration.** Jede Annahme steht als **Prämisse eines Satzes**
oder als Definitionsentscheidung im Dateikopf — sie ist damit an der Aufrufstelle
sichtbar und nicht in einer globalen Liste versteckt.

| Kennung | Datei | Was angenommen wird |
|---|---|---|
| **A1** | `Bereich` | die Zielbreite ist als Intervall **gegeben**; dass `u32` gerade `[0, 4294967295]` ist, steht hier nicht |
| **A2** | `Bereich` | die konkrete Semantik ist die **unbeschränkte** Rechnung über `Int` — dieselbe Modellwahl wie `messung/P6.md`:75 |
| **A3** | `Bereich` | `stabil` ist ein **Prädikat**, kein Beweis |
| **B1** | `Wirkung` | `eigen f` — was der Rumpf selbst tut — ist **gegeben**. Der Anweisungsabstieg steht nicht hier; er ist die Klasse `W16` |
| **B2** | `Wirkung` | eine `extern fn` bekommt **keine** Rumpfprüfung; ihre Deklaration geht als Wahrheit ein. **Als Prämisse `fremd_ehrlich` sichtbar gemacht** |
| **B3** | `Wirkung` | die Vergleichbarkeit zweier Orte ist eine gegebene Relation |
| **K1** | `Kosten` | **`Ĉ(konstanter Ausdruck) = 0` ist eine Aussage über den ERZEUGER** — `messung/K001.md` §5 nennt sie selbst „die schwächste Stelle des ganzen Arguments" |
| **K2** | `Kosten` | die Fallliste ist die aus `messung/K001.md` §3; ob sie **vollständig** ist, fällt hier nicht |
| **K3** | `Kosten` | `retry … bounded N` — dass ein Durchlauf innerhalb von `N` bleibt, ist die **Laufzeit**-Zusage des Wächters |
| **K4** | `Kosten` | die Domänenschranke ist **gegeben**. *Genau in dieser Lücke lebte der `mappings of`-Fehler* |
| **R1** | `Rang` | **die Rangdisziplin ist eine Prämisse.** Dass `geteilt.rs` sie an **jeder** Nahmestelle herstellt, ist der offene Posten aus `messung/H006.md` §6 |
| **R2** | `Rang` | der Rang ist total (`H014`, `H016`) — §4 zeigt, was ohne das geschieht |
| **R3** | `Rang` | nur **deklarierte** Sperren |
| **T1–T3** | `Terminierung` | Domänenschranke; **dass** das Maß fällt; die wohlfundierte Ordnung von `by consuming` |
| **L1–L3** | `Linear` | die Verbrauchsstellen sind gegeben; Divergenz ist draußen; Alias und Geisterlöschung sind draußen |
| **P1–P3** | `Phasen` | der Index ist die Ordnung; der Anweisungsabstieg steht nicht hier; die weichere Lesart ist nicht modelliert |

---

## Was ausdrücklich NICHT bewiesen ist

1. **Die Naht zum Rust.** Kein Satz hier sagt etwas über `gabbro-check`. Das Modell
   nachzubilden ist **nicht** dasselbe wie die Implementierung zu prüfen — und die
   Klasse, in der das schiefgeht, hat einen Namen: `W16`, *ein Werkzeug, das eine
   Mischung misst, sieht plausibel aus.*
2. **Der Anweisungsabstieg**, in **jeder** Datei. Alle sieben Modelle nehmen an, dass
   der Prüfer die Stellen **findet**, um die es geht. Das Passregister nennt dafür in
   fast jedem Satz Schweigestellen (`_`-Arme, `let … else`, `until`-Prädikate,
   `traverse`-Gegenstände). **Genau dort sind bisher die meisten Funde gefallen.**
3. **Der Erzeuger.** `K1` ist die schärfste Form davon: L1 hängt an einer Aussage über
   6 976 Zeilen `emit.rs`, die niemand aufgeschrieben hat.
4. **Alias.** In `Bereich` als Prämisse `andere_unveraendert`, in `Linear` als (L3), in
   `Rang` gar nicht. `messung/RACE.md` führt sie als A2/A3, und **nichts trägt sie**.
5. **Fortschritt.** `keine_verklemmung` sagt nicht, dass jeder Faden drankommt.
6. **Vollständigkeit, überall.** Jeder Satz hat die Form *„wer durchgeht, erfüllt X"* —
   nie *„wer X erfüllt, geht durch"*. `rangregel_ist_nicht_notwendig` misst diesen
   Abstand an einer Stelle aus.
7. **Die Speichermodell-Hälfte.** `paarung.ordnung`, `m3.barriere` und `V2` §4d liegen
   in der Axiomschicht (A10) und sind hier nicht angefasst.
8. **`mathlib`-Tiefe.** Wo ein Satz sie gebraucht hätte, ist er **weggelassen und
   benannt** — siehe unten.

### Was `mathlib` gekostet hätte, und deshalb fehlt

| weggelassen | warum |
|---|---|
| die **Schärfe** der Intervallmultiplikation (nicht nur die Überdeckung) | braucht die Fallunterscheidung nach Vorzeichen als eigene Theorie; die **Überdeckung** ist der tragende Teil und steht |
| das **Ergebnisintervall der Division** | Rundungsrichtung. `messung/P6.md`:85 sagt es für Isabelle: *„Isabelles `div` auf `int` rundet gegen minus unendlich, C schneidet gegen null ab"* — dieselbe Absage, derselbe Grund |
| IEEE-754 | `beweise/Intervall_Aussen.thy` bucht es schon als Annahme; ohne AFP/mathlib gibt es keinen Träger |
| `Finset`/`Fintype` in `Wirkung` | **wurde nicht gebraucht** — und das ist ein Ergebnis: der Hauptsatz hängt nicht an der Zahl der Funktionen, sondern an der Form der Induktion |

---

## Die Funde — wo die Spezifikation beim Formalisieren nachgab

*Das ist der eigentliche Ertrag. Jeder Fund nennt die Quellstelle und den Satz, der ihn
festhält.*

### Fund 1 — V2: „hat den Typ" oder „wird geschnitten mit"? · `SPRACHE.md`:685

> *„under the fact `a >= b`, `a - b` **has type** `0 .. a.max − b.min`"*

Wörtlich gelesen **ersetzt** V2 das gewöhnlich gerechnete Intervall. Das ist sound —
aber es ist **nicht immer eine Verengung**: für `a = [10,10]`, `b = [0,0]` liefert die
gewöhnliche Subtraktion die **exakte** Antwort `[10,10]`, die wörtliche V2-Regel
`[0,10]`. **An einer Stelle, an der V2 helfen soll, weiß der Prüfer dann weniger.**

*Satz:* `Bereich.v2_woertlich_ist_nicht_immer_enger`. Die zweite Lesart — schneiden —
steht daneben als `sub_v2` mit `sub_v2_nie_schlechter`. **Der Text lässt beide zu und
entscheidet nicht.**

### Fund 2 — `E008` vergleicht die ART, nicht die Wirkung · `gabbro paesse --je-satz`

Das Passregister sagt zu `wirkungen.abschluss`: *„places are compared only for known
world state: for everything else only the KIND is compared, so `writes a` covers
`writes b`."* Beim Formalisieren wird daraus eine harte Aussage über den **Satz selbst**:

> **`huelle_deckt` gilt dann nicht über `Wkg`, sondern über `Art`.**

Das ist eine echt schwächere Aussage, und sie steht so in keiner Satzformulierung des
Registers — dort liest sich `HOLDS` wie eine Aussage über Wirkungen. *Satz:*
`Wirkung.huelle_deckt_grob` und `Wirkung.grob_deckt_mehr`.

### Fund 3 — `retry` endet „durch `bounded`" nur, wenn ein Durchgang etwas kostet · `SYNTAX.md`:902

> *„`retry` | ends? **yes, through `bounded`** | termination as a NUMBER"*

Das Maß ist das Restbudget. **Fällt es nicht, endet nichts.** `K006` hält die Schranke
gegen den Rumpf — das ist die **obere** Seite. Eine **untere** gibt es nirgends, und
`SPRACHE.md`:949 stellt ausdrücklich fest, dass `if`, `match`, `return` und `leave`
**nichts** kosten.

> **Die Spezifikation sagt an keiner Stelle, dass ein `retry`-Durchgang mindestens eine
> Operation kostet.** Ohne diese Zusage folgt „endet durch `bounded`" nicht.

*Sätze:* `Terminierung.retry_endet` (mit der Bedingung) und
`Terminierung.retry_ohne_kosten_endet_nicht` (ohne sie). *Was hier nicht entschieden
wird:* ob die Grammatik einen solchen Rumpf zulässt und ob das `until`-Prädikat ins
Budget zählt. **Das ist die Frage, die der Text offenlässt.**

### Fund 4 — der Basisnamenvergleich in M2 ist eine Abstraktion mit einer Richtung · `gabbro paesse --je-satz`

*„consumption matches on the BASE NAME, so `wecken(p.feld)` counts as consuming `p`."*
Das steht im Register als **eine Lücke unter mehreren**. Formalisiert zeigt sich, dass
sie in der **unsicheren** Richtung verliert: der Pass sieht für die Basis `p` eine `1`,
während `p.a` einmal und `p.b` **null**mal verbraucht wird — ein Leck, das der Pass
**nicht sehen kann**, nicht bloß eines, das er übersieht.

*Satz:* `Linear.basisname_verwischt`.

### Fund 5 — „jedes Programm terminiert" ist keine Aussage dieser Sprache · `SYNTAX.md`:855

Der Auftrag an diese Formalisierung lautete: *„die drei Schleifenformen mit ihren
Abstiegsmaßen ⇒ jedes Programm terminiert."* **Der Satz ist falsch**, und `SYNTAX.md`
sagt es selbst in der Überschrift: *„three forms, and infinite is one of them. The rule
is not 'every loop ends' but: what a loop may do stands beside it."*

Dazu kommt: es sind **vier** Formen mit einem Maß, nicht drei — `traverse` hat drei
Spielarten (`unvisited`, `decreasing`, `consuming`), `retry` ist die vierte, `forever`
die fünfte ohne Maß. **Und Rekursion ist eine zweite Quelle**, die `K008`/`K009` mit
`decreases` abdecken — wieder nur notwendig, nicht hinreichend.

*Sätze:* `Terminierung.forever_laeuft_ewig`, `forever_traegt_kein_mass`,
`programm_endet_unter_massen` (die ehrliche, bedingte Form).

### Fund 6 — `S005` und `S008` haben denselben Abstand, und er ist messbar

Das Register nennt beide als *„necessary, not sufficient"*. Formalisiert sind es zwei
Sätze mit **identischer Struktur**: die geprüfte Bedingung ist ein Prädikat über dem
**Text**, die gebrauchte eine über dem **Lauf**, und zwischen beiden liegt ein
konkreter Gegenlauf. *Sätze:* `Terminierung.s005_ist_nicht_hinreichend`,
`s008_ist_nicht_hinreichend`. **Das ist keine Kritik an den Regeln** — es ist die
Buchung, dass beide dieselbe Naht haben und deshalb derselbe Beweiser sie schließen
müsste.

### Fund 7 — warum `K001` an jeder rekursiven Funktion fiel, folgt aus der Prämisse

`messung/K001.md` §4 und `SYNTAX.md`:749 stellen den Befund fest. **Formalisiert ist er
kein Befund, sondern eine Folgerung:** die Prämisse des Satzes lautet
`Ĉ(rumpf f) ≤ dekl f`, und ein Selbstruf zählt `dekl f` — also erzwingt sie, dass der
ganze übrige Rumpf **null** kostet. *Satz:* `Kosten.rekursion_bricht_die_praemisse`.
*Das war vorher eine Beobachtung; jetzt ist es eine Rechnung.*

---

## Was als nächstes den meisten Wert hätte

1. **Die Naht.** Ein Differenztest zwischen `kostenK` aus `Kosten.lean` und dem, was
   `gabbro pruefe` an einer Datei rechnet. *Solange die fehlt, ist jeder Satz hier ein
   Satz über ein Modell.*
2. **Fund 3 entscheiden.** Entweder die Spezifikation sagt, dass ein `retry`-Durchgang
   mindestens eine Operation kostet — oder `SYNTAX.md`:902 muss die Zeile
   *„ends? yes, through `bounded`"* zurücknehmen.
3. **Fund 1 entscheiden.** Eine Zeile in `SPRACHE.md`:685: ersetzt V2 oder schneidet es?
4. **Die Domänensätze aus `messung/K001.md` §6.** Drei kleine Sätze, je einer pro
   Domänenform — sie sind der Unterschied zwischen `kosten.domaenenschranke`
   `CONJECTURED` und `PROVED`, und sie passen in dieses Modell.
