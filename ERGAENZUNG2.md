# ERGÄNZUNG 2 — die offenen Posten der Ergänzung, und der Prüfer als Plan

**Nachtrag zu [`FESTLEGUNG.md`](FESTLEGUNG.md) und [`ERGAENZUNG.md`](ERGAENZUNG.md).** Die erste
Ergänzung hat vier offene Ebenen hinterlassen: Löcher in den eigenen Konstrukten (das größte: RMW),
ungelaufene Messungen, grundsätzlich Unbehauptetes, und die Tatsache, dass keine Zeile Prüfer
existiert. Dieses Dokument schließt die erste Ebene, benennt die zweite und dritte als
Arbeitsliste mit Reihenfolge — und legt für den Prüfer einen **Plan mit Stufen und Toren** fest
statt einer Absichtserklärung.

> **EINGETRAGEN und ABGELEITET (2026-08-14).** Abnahmepunkt 2 dieses Dokuments verlangt, die
> Wortzählung **von der vereinigten Wortschatztabelle** zu nehmen statt von Hand (Falle 80). Der
> Terminaldeckungs-Wächter hat gezählt: **17 neue Wörter** über beide Ergänzungen —
> `awaits entry regs out preserves clobbers stack dispatch vector` (9, die Zählung von
> ERGAENZUNG.md war **richtig**) plus
> `exchange update returns nested ist per cpu masked` (**8**, nicht 5).
> §3.2 nannte selbst schon sieben und liess die Drift absichtlich stehen; **es fehlte zusätzlich
> `masked`.** Damit ist der Punkt geschlossen: **die Zahl kommt jetzt aus der Tabelle, nicht aus
> einem Kopf.**

Stand 2026-08-14. **Neue Wörter (abgeleitet, acht):** `exchange update returns nested ist per cpu masked`
**Berichtigung an ERGAENZUNG.md:** `preserves { all }` benutzte ein Wort außerhalb des
Wortschatzes — das eigene Dokument verletzte die eigene Regel, und der Terminaldeckungs-Wächter
hätte es gefunden, wenn er gelaufen wäre. `all` wird **nicht** aufgenommen; ein Eintritt zählt
seine Register auf (D2 heißt vollständig, nicht bequem). Das Timer-Beispiel ist entsprechend zu
korrigieren.

---

## 1. RMW — die dritte Form der Paarung

**Das Loch:** `publishes` sitzt am Store, `awaits` am Load; `fetch_add`, `compare_exchange`,
Ticket-Nehmen sind **beides in einem Befehl**. Ohne dritte Form zählt die Ordering-Stichprobe
einen vierten Ausgang und widerlegt §1 der Ergänzung an der eigenen Abnahme.

```ebnf
exchstmt = "let" ident "=" place "exchange" xform
           [ "publishes" ( placelist | "nothing" ) ]
           [ "awaits"    "{" placelist "}" ] ";" ;
xform    = "update" "(" ident ")" block          (* der Rumpf rechnet alt -> neu; rein, M1 *)
         | expr "when" pred "returns" ident ;    (* compare-exchange: neu when alt-Bedingung *)
```

```gabbro
-- Ticket nehmen: publiziert nichts, erwartet nichts — reiner Zaehler
let my = NEXT_TICKET exchange update(t) { t + 1 } publishes nothing;

-- Besitzuebernahme: CAS, der bei Erfolg Sichtbarkeit erwirbt UND weitergibt
let won = FP_OWNER[core] exchange my_tid when old == NOBODY returns old
          publishes { FP_STATES[my_tid] }
          awaits    { FP_STATES[old] };
if won == NOBODY { -- Erfolgzweig: awaits-Plaetze lesbar, publishes-Zusage aktiv
}
```

**Regeln, alle Typregeln:**

1. Der `update`-Rumpf ist rein (`effects { pure }` impliziert), M1-typisiert — ein Überlauf im
   RMW ist damit ein Übersetzungsfehler, kein 2-Uhr-nachts-Fund.
2. `publishes` am `exchange` erzwingt mindestens release, `awaits` mindestens acquire, beides
   zusammen acq_rel — **abgeleitet**, wie in Ergänzung §1.3.
3. Sichtbarkeit aus `awaits` entsteht **nur im Erfolgzweig** (V3-artig über das `returns`-Ergebnis).
4. Die Paarungspflicht gilt über alle drei Formen gemeinsam: ein `publishes` kann von einem Load
   **oder** einem `exchange` empfangen werden; abgeglichen wird die vereinigte Menge.

**Absenkung:** `atomic_fetch_*` wo der `update`-Rumpf einem Primitiv entspricht (Abgleich über
eine geschlossene Mustertabelle: `t+1`, `t-1`, `t|m`, `t&m`, `max` via `accumulates`), sonst die
**beschränkte** CAS-Schleife — beschränkt, weil sie im Übersetzer als `retry bounded NCORES *
K ops on_exceeded contention` emittiert wird, mit K aus der `held`-Rechnung: die Sprache emittiert
nichts, was sie verbietet (die `accumulates`-Lektion, verallgemeinert).

---

## 2. Sichtbarkeit über Funktionsgrenzen: `Vis` wird reichbar

**Das Loch:** Sichtbarkeit war ein Zweigfakt und starb an der Funktionsgrenze — prüft eine
Funktion die Flagge und liest eine andere die Nutzlast (der übliche Schnitt), war das korrekte
Programm nicht schreibbar.

**Die Lösung ist kein neues Konstrukt, sondern die konsequente Anwendung von M2:** der
Erfolgzweig eines `awaits`-Loads/-`exchange` **erzeugt** `linear ghost Vis(P)` je erwartetem
Platz. `Vis` ist reichbar wie jeder Geisterwert (Parameter, Rückgabe), das Lesen eines
fremd-publizierten Platzes verlangt `&Vis(P)` geliehen, und die Erzeugerliste aus Festlegung §4
wird um `Vis` ergänzt: **nur** der Erfolgzweig erzeugt es, ein von Hand gebauter Beleg ist ein
Typfehler. Verbrauch ist nicht nötig (Sichtbarkeit erlischt nicht) — `Vis` ist der eine
**affine** Geisterwert der Sprache, und dass er affin statt linear ist, steht hier als
Entscheidung mit Grund, nicht als Versehen.

---

## 3. Eintritt — die fünf Nachträge

### 3.1 Der Syscall, der nicht zurückkehrt (der Normalfall des Mikrokernels)

`regs out` beschreibt den Rückweg **in denselben Thread**. `dispatch` darf stattdessen in
`switch_to`/`resume` enden — dann gilt: der Eintritt hat **zwei typisierte Ausgänge**, `returns`
(regs out an den Rufer) und `resume k` (voller Kontext aus `k`, der `regs out`-Vertrag ist
gegenstandslos, weil der komplette Registersatz aus dem Zielkontext kommt). Die `entry`-Deklaration
nennt beide:

```gabbro
entry syscall arch x86_64 {
    regs in  { nr: rax, a0: rdi, a1: rsi, a2: rdx, a3: r10 }
    regs out { ret: rax }                  -- Ausgang 1: returns
    preserves { rbx, rbp, r12, r13, r14, r15, rsp_user }
    clobbers  { rcx, r11 }
    stack KernelStack
    dispatch caprock::syscall::dispatch;   -- -> Result | never (resume)
}
```

Der Dispatch-Rückgabetyp `Result | never` macht die zwei Ausgänge im Typ sichtbar: `return`
nimmt Ausgang 1, `resume` Ausgang 2. Der gesicherte Rufer-Kontext ist dabei ein gewöhnlicher
`Context`-Wert — wer ihn fallen ließe, verlöre einen Thread, also ist `Context` **linear**:
`return` verbraucht ihn in den Rückweg, `resume` legt ihn in die Ablage des Schedulers. Ein
vergessener Thread ist damit ein Typfehler — dieselbe Klasse wie `Parked`.

### 3.2 Stapel je CPU, Verschachtelung, NMI

```ebnf
entryextra = [ "stack" ident [ "per" "cpu" ] [ "ist" constexpr ] ]
             [ "nested" ( "never" | "masked" | "bounded" constexpr ) ] ;
```

`stack KernelStack per cpu` macht den Per-CPU-Stapel zur Deklaration (die Auswahl emittiert die
eine `iasm`-Stelle aus `gs`/`tpidr`). `nested never` (Syscall), `nested masked` (IRQ läuft mit
maskierten Interrupts), `nested bounded 1` (ein Ebenenwechsel erlaubt) — die
Verschachtelungstiefe ist damit M1-Material statt Konvention. NMI und Doppelfehler nehmen
`ist n` (eigener Stapel aus der Interrupt-Stack-Table) und **dürfen nur `raw`-freien, sperrenlosen
Code rufen** (`effects` des Dispatch-Ziels: kein `locks`) — der klassische NMI-Deadlock ist
nicht schreibbar.

Neue Wörter dafür: `nested`, `ist`; `per` und `cpu` — Moment: **vier**, plus `exchange update
returns` aus §1 sind sieben. Die Kopfzeile nennt fünf; das ist genau die Drift, die der
Terminaldeckungs-Wächter fängt, und sie bleibt hier absichtlich stehen als Erinnerung, dass die
**Grammatikvereinigung vor allem anderen** laufen muss (§6, Stufe P1).

### 3.3 `Result`-Kodierung

Ein `regs out`-Register trägt einen `tagged`-Wert nur über eine deklarierte Kodierung:
`ret: rax = Result { Ok(v) -> v in 0 .. 0x7FFF_FFFF_FFFF_FFFF, Err(e) -> -(e as i64) }` — die
Kodierung steht an der `entry`-Deklaration, Stubs und Dispatcher erzeugen beide Seiten daraus.
Eine Kodierung, die die Wertebereiche überlappen ließe, ist ein Übersetzungsfehler (D2).

### 3.4 FP-Besitz, entworfen statt skizziert

`FpArea` ist je Thread, **eager** gesichert im `switch_to`-Primitiv (die lazy-Variante ist die
CVE-2018-3665-Falle und wird nicht angeboten — eine Entscheidung, keine Lücke). `MayUseFp(tid)`
ist ein linearer Geisterwert am Thread; `xsave`/`xrstor`-Axiome verlangen ihn geliehen. Damit ist
FP-Zustand Besitz wie jeder andere, und der Sonderpfad verschwindet.

### 3.5 Der Rand des Boot-Satzes, benannt

S2 deckt die Gabbro-Ebene. **Außerhalb der Sprache liegen:** die frühe Trampolinstrecke
(physisch→virtuell, vor der ersten Gabbro-Zeile) und das Linkerskript (Sektionsgrenzen,
`.boot`-Platzierung). Beide wandern als **benannte Annahmen** in die Axiomschicht
(`assume linker_boot_disjoint … falsifier probe_sections;` — die Sonde liest die Linker-Map im
Prüfgerüst), damit der Boot-Satz keinen stillen Rand hat.

---

## 4. Das Speichermodell als Axiom — bisher stillschweigend

`publishes`/`awaits`/`exchange` versprechen Sichtbarkeit **unter der Annahme**, dass die
C11-Abbildung auf der Zielarchitektur trägt. Das stand nirgends. Jetzt:

```gabbro
assume c11_release_acquire_x86
    "release-Store / acquire-Load auf x86-64 (TSO): Absenkung auf mov genuegt"
    falsifier probe_mp_x86;          -- Message-Passing-Litmus, im Pruefgeruest gefahren
assume c11_release_acquire_aarch64
    "stlr/ldar tragen release/acquire auf aarch64"
    falsifier probe_mp_aarch64;
```

Die Litmus-Sonden (MP, SB, LB — die klassischen drei) laufen im Prüfgerüst als `check` mit
`counterprobe`. Damit ist das Speichermodell **zählbar** Teil der Axiomschicht statt implizit —
und die Zusage aus Ergänzung §1 heißt vollständig: *Paarung korrekt unter c11_*-Annahmen.*

---

## 5. Grundsätzlich offen — unverändert, damit es niemand als erledigt liest

**D8** (Fortschritt/Aushungern): kein Mechanismus, kein Konstrukt behauptet einen. **L4**: die
eine unformulierbare Pflicht. **Die Erzeuger-Schablonen** (`by consuming`-Ordnung, `table ops`):
benannt, nicht entworfen — sie sind Teil des Prüferplans (P4), nicht dieses Dokuments.

---

## 6. Der Prüfer — ein Plan mit Stufen und Toren, keine Absichtserklärung

**Grundsatzentscheidungen, vorab und mit Grund:**

| | Entscheidung | Grund |
|---|---|---|
| Wirtssprache | **Rust, `forbid(unsafe_code)`**, keine Beweiswerkzeug-Abhängigkeit | der Prüfer ist Typregeln, kein Löser; die CSolver/Miri-Disziplin ist vorhanden |
| Architektur | Lexer → Parser (aus der **vereinigten** EBNF, handgeschrieben, kein Generator) → ein Kernbaum → **Prüfpässe in fester Reihenfolge** (Namen, D1/D2, M1+V1–V3, M3, M2, M4/Schleifen, Paarung, effects, costs) → C-Emission | jede Regel dieser drei Dokumente ist genau **ein** Pass oder ein benannter Teil eines Passes — die Spezifikation ist die Passliste |
| Absenkung | syntaxgesteuert, ein Konstrukt → eine C-Form, deterministisch byteweise | Festlegung §14, unverändert |
| Selbstanwendung | **nie** — der Prüfer bleibt Rust (Verbotsliste: Selbst-Hosting) | ein Vorhaben, das seinen Prüfer umbaut, hat keinen |
| Prüfstrategie | jeder Pass mit Sprechprobe in beide Richtungen (Gift fällt, Sauberes passiert) **plus Mutationsprobe auf die Emission** (Code UND Annotation) | die Wunschform-Beweis-Lektion |

**Die Stufen — jede mit Tor, jede kann das Vorhaben beenden:**

| Stufe | Inhalt | Tor (vorab, zweiseitig) |
|---|---|---|
| **P0** | **Wiederholungsmessung auf Papier** gegen Festlegung+Ergänzungen: 74 Pflichten + Ordering-Stichprobe (≥ 30, geschichtet) + `narrow`-Zählung | hängende Klempnerei **0**, Ordering-Stichprobe ohne vierten Ausgang, `narrow` ≤ 24. **Jede Verfehlung: erst Konstrukt nachziehen, KEIN Prüfercode vorher** |
| **P1** | **Grammatikvereinigung** (Festlegung + beide Ergänzungen in die EBNF), beide Wächter, Widerspruchslauf über den Ordner | Wächter grün; Widersprüche 0 offen. Die zweimal bezahlte Fehlerklasse — deshalb **vor** der ersten Prüferzeile |
| **P2** | **Lexer+Parser** über alle Fragmente des Ordners | 100 % der Fragmente parsen; drei Gift-Fragmente scheitern mit benannter Absage |
| **P3** | **M1+V1–V3 als erster Prüfpass**, gegen `space.rs`-Fragment und die 102-Fundstellen-Stichprobe | die Stichprobe typisiert ohne `narrow`-Inflation; Sprechprobe: `refcount -= 1` ohne V-Fakt **fällt** |
| **P4** | **M2 (linear/ghost) + Erzeuger-Schablone** für `table ops`/`by consuming` — hier wird der benannte Posten entworfen und die Schablonen-Beweise werden als geschlossene Manifesteinträge geführt | S1a/S1b/Parked/D0-Klasse als Sprechproben fallen; Mutationsprobe auf die Schablone fängt eine stimmig abgeschwächte Mutation **nicht** — also läuft der Differenztest gegen `space.rs` (Rust) daneben, wie in der Festlegung gebucht |
| **P5** | **C-Emission** für das `space.rs`-Fragment, Differenztest + Differenz-Benchmark gegen die Rust-Fassung | byteidentische Wiederholung; erzeugt ≤ Handschrift + Rauschen; `lesen(schreiben(x)) == x` für die beteiligten Formate |
| **P6** | Paarungs-Pass + `entry`-Emission für **eine** Architektur, Litmus- und `entry`-Sonden im Prüfgerüst | Sonden grün auf echter Hardware oder KVM; die drei Boot-Prüfzeilen laufen |
| **P7** | **Ein Caprock-Modul end-to-end** in Produktion (Kandidat: `caprock-part` — klein, format-lastig, echter Verbraucher), Strangler-Muster, Rust-Fassung bleibt daneben | Abnahmereihe grün, Kennzahl des Moduls gemessen und berichtet (Ziel 0,5:1, Abbruch > 3:1) |

**Reihenfolgeregel, die den ganzen Plan trägt:** P0 und P1 kosten Papier und Skripte, kein
Übersetzerbau — und sie können V2, `awaits`, `embeds` und die Grammatik **einzeln** widerlegen.
Deshalb gilt: **keine Prüferzeile vor Tor P1.** Der Korrekturkreislauf hat in diesem Ordner
mehrfach schneller gelaufen als der Messkreislauf; dieser Plan ist so gebaut, dass das strukturell
nicht mehr geht — jede Stufe verbraucht das Ergebnis der vorigen, wie eine `Duty`.

**Aufwand:** keine Schätzung — eine erfundene wäre schlimmer als keine (die VOLLDECKUNG-Regel).
Stattdessen die Tore; und neben dem Plan steht die Caprock-Frage, die kein Gabbro-Dokument
beantwortet: A4, Z24 und die A3-Folgeposten warten, und dieser Plan ist erst dann mehr als
Papier, wenn P0 gefahren ist.

---

## 7. Abnahme dieser zweiten Ergänzung

1. Das `preserves { all }`-Beispiel in ERGAENZUNG.md berichtigt (Register aufgezählt).
2. Die Wortzählung der Kopfzeile gegen §3.2 aufgelöst — von der vereinigten Wortschatztabelle,
   nicht von Hand (Falle 80: eine Zahl, die ein Mensch parallel zur Wahrheit führt).
3. P0 gefahren, **bevor** irgendetwas anderes aus §6 beginnt.
