# ERGÄNZUNG zur Festlegung — der Rest bis „nur noch Logik"

**Nachtrag zu [`FESTLEGUNG.md`](FESTLEGUNG.md).** Die Bilanz der Festlegung nannte drei Löcher:
die **zwölfte Klasse** (Ordering-Paarung, 2 231 Fundstellen deklariert statt bewiesen), den
**Eintrittspfad** (Syscalls/IRQs ohne Konstrukt) und den **Boot-Unerreichbarkeitsbeweis** (bisher
eine Typregel plus ein Satz Prosa). Dieses Dokument schließt sie und zieht danach die ehrliche
Restliste: was nach allem noch zu beweisen bleibt — und in welcher Klasse.

Stand 2026-08-14. **Neue Wörter (geschlossen, neun):**
`awaits entry regs out preserves clobbers stack dispatch vector`

> **BERICHTIGT beim Eintragen (2026-08-14):** das `timer`-Beispiel schrieb `preserves { all }`.
> **`all` ist kein Wort des Wortschatzes** — ERGAENZUNG 2 §7.1 verlangt die Aufzaehlung, weil D2
> vollstaendig heisst und nicht bequem. Die sechzehn Register stehen jetzt da.

---

## 1. Die zwölfte Klasse: Ordering wird gepaart, nicht deklariert

**Der Fehlbestand:** `atomic … release` legt eine Ordnung fest, aber dass ein `release`-Store und
der zugehörige `acquire`-Load ein **Paar** bilden und die Ordnung für die Nutzlast **reicht**,
prüfte nichts. Nach dem eigenen Kriterium ist das Klempnerei (erwähnt nur die Maschine) — und mit
2 231 Fundstellen der größte ungedeckte Posten des Baums.

### 1.1 `awaits` — die Gegenseite von `publishes`

```ebnf
awaitload = "let" ident "=" place "awaits" "{" placelist "}" ";" ;
```

Die Festlegung setzte die Publikation an den Store (`FP_OWNER[core] = tid publishes
{ FP_STATES[tid] };`). **Die Ergänzung setzt den Empfang an den Load:**

```gabbro
let owner = FP_OWNER[core] awaits { FP_STATES[owner] };
if owner == my_tid {
    -- HIER ist FP_STATES[owner] lesbar: der Load hat die Sichtbarkeit erworben
}
```

**Drei Regeln, alle Typregeln, kein Speichermodell-Löser:**

1. **Paarungspflicht.** Jeder `awaits`-Load auf ein Atomic verlangt, dass es einen
   `publishes`-Store auf **dasselbe** Atomic mit **denselben** Plätzen gibt (statisch abgeglichen,
   Namensgleichheit nach Indexsubstitution). Ein `awaits` ohne Gegenstück, ein `publishes` ohne
   Empfänger: Übersetzungsfehler — verwaiste Hälften sind genau die Fehlerklasse der 872
   Fundstellen in `threads/mod.rs`.
2. **Sichtbarkeit ist ein Zweigfakt** (V-Regel-Familie aus der Festlegung): erst der geprüfte
   Zweig, der den geladenen Wert bestätigt, macht die erwarteten Plätze lesbar. Ein Lesen
   fremd-publizierter Plätze **ohne** erworbene Sichtbarkeit ist ein Übersetzungsfehler.
3. **Ordnung folgt aus der Paarung, nicht umgekehrt.** `publishes { … }` erzwingt mindestens
   `release` am Store, `awaits` mindestens `acquire` am Load — die Ordnungswörter an der
   Deklaration werden **abgeleitet und geprüft** statt gewählt. `relaxed` ist nur mit
   `publishes nothing`/ohne `awaits` schreibbar (Zähler). `seq` bleibt für Algorithmen, die eine
   **globale** Ordnung brauchen — und genau die fallen nicht unter die Paarung:

> **Grenze, benannt:** Die Paarung deckt Nachrichtenübergabe (Erzeuger→Verbraucher, Besitzwechsel,
> Flaggen mit Nutzlast) — nach der Fundstellenstruktur des Baums die dominante Form. Algorithmen,
> deren Korrektheit an einer globalen seq-Ordnung über **mehrere** Atomics hängt, sind mit `seq`
> schreibbar, aber ihre Korrektheit ist **Logik** und steht als `obligation` im Manifest. Die
> Wiederholungsmessung zählt, wie viele das sind; die Vermutung ist „einstellig", und sie ist als
> Vermutung markiert.

**Absenkung:** exakt die C11-Atomics, die heute dastehen — Mehrkosten 0. Der Gewinn ist nicht im
Erzeugnis, sondern darin, dass ein fehlendes `acquire` **nicht mehr schreibbar** ist.

---

## 2. Der Eintrittspfad: `entry` — Syscalls und IRQs aus einer Deklaration

### 2.1 Das Konstrukt

```ebnf
entrydecl = "entry" ident [ "vector" constexpr ] "arch" ident "{"
              "regs" "in"  "{" { ident ":" ident "," } "}"
              "regs" "out" "{" { ident ":" ident "," } "}"
              "preserves" "{" identlist "}"
              "clobbers"  "{" identlist "}"
              "stack" ident
              "dispatch" path ";"
            "}" ;
```

```gabbro
entry syscall arch x86_64 {
    regs in  { nr: rax, a0: rdi, a1: rsi, a2: rdx, a3: r10 }
    regs out { ret: rax }
    preserves { rbx, rbp, r12, r13, r14, r15, rsp_user }
    clobbers  { rcx, r11 }                      -- syscall/sysret-Realitaet
    stack KernelStack
    dispatch caprock::syscall::dispatch;
}

entry timer vector 0x20 arch x86_64 {
    regs in {} regs out {}
    preserves { rax, rbx, rcx, rdx, rsi, rdi, rbp, rsp,
                r8, r9, r10, r11, r12, r13, r14, r15 }
    clobbers  {}
    stack IrqStack
    dispatch caprock::irq::timer_tick;
}
```

**Was durch Konstruktion fällt:** Die Registerabdrücke sind **vollständig** — jedes
Architekturregister ist genau einer der drei Mengen zugeordnet, sonst Übersetzungsfehler (D2 auf
Registern). Der Stapelwechsel ist das Primitiv, das keine strukturierte Sprache ausdrückt, hier
als deklarierte Zeile. `dispatch` zeigt auf eine **gewöhnliche Gabbro-Funktion** mit `tagged`
Syscall-Nummer, M1-beschränkt, erschöpfendem `match` — ab der ersten Gabbro-Zeile gelten M1–M4,
und die Grenze Assembler/Sprache ist **eine** Deklaration breit. `resume`/`iretq` ist der
typisierte Rückweg (Bestand §12).

**Was nicht fällt, unverändert ehrlich:** Der Eintrittspfad hat **keinen nachgelagerten
Beweiser**. Die Emission kommt aus der einen `iasm`-Stelle; je `entry` und Architektur gehört eine
**Sonde** in die Abnahmereihe (Benutzerregister nach Rückkehr byteidentisch, `clobbers` wirklich
und ausschließlich verändert, Kernelstack-Kanarienvogel). Deklariert, einmal emittiert,
falsifiziert — nicht bewiesen. So steht es im Manifest, Klasse „Eintritt".

### 2.2 Ein Ursprung, zwei Erzeugnisse: die Stub-Regel

Aus **derselben** `entry`- und `dispatch`-Deklaration erzeugt der Übersetzer **auch die
Userspace-Stubs** (die Aufrufseite: Register laden, `syscall`, Ergebnis typisieren). ABI-Drift
zwischen Kernel und `programs/` — bisher eine reine Disziplinfrage — wird damit **unschreibbar**:
es gibt nur eine Quelle. Die Treiber- und Programmseite (virtio-blk-Dienstschleife) ruft typisierte
Stubs mit denselben Verträgen, die der Kernel prüft.

### 2.3 FP-/SIMD-Zustand

Der Kernel behandelt FP-Zustand als **undurchsichtigen Sicherungsbereich**: `opaque type FpArea`
mit deklarierter Größe/Ausrichtung je Architektur; `xsave`/`xrstor` (bzw. FPSIMD-Sicherung auf
aarch64) sind **Axiome** mit Effekt auf `FpArea` und fahrbarem Falsifikator — die
CVE-2018-3665-Klasse (lazy-FP-Leck) ist damit eine `MayWrite`-artige Besitzfrage über `FpArea`
plus ein Axiom, nicht ein Sonderpfad.

---

## 3. Boot-Unerreichbarkeit — ein Satz in drei Schichten

**Zu zeigen:** *Nach `boot_end` ist kein `raw`-Code erreichbar.* Bisher trug das eine Typregel und
ein Falsifikator-Satz. Jetzt ist es ein benannter Satz mit drei Schichten, jede mit ihrer
Vertrauensklasse — weil „statisch heißt nur: kein Aufrufer" (Falle 47) und eine Schicht allein
eine Bitte wäre.

| Schicht | Regel | deckt | Vertrauensklasse |
|---|---|---|---|
| **S1 — Typen** | jede `raw fn` verlangt `&BootPhase`; `BootPhase` ist linear, entsteht genau einmal im Boot-`entry`, wird von `boot_end` verbraucht. Danach **typisiert kein Aufruf** | jede statische Aufrufkette | Prüfer (M2) |
| **S2 — Verweise** | `raw fn` liegt erzwungen in `section ".boot"`; **Adressnahme einer `raw fn` ist nicht schreibbar** (kein `fnptr` auf `raw`, keine Sprungtabelle mit `.boot`-Zielen, kein `ptr<code>`-Literal dorthin). Nicht-`raw`-Code in `.boot` ist ein Übersetzungsfehler | jede dynamische Erreichbarkeit über Zeiger | Prüfer (M3/D2) |
| **S3 — Hardware** | `boot_end` verbraucht die Marke **und** hebt die Abbildung von `.boot` auf, **ein Ereignis**; die Nachbedingung ist als `walk`-Fakt formulierbar: `!exists m in mappings of kernel_root: m.section == boot`. Sonde: Zugriff auf eine `.boot`-Adresse nach `boot_end` **muss faulten** | Sprünge, die S1/S2 nicht sieht (Fehlspekulation ausgenommen, ROP auf tote, aber abgebildete Bytes) | Axiomschicht + Falsifikator |

**Damit ist der Satz nicht „bewiesen im Prüfer", sondern sauber zerlegt:** S1+S2 sind Typregeln
des unverifizierten Prüfers, S3 ist eine Hardware-Annahme mit fahrbarer Sonde. Das Manifest führt
ihn als einen Eintrag mit drei Teilzusagen — stärker als Rusts `#[deprecated]`-Disziplin, stärker
als Verus' affines `tracked` (die Marke ist **linear**: wiederherstellen und kopieren sind
Typfehler), und ohne dass irgendwo „unsafe, aber vorsichtig" steht.

---

## 4. Die Restliste — was nach allem übrig bleibt

Nach Festlegung + Ergänzung gilt: **Caprock, Treiber und Systemprogramme sind vollständig
schreibbar** (Bereichskatalog §16 der Festlegung, plus Eintritt, Stubs, FP, Ordering). Für die
formale Verifikation bleibt, nach Klassen getrennt — denn „nur noch Logik" ist nur ehrlich, wenn
die Vertrauensposten daneben stehen:

### 4.1 Zu beweisen (die eigentliche Logik-Arbeit)

| # | Posten | Ort |
|---|---|---|
| L1 | `ensures` der algorithmischen Rümpfe: IPC-Fastpath, Scheduler-Wahl, revoke-**Funktionalität** | Manifest, je Funktion |
| L2 | seq-Ordnungs-Algorithmen jenseits der Paarung (§1, vermutet einstellig — zu zählen) | Manifest |
| L3 | `breaking`-Wiederherstellungen ohne erzeugte Schlussoperation | Manifest (Buchungsregel F8/F9) |
| L4 | die eine bekannte unformulierbare Pflicht | Manifest, mit Fundstelle |

**Das — und nur das — muss ein Mensch oder ein externes Werkzeug beweisen.**

### 4.2 Vertrauen statt Beweis (benannt, ratschenfähig, kein Arbeitsposten)

Der unverifizierte Prüfer; die syntaxgesteuerte Absenkung; die eine `iasm`-Emissionsstelle samt
`entry`-Sonden; die Axiomschicht (privilegierte Befehle, MMU-Modell, `xsave`, `extern fn`); die
amortisierten Erzeuger-Schablonen (`by consuming`-Ordnung, `table ops`-Invariantenerhaltung).
Alles im Manifest mit Namen und Klasse — die Ratsche läuft über Namen.

### 4.3 Ohne Mechanismus (offen, kein Konstrukt behauptet)

**D8 — Fortschritt und Aushungern.** `progress` benennt Annahmen, beweist keine Lebendigkeit.
Kein Konstrukt dieser beiden Dokumente ändert das, und es steht hier, damit es nicht als erledigt
gelesen wird.

---

## 5. Abnahme dieser Ergänzung

1. **Wiederholungsmessung auf 12 Klassen erweitern:** die 74 Pflichten plus eine
   Ordering-Stichprobe (≥ 30 der 2 231 Fundstellen, geschichtet nach Datei) gegen §1 — jede
   Fundstelle ist Paarung, Zähler oder benannter seq-Fall; ein vierter Ausgang widerlegt §1.
2. **Ein `entry` je Architektur als Fragment** in den Ordner, gegen die reale
   syscall/sysret- bzw. SVC-Konvention gehalten (die `clobbers`-Zeile ist der Prüfstein).
3. **Der Boot-Satz als drei Prüfzeilen** in der Abnahmereihe: S1/S2 als Prüfer-Sprechprobe
   (ein Aufruf nach `boot_end` muss die Übersetzung brechen), S3 als Sonde im Testkernel.
4. **Grammatikvereinigung**: Festlegung + Ergänzung in die EBNF eingehängt, beide Wächter
   (Erreichbarkeit von `program`, Terminaldeckung) grün — diese Fehlerklasse ist zweimal bezahlt.
5. Danach der Widerspruchslauf über den ganzen Ordner, wie nach den sechs Umbauten.
