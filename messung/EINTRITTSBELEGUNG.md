# «B27» — die Registerbelegung: der Eintrag war falsch, und der Träger stand seit acht Tagen da

*Gemessen am 2026-08-28, Bahn A, Schritt A3, auf `ki-pc-fisch-101:gabbro-A` — **mit dem
unveränderten Prüfer**, vor jeder Änderung. Das Ergebnis ist eine **Berichtigung** und kein
Bau, und das ist der gute Fall (§1.8).*

> **Der Plan hat hier zweimal danebengezielt, und beide Male anders, als er vermutete.**
> `dokumente/PLAN-AUTONOM.md` schreibt zu A3:
>
> > *„`entry … regs in { … } regs out { … } preserves { … } clobbers { … } stack … dispatch
> > …` … `entry` ist ein Kandidat für dieselbe Klasse wie `when` und `raw fn`: eine Form mit
> > Produktion, Parser und AST, deren Klauseln **kein Pass liest**. … Wenn sich das
> > bestätigt, ist A3 kein Bau, sondern die vierte Klausel ohne Leser."*
>
> **Es hat sich NICHT bestätigt — und A3 ist trotzdem kein Bau.** `entry`s Klauseln haben
> Leser; und «B27» handelt gar nicht von `entry`.

---

## 1. Der Befund, in drei Messungen

```bash
./instrumente/pruefe-klauseln.py
ssh ki-pc-fisch-101 'cd gabbro-A && ./target/debug/gabbro pruefe ~/gabbro-A-w24/a3-prim.gab'
ssh ki-pc-fisch-101 'cd gabbro-A && ./target/debug/gabbro emit   ~/gabbro-A-w24/a3-prim.gab'
ssh ki-pc-fisch-101 'cd gabbro-A && ./target/debug/gabbro pruefe ~/gabbro-A-w24/a3-abi.gab'
ssh ki-pc-fisch-101 'cd gabbro-A && ./target/debug/gabbro emit   ~/gabbro-A-w24/a3-invoke-asm.gab'
```

### (a) `entry`s Klauseln haben Leser — der Verdacht des Plans trifft nicht

`pruefe-klauseln.py` führt aus `EntryDecl` **drei** Felder als *NUR GETRAGEN* (abgesenkt oder
berichtet, von keinem Pass geprüft): `ist`, `stack`, `vektor`. **`regs_in`, `regs_out`,
`preserves` und `clobbers` stehen NICHT darunter** — sie werden gelesen:

* `namen.rs`:805–825 — kein Register zweimal in `regs in`/`regs out`, und **kein Register
  zugleich in `preserves` und `clobbers`**;
* `zeugnis.rs`:557–558 — beide Listen stehen im Zeugnis;
* `schablonen.rs`:560 — eine Erzeugerpflicht nennt sie wörtlich: *„(1) Der erzeugte
  Eintrittspfad erhält jedes Register aus `preserves`. (2) Er schreibt kein Register
  außerhalb von `clobbers`."*

**`entry` ist damit nicht die vierte Klausel ohne Leser.** Der Verdacht war berechtigt und
ist gemessen widerlegt — genau wofür `pruefe-klauseln.py` gebaut wurde.

### (b) «B27» handelt nicht von `entry`, sondern von der GEGENRICHTUNG

`FRAGMENTE.md`:944–949, wörtlich:

> *„«B27» Der Syscall-Einstieg: `arch ident` gibt es (:273), die REGISTERBELEGUNG nicht. Die
> Vorlage schrieb dafür einen `abi { in rax = nr, …, trap 0x80 }`-Block; `fndecl` kennt ihn
> nicht. Damit hat der einzige Ort, an dem 168 gemessene `asm!`-Stellen zusammenlaufen
> sollten, in der Grammatik keinen Träger — die vertrauenswürdige Fläche schrumpft nicht,
> sie wandert in eine `prim`-Deklaration ohne Inhalt."*

Das ist der **ausgehende** Systemaufruf an einem `prim fn`, nicht der Kerneintritt `entry`.
Zwei verschiedene Gegenstände, und die Registerzeile hat sie zusammengezogen.

| Probe | geschrieben | gemessen |
|---|---|---|
| **A** | `prim fn invoke(…) -> u64 effects { writes machine_regs } arch x86_64;` | **0 Fehler** — und `gabbro emit` schreibt `uint64_t invoke(uint64_t nr, …);`, **eine Vorwärtsdeklaration ohne Inhalt.** *Die Zeile des Fragments, wörtlich bestätigt* |
| **B** | `abi { in rax = nr, in rdi = cap, …, trap 0x80 }` am `prim fn` | `Fehler: [P001] `;` erwartet, Bezeichner `abi` gefunden` — **die Form gibt es nicht** |

Bis hierher liest sich alles wie eine echte Lücke. **Die dritte Messung dreht es um.**

### (c) Der Träger EXISTIERT — und das Fragment griff zum falschen Konstrukt

`beispiele/36-asm.gab` schreibt seit dem **2026-08-20** einen Systemaufruf mit voller
Registerbelegung:

```gabbro
impl fn schreiben(fd : u64, puffer : u64, laenge : u64) -> u64
    effects { writes GERAET } costs <= 1 ops arch x86_64
    = asm { "mov $1, %eax" "syscall"
            in  { fd : "D", puffer : "S", laenge : "d" }
            out { result : "=a" }
            clobbers { memory } };
```

`in { … }`, `out { … }`, `clobbers { … }`, `arch` — **das IST die Registerbelegung.** Und
F5s eigene Zeile, als `asm`-Rumpf statt als `prim`-Deklaration geschrieben, geht durch:

```
/home/fisch/gabbro-A-w24/a3-invoke-asm.gab: 3 Items, 0 Fehler, 0 Hinweise
```

```c
static uint64_t invoke(uint64_t nr, uint64_t cap, uint64_t m0, uint64_t m1,
                       uint64_t m2, uint64_t m3, uint64_t tag) {
    uint64_t result;
    __asm__ __volatile__(
        "syscall\n"
        : [result] "=a" (result)
        : [nr] "a" (nr), [cap] "D" (cap), [m0] "S" (m0), [m1] "d" (m1),
          [m2] "r" (m2), [m3] "r" (m3), [tag] "r" (tag)
        : "memory");
    return result;
}
```

**Die vertrauenswürdige Fläche wandert also NICHT in eine `prim`-Deklaration ohne Inhalt —
sie steht in einem `asm`-Rumpf, der geprüft wird, abgesenkt wird und durch `cc -Werror`
geht.** Der Satz der Registerzeile war am Tag seiner Niederschrift richtig und ist es seit
dem 2026-08-20 nicht mehr; nachgeführt wurde er nicht. *Dieselbe Klasse wie «B17» und «B9»:
eine Zeile, die nur nicht mitgeführt wurde.*

---

## 2. Zwei Formen, gegeneinander — und beide Seiten je Form

Die Frage, die nach der Berichtigung übrig bleibt, ist NICHT „gibt es einen Träger", sondern:
**soll die Belegung in Registernamen oder in C-Zwangsbuchstaben stehen?**

### Form 1 — `asm` mit C-Zwangsbuchstaben (heute gebaut)

```gabbro
in { fd : "D", puffer : "S", laenge : "d" }  out { result : "=a" }
```

**Dafür**

* **Sie ist gebaut, geprüft und abgesenkt** — und `pruefe-emission.sh` übersetzt sie mit
  `-Werror` bei `-O0` und `-O2`.
* Sie delegiert die Zuordnung an den einen Übersetzer, der sie ohnehin auflösen muss. *Ein
  Erzeuger, der Registernamen selbst in Zwänge übersetzt, baut eine zweite Tabelle neben
  `cc`s eigener — und bei Abweichung entscheidet die falsche.*
* Sie ist **architekturneutral in der Grammatik**: `arch` trennt die Fälle, die Buchstaben
  sind Sache der Zielkette.

**Dagegen — und das ist der ehrliche Rest**

* **Gabbro PRÜFT die Belegung nicht.** `"D"` und `"S"` sind für den Prüfer undurchsichtige
  Zeichenketten; wer sie vertauscht, bekommt ein Programm, das übersetzt und falsch
  aufruft. *Das ist genau die Fläche, die «B27» schrumpfen sehen wollte, und sie ist nur
  verschoben, nicht geprüft.*
* `zeugnis.rs` zählt die Befehlszeilen, sagt aber nichts über die Zuordnung.

### Form 2 — `abi { in rax = nr, …, trap 0x80 }` am `prim fn` (die Vorlage)

**Dafür**

* Sie steht in Registernamen und ist damit **nachprüfbar**: ein Pass könnte gegen eine
  Tabelle je `arch` halten, ob `rax` existiert, ob ein Register zweimal belegt ist, ob die
  Rückgabe auf dem Register liegt, das die Aufrufkonvention nennt.
* `trap 0x80` sagt die Falltür aus, statt sie in einen Befehlstext zu schreiben, den Gabbro
  nicht liest.

**Dagegen — dreimal, und das dritte entscheidet**

* **Ein neues Wort** (`abi`) plus `trap`, und eine Registernamentabelle je Architektur im
  Prüfer. `messung/SCHLEIFENINVARIANTE.md` §3: *ein zweites Wort für einen vorhandenen
  Begriff ist teurer als eine zweite Fundstelle für ein vorhandenes Wort* — und der Begriff
  „Registerbelegung" hat mit `asm`s `in`/`out` schon eine Fundstelle.
* Sie deckt **nur** die Syscall-Form. Ein `outb`, ein `cpuid`, ein `wrmsr` bleiben beim
  `asm`-Rumpf; die Sprache trüge dann **zwei** Registerbelegungen für eine Sache (W7).
* **Und der gemessene Bedarf fehlt.** Im ganzen sauberen Korpus steht **genau eine**
  `prim fn`-Stelle mit `arch` und keiner Belegung — im Fragment, das die Lücke meldet. Der
  Korpus schreibt Systemaufrufe längst als `asm`-Rumpf. *Regel A: kein Konstrukt ohne
  gemessenen Bedarf; hier ist die benannte Absage das Ergebnis.*

---

## 3. Die Entscheidung, und der Grund ist der Begriff

**Nichts gebaut. Der Eintrag wird berichtigt, und der verbleibende Rest wird BENANNT statt
als Lücke geführt.**

Der Grund ist nicht der Preis, sondern der Begriff: **`prim` heißt „anderswo erklärt".** Eine
`prim`-Deklaration zu einer Vorwärtsdeklaration ohne Inhalt abzusenken ist nicht ihr Mangel,
sondern ihre Bedeutung. Das Fragment hat zum falschen Konstrukt gegriffen — für „hier steht
Assembler, und Gabbro liest ihn nicht" gibt es `= asm { … }`, und das trägt `arch`, `effects`,
`costs`, die Belegung und die Absenkung.

**Was als Rest stehen bleibt und ausdrücklich KEINE `gap:`-Zeile bekommt:** die Belegung ist
in C-Zwangsbuchstaben geschrieben und wird an `cc` delegiert, nicht geprüft. *Das ist eine
benannte Delegation und keine fehlende Form* — dieselbe Art Eintrag wie „Gabbro liest den
Befehlstext nicht", die `beispiele/36` in seiner ersten Zeile selbst ausspricht.

> **Der Name steht seit dem 2026-08-30 im ZEUGNIS** — bis dahin war die Delegation
> entschieden und nirgends ausgesprochen, und *eine stillschweigende Delegation ist keine.*
> Sie steht in Abschnitt E **neben** den `ASSEMBLY`-Zeilen, nicht darüber und nicht weg:
>
> ```
>      ASSEMBLY -- 2 bodies, 3 instruction lines. Gabbro does NOT read them:
>        ausgeben                   1 lines
>        schreiben                  2 lines
>
>      REGISTER ALLOCATION -- delegated to `cc`, NOT checked here («B27»).
>        The `in`/`out`/`clobbers` letters are C constraint letters and reach the
>        compiler unread. Swapping two of them yields a program that compiles
>        and calls wrong. A named delegation, not a missing form: no pass holds
>        them against a register table, because the corpus shows no demand for
>        one (messung/EINTRITTSBELEGUNG.md).
> ```
>
> **Sie kauft nichts, was sie nicht sagt.** Wer zwei Buchstaben vertauscht, bekommt weiter
> ein übersetzbares, falsches Programm — die Zeile verschweigt genau das nicht, sondern ist
> der Ort, an dem es steht. *Ein Pass gegen eine Registertabelle je `arch` wäre nicht falsch,
> er hat nur null gemessenen Bedarf (Regel A), und eine Tabelle je Architektur ist Pflege.*

---

## 4. Was diese Entscheidung NICHT kauft

* **Sie prüft die Belegung weiterhin nicht.** Wer `"D"` und `"S"` vertauscht, bekommt ein
  übersetzbares, falsches Programm. Ein Pass, der Zwangsbuchstaben gegen eine Tabelle je
  `arch` hält, wäre möglich und ist **nicht gebaut** — er wäre der kleinere Bau, den Form 2
  groß gemacht hat, und er braucht kein neues Wort.
* **Sie schrumpft die vertrauenswürdige Fläche nicht.** Die 168 gemessenen `asm!`-Stellen
  laufen an einer Form zusammen, die Gabbro nicht liest. *Was «B27» wollte, war weniger
  Assembler; was es gibt, ist Assembler an einem Ort mit Vertrag drumherum.* Der Unterschied
  ist real und wird hier nicht kleingeredet.
* **Sie sagt nichts über `entry`.** Dort haben die Klauseln Leser (§1a), aber `ist`, `stack`
  und `vektor` sind *NUR GETRAGEN* — abgesenkt, von keinem Pass geprüft. Das ist eine eigene
  Zeile in `pruefe-klauseln.py`s Buch und bleibt dort.
* **Sie öffnet `trap` nicht.** Die Falltür steht weiter im Befehlstext (`"syscall"`), den
  Gabbro nicht liest.
