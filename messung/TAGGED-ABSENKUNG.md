# `tagged` → C: der W24-Vorlauf dreht den Auftrag zur Hälfte um

**Stand 2026-08-30, gemessen mit einem gebauten `gabbro emit` und `cc`.** Nichts
hiervon ist gebaut worden — `ki-pc-fisch-101` war nicht erreichbar. Das Dokument
sagt, was HEUTE herauskommt und was die Entscheidung vom 2026-08-28 davon noch
verlangt.

## Der Auftrag lautete

> * **Kleinster Typ, der die Varianten fasst** — nicht `u32`. Grund: `tagged` kommt
>   in Slots vor, und eine feste `u32`-Marke kostet Speicher, den `count N`-Tabellen
>   **vervielfachen**.
> * **BENANNTE Vereinigung**, also `struct { <kleinste Marke> tag; union { … } u; }`
>   und nicht die anonyme Union.

## Was `gabbro emit` heute schreibt

`beispiele/34-markierter-wert.gab`, `tagged type Nachricht = { Leer, Kurz(u32),
Lang(u64), Antwort(Zaehler) }`:

```c
typedef enum {
    Nachricht_Leer, Nachricht_Kurz, Nachricht_Lang, Nachricht_Antwort,
} Nachricht_marke;

typedef struct {
    Nachricht_marke marke;
    union {
        uint32_t Kurz;
        uint64_t Lang;
        uint32_t Antwort;
    } last;
} Nachricht;
```

**Die benannte Vereinigung steht schon da** (`} last;`, nicht anonym). Der zweite
Punkt des Auftrags ist erledigt, bevor er begonnen wurde.

Und die Absenkung ist sorgfältiger als erwartet: ein `tagged type` **ohne jede
Nutzlast** bekommt gar keine Union, statt einer leeren —

```c
typedef struct { Rolle_marke marke; } Rolle;
```

*Ein `union { }` wäre kein C.* Der Fall ist bedacht.

## Der erste Punkt ist offen — aber sein GRUND hält nicht

Die Marke ist ein C-`enum`, also hier vier Byte. Insofern: offen. Die Begründung
(„kostet Speicher, den `count N`-Tabellen vervielfachen") ist aber nachgerechnet
worden, mit `cc -std=c11` auf dieser Maschine:

| breiteste Nutzlast | `enum`-Marke | `uint8_t`-Marke | |
|---|---|---|---|
| `u64` | 16 B | 16 B | **kein Gewinn** |
| `u32` | 8 B | 8 B | **kein Gewinn** |
| `u16` | 8 B | 4 B | Gewinn (halbiert) |
| `u8` | 8 B | 2 B | Gewinn (geviertelt) |

**Die Ausrichtung frisst die Ersparnis.** Trägt die Union ein `uint64_t`, richtet
sich die Struktur auf acht Byte aus; die Marke sitzt dann in einem Feld, das
ohnehin aufgefüllt wird. Vier Byte sparen heisst dort: null Byte sparen. Bei
`Nachricht` in einer `count 256`-Tabelle sind es **4096 Byte gegen 4096 Byte**.

### Und wo der Gewinn tatsächlich liegt, ist die Umkehrung des Erwarteten

Jeder `tagged type` des Korpus mit Nutzlast trägt mindestens vier Byte
(`Pa`, `EpId`, `u32`, `u64`, `Kontonr`, `Laenge`, `Rest`) — für sie alle ist die
Tabelle oben die Zeile „kein Gewinn".

**Es gewinnen die Typen OHNE Nutzlast**, und nur sie:

| | heute | kleinste Marke |
|---|---|---|
| `struct { Rolle_marke marke; }` | 4 B | 1 B |
| dieselbe in `count 1024` | **4096 B** | **1024 B** |

Das ist der Faktor vier, den der Auftrag vermutet hat — er steht nur an der
anderen Stelle. Betroffen sind `Rolle = { Boot, Helfer }` (`beispiele/41`),
`Op = { Info, Read, Write, Flush, Scan, Stop }` (`messung/fragmente/F05.gab`) und
`BufPhase = { Driver, Device }`.

## Was daraus folgt

1. **Benannte Vereinigung: keine Arbeit.** Erledigt, samt dem Sonderfall der
   leeren Union.
2. **Kleinste Marke: lohnt sich, aber nicht aus dem genannten Grund** — und nicht
   für die Typen, an die der Grund gedacht hat. Die Regel wäre: *die Marke bekommt
   den kleinsten Ganzzahltyp, der die Variantenzahl fasst*, und der Gewinn fällt
   dort an, wo keine Nutzlast die Ausrichtung hochzieht.
3. **Regel A greift**: kein Konstrukt ohne gemessenen Bedarf. Der Bedarf ist jetzt
   gemessen — er ist kleiner und anders geschnitten als angenommen. *Wer die
   Änderung baut, baut sie für drei Typen, nicht für alle.*

**Nicht getan und warum:** die Änderung selbst. Eine Absenkung ohne einen einzigen
gebauten Lauf ist nicht buchbar, und `cargo`/`isabelle` lagen an diesem Tag beide
hinter einem toten Sprunghost.
