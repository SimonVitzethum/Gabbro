# Gabbro — die Konstrukte

**Diese Datei ist die Quelle für den Sprachentwurf.** Der `README` nennt Zweck, These und
Abbruchbedingungen; die Syntaxbeispiele dort sind Auszüge und stehen hier vollständig.

Stand 2026-08-13. **Nichts davon ist übersetzt worden.** Was gemessen ist, steht als gemessen da.

---

## Das Ziel, in einem Satz

> **Gabbro beweist nicht — es erzeugt Programme, deren Gold-Beweis billig ist.**

Der Beweis wird von einem vorhandenen Beweiser geführt (Verus auf Rust-Ausgabe, GNATprove auf
Ada-Ausgabe, oder ein Beweiser über dem erzeugten C). Gabbros Beitrag ist, dass **jedes Konstrukt
seinen Vertrag mitbringt** — Bereich, Fortschritt, Wirkungsraum, Vorbedingung, Übergang. Wer sie
schreibt, hat die Spezifikation schon geschrieben.

### Die Kennzahl, an der das zu messen ist

Gold ist teuer, weil die **Spezifikation** teuer ist. Die belastbare Grösse dafür ist
**Zeilen Spezifikation je Zeile Code**:

| | Verhältnis |
|---|---|
| seL4 (Isabelle über C) | rund **20 : 1** |
| HACL\* (F\* über Low\*) | vergleichbare Grössenordnung |
| **Gabbro — Ziel** | **≤ 1 : 1** — der Beschreiber **ist** die Spezifikation |

- [ ] **Ohne eine gemessene Zahl ist „leicht beweisbar" ein Schlagwort.** Das Verhältnis ist
      am ersten erzeugten Modul zu messen, gegen einen handgeschriebenen Beweis desselben Moduls.
      Verfehlt Gabbro das Ziel deutlich, ist die These widerlegt — und das gehört in die
      Abbruchbedingungen.

---

## 1. `format` — Drahtformate

Reine Funktion an einer Grenze: Bytes rein, Struktur **oder benannte Absage** raus.

```gabbro
format ManifestEintrag @version 3 endian little {
    program_id  : u32
    entry_len   : u32   where == sizeof(Self)
    iface       : u32
    domain      : u8    in { Trusted = 0, Hardware = 1, User = 2 }
    _pad        : [u8; 3]  reserved
    code_hash   : [u8; 32]
    selector    : GeraeteSelektor
}
```

**Erzeugt:** Leser, Schreiber, C-`struct` mit festen Breiten, **je Abweisungsgrund ein eigener
Code**. `where` ist Teil des Formats: der Leser liefert **niemals** eine Struktur, die es verletzt.

**Offen:** variable Längen (die harten 20 % jedes Parser-Erzeugers, Syntax fehlt) ·
Versionsevolution (liest v3 auch v2 — Absage oder Migration?) · Roundtrip `lesen(schreiben(x)) == x`
im Differenztest.

---

## 2. `table` — Tabellen mit Invarianten

**Achtung: andere Kategorie als `format`.** Ein Format ist eine Funktion, eine Tabelle ist
**mutierter Zustand**. Was Gabbro hier erzeugt, ist eine offene Entscheidung — s. `README`,
Zuschnitt (a)/(b)/(c) — und **sie entscheidet den Wert des ganzen Ordners.**

```gabbro
table CapSpace {
    kapazitaet : const 80256

    slot {
        used   : bool
        object : index into objects
        parent : option index into slot
        first_child, next_sibling : option index into slot
        gen    : u32  wrapping        -- Umlauf ist AUSGESPROCHEN, s. Konstrukt 5
    }

    invariant kind_zeigt_zurueck cost O(n * kette) laeuft offline:
        forall s where s.parent = Some(p) => s in chain(p.first_child, next_sibling)
}
```

**`cost` und `laeuft` sind Pflicht, nicht Schmuck.** Eine Invariante ohne Kostenangabe ist
unter dem Kern-Lock kein Audit, sondern ein Ausfall — `colors.rs` hält heute **42 Ticks** und gilt
deshalb als Schuldposten. Und **inkrementelle** Prüfung setzt voraus, dass der Prüfer das Delta
kennt, das **nur der Mutator** kennt: **wer Invarianten im heissen Pfad will, hat Zuschnitt (c)
bereits gewählt.**

---

## 3. `traverse` — Schleifen gibt es nicht

„Endlich" ist das **schwächste** Versprechen: eine Schleife mit Schrittgrenze terminiert und kann
trotzdem ausserhalb der Tabelle indizieren. Genau das ist **S1a**.

```gabbro
traverse geschwister of p
    over  chain(first_child, next_sibling) in slots
    by    unbesucht                  -- Kosten: s. u.
    touches read slots
{ if it == s { found } }
```

| Angabe | tötet |
|---|---|
| `over` | ein Index **ausserhalb der Menge ist nicht formulierbar** (S1a) |
| `by` | Terminierung — und **Zyklen**, wenn der Fortschritt „noch nicht besucht" ist |
| `touches` | fremde Schreibzugriffe; `restrict` **nur an den Parametergrenzen** erzeugter Funktionen |

**`by unbesucht` hat einen Preis, und Regel 3 erzwingt ihn:** ein blosser Schrittzähler
terminiert nur — ein Zyklus würde **stillschweigend abgeschnitten** statt als Absage `Zyklus`
gemeldet, und das wäre Deutung. Also Bitmap (~10 KB über 80 256 Slots, O(n)-Reset) oder
Generationsstempel je Slot. **Die Kostenangabe gehört an `by` selbst:** welche Struktur, wer setzt
sie zurück, was kostet der Reset, darf sie unter dem Lock leben.

---

## 4. `state` — erlaubte Übergänge

Nennt die **zulässigen** Übergänge; alles andere ist nicht formulierbar. Das I9-Fenster
(`used = false` bei `refcount = 1`) wäre damit kein Zufall der Reihenfolge mehr, sondern ein
nicht existierender Übergang.

**Und derselbe Mechanismus trägt eine Ebene tiefer:** `iretq`/`eret` ist ein **typisierter
Übergang in einen gespeicherten Maschinenzustand** — dasselbe Konstrukt, angewandt auf Register
statt auf Felder. Das ist der Grund, warum „Syscalls ohne Assembler" kein Fremdkörper wäre.

---

## 5. Arithmetik mit Vorbedingung

`refcount -= 1` gibt es nicht. Es gibt:

```gabbro
decrement refcount requires refcount > 0        -- oder: wrapping
```

Damit ist **S1b** unformulierbar statt hinterher auffindbar. **Ein Umlauf, den niemand
ausgesprochen hat, ist ein Fehler; einer, der ausgesprochen ist, ein Entwurf** — genau der
Unterschied zwischen S1b und den Generationen, auf deren absichtlichem Umlauf `resolve` ruht.

---

## 6. `assume` / `falsifier` — Hardware-Annahmen

Kein Formalismus deckt „die VT-d-Einheit ehrt `TE=1`". Die Annahme lässt sich aber **benennen**
und **testbar** machen:

```gabbro
assume vtd_te_wirkt
    "GCMD.TE schaltet die Uebersetzung scharf; DMA ohne Kontexteintrag wird danach
     als Fault gemeldet und nicht durchgelassen."
    falsifier probe_vtd_te
```

Das Muster stammt aus Caprock: **ein Wächter prüft die EXISTENZ eines Grundes, nie seine
WAHRHEIT** — deshalb tragen die Identitätsgründe dort einen Falsifikator.

**Drei Klassen, nicht zwei** — die dritte darf nie wie die erste aussehen:

| Klasse | heisst |
|---|---|
| **falsifiziert** | Sonde lief und hielt — eine **Stichprobe**, kein Beweis |
| **nicht falsifizierbar** | keine Sonde möglich, **mit Grund** (`pprobe` meldet unter KVM grundsätzlich `SKIP`) |
| **nicht gefahren** | offen |

**CPU-Errata sind genau Annahmen, die fast immer halten.** Eine bestandene Sonde prüft *diese*
Maschine, *diese* Konfiguration, *diesen* Augenblick — dieselbe Klasse wie „0 Treffer in
114 Läufen". Der Gewinn ist trotzdem real: **Annahmen werden zählbar und ratschenfähig**, und ein
Beweis, dessen Annahmenmenge niemand kennt, ist ein Beweis ohne Reichweite.

- [ ] Der Falsifikator ist Code wie jeder andere und braucht seine **eigene Sprechprobe**:
      *kann er überhaupt fehlschlagen?*

---

## 7. Wirkungen (`Global`/`Depends`-Form)

Jede Operation nennt, was sie liest und schreibt. Dafür gibt es **eine Messung am Mechanismus**:
im Caprock-Scheduler wurden mit SPARKs `Depends` **63 von 63** Datenabhängigkeiten bewiesen, und
„der Rust-Code liest überall genau einmal in eine Kopie" ging von *gelesen* zu *bewiesen*.
**Die Übertragbarkeit auf Gabbro ist damit angenommen, nicht gemessen** — SPARK prüft vorhandenen
Code, Gabbro erzeugt ihn.

---

## Die Linie: sieben Konstrukte, mehr nicht

`format` · `table` · `traverse` · `state` · Arithmetik-Vorbedingung · `assume`/`falsifier` ·
Wirkungen.

**Keine allgemeinen Vor-/Nachbedingungen, keine Quantoren über Rechenausdrücke.** Wer die braucht,
braucht Verus oder F\* — das zu sagen ist ehrlicher als eine halbe Beweissprache.

### Und die Linie bricht voraussichtlich an `revoke`

`decrement requires` ist eine Vorbedingung **auf einem Feld**. Die Korrektheitsbedingung von
`revoke` ist **strukturell**: ein Teilbaum verschwindet, und dass danach `kind_zeigt_zurueck` und
die Kettenendlichkeit noch gelten, ist eine Aussage über **Baumform** — strukturelle Induktion,
also genau die ausgeschlossenen Quantoren.

- [ ] **`revoke` in diesen sieben Konstrukten auf Papier ausdrücken — der billigste nächste
      Schritt des Ordners, vor jeder anderen Entscheidung.** Geht es nicht, bleibt entweder die
      **gefährlichste** Mutation ausserhalb der Garantie, oder die Linie wandert — und dann ist
      Gabbro der Beweisassistent mit Syntax, dem es ausweichen wollte.
