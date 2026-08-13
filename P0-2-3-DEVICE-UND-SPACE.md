# P0.2 und P0.3 — beide Tore GEFALLEN

**Gefahren am 2026-08-13** von einem unabhaengigen Pruefer, gegen echten Caprock-Code, nur auf
Papier. Bericht und Artefakte im Sitzungs-Scratchpad (`vtd.gabbro`, `delete_leaf.gabbro`,
`delete_leaf.beweis`). Die Zahlen unten habe ich nachgezaehlt, wo sie tragen.

---

## P0.2 — `vtd.rs` als `device`-Block. **Gefallen, und der Grund ist der Nenner**

Der Block: **96 Deklarationszeilen** (15 Register, 5 `transition`, 2 `reason`, 3 `format`,
3 `assume`). `vtd.rs`: **1 448 Zeilen** ohne Leerzeilen, davon **577 Prosa** (nachgezaehlt).

| Faktor gegen … | Wert | Tor ≥ 5 | beantwortet die Frage … |
|---|---|---|---|
| die **ganze Datei** (1 448) | **15,1** | bestanden | „wie viel kleiner ist eine Deklaration als eine Datei, die groesstenteils etwas anderes ist" — **fuer die These bedeutungslos** |
| das, was er **deckt** (306) | **3,2** | **GEFALLEN** | die eigentliche Frage |
| gedeckten **Code** ohne Prosa (191) | **2,0** | **GEFALLEN** | dieselbe, schaerfer |

> **Der Faktor 15 ist genau das Artefakt, gegen das das Tor gebaut war.** Wer ihn meldet, misst die
> Groesse des ungedeckten Restes und nennt sie Knappheit.

**Ungedeckt: 1 141 von 1 448 Zeilen = 78,9 %** (beim Code 78,1 %). Der Pruefer hat die Datei in
66 Bloecke zerlegt und lueckenlos klassifiziert, **zugunsten von Gabbro gerechnet**: ~185 Zeilen
Mehrinstanz-Logik, ~150 Queued Invalidation, ~168 Second-Level-Seitentabellen, ~151 IRTE-Vergabe,
~145 Fehlerbuchhaltung, ~330 Hochlauf.

**Eine ehrliche Gabbro-Fassung der ganzen Datei: ≈ 1 353 Zeilen — Faktor 1,07.**

**Damit ist die Knappheitsthese in der Form widerlegt, in der sie im Plan stand.** `device` ist auf
seinem Gebiet doppelt so knapp wie Rust, nicht fuenffach — und sein Gebiet ist ein Fuenftel der
Datei. Registerlayout ist das Leichte; Warteschlangen, Invalidierung und Fehlerbuchhaltung sind Code.

---

## P0.3 — `delete_leaf` zweimal. **Ueber der Abbruchmarke**

| | Zeilen |
|---|---|
| Gabbro-Code | 63 |
| Spezifikation (nach der Regel: steht in der Quelle, wird vor der Codeerzeugung geloescht) | 71 |
| **Verhaeltnis** | **1,13 : 1** (enger Nenner: 1,69 : 1) |

**Aber die Zahl ist eine Untergrenze, und das ist der eigentliche Befund:** sechs Beweisposten sind
Stuempfe (`{ ... }`). Ausgeschrieben liegt das Verhaeltnis bei **3,6–6 : 1** — **ueber der
Abbruchmarke von 3 : 1**. Dazu: **31 von 134 Zeilen (23 %) sind heute gar nicht schreibbar.**

---

## Das Aggregat — und es erledigt die 10 %-Annahme

Ueber **67,3 % des Baums (44 832 Zeilen)**, drei Toepfe:

| | Anteil |
|---|---|
| **(a)** ausdrueckbar, Beweispflicht faellt durch Konstruktion | **15,1 %** |
| **(b)** ausdrueckbar, braucht handgeschriebene Spezifikation | **65,1 %** |
| **(c)** heute nicht ausdrueckbar | **19,8 %** |

`PLAN.md` rechnete mit **10 %**, die handgeschriebene funktionale Beweise brauchen. Gemessen sind
es **65,1 %** — und die Zahl landet neben den **68,8 %** algorithmischem Rest, die derselbe Plan
selbst fuehrt. **Die Annahme, die die ganze bedingte Ja-Antwort trug, ist nicht haltbar.**

Bei 65 % zu 5 : 1 liegt das Mittel nicht bei 0,8 : 1, sondern **jenseits von 3 : 1** — also an der
Abbruchmarke.

---

## Was das heisst, ohne Beschoenigung

1. **Zwei der drei billigen Papiertore sind gefahren, beide gingen gegen den Ordner.**
2. **Die 0,5 : 1-These ist in ihrer bisherigen Begruendung tot.** Sie ruhte auf „10 % brauchen
   Handbeweis"; gemessen sind 65 %.
3. **Was ueberlebt, ist kleiner und benennbar:** auf den 15,1 %, wo die Beweispflicht durch
   Konstruktion faellt, tut sie es. Das ist ein echter Gewinn — aber es ist ein Fuenftel des
   Kernels, nicht der Kernel.

- [ ] **Die Abbruchbedingung ist beruehrt, nicht ausgeloest** — sie verlangt eine Messung an zwei
      Modulen in Phase P6, nicht eine Hochrechnung. **Aber die Hochrechnung steht jetzt da**, und
      wer sie ignoriert, hat die Marke nachtraeglich gewaehlt.
- [ ] **P0.4 (IPC-Fastpath) ist damit nicht mehr die Entscheidung, sondern die Bestaetigung.**
