# L1 und L2 — Maschinenmodell und Speichermodell, entworfen und gemessen

**2026-08-14.** Die zwei schwersten Posten aus [`GOLD-LUECKE.md`](GOLD-LUECKE.md). Tragende Zahlen
nachgeprueft.

---

## L1 — Die Axiomzahl: **106**, und der schoenste Fund war schon da

| | |
|---|---|
| Axiome, je Register und Breite gezaehlt | **106** — x86_64 40, aarch64 58, MMIO-Zugriff 8 |
| konservativ (parametrisiert) | **65** |
| davon **reine Lesungen** | **30 (28 %)** — sie aendern keinen Zustand und sind der billige Teil |
| dazu Kontrollfluss-Primitive, Geraeteannahmen | ~8 + ~25 |
| **Die Annahmenmenge A1…An eines Zwei-Architektur-Kernels** | **rund 130 Namen** |

**Damit hat „speichersicher unter A1…An" erstmals einen Inhalt.** 130 ist gross genug, um eine
Ratsche zu rechtfertigen, und klein genug, um sie zu fuehren.

### Zwei Korrekturen an meiner Vorabmessung, beide gegen mich

* **168 `asm!` waren nie 168 Fundstellen** — es sind Aufrufe **plus** `global_asm!` **plus**
  Doc-Erwaehnungen. *(Nachgezaehlt: 150 + 15; die Abweichung zur Agentenzahl ist ein anderes
  Suchmuster, nicht ein anderer Befund.)*
* **Von 129 volatilen Zugriffen sind nur 61 Geraete-MMIO.** Die anderen 68 sind Marken und
  `packed`-Strukturen im normalen RAM. **Ich hatte volatile mit Geraet gleichgesetzt.**

### Der Fund: die Axiomschicht steht schon im Baum, nur ohne Namen

> **Der arch-neutrale Durchschnitt sind ~20 Familien** — aus zwei unabhaengigen Richtungen
> hergeleitet (Absenkungsklassen und Schnittmenge beider Architekturen).
> **Nachgeprueft, und es sind exakt 20:** `caprock-hal/src/x86_64/cpu.rs` hat 27 oeffentliche
> Funktionen, `aarch64/cpu.rs` hat 20, **die Schnittmenge ist 20** — namensgleich:
> `local_irq_save/restore/enable/disable`, `dsb_sy`, `isb`, `csdb`, `csv2`, `csv3`,
> `speculation_barrier`, `array_index_nospec`, `sb_supported`, `core_id`, `mpidr_affinity`,
> `current_el`, `halt`, `wfi`, `irqs_freigegeben`, `hypervisor_present`, `sync_code_range`.

**Caprock hat die Axiomabstraktion gebaut, ohne sie so zu nennen.** Das ist der billigste denkbare
Anfang fuer L1: die Schnittstelle existiert, es fehlen die Uebergangsfunktionen dahinter.

---

## L2 — RC11 ohne die SC-Achse. Und die Wahl ist weniger tragend als gedacht

**Kein Modell erfunden.** Gewaehlt: **RC11 ohne SC**, mit Ownership-Transfer (RSL/FSL/iRC11) als
Oberflaeche — **der Programmierer sieht RC11 nie**, er schreibt `publishes`.

**Die Begruendung ist gemessen, nicht gewaehlt:**

| | |
|---|---|
| `Ordering::SeqCst` im ganzen Baum | **0** — nachgezaehlt |
| `compare_exchange` | 11 |
| nichttriviale lock-freie Algorithmen | 3 |
| Seqlock, RCU, `AtomicPtr`-CAS | **keine** |
| Anteil der Ordnungsangaben in **Selbsttestcode** | **70 %** |

*Promising* faellt, weil sein Alleinstellungsmerkmal (out-of-thin-air) in Caprock kein Gegenstueck
hat; „Rusts Modell" ist kein dritter Kandidat, sondern C11 mit anderer Syntax.

> **Die schaerfere Fassung, und sie relativiert L2 selbst:** was Caprock **beansprucht**, ist
> **RMW-Atomizitaet plus Kohaerenz je Adresse** — und die ist in **allen drei** Modellen identisch.
> Jede Dekker-foermige Stelle im Baum kollabiert darauf. **Die Modellwahl ist damit deutlich
> weniger tragend, als die Luecke unterstellt hat.**

---

## Was NICHT abgedeckt ist

**Die Naht CPU ↔ Geraet ist Forschung**, und der Grund ist differenziert statt pauschal:

| Seite | Stand |
|---|---|
| CPU | **mechanisch** — Ueberapproximation plus voller Zaun |
| Geraet | **benannte Annahme mit Falsifikator** — das kann Gabbro |
| **die Verbindung** | **kein mechanisiertes Vorbild.** Fuer die MMU gibt es Vorarbeit (Syeda & Klein), fuer DMA-Geraete nicht |

**W^X bleibt unformulierbar**, und die Ursache ist dieselbe wie bekannt: **ein PTE ist Zeiger und
Bitfeld zugleich.** Neu ist die Folge — **der TLB-Entwurf haengt daran.** Damit ist das
PTE-Konstrukt kein offener Punkt mehr, sondern ein **Blocker mit Grund**.

---

## Der schwaechste Teil — vom Entwerfer selbst benannt, und es ist das Hausmuster

> **„Der Maschinenzustand ist die Menge der linearen Geisterwerte."**

Wahr fuer Zustand, den ein Kern **haelt**. Stillschweigend erweitert auf **den** Maschinenzustand —
**exakt der Zug, den `HISTORIE.md` als Muster fuehrt**, diesmal von einem Agenten an sich selbst
gefunden. `vspace_wx_ok` ist **eine** gemessene Gegeninstanz, und **wie viele es sonst gibt, ist
nicht gezaehlt**.

- [ ] **Diese Zahl entscheidet, ob L1 ein Entwurf ist oder eine Skizze.** Sie ist billig zu
      erheben und steht als naechster Schritt.

Nachrangig, aber lehrreich: **die erste eigene Axiomzaehlung lag bei 75 statt 106 — 29 % zu klein,
und alle Auslassungen in dieselbe Richtung.** Eine Zaehlung, deren Fehler ein Vorzeichen haben, ist
keine Zaehlung.

---

## Grammatik

**Ein neues Wort** (`result`), vier Produktionen, **kein neuer Mechanismus** — und `result` war
unabhaengig schon noetig: ohne es kann **keine** Funktion mit Rueckgabewert in `ensures` ueber ihn
zusichern. **Die sieben Domaenen halten** — bezahlt mit W^X.
