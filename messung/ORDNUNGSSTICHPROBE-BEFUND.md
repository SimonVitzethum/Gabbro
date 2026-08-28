# Die Ordnungsstichprobe — der Befund

*Ausgeführt am 2026-08-28 nach [`ORDNUNGSSTICHPROBE.md`](ORDNUNGSSTICHPROBE.md). Das Protokoll
stand vor der ersten gelesenen Stelle; die Fächer sind nicht nachträglich erfunden.*

**Gegenstand:** die 2 231 `Ordering::`-Stellen in `/home/simon/Dokumente/caprock-messbasis`,
Zweig `arch/x86_64`. Der Baum wurde ausschliesslich **gelesen** (`grep`, `awk`, `sed`); es gibt
keinen Schreibzugriff und keinen Commit dorthin.

**Urteil in einem Satz:** §1 trägt über dieser Stichprobe — **kein X in 39 gezogenen Stellen** —,
aber er trägt über einem Gegenstand, der **zu 78 % aus Prüfgerüst besteht**, und seine drei
Typregeln **erkennen** den einen `seq`-Fall nicht, sie nehmen ihn nur an, wenn jemand ihn von
Hand hinschreibt.

---

## 1. Die Grundgesamtheit ist nicht, was die Zahl 2 231 sagt

Das ist der grösste Einzelbefund und er steht vor der Stichprobe, weil er sie zur Hälfte
vorwegnimmt.

```
$ cd /home/simon/Dokumente/caprock-messbasis
$ grep -r --include='*.rs' -o 'Ordering::' . | wc -l
2231
```

Die Zahl stimmt. Aber `kernel/src/threads/mod.rs` — die Datei, die §1 wörtlich als seine
Motivation nennt (*„orphaned halves are exactly the error class of the 872 sites in
`threads/mod.rs`"*) — wird auf diesem Zweig **gar nicht kompiliert**:

```
$ sed -n '69,70p' kernel/src/main.rs
#[cfg(all(target_arch = "aarch64", feature = "selftest"))]
mod threads;
```

`target_arch` ist hier `x86_64`. Und selbst auf aarch64 hängt das Modul an `selftest`, das
laut `kernel/Cargo.toml` **nicht in `default`** steht (A-2.2, gedreht 2026-07-29). Dasselbe gilt
für `handlermess.rs` (`system.rs:9158`, `#[cfg(feature = "selftest")]`), `sperrmark.rs`
(`main.rs:62`) und `threads/fuzz.rs` (zusätzlich `kernel-fuzz`).

Gemessen mit einem Skript, das je Stelle die nächste umschliessende `fn`/`mod` sucht und deren
`#[cfg]` liest (Skript im Scratchpad, `gate.py`):

| | Stellen | Anteil |
|---|---:|---:|
| hinter `selftest` / `kernel-fuzz` / `sperrwacht` oder modul-gegated → **K4** | **1 748** | **78,4 %** |
| nur `aarch64` (**kein** K-Wegfall, auf diesem Zweig aber nicht kompiliert) | 25 … 66 * | 1 … 3 % |
| im x86_64-Vorgabebau tatsächlich kompiliert | **458** | **20,5 %** |

\* methodenabhängig: je nachdem, ob die Zuordnung an der nächsten `fn` oder am nächsten `mod`
hängt (`mod smmu_enforcer_arm` in `system.rs` trägt allein 39 Stellen). Die Zahl ist klein und
für das Urteil ohne Gewicht; die K4-Zahl ist die robuste.

Je Datei, dieselbe Messung:

```
threads/mod.rs   1054  -> 100 % K4 (Modul auf diesem Zweig nicht kompiliert)
bringup.rs        397  ->  96 % K4 (nur `run`, `ap_entry`, `devsel_bericht` ungegated: 16 Stellen)
system.rs         186  ->   9 % K4  <- der eigentliche Kernel
threads/fuzz.rs   126  -> 100 % K4 (in K4 namentlich genannt)
```

**Was daraus folgt:** „2 231 Stellen" ist die Zahl des *Baums*, nicht die des *Kernels*. Die
Klasse, die §1 schliessen will, ist im ausgelieferten Bau rund **458 Stellen** gross. Das macht
§1 nicht kleiner — es macht ihn *billiger*, und es macht die Vermutung „einstellig" für die
`seq`-Fälle plausibler, als sie gegen 2 231 klänge.

---

## 2. Der Zug — deterministisch und nachziehbar

Schichtung nach Abschnitt 3 des Protokolls. **Zwei Zählweisen sind möglich** und ich nenne
beide, weil das Protokoll sie vermischt: seine Gesamtzahl 2 231 sind **Vorkommen**, seine
Dateizahlen (872/390/184/112) sind **Zeilen mit Treffer** (deren Summe ist 2 017; 213 Zeilen
tragen zwei `Ordering::`). **Die Schichtzugehörigkeit ist unter beiden identisch** — geprüft —,
also ist die Wahl folgenlos. Gezogen wurde über **Vorkommen**, passend zur Kopfzahl 2 231.

Zugregel unverändert: Stellen je Datei in Quellreihenfolge 1..N, gezogen an
`floor(k·N/(m+1) + 0,5)` für `k = 1..m` (Aufrunden bei .5; Pythons `round()` rundet zur geraden
Zahl und wurde deshalb nicht benutzt).

| Schicht | Dateien | je Datei | Summe |
|---|---:|---:|---:|
| **A** — ≥ 100 Stellen | 4 | 5 | 20 |
| **B** — 10 … 99 Stellen | **14** | 1 | 14 |
| **C** — 1 … 9 Stellen, die 5 grössten | 5 | 1 | 5 |
| | | | **39** |

> **Abweichung vom Protokoll, benannt:** Abschnitt 3 schätzt Schicht B auf „~11" Dateien.
> Es sind **14** (10–99 Stellen: caprock-sync 58, handlermess 49, vtd 42, verifizierer 40,
> userstackmark 30, loader 30, konsole 26, kstackmark 25, x86_64/mmu 24, sperrmark 16,
> x86_64/exception 16, sidecarkopie 12, caprock-sched 12, aarch64/mmu 12). Der Auftrag sagt
> „alle Dateien mit 10–99 Stellen"; ich bin dem Wortlaut gefolgt, nicht der Schätzung.
> Schicht C ist eindeutig: 9, 9, 7, 6, 6 — die sechste hat 5.

---

## 3. Die 39 Stellen

Fach nach dem Protokoll. `#n` ist die Nummer des Vorkommens in der Datei (bei zwei Vorkommen
in einer Zeile steht dabei, das wievielte).

### Schicht A

| # | datei:zeile | Wort | Fach | Begründung (Prüffrage aus §1) |
|---|---|---|---|---|
| 1 | `threads/mod.rs:3390` (#176, 2. der Zeile) | `Acquire` | **W** K4 | `XCORE_WOKEN` in einem `println!("DBG pending: …")` der Selbsttest-Notbremse; Modul auf diesem Zweig nicht kompiliert. |
| 2 | `threads/mod.rs:3919` (#351) | `Release` | **W** K4 | `RCAP_DONE` — Fertigmerker der Reply-Cap-Revocation-Prüfzeile im Demo-Treiber. |
| 3 | `threads/mod.rs:4605` (#527) | `Relaxed` | **W** K4 | `SMMU_EVTQ` aus `system::testsupport::…` — Testgerüst, das ein Testergebnis puffert. |
| 4 | `threads/mod.rs:4946` (#703) | `Relaxed` | **W** K4 | `CROSS_NT` — Notification-Slot der ext-27-Kreuzmatrix, reiner Suitenzustand. |
| 5 | `threads/mod.rs:5539` (#878) | `Relaxed` | **W** K4 | `R1[i]` — IPC-Ergebnisse, gelesen in `report()` zum Drucken. |
| 6 | `bringup.rs:1246` (#66) | `Release` | **W** K4 | `PARK_MESS` in `#[cfg(selftest)] fn park_messen`; die Static selbst ist gegated. |
| 7 | `bringup.rs:2715` (#132) | `Acquire` | **W** K4 | `CKPT_PROGRESS` in `#[cfg(selftest)] fn ckpt_bericht` (Z. 2701). |
| 8 | `bringup.rs:3204` (#199) | `Release` | **W** K4 | `CKPT_DONE` in `#[cfg(selftest)] fn drv_service_step` (Z. 2985). |
| 9 | `bringup.rs:3385` (#265) | `Release` | **W** K4 | `CKPT_REQ`, dieselbe gegatete Funktion. |
| 10 | `bringup.rs:4071` (#331) | `Relaxed` | **W** K4 | `FP_PROGRESS[0]` in `#[cfg(selftest)] fn all_done` (Z. 3995). |
| 11 | `system.rs:1368` (#31) | `Relaxed` | **P** | `FP_OWNER[core] = NONE` — Besitzübergabe an den FP-Registersätzen; **§1s eigenes Beispiel**, `publishes { FP_STATES[slot] }` ist schreibbar. |
| 12 | `system.rs:2754` (#62) | `Relaxed` | **P** | `FP_OWNER[src]`-Lesung vor `fp::save` in `migrate_to` — dieselbe Paarung, Empfängerseite. |
| 13 | `system.rs:5156` (#93) | `Release` | **P** | `IRQ_ANY_PENDING = true` trägt die Nutzlast `IRQ_PENDING[i]` (und darüber `IRQ_NTFN`/`IRQ_BADGE`); `drain_pending_irqs` ist der Empfänger. |
| 14 | `system.rs:5569` (#124) | `Acquire` | **P** | `cmdq_phys` ist die **Nutzlast** der Paarung an `self.active` (Z. 5415 `Release` nach Z. 5406); in Gabbro wird daraus eine gewöhnliche Stelle im geprüften Zweig. |
| 15 | `system.rs:6524` (#155) | `Relaxed` | **Z** | `UNDECLARED_COUNT.fetch_add` — Telemetriezähler, keine Nutzlast. |
| 16 | `threads/fuzz.rs:111` (#21) | `Relaxed` | **W** K4 | `fuzz.rs` ist in K4 namentlich genannt; zusätzlich `kernel-fuzz`. |
| 17 | `threads/fuzz.rs:160` (#42) | `Acquire` | **W** K4 | `CERTFUZZ_OK` in `all_passed()` — dito. |
| 18 | `threads/fuzz.rs:200` (#63) | `Acquire` | **W** K4 | `FUZZ_SMP_OK` in `report()` — dito. |
| 19 | `threads/fuzz.rs:278` (#84) | `Relaxed` | **W** K4 | `HWFUZZ_LCG` — der PRNG des Fuzzers. |
| 20 | `threads/fuzz.rs:998` (#105) | `Relaxed` | **W** K4 | `IPCF_STOP` — Abbruchflagge der Fuzzer-Aktoren. |

### Schicht B

| # | datei:zeile | Wort | Fach | Begründung |
|---|---|---|---|---|
| 21 | `caprock-sync/src/lib.rs:728` (#29) | `Relaxed` | **W** K4 | `STELLE_BEREINIGT` in `#[cfg(feature = "sperrwacht")] fn hochlauf_abschliessen` — die Sperrhaltedauer-**Marke**, vom Kernel-`selftest` mitgezogen. (K3 berührt sie zusätzlich: sie setzt den Akkumulator zurück, den `caprock-sync:572-592` bildet.) |
| 22 | `handlermess.rs:501` (#25) | `Release` | **W** K4 | `R_START` im Binder der Prüfzeile `handler`; `pub mod handlermess` steht in `system.rs:9158` unter `#[cfg(feature = "selftest")]`. |
| 23 | `vtd.rs:686` (#21) | `Acquire` | **Z** | `AGG_COHERENT` — dreiwertiger, gemerkter Fähigkeitswert (0 = unbekannt → neu rechnen). Keine getrennte Nutzlast, der Wert **ist** die Auskunft; `relaxed`/`publishes nothing` ist korrekt. *Kein Zähler — s. §5.* |
| 24 | `verifizierer.rs:598` (#20) | `Release` | **W** K4 | `SONDE_TID` ist `#[cfg(selftest)]` (Z. 403), ebenso die umschliessende Funktion. |
| 25 | `userstackmark.rs:278` (#15) | `Acquire` | **W** K4 | `EICHUNG.load` in `eichstand()` — die Eichung des Messgeräts; `*mark.rs` ist in K4 namentlich genannt, und geschrieben wird `EICHUNG` nur von der `#[cfg(selftest)]`-Fassung von `eichung()`. |
| 26 | `loader.rs:682` (#15) | `Relaxed` | **P** | `PROG_TIDS[i]` ist der Schlüssel, `PROG_TID_RAW[i]` die daran hängende Nutzlast (`thread_of_program` sucht über den einen und liest den anderen). **§1 fände hier einen echten Mangel** — s. §6. |
| 27 | `konsole.rs:337` (#13) | `Relaxed` | **Z** | `risse.fetch_add` — Zähler zerrissener Zeilen, gelesen nur für `Stand`. |
| 28 | `kstackmark.rs:221` (#13) | `Relaxed` | **W** K4 | `TIEFSTER_SLOT` in `#[cfg(selftest)] unsafe fn messen`; zusätzlich `*mark.rs`. |
| 29 | `x86_64/mmu.rs:763` (#12) | `Relaxed` | **Z** | `GUARDS_LIVE.load` in `guard_stats()` — Kennzahl für eine Berichtszeile. |
| 30 | `sperrmark.rs:441` (#8) | `Release` | **W** K4 | `EICHUNG.store`; `mod sperrmark` steht in `main.rs:62` unter `#[cfg(selftest)]`, und es ist ein `*mark.rs`. |
| 31 | `x86_64/exception.rs:692` (#8) | `Relaxed` | **Z** | `NMI_FENSTER[k].load` in `nmi_bilanz()` — Aufsummierung eines Gelegenheitszählers. |
| 32 | `sidecarkopie.rs:106` (#6) | `Relaxed` | **Z** | `ZUSTELLUNGEN.fetch_add` — ein **Erzeugungszähler**, im Protokoll wörtlich als Z genannt. Die Eindeutigkeit kommt aus dem RMW, nicht aus der Ordnung. |
| 33 | `caprock-sched/src/lib.rs:1399` (#6) | `Relaxed` | **Z** | `CORE_LOAD[self.core].store` — sperrfrei lesbare Lastkennzahl für die Platzierung (Z. 518 ff.). Kein K1: gelesen wird sie **ausserhalb** jedes Scheduler-Locks. |
| 34 | `aarch64/mmu.rs:800` (#6) | `Relaxed` | **S** | `CWG_MAX.fetch_max` — die Korrektheit hängt an einer Ordnung über **zwei** Atomics (`CWG_MAX`, `CWG_SEALED`) mit **N Schreibern**. Vollständig ausgeschrieben in §4. |

### Schicht C

| # | datei:zeile | Wort | Fach | Begründung |
|---|---|---|---|---|
| 35 | `x86_64/timer.rs:96` (#5) | `Relaxed` | **Z** | `TICKS[core].load` — Tickzähler je Kern. |
| 36 | `x86_64/gdt.rs:389` (#5) | `Relaxed` | **Z** | `OHNE_TSS.fetch_add` — Zähler der Kerne über `MAX_TSS_CORES`, gelesen in Z. 259 für den Bericht. |
| 37 | `x86_64/pcie.rs:81` (#4) | `Acquire` | **Z** | `ECAM_BASE.load` in `cfg_addr` — der Wert **ist** die Adresse; diese Lesung braucht `MAX_BUS` nicht, also kein `awaits`, also `relaxed`. *Kein Zähler — s. §5.* |
| 38 | `caprock-microkit/src/lib.rs:693` (#3) | `Relaxed` | **Z** | `PD_CREATE_SCAN_ITER.fetch_add(iter)` — Füllstandszähler des linearen Slot-Scans (C4). |
| 39 | `x86_64/intc.rs:170` (#3) | `Release` | **P** | `MODE = 1` ist die **Nutzlast** der Veröffentlichung an `READY` (Z. 174, `Release`), die `eoi()` (Z. 194, `Acquire`) empfängt und über `x2apic_active()` liest. |

---

## 4. Die Summen

| Fach | Zahl | Anteil am Nenner |
|---|---:|---:|
| **P** — Paarung | **6** | 33 % |
| **Z** — Zähler | **11** | 61 % |
| **S** — benannter `seq`-Fall | **1** | 6 % |
| **X** — vierter Ausgang | **0** | 0 % |
| **Nenner (ohne W)** | **18** | |
| **W** — Wegfall | **21** | |

**Die 21 W, je K-Grund:**

| Grund | Zahl | Stellen |
|---|---:|---|
| **K4** — Mess- und Selbsttestgerüst | **21** | 1–10, 16–22, 24, 25, 28, 30 |
| **K1** — unter einer Sperre | 0 | — |
| **K2** — im Inneren eines Konstrukts | 0 | — |
| **K3** — von `accumulates` besser gedeckt | 0 | (Nr. 21 wird davon berührt, fällt aber schon über K4) |

**Alle 21 Wegfälle sind K4.** Das ist keine Verteilung, das ist ein einziger Grund — und es ist
dieselbe Zahl wie in §1: 78 % der Grundgesamtheit ist Prüfgerüst, und die Ziehung hat es
proportional getroffen (21/39 = 54 %, weil die Schichtung gegen die Klumpung arbeitet und
Schicht B/C überrepräsentiert).

**K1 kam nie zum Zug, und das ist ein Befund für sich.** Bei zwei Stellen sah es zunächst danach
aus (Nr. 11/12 an `FP_OWNER`, Nr. 33 an `CORE_LOAD`) — beide Male trägt die Sperre die Stelle
**nicht**: `fp_reset_slot` läuft über die `FP_OWNER`-Einträge **aller** Kerne, während es nur den
eigenen `SCHED` hält (`system.rs:1365`), und `CORE_LOAD` wird ausdrücklich sperrfrei gelesen
(`caprock-sched:518`). Caprock benutzt Atomics dort, wo die Sperre gerade nicht reicht —
K1 ist im Protokoll richtig vorgesehen, in dieser Stichprobe aber leer.

---

## 5. Kein X — und wo es knapp war

Es gibt **kein X**. Das ist das schwächere der beiden möglichen Ergebnisse und ich schreibe
deshalb aus, wo die Einordnung wirklich eng war, damit sie überprüfbar ist statt geglaubt.

### 5.1 Die knappste Stelle: Nr. 34, `aarch64/mmu.rs:800`

```rust
// crates/caprock-hal/src/aarch64/mmu.rs
757  static CWG_MAX: AtomicU64 = AtomicU64::new(0);
...
783  pub fn record_cache_granule() {          // <- von JEDEM Kern gerufen
784      let g = local_cwg();                 //    (init_primary Z.289, init_secondary Z.296)
790      if CWG_SEALED.load(Ordering::Acquire)
791          && g > CWG_MAX.load(Ordering::Relaxed) { panic!(…) }
800      CWG_MAX.fetch_max(g, Ordering::Relaxed);        // <-- die gezogene Stelle
801  }
806  static CWG_SEALED: AtomicBool = AtomicBool::new(false);
817  pub fn seal_cache_granule() {            // <- NUR von Kern 0 gerufen (main.rs:282)
818      CWG_SEALED.store(true, Ordering::Release);
819  }
821  pub fn dma_granule() -> u64 {
822      if !CWG_SEALED.load(Ordering::Acquire) { return CWG_ARCH_MAX; }
826      match CWG_MAX.load(Ordering::Relaxed) { 0 => CWG_ARCH_MAX, g => g }
830  }
```

`dma_granule()` gattert `install_dma_cap` (`system.rs:6766`, `dma_granule_ok`) — eine
**Autoritätsprüfung**, keine Diagnose. Die Verpflichtung lautet: *ist `CWG_SEALED` einmal wahr,
enthält `CWG_MAX` das Maximum **aller** Kerne.*

**Warum es kein P ist:** man könnte `CWG_SEALED = true publishes { CWG_MAX }` hinschreiben, und
§1s Regel 1 (statischer Namensvergleich) liesse es **durch**. Es wäre trotzdem falsch: das
`release` von Kern 0 veröffentlicht **die Schreibzugriffe von Kern 0**, nicht das `fetch_max`
von Kern 5. §1s Regel 3 („Order follows from the pairing") gilt für **zwei** Parteien; hier sind
der Veröffentlichende und der Schreiber der Nutzlast verschiedene Kerne. Eine Paarung, die
typprüft und trotzdem nicht trägt, wäre schlimmer als gar keine.

**Warum es kein Z ist:** heute steht dort `relaxed`, also genau die Z-Form
(`publishes nothing`). Sie ist eine **falsche Erklärung** — der Wert wird gebraucht, und zwar
geordnet gegen ein anderes Atomic.

**Warum es doch ein S ist, und kein X:** die Verpflichtung ist eine Aussage über die
**Reihenfolge** zweier verschiedener Atomics (`CWG_MAX`, `CWG_SEALED`) — keine getrennte
Nutzlast wird von einer Flagge mitgetragen, der akkumulierte Wert ist die Sache selbst. Beide
Bedingungen der Schärfung sind erfüllt: (a) es hängt an der Ordnung, (b) an zweien. Mit `seq`
auf beiden plus einer `obligation` („nach dem Versiegeln enthält `CWG_MAX` das Maximum aller
Kerne") ist es schreibbar und die Erklärung ist wahr. **Genau die Sorte, die §1 als
„einstellig" vermutet — hier ist eine davon, gezählt.**

> **NACHGETRAGEN 2026-08-28: der Finder ist gebaut, und er hätte Nr. 34 gefunden.** `V009`
> (`paarung.rs`) sagt genau diese Gestalt ab — ein Atomic ohne Nutzlast, dessen Wert einen
> Zweig gattert, hinter dem ein fremder geteilter Platz gelesen wird. Und `V010` fängt die
> Paarung aus dem Absatz darüber, die typprüft und nicht trägt. **Was er NICHT findet und was
> der vollständige Zuschnitt gekostet hätte (18 Fehlalarme über dem sauberen Korpus), steht
> in [`ORDNUNGSFINDER.md`](ORDNUNGSFINDER.md) §2.**

> **Zwei Dinge, die dabei mit auffallen und nicht zum Fach gehören:**
> 1. §1 verspricht *„Lowering: exactly the C11 atomics that stand there today — extra cost 0."*
>    An dieser Stelle stimmt das **nicht**: heute steht `relaxed`, richtig wäre `seq`. Die
>    Korrektur kostet.
> 2. **§1s drei Typregeln können ein S nicht *finden*.** Sie prüfen Paarungen; eine Stelle, die
>    `publishes nothing`/`relaxed` erklärt, geht durch. Wer dieses Feld als Z deklariert,
>    bekommt keinen Fehler — er bekommt einen Übersetzer, der schweigt. Das ist keine
>    Widerlegung der Dreiteilung, aber eine Lücke in der **Prüfung**, und sie sitzt genau an dem
>    Fach, das §1 als Randfall abtut.

### 5.2 Zwei Stellen, an denen Z nur *operativ* passt: Nr. 23 und Nr. 37

`AGG_COHERENT` (`vtd.rs:686`) und `ECAM_BASE` (`pcie.rs:81`) sind **keine Zähler, keine
Statistik, keine Kennzahl** — es sind **Einmal-Latches**: ein Wert wird einmal ermittelt, mit
`Release` abgelegt und mit `Acquire` gelesen; eine getrennte Nutzlast hängt nicht daran.

Ich habe sie nach der **Prüffrage** des Protokolls eingeordnet („Trägt er KEINE Nutzlast?") und
nicht nach dem Substantiv der Fachspalte („Zähler"). Nach der Prüffrage sind es Z, und die
Gabbro-Form `relaxed` + `publishes nothing` + kein `awaits` ist schreibbar **und korrekt** — die
Wertübergabe eines Atomics leistet die Atomizität, nicht die Ordnung. §1 würde diese beiden
Stellen sogar **verschärfen**: das `Acquire` ohne `awaits` wäre nicht mehr schreibbar.

**Aber die Gabelung gehört benannt, weil sie das Urteil dreht:**

| Lesart von Z | P | Z | S | **X** | Urteil |
|---|---:|---:|---:|---:|---|
| operativ („trägt keine Nutzlast") — **die des Protokolls** | 6 | 11 | 1 | **0** | §1 trägt |
| wörtlich („Zähler / Statistik / Kennzahl") | 6 | 9 | 1 | **2** | §1 widerlegt |

Ich halte die operative Lesart für die richtige: das Protokoll stellt in der Fachspalte eine
**Frage**, und die Beispiele hinter dem Gedankenstrich sind Erläuterung. §1 selbst formuliert die
Regel als *„`relaxed` is writable only with `publishes nothing`/without `awaits`"* und setzt
„(counters)" nur in Klammern dahinter. **Wer die andere Lesart wählt, hat zwei X und die Zahlen
stehen oben.** Die Sache selbst ist unstrittig; strittig ist ein Wort, und dann sagt man es.

*Folgerung für die Sprache, nicht für die Messung:* das Fach heisst falsch. „Zähler" beschreibt
9 von 11 Fällen; die anderen zwei sind Latches. Ein Name wie **„ohne Nutzlast"** träfe alle elf
und nähme der Gabelung den Boden.

> **NACHGETRAGEN 2026-08-28: die Folgerung ist gezogen.** `SPRACHE.md` Teil II §1 sagt
> **„payload-free"** statt „(counters)", und die Begründung mit beiden Formen steht in
> [`ORDNUNGSFINDER.md`](ORDNUNGSFINDER.md) §6. **Kein neues Sprachwort** — `publishes nothing`
> sagte es schon; es fehlte nur der Name für das Fach. *Die Zahlen dieses Berichts ändern sich
> dadurch nicht; die Tabelle oben führt beide Lesarten weiter.*

---

## 6. Was die Stichprobe nebenbei über Caprock sagt

Nicht Gegenstand der Messung, aber beim Lesen gefunden und zu belegbar, um es wegzulassen:

**Nr. 26, `loader.rs:678-687` — eine Paarung, die §1 abfangen würde.**

```rust
630  pub fn record_program_thread(program_id: u32, tid: ThreadId) {
632      let cur = pid.load(Ordering::Relaxed);
633      if cur == program_id || cur == 0 {
634          pid.store(program_id, Ordering::Relaxed);        // ZUERST der Schluessel
635          raw.store(tid.to_raw() + 1, Ordering::Relaxed);  // DANN die Nutzlast
...
678  pub fn thread_of_program(program_id: u32) -> Option<ThreadId> {
682      .find(|(p, _)| p.load(Ordering::Relaxed) == program_id)   // <-- gezogene Stelle
684      .and_then(|(_, raw)| { let v = raw.load(Ordering::Relaxed); … })
```

Der Schlüssel wird **vor** der Nutzlast abgelegt, beide `relaxed`, in beide Richtungen gesucht
(`program_of_thread` sucht über `raw` und liest `pid`, `thread_of_program` umgekehrt). Ein
`publishes { PROG_TID_RAW[i] }` erzwänge `release` — und `release` verlangt, dass die Nutzlast
**vorher** steht. Die Reihenfolge in Z. 634/635 ist verkehrt. Beide Pfade sind Produktionscode
(`record_program_thread` aus `loader.rs:1592/1630`, `thread_of_program` aus `vollzaehligkeit`,
die `manifest_report()` ausserhalb von `selftest` ruft). **Das ist genau die Fehlerklasse, für
die §1 gebaut ist, und §1 fände sie.**

**Nr. 32, `sidecarkopie.rs:139-142` — eine Veröffentlichung, die §1 gar nicht sieht.**

```rust
141      core::sync::atomic::fence(Ordering::Release);
142      p.add(redirect::KOPF_MAGIE).write_volatile(redirect::MAGIE);
```

Die Kennung wird als **`write_volatile`** abgelegt, nicht als atomarer Store; die Ordnung kommt
aus einer freistehenden `fence`. `publishes` hängt in §1 an einem Store auf einem Atomic — diese
Veröffentlichung wäre also nicht zu *annotieren*, sondern **umzuschreiben**. Sie steckt in den
2 231 (die `fence` trägt ein `Ordering::`), aber sie ist keine Paarung im Sinne von §1.

**Ein Bruch mit §1s eigenem Beispiel.** §1 illustriert die Paarung an
`FP_OWNER[core] = tid publishes { FP_STATES[tid] }`. Im Baum ist `FP_STATES` ein
`SpinLock<Slab<FpState>>` (`system.rs:662`) und wird **nur unter dieser Sperre** angefasst
(1342, 1364, 2755). Die Sichtbarkeit der Nutzlast leistet dort die Sperre; die Paarung ist an
dieser Stelle Gürtel neben Hosenträgern. Was `FP_OWNER` wirklich bewacht, sind die **lebenden
FP-Register der CPU** — kein Speicherplatz, den eine `placelist` nennen könnte. Ich habe Nr. 11
und 12 trotzdem als **P** gezählt, weil §1 sie selbst so nennt; wer strenger zählt, bekommt hier
zwei weitere Grenzfälle.

---

## 7. Was diese Messung NICHT sagt

* **Nicht**, dass §1 über den restlichen 2 192 Stellen trägt. 39 gezogene Stellen, geschichtet
  gegen die Klumpung, deterministisch. Sie konnte §1 widerlegen; bestätigt hat sie ihn nur für
  ihren eigenen Umfang.
* **Nicht**, dass es im Baum keine X gibt. Ein X in 39 Ziehungen nicht zu treffen ist bei einer
  X-Rate unter ~2,5 % der Normalfall, nicht die Ausnahme. Das Ergebnis „0 von 18" schliesst
  Raten bis in den einstelligen Prozentbereich **nicht** aus.
* **Nicht**, dass die Vermutung „einstellig" für die `seq`-Fälle stimmt. Sie ist mit **1 S in
  18** verträglich — und 1/18 auf 458 kompilierte Stellen hochgerechnet wären ~25, also
  *zweistellig*. Die Stichprobe ist für diese Hochrechnung zu klein (ein einziger Fund), aber
  sie zeigt zumindest nicht in die Richtung, die §1 vermutet. **Das ist die Zahl, die eine
  Wiederholungsmessung als erstes schärfen müsste.**
* **Nicht**, dass die 78 % K4 ein Mangel an Caprock sind. Sie sind das Gegenteil: ein Baum, der
  seine Prüfinfrastruktur hinter einem Feature führt und sie nicht ausliefert. Für **Gabbro**
  heisst es nur, dass die Zahl 2 231 als Aufgabengrösse zu gross ist.
* **Nicht**, dass die aarch64-Stellen (Nr. 34 unter anderem) auf dem gemessenen Zweig laufen.
  `crates/caprock-hal/src/aarch64/` und `mod smmu_enforcer_arm` sind auf `arch/x86_64` nicht
  kompiliert. Das Protokoll kennt dafür **keinen** Wegfall, also sind sie mitgezählt — mit
  diesem Vermerk. Nr. 34 ist im ausgelieferten **aarch64**-Kernel echter Produktionscode.
* **Nicht**, dass die Zuordnung „W nach K4" bei Nr. 25 und 28 zwingend ist. `userstackmark.rs`
  und `kstackmark.rs` werden im Vorgabebau **kompiliert**; gegated sind dort die schreibenden
  Funktionen, die gezogenen Stellen sind Lesungen, die dann konstant 0 liefern. K4 nennt
  `*mark.rs` namentlich, deshalb W — aber die Entscheidung ist benannt und nicht selbstredend.

---

## 8. Nachziehen

```bash
# Grundgesamtheit
cd /home/simon/Dokumente/caprock-messbasis && git rev-parse --abbrev-ref HEAD   # arch/x86_64
grep -r --include='*.rs' -o 'Ordering::' . | wc -l                              # 2231

# Der Zug (Skript im Scratchpad dieser Sitzung: zug.py)
#   Stellen je Datei in Quellreihenfolge 1..N nummeriert (Vorkommen, nicht Zeilen),
#   gezogen an floor(k*N/(m+1) + 0.5) fuer k = 1..m.
#   Schicht A: m=5 ueber threads/mod.rs, bringup.rs, system.rs, threads/fuzz.rs
#   Schicht B: m=1 ueber die 14 Dateien mit 10..99 Stellen
#   Schicht C: m=1 ueber timer.rs, gdt.rs, pcie.rs, microkit/lib.rs, intc.rs

# Die Gate-Messung (gate.py): je Stelle die naechste umschliessende fn/mod und deren #[cfg].
#   -> 1748 K4 (78,4 %) · 458 im x86_64-Vorgabebau (20,5 %)
```

Wer nachrechnet, bekommt dieselben 39 Stellen. Wer anders einordnet, muss §5.2 widersprechen —
und dort steht, wie die Zahlen dann lauten.
