# Compiler-Schlussplan: vollständiger, übersetzungsvalidierter, schneller Direkt-Compiler

*Status 2026-10-04: verbindlicher Schließungsplan (PROPOSED, kein Beweis-Claim).
Zentraler Fortschrittsnachweis bleibt `DIRECT-COMPILER.md` (Ledger).
Design: `DIRECT-COMPILER-DESIGN.md`. Optimierer-Spec: `grammatik/OPTIMIZER.md`.
Dieser Plan ist für die Compiler-Schließung maßgeblich; wo ältere Wellen-Docs
(Zahlen, 20er-Kapazität, IR-Erwartung) anderes sagen, gilt dieser Plan plus
Ledger. Nichts hier behauptet eine geschlossene Kette.*

## 0. Geltung und Nicht-Widerspruch

* **Kapazität:** höchstens **15** gemanagte Muse-Modellprozesse insgesamt
  (Autoren, Reviewer, Organisation, Reparaturen). Ältere 20/40-Angaben
  (z. B. `WELLE-A.md`) sind historisch und überholt.
* **Keine persistente SSA-Sprache:** normative Quelle ist das getypte
  `Syntax`/`Semantik`-Modell mit `exec` (Candidate A der
  `DIRECT-LOWERING-DECISION.md`, 594/606 gemergt). Lane 287 ist superseded
  (report-only). SCFG = source-verankerte Blocklisten + vom Validator
  nachgerechnete Claims (L1–L4). Rust-CFG/SSA sind transiente untrusted Hints.
* **Pilot unzureichend:** 14 `Befehl`-Formen (`Typen.lean`, `BYTE-PILOT.md`)
  sind Bootstrap, kein Leistungs- oder Abdeckungsziel. Für 80% GCC-`-O3`
  ist die erweiterte Formenmenge aus §4 erforderlich und zu beweisen.
* **Friend-Übergabe tabu:** `X86/OptimizationRules.lean` und
  `X86/OptimizationWitnesses.lean` bleiben reserviert und werden von
  Compiler-Lanes nicht angefasst.
* **Default Refuse:** unbewiesene Form, fehlgeschlagener Check, fehlender
  Beweis, fehlende Bindung → Abweisung. Optionale Opt darf auf eine billigere
  validierte Route derselben Quelle zurückfallen; Pflicht-Fehler (Decode,
  Permission, Relok, Entry, Duty-Mismatch, Verfeinerung) weisen ab — nie
  Warnung, nie stilles Überspringen.
* **Axiome:** `gabbro_ziel` behält exakt `propext, Classical.choice,
  Quot.sound`. Kein `sorry/admit/axiom/native_decide`, keine
  Per-Programm-Regeln, kein geratenes `ensures`.

## 1. Kette (Lean zuerst, dann Rust)

```
Quelle --T3 uebersetzeAllg--> P + Duties (in Lean aus Quelle gerechnet)
  |
  +-- Rust (untrusted) --> Final-Image-Bytes + Zertifikat-Hints
  |     Blöcke -> Opts -> RA -> Auswahl -> Kodierung -> Bild/Relok
  Lean-Validator valX86 (Bool, bewiesen: valX86_sound)
  |  Bild + Mapping + Decode + Byteschritt + TSO->W->GX
  v
schluss_x86 : geladenes Byte-Bild verfeinert P/GX (generisch, ohne
  vorausgesetzte Verfeinerungs-Prämisse; Verfeinerung wird abgeleitet)
  + gabbro_ziel (Prämissen (a)(b)(c)(d) unverändert)
```

Nur benanntes Silizium/Device/Timing ist Hardware-Annahme. OS, Loader,
Scheduler, Runtime, Bindungs-Körper sind User-Logik mit geprüften Verträgen.

## 2. Pipeline (7 Stufen, jeweils Lean-Modell + Beweis vor Rust)

1. **Frontend:** T3-Treue, volle Einheit/Duties (`DutyExport`, `LowerMap`);
   alle zugelassenen Konstrukte + erreichbaren Funktionen.
2. **Direkt-Lowering:** source-verankerte Blöcke → Maschinenblöcke
   (L1–L4); Calls/Schleifen/Kontrollfluss, Regionen/Arenen mit Decke,
   Atomics/Locks, Gates/`syscall`/`extern` als User-Körper.
3. **Optimierung mit Zertifikat:** Regeln mit Prämisse + Beweis +
   Negativ-Probe; Validator rechnet nach.
4. **RA + private Spills:** disjunkte Register/Stack-Frames, ABI-Profile,
   keine Lecks über Logs/FolgeG.
5. **Auswahl + Kodierung:** kanonisch + kompakt, Längen 1–15, nur bewiesene
   Enkodierung wird emittiert.
6. **Bild + Relok + Mapping:** geprüfte Adressarithmetik, Patch-then-Redecode,
   Datei→VA→Bias, R/W/X, Entry/Runtime/Binding vollständig im Bild.
7. **Validierung + Ausführung:** `Byteschritt` aus echtem Speicher,
   TSO pro Zugriff → W → GX, Budget→Work-Transfer, Fehler/MXCSR/Flags erhalten.
   Danach Rust-Implementierung derselben Interfaces, dann Messung.

## 3. Optimierungen (80% Minimum pro Klasse, 95% Ziel, >110% Ambition)

Score Fix-Work: `100*C/Gabbro`; Throughput: `100*Gabbro/C`.
Gleiche Hardware/ISA-Features, gleiche Semantik, Versionen/Flags protokolliert,
nur validierte Direkt-Binaries zählen (Legacy-C getrennt gelabelt).

**Muss für 80%:** Konstanten-/Kopien-Propagation, DCE, CSE; selektives Inlining
mit Ghost-Rekonstruktion von Call-Logs/`FolgeG`; RA + private Spills; Peephole +
kompakte Kodierung; LICM + begrenztes Unrolling; Stärke-Reduktion aus Bereichen;
redundante Prüfung nur an bewiesenen Stellen entfernen; Alias-Trennung aus
Regionen/Disjointheit; Protected-Load-Reuse; Branch-/Call-Layout.

**Für 95%/110%:** selektive SIMD (erst nach Korrespondenz), Profil-Auswahl unter
validen Translationen, Linkzeit-Layout. Tuning wählt nur unter bereits validen
Translationen — schwächt nie Beweise, ändert nie FP/Concurrency/Verträge.

**Nie:** Fast-Math, Reassoziation, FMA-Einführung, Weitenwechsel, spekulative
Lasten über Sync, `ensures`-Raten.

## 4. Instruktionen (Minimum für 80%, alles bewiesen byte-seitig)

* Moves imm8/imm32/imm64 (zero/sign-extended), reg↔reg alle Breiten 8/16/32/64,
  `movsx/movzx`, LEA ohne Flags; `xor reg,reg`-Idiom, Akku-Kurzformen.
* ALU ADD/SUB/CMP/TEST/AND/OR/XOR/NOT/NEG mit imm8 + imm32 + reg.
* Shifts/Rotates mit imm + CL, breiten-gewählt.
* IMUL (inkl. imm8/imm32-Dreiform), MUL, DIV/IDIV mit Divide-Error-Kanal.
* Kontrollfluss near + short jmp/jcc, indirekt jmp/call, ret; 16 `Bedingung`,
  RFLAGS definiert vs. undefiniert (AF!) korrekt.
* Adressierung disp0/disp8/disp32, SIB + Scale, kein-Index-RSP-Regel,
  RIP-relativ für Daten + Sprungtabellen.
* Stack/ABI 16-B-Align, System-V + freestanding-Profile, Caller/Callee-Save.
* Scalar-FP SSE2: MOVSD/MOVSS, ADD/SUB/MUL/DIV, CVT, UCOMISD, MXCSR
  (bit-genau IEEE, keine Vektor-Pflicht für 80%).
* Nebenläufigkeit: LOCK + XCHG/CMPXCHG/Fetch-Familie, MFENCE/SFENCE/LFENCE,
  TSO-Forwarding/Drain pro Zugriff nach W/GX (keine Wort-Atomarität per
  Behauptung aus 8 Byte-Fakten).
* System: CPUID/XGETBV nur als Feature-Gate, Port-IO/MMIO als Profil,
  IDT/TSS/Eintritt + Maskierung, SYSCALL-MSR nur über Profil + User-Binding;
  Fehler präzise geordnet (Fetch vs. Daten, Page vs. GP).
* Nicht für 80% nötig: AVX/AVX2-Vektoren, BMI, String-Ops breit, Kernel-FPU
  im Modulpfad (kommen nach `schluss_x86`, je Workload-Klasse).

## 5. Schnelle Kompilation (separates Ziel neben 80%)

Zeit bis zum akzeptierten Final-Image inkl. Checks, Opts, Erzeugung,
Validierung, Lean-Kernel-Prüfung. Stufen-Zeiten, Peak-RSS, kalt/warm/
inkrementell getrennt. Begrenzte Suche, deterministische Pass-Budgets, lokale
Zertifikate, kontextkorrekte wiederverwendbare Beweise, Cache-Index ≠ Beweis
(Identität immer nachgeprüft). Budget-Erschöpfung behält bewiesene Route;
fehlende Korrespondenz weist weiter ab. Numerische Compile-Ziele aus
gemessenen Baselines, nicht erfunden.

## 6. Wellen (Vorschlag für das neue Orchestrierungstool)

1. Schluss-Slice: ein Programm Ende-zu-Ende (`schluss_x86`-Skelett +
   `valX86_sound`-Anfang).
2. Kompakt-Kodierung + Adressformen (imm8/disp8/RIP/SIB).
3. RA + Spills + Peephole mit Zertifikaten.
4. LICM/Unroll/Stärke-Reduktion aus Bereichen.
5. TSO-Wortgruppe + LOCK/Fence-Integration.
6. FP-Scalar + MXCSR final.
7. Rust-Backend + Perf-Harness (erst nach 1–6 in Lean akzeptiert).

Jede Welle: disjunkte Dateien, exakte Kandidat-Hashes, unabhängiges
Review (ACCEPT/REPAIR), grüner Build, Standard-Axiome, Zeuge wo ∀-über-Syntax,
Gift-Probe wo Verweigerung. Serielle geprüfte Publikation.
