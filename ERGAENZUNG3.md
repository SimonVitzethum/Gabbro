# ERGÄNZUNG 3 — Hardware-Annahmen vollständig, und der Bootpfad als Sprache

**Nachtrag zu [`FESTLEGUNG.md`](FESTLEGUNG.md), [`ERGAENZUNG.md`](ERGAENZUNG.md),
[`ERGAENZUNG-2.md`](ERGAENZUNG-2.md).** Die Axiomschicht war ein System mit Beispielen; hier wird
sie **ausgezählt** — nicht aus Vorstellung, sondern **gemessen am Zweig `arch/x86_64` von
Caprock** (`kernel/src/arch/x86_64/`, `crates/caprock-hal/src/x86_64/`). Und der unsichere
Bootcode, bisher ein Satz in drei Schichten über einer Prosastrecke, wird zur Sprache: das echte
Trampolin (`mod.rs`, `_start` bis `x86_rust_entry`) ist die Vorlage, Zeile für Zeile.

> **EINGETRAGEN 2026-08-14, mit vier nachgeprueften Zahlen und einer Namensberichtigung.**
> Grammatik: **119 Regeln, 0 offen, 189 Terminale gegen 189 Wortschatzwoerter**, beide Waechter
> gruen. Der Waechter zaehlt **zwei** neue Woerter — die Kopfzeile stimmt diesmal.
>
> **Nachgeprueft am Zweig, alle vier:**
> `int 0x80` steht woertlich in `crates/caprock-hal/src/x86_64/syscall.rs:23`, und der Kommentar
> bei `:4` stellt es ausdruecklich dem `syscall`/`sysret`-Weg gegenueber — **die Berichtigung an
> ERGAENZUNG §2 ist richtig.** `ABI_TO_GPR` ist `[usize; 7]` ab `RAX, RDI, RSI`
> (`exception.rs:73`). **Kein einziges `xsave`/`xrstor` im Baum** (7 `fxsave`, 6 `fxrstor`) — die
> `FpArea`-Praezisierung stimmt. Und der Port-Posten, den A12 aus der Axiomschicht holt, ist mit
> **70 Fundstellen** (52 `outb`/`outl`, 18 `inb`) **groesser** als die Zaehlung angibt.
>
> **Eine Namensberichtigung beim Eintragen:** `via int 0x80` ist nicht schreibbar, weil `int` in
> der Lexik die **Zahlenklasse** ist (`int = dec | hex | bin`). Der Mechanismus ist ein Bezeichner
> aus geschlossener Menge, der Vektor kommt aus dem vorhandenen `vector`:
> `entry syscall vector 0x80 via softint arch x86_64 { … }`. **Kein zusaetzliches Wort.**

Stand 2026-08-14. **Neue Wörter (geschlossen, zwei):** `port step`
(`via`, `boot`, `requires`, `ensures` werden wiederverwendet — eine Grammatikerweiterung ist
keine Wortschatzerweiterung.)

---

## 0. Die Zählung — was der Zweig wirklich anfasst

Privilegierte und geordnete Befehle im x86_64-Teil, dedupliziert (Fundstellen, nicht Aufrufe):

| Befehl | # | | Befehl | # | | Befehl | # |
|---|---|---|---|---|---|---|---|
| `outb`/`out` | 46+ | | `mov cr0` | 7 | | `sfence` | 2 |
| `hlt` | 35 | | `iretq` | 7 | | `rdtsc` | 2 |
| `cpuid` | 26 | | `lfence` | 7 | | `invlpg` | 2 |
| `inb` | 17 | | `mov cr3` | 6 | | `sysret` | 1 |
| `wrmsr` | 12 | | `lgdt` | 4 | | `swapgs` | 1 |
| `cli` | 12 | | `fxsave` | 4 | | `sti` | 1 |
| `rdmsr` | 11 | | `mov cr4` | 3 | | `pause`/`mfence`/`lidt`/`fxrstor` | je 1 |
| `ltr` | 10 | | `rdtscp` | 3 | | | |

MSRs: `EFER (0xC000_0080)`, `IA32_APIC_BASE`, `IA32_ARCH_CAPABILITIES`. CPUID-Blätter: 0, 1, 7.
Noch nicht auf x86 (laut `bringup.rs`): SMP (INIT-SIPI-SIPI), PCID/per-VSpace, Ring-3-PDs im
Kern, Loader, IOMMU-Aktivierung — deren Axiome stehen unten als **vorgemerkt**, nicht als gezählt.

**Zwei Berichtigungen an den eigenen Ergänzungen, aus dem echten Code:**

1. **Der Syscall-Mechanismus ist `int 0x80`, nicht `syscall`/`sysret`.** Kernel-Threads lösen
   `int 0x80` aus (IDT-Gate, DPL 3), weil es denselben Trap-Frame legt wie jeder Interrupt — der
   Dispatch bleibt einheitlich, und `rcx`/`r11` überleben. ERGAENZUNG §2 nahm die
   `syscall`-Konvention als gegeben. Das `entry`-Konstrukt bekommt deshalb die
   Mechanismenwahl: `entry syscall via int 0x80 …` | `via syscall` | `via svc` (aarch64) —
   **die `clobbers`-Menge folgt aus dem Mechanismus** und wird geprüft statt abgeschrieben
   (int: keine; syscall: `rcx, r11`). Die echte ABI aus `syscall.rs`/`exception::ABI_TO_GPR`:
   `nr: rax, ep: rdi, m0: rsi, m1: rdx, m2: r10, m3: r8, tag: r9`, Rückgabe in denselben sechs.
2. **FP ist `fxsave`/`fxrstor` (512-Byte-Bereich), nicht `xsave`.** ERGAENZUNG-2 §3.4 wird
   präzisiert: `FpArea` ist auf diesem Zweig der FXSAVE-Bereich; `xsave` ist die Erweiterung
   **hinter einem Feature-Zeugen** (§2).

---

## 1. Der sechste Adressraum: `port`

Die Zählung zeigt, was das MMIO-Modell übersah: **Port-IO ist auf x86 ein eigener Adressraum**
(Konsole `0x3F8`, PCI-Konfiguration `0xCF8`/`0xCFC`, PIC, PIT) — mit eigener Befehlsform
(`in`/`out`), eigener Breitenregel und ohne Abbildung im Seitenwerk.

```gabbro
device SerialCom1 at port {
    reg DATA : u8 @0x3F8 class rw
    reg LSR  : u8 @0x3FD class r fields { THRE @5, DR @0 }
}
device PciConfig at port {
    reg ADDR : u32 @0xCF8 class w
    reg DATA : u32 @0xCFC class rw
}
```

`at port` senkt Zugriffe auf `in`/`out` ab statt auf volatile Loads/Stores; `class`, `fields`,
`transition`, `keeping` gelten unverändert. Auf Architekturen ohne Port-Raum ist ein
`port`-Gerät nur unter `arch x86_64` deklarierbar (D2: kein stiller Auffang). Damit sind die
größten Fundstellenposten der Zählung (`outb`/`inb`) **Gerätesprache statt Axiome** — die
Axiomschicht schrumpft, wo ein Konstrukt trägt, und genau so herum soll die Ratsche laufen.

---

## 2. Feature-Zeugen: `Has(F)` — CPUID als Erzeuger

Laufzeit-Features (CPUID 0/1/7, `IA32_ARCH_CAPABILITIES`) sind keine `when`-Konstanten. Sie
werden **Zeugen**: die CPUID-Sonde ist der einzige Erzeuger von `ghost Has(Feature)` (affin, wie
`Vis` — Fähigkeit erlischt nicht), und jedes Axiom, dessen Befehl ein Feature voraussetzt,
verlangt den Zeugen geliehen:

```gabbro
axiom rdtscp() -> u64 requires Has(RDTSCP) effects { pure }  falsifier probe_tsc;
axiom xsave(a: ptr<normal, w> XsaveArea) requires Has(XSAVE), MayUseFp(tid)
      effects { writes a }                                    falsifier probe_fp_roundtrip;
```

Ein `rdtscp` ohne vorherige Erkennung ist damit **nicht schreibbar** — die #UD-Klasse
(Befehl auf alter CPU) wird Übersetzungsfehler. Die Erzeugerliste (Festlegung §4) wird um
`Has` ergänzt: nur die generierte CPUID-Sonde erzeugt es.

---

## 3. Der Annahmenkatalog x86_64 — vollständig gegen die Zählung

Jede Zeile: Effekt aufs Maschinenmodell, Zeugenfluss (M2-Token), Falsifikatorstatus.
**F** = Sonde fahrbar (QEMU/KVM, im Prüfgerüst), **U** = unfalsifizierbar mit Grund,
**V** = vorgemerkt (Code existiert noch nicht).

| # | Axiom | Effekt / Token | Status |
|---|---|---|---|
| A1 | `write_cr3(p)` | wechselt Wurzel, invalidiert Nicht-Global-TLB; `consumes/mints ActiveTable(p)` | F: Sonde mappt um, liest |
| A2 | `write_cr0(v)` | `PG`-Bit: `requires PaeSet, LmeSet, Cr3Set` → `mints Paging`; `WP`-Bit → `mints WriteProtect` | F: Ro-Schreibsonde muss faulten |
| A3 | `write_cr4(v)` | `PAE` → `mints PaeSet`; verbotene Übergänge als fehlende Token unformulierbar | F |
| A4 | `wrmsr_efer(v)` | `LME` → `mints LmeSet`; **`LME`-Setzen bei `PG=1` ist tokenlos unschreibbar** | F |
| A5 | `lgdt(d)` / `lidt(d)` / `ltr(s)` | lädt Deskriptortabellen; **Hardware schreibt Accessed-Bits IN die GDT** (s. §5.3) | F: Byte-Vergleich vor/nach |
| A6 | `invlpg(va)` | invalidiert einen TLB-Eintrag; Teil der Unmap-Quiesce-Folge | F: Stale-TLB-Sonde |
| A7 | `iretq(frame)` / `sysret` | typisierter Übergang (Bestand `resume`); `sysret` nur `via syscall` | F: `entry`-Sonden (E2 §5.2) |
| A8 | `int 0x80` | Gate DPL 3 legt vollständigen Trap-Frame; **keine** Clobber | F: Registerbild-Sonde |
| A9 | `cli`/`sti` | maskiert/demaskiert; `mints/consumes IrqsOff` — `sti` ohne Token unschreibbar | F |
| A10 | `hlt` | wartet auf Interrupt; nur mit `progress`-Annahme in `forever` | F: Watchdog |
| A11 | `pause` | Spin-Hinweis, semantikfrei | U: „kein beobachtbarer Effekt" |
| A12 | `in`/`out` (Raum `port`) | Geräteeffekt laut `device`-Deklaration; seriell abgesetzt | F je Gerät |
| A13 | `rdmsr`/`wrmsr` (APIC_BASE, ARCH_CAP) | je MSR ein deklarierter Effekt; unbekannte MSR-Nummer unschreibbar (D2) | F |
| A14 | `cpuid(leaf)` | rein; **einziger Erzeuger von `Has(F)`** | F: Kreuzvergleich Blatt 0/1/7 |
| A15 | `rdtsc`/`rdtscp` | monoton je Kern **nicht** garantiert — nur Messwert, nie Ordnung | U: „Invarianz ist Plattformlos" — Nutzung als Ordnung ist Übersetzungsfehler |
| A16 | `fxsave`/`fxrstor` | 512-B-Bereich, `requires MayUseFp` | F: Roundtrip-Sonde |
| A17 | `clflush` + `sfence` | Zeile ausgeschrieben; Teil der DMA-Publikationsfolge im `dma`-Raum | F: Geräte-Echo |
| A18 | `lfence`/`mfence` | Ordnungspunkte über TSO hinaus (rdtsc-Serialisierung, MMIO) | mit A19 |
| A19 | TSO / C11-Abbildung | `c11_release_acquire_x86` (Bestand E2 §4) | F: Litmus MP/SB/LB |
| A20 | `swapgs` | Kernel-GS-Basis; nur in `entry`-Emission, `requires` Eintrittskontext | F: GS-Sonde |
| A21 | Multiboot1-Vertrag | Protected Mode, `ebx` = Info-Zeiger, Header in ersten 8 KiB | F: der Boot **ist** die Sonde |
| A22 | Linker-Disjunktion | `.boot*` ⟂ `.text/.rodata`; `[__text_start,__rodata_end)` unveränderlich nach Boot | F: Linker-Map-Sonde (E2 §3.5) |
| A23 | INIT-SIPI-SIPI, ICR | SMP-Start | **V** (Zweig hat kein SMP) |
| A24 | PCID/`invpcid` | per-VSpace-TLB | **V** |
| A25 | VT-d-Aktivierung | `vtd.rs`/`dmar.rs` liegen im HAL; Übergänge sind `device`-Sprache, die Wirksamkeit (`vtd_te_effective`) bleibt Axiom | F, sobald aktiviert |

**Die Ratsche über diesem Katalog:** 22 gezählte + 3 vorgemerkte Einträge. Jeder neue Eintrag
braucht Fundstelle und Status; wächst der Katalog ohne neue Hardware-Fläche, greift
Abbruchbedingung 5. Und die Gegenrichtung ist der Erfolgsfall: A12 hat gerade die zwei größten
Befehlsposten aus der Axiomschicht in die Gerätesprache verschoben.

---

## 4. Die Mode-Leiter: verbotene Übergänge sind fehlende Token

Der Kern von §3, herausgehoben, weil er die x2APIC-Lektion verallgemeinert: **Die
Boot-Reihenfolge PAE → LME → CR3 → PG ist keine Prosa-Vorschrift, sondern ein
Token-Fluss** (M2). `write_cr0` mit PG-Bit *verlangt* `PaeSet`, `LmeSet`, `Cr3Set`; wer die
Reihenfolge bricht, hat den Token nicht und **übersetzt nicht**. Der 32-Bit-Teil des Trampolins
wird damit prüfbar, obwohl er vor der ersten „richtigen" Gabbro-Zeile liegt — weil er aus einer
Deklaration **erzeugt** wird:

---

## 5. Der Bootpfad als Sprache — gegen das echte Trampolin

Vorlage: `kernel/src/arch/x86_64/mod.rs` (`.multiboot`-Header, `_start` in `.code32`,
Seitentabellenbau, CR-Leiter, `retf` → `long_mode`, `.bss`-Nullung, `call x86_rust_entry`).

### 5.1 Das `boot`-Konstrukt

```ebnf
bootdecl = "boot" ident "arch" ident "{"
             { "step" ( axiomcall | ident "=" constexpr ) ";" }
             "dispatch" path ";"
           "}" ;
```

```gabbro
boot multiboot1 arch x86_64 {
    step stack   = boot_stack_top;            -- esp laden
    step save_bootinfo(ebx);                   -- Multiboot-Zeiger retten
    step load_tables(BOOT_IDENTITY);           -- §5.2: VORBERECHNET, kein rep stosd
    step write_cr3(BOOT_IDENTITY.root);        -- mints Cr3Set
    step write_cr4(PAE);                       -- mints PaeSet
    step wrmsr_efer(LME);                      -- mints LmeSet
    step write_cr0(PG);                        -- requires alle drei -> mints Paging
    step load_gdt(GDT64); step far_return(CODE64);
    step zero_bss(__bss_start, __bss_end);     -- erzeugt, aus Linker-Symbolen
    dispatch caprock::x86_rust_entry;          -- erste Gabbro-Funktion; mints BootPhase
}
```

**Der Emittent ist dieselbe eine `iasm`-Stelle** wie bei `entry`; der Prüfer prüft den
Token-Fluss der Leiter (§4) **vor** der Emission. Nach `dispatch` gilt: `BootPhase` existiert,
jede `raw fn` ist erreichbar, und der Drei-Schichten-Satz (E1 §3) übernimmt. Der `hlt`-Fänger
nach der Rückkehr ist `divergent` und wird miterzeugt.

### 5.2 Die Boot-Seitentabellen sind Daten, kein Code

Das echte Trampolin **baut** die Identitätsabbildung zur Laufzeit (`rep stosd`, Schleife über
512 PD-Einträge). Die Abbildung ist aber **konstant**: 1 GiB identisch, 2-MiB-Seiten,
`present|writable|PS`. In Gabbro ist sie ein `const` vom `walk`-Typ, **zur Übersetzungszeit
ausgerechnet** und nach `.boot.data` gelegt — `step load_tables` lädt nur noch. Weniger
Zone-0-Befehle, und die Abbildung selbst ist M1/`walk`-geprüft statt handgeschriebene
Bitarithmetik in 32-Bit-Assembler. (Die Verschiebung der physischen Basis ist Link-Zeit-Arbeit:
Linker-Symbole sind `extern`-Konstanten, A22.)

### 5.3 Die GDT-Lektion aus dem echten Code — als Platzierungsregel

Der Zweig dokumentiert einen bezahlten Fund: **die CPU schreibt beim Laden eines
Segmentregisters das Accessed-Bit in den Deskriptor** — die GDT muss beschreibbar liegen, sonst
#PF unter `WP=1`, und ein Accessed-Bit in `.rodata` hätte den Code-Hash (A-1.3) lauffremd
gemacht. Das ist jetzt Axiom **A5** plus eine **Platzierungsregel**: die GDT/IDT/TSS-Deklaration
ist ein `format` im `normal`-Raum mit Pflichtrecht `w`; eine Platzierung in einem `r`-Abschnitt
ist ein **Übersetzungsfehler**. Die Falle ist damit unschreibbar statt gut kommentiert.

### 5.4 Multiboot-Info ist ein `format`

Der gerettete `ebx`-Zeiger ist klassische **unvertraute Eingabe**: `format Multiboot1Info` mit
Flags-Feld, bedingtem Speicherplan (`mmap_length`/`mmap_addr` mit `offset_into`-Bindung) und
benannten Absagen (`reason MbAbsage { keine_mmap = 1 "…", … }`). Der Rückfall
`RAM_END_FALLBACK` aus `bringup.rs` wird ein benannter Absage-Zweig statt einer stillen
Konstante.

### 5.5 Der vollständige Boot-Satz, erweitert

Zu den drei Schichten (S1 Typen, S2 Verweise, S3 Abbildung+Sonde) kommt die vierte Zeile, die
der echte Zweig verlangt: **S0 — die Zone vor der ersten Gabbro-Funktion ist erzeugt, nicht
geschrieben.** Ihr Inhalt ist die `boot`-Deklaration; ihr Vertrauen ist die eine Emissionsstelle
plus die Token-Leiter im Prüfer; ihr Falsifikator ist der Boot selbst (A21) plus die
Abschnittssonde (S3). **Und S3 wird um den Identitätsabbau ergänzt:** nach `mmu::init_primary`
muss auch die 1-GiB-Identitätsabbildung fallen, nicht nur `.boot` — die Nachbedingung heißt
vollständig: `!exists m in mappings of kernel_root: m.section == boot || m.identity`.

---

## 6. Abnahme dieser dritten Ergänzung

1. **Katalog gegen Zählung:** jedes Axiom A1–A22 hat eine Fundstelle im Zweig; jeder gezählte
   Befehl hat ein Axiom oder ein Konstrukt (A12!). Ein Befehl ohne Zeile oder eine Zeile ohne
   Befehl ist ein Fehler dieser Ergänzung.
2. **Die Mode-Leiter als Sprechprobe:** ein `boot`-Block mit vertauschtem `write_cr0(PG)` vor
   `wrmsr_efer(LME)` muss die Übersetzung brechen (fehlender Token), der echte muss durchgehen.
3. **`entry via int 0x80`** gegen `exception::ABI_TO_GPR` gehalten — Registerliste identisch,
   sonst ist §0.1 falsch abgeschrieben.
4. **Die vorberechneten Boot-Tabellen** byteidentisch gegen das, was das heutige Trampolin zur
   Laufzeit baut (einmalige Dump-Sonde in QEMU).
5. Aufnahme in die Wiederholungsmessung P0: die Bootstrecke und die Port-IO-Fundstellen zählen
   mit — die Klassen „Eintritt" und „Boot" dürfen danach keine hängende Klempnerei mehr führen.
